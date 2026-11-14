import LeanAsm.X64.State

namespace LeanAsm.X64

private def multiplyFlags (overflow : Bool) : Flags :=
  { Flags.undefined with cf := some overflow, of := some overflow }

private def product (signed : Bool) (size : Size) (a b : Word) : Int :=
  if signed then size.signed a * size.signed b
  else Int.ofNat ((size.trim a).toNat * (size.trim b).toNat)

private def productOverflow (signed : Bool) (size : Size) (value : Int) : Bool :=
  if signed then decide (value < -(2 ^ (size.bits - 1)) ∨ 2 ^ (size.bits - 1) ≤ value)
  else decide (2 ^ size.bits ≤ value)

def execMultiply (signed : Bool) (size : Size) (source : RM) (state : State) :
    Except Error State := do
  let rhs ← source.read size state state.rip
  let value := product signed size (state.getReg .rax) rhs
  let full := BitVec.ofInt (2 * size.bits) value
  let low := BitVec.ofNat 64 full.toNat
  let high := BitVec.ofNat 64 (full.toNat / 2 ^ size.bits)
  let updated := if size == .b8 then state.writeReg .b16 .rax low
    else (state.writeReg size .rax low).writeReg size .rdx high
  return { updated with flags := multiplyFlags (productOverflow signed size value) }

def execImul (size : Size) (dst : Reg) (source : RM) (state : State) :
    Except Error State := do
  let rhs ← source.read size state state.rip
  let value := product true size (state.getReg dst) rhs
  return { state.writeReg size dst (BitVec.ofInt 64 value) with
    flags := multiplyFlags (productOverflow true size value) }

private def dividend (size : Size) (state : State) : BitVec (2 * size.bits) :=
  let n := if size == .b8 then (Size.b16.trim (state.getReg .rax)).toNat else
    (size.trim (state.getReg .rdx)).toNat * 2 ^ size.bits +
      (size.trim (state.getReg .rax)).toNat
  BitVec.ofNat (2 * size.bits) n

private def divide (signed : Bool) (size : Size) (state : State) (divisor : Word) :
    Except Error (Word × Word) := do
  if divisor == 0 then throw .divisionError
  let numerator := dividend size state
  if signed then
    let q := numerator.toInt.tdiv (size.signed divisor)
    let r := numerator.toInt.tmod (size.signed divisor)
    unless -(2 ^ (size.bits - 1)) ≤ q && q < 2 ^ (size.bits - 1) do throw .divisionError
    return (BitVec.ofInt 64 q, BitVec.ofInt 64 r)
  else
    let q := numerator.toNat / divisor.toNat
    unless q < 2 ^ size.bits do throw .divisionError
    return (BitVec.ofNat 64 q, BitVec.ofNat 64 (numerator.toNat % divisor.toNat))

def execDivide (signed : Bool) (size : Size) (source : RM) (state : State) :
    Except Error State := do
  let divisor ← source.read size state state.rip
  let (quotient, remainder) ← divide signed size state divisor
  let updated := if size == .b8 then
      state.writeReg .b16 .rax ((Size.b8.trim quotient) ||| ((Size.b8.trim remainder) <<< 8))
    else (state.writeReg size .rax quotient).writeReg size .rdx remainder
  return { updated with flags := Flags.undefined }

end LeanAsm.X64
