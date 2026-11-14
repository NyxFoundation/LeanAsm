import LeanAsm.X64.Basic

namespace LeanAsm.X64

/-- None means architecturally undefined, not false. Consumers of an undefined
    flag trap rather than silently choosing a hardware-dependent value. -/
structure Flags where
  cf : Option Bool := some false
  pf : Option Bool := some false
  af : Option Bool := some false
  zf : Option Bool := some false
  sf : Option Bool := some false
  of : Option Bool := some false
  deriving DecidableEq, BEq, Repr

def Flags.undefined : Flags := ⟨none, none, none, none, none, none⟩

def requireFlag : Option Bool → Except Error Bool
  | some value => .ok value
  | none => .error .undefinedFlag

def Cond.eval (cond : Cond) (flags : Flags) : Except Error Bool := do
  match cond with
  | .o => requireFlag flags.of | .no => return !(← requireFlag flags.of)
  | .b => requireFlag flags.cf | .ae => return !(← requireFlag flags.cf)
  | .e => requireFlag flags.zf | .ne => return !(← requireFlag flags.zf)
  | .s => requireFlag flags.sf | .ns => return !(← requireFlag flags.sf)
  | .p => requireFlag flags.pf | .np => return !(← requireFlag flags.pf)
  | .be | .a =>
      let cf ← requireFlag flags.cf
      let zf ← requireFlag flags.zf
      return if cond == .be then cf || zf else !(cf || zf)
  | .l | .ge | .le | .g =>
      let sf ← requireFlag flags.sf
      let of ← requireFlag flags.of
      let less := sf != of
      if cond == .l then return less
      if cond == .ge then return !less
      let zf ← requireFlag flags.zf
      return if cond == .le then zf || less else !(zf || less)

def resultFlags (size : Size) (value : Word) : Flags :=
  let result := size.trim value
  let parity := (List.range 8).foldl (fun n i => n + (result.toNat / 2 ^ i) % 2) 0
  { Flags.undefined with
    pf := some (parity % 2 == 0)
    zf := some (result == 0)
    sf := some (result.getLsbD (size.bits - 1)) }

def arithmetic (size : Size) (subtract : Bool) (a b : Word) (carry : Bool) :
    Word × Flags :=
  let x := (size.trim a).toNat
  let y := (size.trim b).toNat
  let c := if carry then 1 else 0
  let result := size.trim (if subtract then a - b - BitVec.ofNat 64 c
    else a + b + BitVec.ofNat 64 c)
  let signed := if subtract then size.signed a - size.signed b - Int.ofNat c
    else size.signed a + size.signed b + Int.ofNat c
  let bound : Int := 2 ^ (size.bits - 1)
  (result, { resultFlags size result with
    cf := some (if subtract then x < y + c else x + y + c ≥ 2 ^ size.bits)
    af := some (if subtract then x % 16 < y % 16 + c else x % 16 + y % 16 + c ≥ 16)
    of := some (decide (signed < -bound ∨ bound ≤ signed)) })

def logical (size : Size) (value : Word) : Word × Flags :=
  (size.trim value, { resultFlags size value with cf := some false, of := some false })

private def rotation (op : ShiftOp) (size : Size) (value : Word)
    (count : Nat) (flags : Flags) : Word × Flags :=
  let n := count % size.bits
  let x := size.trim value
  let result := size.trim (if op == .rol then
    (x <<< n) ||| (x >>> (size.bits - n)) else
    (x >>> n) ||| (x <<< (size.bits - n)))
  let cf := if op == .rol then result.getLsbD 0 else result.getLsbD (size.bits - 1)
  let overflow := if op == .rol then result.getLsbD (size.bits - 1) != cf
    else result.getLsbD (size.bits - 1) != result.getLsbD (size.bits - 2)
  (result, { flags with cf := some cf, of := if count == 1 then some overflow else none })

def shiftResult (op : ShiftOp) (size : Size) (value : Word)
    (rawCount : Nat) (flags : Flags) : Word × Flags :=
  let count := rawCount % (if size == .b64 then 64 else 32)
  let x := size.trim value
  if count == 0 then (x, flags)
  else if op == .rol || op == .ror then rotation op size x count flags
  else
    let result := size.trim (match op with
      | .shl => x <<< count
      | .shr => x >>> count
      | .sar => BitVec.ofInt 64 (size.signed x / (2 ^ count))
      | _ => x)
    let cf := if op == .sar then some (x.getLsbD (min count size.bits - 1))
      else if count ≥ size.bits then none
      else some (x.getLsbD (if op == .shl then size.bits - count else count - 1))
    let overflow := match op with
      | .shl => (cf.map fun carry => result.getLsbD (size.bits - 1) != carry)
      | .shr => some (x.getLsbD (size.bits - 1))
      | _ => some false
    (result, { resultFlags size result with
      cf := cf
      of := if count == 1 then overflow else none })

end LeanAsm.X64
