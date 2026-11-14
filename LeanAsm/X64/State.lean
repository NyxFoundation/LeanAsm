import LeanAsm.X64.Memory
import LeanAsm.X64.Flags
import LeanAsm.X64.Encoding

namespace LeanAsm.X64

structure State where
  regs : Vector Word 16 := Vector.replicate 16 0
  rip : Word := 0
  flags : Flags := {}
  memory : Memory := {}
  deriving Repr

def State.getReg (state : State) (reg : Reg) : Word :=
  state.regs[reg.toNat]'reg.toNat_lt

def State.setReg (state : State) (reg : Reg) (value : Word) : State :=
  { state with regs := state.regs.set reg.toNat value reg.toNat_lt }

def State.writeReg (state : State) (size : Size) (reg : Reg) (value : Word) : State :=
  let result := size.trim value
  state.setReg reg (if size == .b8 || size == .b16 then
    (state.getReg reg &&& ~~~size.mask) ||| result else result)

def Address.eval (address : Address) (state : State) (nextRip : Word) : Word :=
  match address with
  | .base reg disp => state.getReg reg + disp.signExtend 64
  | .indexed baseReg index scale disp =>
      (baseReg.map state.getReg).getD 0 +
        state.getReg index * BitVec.ofNat 64 scale.factor + disp.signExtend 64
  | .rip disp => nextRip + disp.signExtend 64

def RM.read (source : RM) (size : Size) (state : State) (nextRip : Word) :
    Except Error Word :=
  match source with
  | .reg register => .ok (size.trim (state.getReg register))
  | .mem address => state.memory.load size (address.eval state nextRip)

/-- A typed instruction image, not a decoder for arbitrary bytes. Fetch accepts
    only the boundaries derived from the encoder. Code cannot be modified. -/
structure Image where
  base : Word
  code : Program
  deriving Repr

def Image.valid (image : Image) (memory : Memory) : Bool :=
  match encodeProgram image.code with
  | .error _ => false
  | .ok bytes =>
      let endAddr := image.base.toNat + bytes.size
      memory.valid && !image.code.isEmpty && decide (endAddr ≤ 2 ^ 64) &&
        memory.regions.all (fun r => !r.writable ||
          decide (r.endAddr ≤ image.base.toNat ∨ endAddr ≤ r.base.toNat))

private def fetchAt (offset : Nat) : Program → Nat → Except Error Instr
  | [], _ => .error .instructionBounds
  | instruction :: rest, current => do
      if current == offset then return instruction
      let size ← instruction.byteSize
      fetchAt offset rest (current + size)

def Image.fetch (image : Image) (rip : Word) : Except Error Instr :=
  if rip.toNat < image.base.toNat then .error .instructionBounds
  else fetchAt (rip.toNat - image.base.toNat) image.code 0

end LeanAsm.X64
