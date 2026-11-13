import LeanAsm.Rv64.Memory

namespace LeanAsm.Rv64

structure State where
  regs : Vector Word 32 := Vector.replicate 32 0
  pc : Word
  memory : Memory := {}
  deriving Repr

def State.getReg (s : State) (r : Reg) : Word :=
  if r = .x0 then 0 else s.regs[r.toNat]'r.toNat_lt

def State.setReg (s : State) (r : Reg) (value : Word) : State :=
  if r = .x0 then s
  else { s with regs := s.regs.set r.toNat value r.toNat_lt }

def State.advance (s : State) : State :=
  { s with pc := s.pc + 4 }

/-- A fixed-width program placed at a concrete address for instruction fetch. -/
structure Image where
  base : Word
  code : Array Instr
  deriving Repr

def Image.endAddr (p : Image) : Nat :=
  p.base.toNat + 4 * p.code.size

def Image.valid (p : Image) (memory : Memory) : Bool :=
  memory.valid &&
    decide (p.base.toNat % 4 = 0 ∧ 0 < p.code.size ∧ p.endAddr ≤ 2 ^ 64) &&
    memory.regions.all (fun r =>
      !r.writable ||
        decide (r.endAddr ≤ p.base.toNat ∨ p.endAddr ≤ r.base.toNat))

def Image.fetch (p : Image) (pc : Word) : Except Trap Instr := do
  unless pc.toNat % 4 == 0 do throw .instructionMisaligned
  unless p.base.toNat ≤ pc.toNat do throw .instructionBounds
  let offset := (pc.toNat - p.base.toNat) / 4
  if h : offset < p.code.size then
    return p.code[offset]
  else
    throw .instructionBounds

end LeanAsm.Rv64
