import Std

/-!
# RV64IM core syntax

A runtime-neutral typed representation of real RV64IM instructions. Pseudo
instructions, labels, sections, and relocations live outside `Instr`, so one
`Instr` always denotes one 32-bit machine instruction.
-/

namespace LeanAsm.Rv64

abbrev Word := BitVec 64

def signExtend12 (value : BitVec 12) : Word := value.signExtend 64
def signExtend13 (value : BitVec 13) : Word := value.signExtend 64
def signExtend21 (value : BitVec 21) : Word := value.signExtend 64

inductive Reg where
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30 | x31
  deriving DecidableEq, BEq, Repr, Hashable

namespace Reg

def toNat : Reg → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3
  | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .x10 => 10 | .x11 => 11
  | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x18 => 18 | .x19 => 19
  | .x20 => 20 | .x21 => 21 | .x22 => 22 | .x23 => 23
  | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27
  | .x28 => 28 | .x29 => 29 | .x30 => 30 | .x31 => 31

theorem toNat_lt (r : Reg) : r.toNat < 32 := by
  cases r <;> decide

def toFin (r : Reg) : Fin 32 := ⟨r.toNat, r.toNat_lt⟩

instance : ToString Reg := ⟨fun r => s!"x{r.toNat}"⟩

-- Standard integer-register ABI names.
abbrev zero := x0
abbrev ra := x1
abbrev sp := x2
abbrev gp := x3
abbrev tp := x4
abbrev t0 := x5
abbrev t1 := x6
abbrev t2 := x7
abbrev s0 := x8
abbrev fp := x8
abbrev s1 := x9
abbrev a0 := x10
abbrev a1 := x11
abbrev a2 := x12
abbrev a3 := x13
abbrev a4 := x14
abbrev a5 := x15
abbrev a6 := x16
abbrev a7 := x17
abbrev s2 := x18
abbrev s3 := x19
abbrev s4 := x20
abbrev s5 := x21
abbrev s6 := x22
abbrev s7 := x23
abbrev s8 := x24
abbrev s9 := x25
abbrev s10 := x26
abbrev s11 := x27
abbrev t3 := x28
abbrev t4 := x29
abbrev t5 := x30
abbrev t6 := x31

end Reg

/-- Real, fixed-width instructions used by the current LeanAsm consumers.
    Environment calls and implementation-specific accelerators are deliberately
    absent from the portable core. -/
inductive Instr where
  | ADD (rd rs1 rs2 : Reg)
  | SUB (rd rs1 rs2 : Reg)
  | SLL (rd rs1 rs2 : Reg)
  | SRL (rd rs1 rs2 : Reg)
  | SRA (rd rs1 rs2 : Reg)
  | AND (rd rs1 rs2 : Reg)
  | OR (rd rs1 rs2 : Reg)
  | XOR (rd rs1 rs2 : Reg)
  | SLT (rd rs1 rs2 : Reg)
  | SLTU (rd rs1 rs2 : Reg)
  | ADDW (rd rs1 rs2 : Reg)
  | SUBW (rd rs1 rs2 : Reg)
  | ADDI (rd rs1 : Reg) (imm : BitVec 12)
  | ANDI (rd rs1 : Reg) (imm : BitVec 12)
  | ORI (rd rs1 : Reg) (imm : BitVec 12)
  | XORI (rd rs1 : Reg) (imm : BitVec 12)
  | SLTI (rd rs1 : Reg) (imm : BitVec 12)
  | SLTIU (rd rs1 : Reg) (imm : BitVec 12)
  | SLLI (rd rs1 : Reg) (shamt : BitVec 6)
  | SRLI (rd rs1 : Reg) (shamt : BitVec 6)
  | SRAI (rd rs1 : Reg) (shamt : BitVec 6)
  | ADDIW (rd rs1 : Reg) (imm : BitVec 12)
  | SLLIW (rd rs1 : Reg) (shamt : BitVec 5)
  | SRLIW (rd rs1 : Reg) (shamt : BitVec 5)
  | LUI (rd : Reg) (imm : BitVec 20)
  | AUIPC (rd : Reg) (imm : BitVec 20)
  | LB (rd rs1 : Reg) (offset : BitVec 12)
  | LH (rd rs1 : Reg) (offset : BitVec 12)
  | LW (rd rs1 : Reg) (offset : BitVec 12)
  | LD (rd rs1 : Reg) (offset : BitVec 12)
  | LBU (rd rs1 : Reg) (offset : BitVec 12)
  | LHU (rd rs1 : Reg) (offset : BitVec 12)
  | LWU (rd rs1 : Reg) (offset : BitVec 12)
  | SB (rs1 rs2 : Reg) (offset : BitVec 12)
  | SH (rs1 rs2 : Reg) (offset : BitVec 12)
  | SW (rs1 rs2 : Reg) (offset : BitVec 12)
  | SD (rs1 rs2 : Reg) (offset : BitVec 12)
  | BEQ (rs1 rs2 : Reg) (offset : BitVec 13)
  | BNE (rs1 rs2 : Reg) (offset : BitVec 13)
  | BLT (rs1 rs2 : Reg) (offset : BitVec 13)
  | BGE (rs1 rs2 : Reg) (offset : BitVec 13)
  | BLTU (rs1 rs2 : Reg) (offset : BitVec 13)
  | BGEU (rs1 rs2 : Reg) (offset : BitVec 13)
  | JAL (rd : Reg) (offset : BitVec 21)
  | JALR (rd rs1 : Reg) (offset : BitVec 12)
  | MUL (rd rs1 rs2 : Reg)
  | MULH (rd rs1 rs2 : Reg)
  | MULHSU (rd rs1 rs2 : Reg)
  | MULHU (rd rs1 rs2 : Reg)
  | DIV (rd rs1 rs2 : Reg)
  | DIVU (rd rs1 rs2 : Reg)
  | REM (rd rs1 rs2 : Reg)
  | REMU (rd rs1 rs2 : Reg)
  | FENCE
  deriving DecidableEq, BEq, Repr

def Instr.isControl : Instr → Bool
  | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU ..
  | .JAL .. | .JALR .. => true
  | _ => false

inductive Trap where
  | memoryBounds
  | memoryMisaligned
  | readOnlyMemory
  | invalidMemory
  | unsupportedWidth
  | instructionBounds
  | instructionMisaligned
  | invalidProgram
  | fuelExhausted
  deriving DecidableEq, BEq, Repr

end LeanAsm.Rv64
