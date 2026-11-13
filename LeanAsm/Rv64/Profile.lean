import LeanAsm.Rv64.Program

/-!
# RV64 instruction profiles

Profiles describe consumer policy without introducing another instruction
inductive. New LeanAsm instructions are unsupported by an existing profile
until their opcode is explicitly added to its allow-list.
-/

namespace LeanAsm.Rv64

inductive Opcode where
  | ADD | SUB | SLL | SRL | SRA | AND | OR | XOR | SLT | SLTU | ADDW | SUBW
  | ADDI | ANDI | ORI | XORI | SLTI | SLTIU | SLLI | SRLI | SRAI
  | ADDIW | SLLIW | SRLIW | LUI | AUIPC
  | LB | LH | LW | LD | LBU | LHU | LWU | SB | SH | SW | SD
  | BEQ | BNE | BLT | BGE | BLTU | BGEU | JAL | JALR
  | MUL | MULH | MULHSU | MULHU | DIV | DIVU | REM | REMU | FENCE
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace Opcode

def all : List Opcode :=
  [.ADD, .SUB, .SLL, .SRL, .SRA, .AND, .OR, .XOR, .SLT, .SLTU, .ADDW, .SUBW,
   .ADDI, .ANDI, .ORI, .XORI, .SLTI, .SLTIU, .SLLI, .SRLI, .SRAI,
   .ADDIW, .SLLIW, .SRLIW, .LUI, .AUIPC,
   .LB, .LH, .LW, .LD, .LBU, .LHU, .LWU, .SB, .SH, .SW, .SD,
   .BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU, .JAL, .JALR,
   .MUL, .MULH, .MULHSU, .MULHU, .DIV, .DIVU, .REM, .REMU, .FENCE]

end Opcode

def Instr.opcode : Instr → Opcode
  | .ADD .. => .ADD | .SUB .. => .SUB | .SLL .. => .SLL
  | .SRL .. => .SRL | .SRA .. => .SRA | .AND .. => .AND
  | .OR .. => .OR | .XOR .. => .XOR | .SLT .. => .SLT
  | .SLTU .. => .SLTU | .ADDW .. => .ADDW | .SUBW .. => .SUBW
  | .ADDI .. => .ADDI | .ANDI .. => .ANDI | .ORI .. => .ORI
  | .XORI .. => .XORI | .SLTI .. => .SLTI | .SLTIU .. => .SLTIU
  | .SLLI .. => .SLLI | .SRLI .. => .SRLI | .SRAI .. => .SRAI
  | .ADDIW .. => .ADDIW | .SLLIW .. => .SLLIW | .SRLIW .. => .SRLIW
  | .LUI .. => .LUI | .AUIPC .. => .AUIPC
  | .LB .. => .LB | .LH .. => .LH | .LW .. => .LW | .LD .. => .LD
  | .LBU .. => .LBU | .LHU .. => .LHU | .LWU .. => .LWU
  | .SB .. => .SB | .SH .. => .SH | .SW .. => .SW | .SD .. => .SD
  | .BEQ .. => .BEQ | .BNE .. => .BNE | .BLT .. => .BLT
  | .BGE .. => .BGE | .BLTU .. => .BLTU | .BGEU .. => .BGEU
  | .JAL .. => .JAL | .JALR .. => .JALR
  | .MUL .. => .MUL | .MULH .. => .MULH | .MULHSU .. => .MULHSU
  | .MULHU .. => .MULHU | .DIV .. => .DIV | .DIVU .. => .DIVU
  | .REM .. => .REM | .REMU .. => .REMU | .FENCE => .FENCE

structure IsaProfile where
  allowed : List Opcode
  deriving Repr

namespace IsaProfile

def rv64im : IsaProfile := ⟨Opcode.all⟩

def Supports (profile : IsaProfile) (instruction : Instr) : Prop :=
  instruction.opcode ∈ profile.allowed

def supports (profile : IsaProfile) (instruction : Instr) : Bool :=
  profile.allowed.contains instruction.opcode

@[simp] theorem supports_eq_true (profile : IsaProfile) (instruction : Instr) :
    profile.supports instruction = true ↔ profile.Supports instruction :=
  List.contains_iff_mem

instance (profile : IsaProfile) (instruction : Instr) :
    Decidable (profile.Supports instruction) :=
  decidable_of_iff (profile.supports instruction = true)
    (profile.supports_eq_true instruction)

end IsaProfile

namespace Program

def Conforms (profile : IsaProfile) (program : Program) : Prop :=
  ∀ instruction ∈ program, profile.Supports instruction

instance (profile : IsaProfile) (program : Program) :
    Decidable (Conforms profile program) := by
  classical
  unfold Conforms
  infer_instance

end Program

end LeanAsm.Rv64
