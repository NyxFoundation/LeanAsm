import LeanAsm.Rv64.Program

/-! Deterministic GNU-as rendering for real instructions only. -/

namespace LeanAsm.Rv64

private def reg (r : Reg) : String := s!"x{r.toNat}"

private def rrr (op : String) (d a b : Reg) : String :=
  s!"{op} {reg d}, {reg a}, {reg b}"

private def rri (op : String) (d a : Reg) (n : Int) : String :=
  s!"{op} {reg d}, {reg a}, {n}"

private def rriU (op : String) (d a : Reg) (n : Nat) : String :=
  s!"{op} {reg d}, {reg a}, {n}"

private def load (op : String) (d a : Reg) (n : Int) : String :=
  s!"{op} {reg d}, {n}({reg a})"

private def store (op : String) (a b : Reg) (n : Int) : String :=
  s!"{op} {reg b}, {n}({reg a})"

private def branch (op : String) (a b : Reg) (n : Int) : String :=
  s!"{op} {reg a}, {reg b}, . + {n}"

def emitInstr : Instr → String
  | .ADD d a b => rrr "add" d a b
  | .SUB d a b => rrr "sub" d a b
  | .SLL d a b => rrr "sll" d a b
  | .SRL d a b => rrr "srl" d a b
  | .SRA d a b => rrr "sra" d a b
  | .AND d a b => rrr "and" d a b
  | .OR d a b => rrr "or" d a b
  | .XOR d a b => rrr "xor" d a b
  | .SLT d a b => rrr "slt" d a b
  | .SLTU d a b => rrr "sltu" d a b
  | .ADDW d a b => rrr "addw" d a b
  | .SUBW d a b => rrr "subw" d a b
  | .ADDI d a n => rri "addi" d a n.toInt
  | .ANDI d a n => rri "andi" d a n.toInt
  | .ORI d a n => rri "ori" d a n.toInt
  | .XORI d a n => rri "xori" d a n.toInt
  | .SLTI d a n => rri "slti" d a n.toInt
  | .SLTIU d a n => rri "sltiu" d a n.toInt
  | .SLLI d a n => rriU "slli" d a n.toNat
  | .SRLI d a n => rriU "srli" d a n.toNat
  | .SRAI d a n => rriU "srai" d a n.toNat
  | .ADDIW d a n => rri "addiw" d a n.toInt
  | .SLLIW d a n => rriU "slliw" d a n.toNat
  | .SRLIW d a n => rriU "srliw" d a n.toNat
  | .LUI d n => s!"lui {reg d}, {n.toNat}"
  | .AUIPC d n => s!"auipc {reg d}, {n.toNat}"
  | .LB d a n => load "lb" d a n.toInt
  | .LH d a n => load "lh" d a n.toInt
  | .LW d a n => load "lw" d a n.toInt
  | .LD d a n => load "ld" d a n.toInt
  | .LBU d a n => load "lbu" d a n.toInt
  | .LHU d a n => load "lhu" d a n.toInt
  | .LWU d a n => load "lwu" d a n.toInt
  | .SB a b n => store "sb" a b n.toInt
  | .SH a b n => store "sh" a b n.toInt
  | .SW a b n => store "sw" a b n.toInt
  | .SD a b n => store "sd" a b n.toInt
  | .BEQ a b n => branch "beq" a b n.toInt
  | .BNE a b n => branch "bne" a b n.toInt
  | .BLT a b n => branch "blt" a b n.toInt
  | .BGE a b n => branch "bge" a b n.toInt
  | .BLTU a b n => branch "bltu" a b n.toInt
  | .BGEU a b n => branch "bgeu" a b n.toInt
  | .JAL d n => s!"jal {reg d}, . + {n.toInt}"
  | .JALR d a n => s!"jalr {reg d}, {n.toInt}({reg a})"
  | .MUL d a b => rrr "mul" d a b
  | .MULH d a b => rrr "mulh" d a b
  | .MULHSU d a b => rrr "mulhsu" d a b
  | .MULHU d a b => rrr "mulhu" d a b
  | .DIV d a b => rrr "div" d a b
  | .DIVU d a b => rrr "divu" d a b
  | .REM d a b => rrr "rem" d a b
  | .REMU d a b => rrr "remu" d a b
  | .FENCE => "fence"

def emitProgram (name : String) (code : Program) : String :=
  ".option norvc\n.option norelax\n.attribute arch, \"rv64im\"\n" ++
    ".text\n.balign 4\n" ++ s!".globl {name}\n.type {name}, @function\n{name}:\n" ++
    String.join (code.map (fun i => s!"  {emitInstr i}\n")) ++
    s!".size {name}, . - {name}\n.section .note.GNU-stack,\"\",@progbits\n"

end LeanAsm.Rv64
