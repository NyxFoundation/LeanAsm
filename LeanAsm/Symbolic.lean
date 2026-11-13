import LeanAsm.Rv64.Basic

/-!
# Symbolic GNU assembly

Labels, sections, data, and variable-width pseudo instructions are kept
separate from `Rv64.Instr`. This layer is useful for source emission but is
not yet part of the fixed-width execution semantics.
-/

namespace LeanAsm.Symbolic

open LeanAsm.Rv64

inductive RR where
  | add | sub | mul | div | divu | rem | remu | sltu | slt
  | sll | srl | sra | bitAnd | bitOr | bitXor | addw | subw
  deriving Repr, BEq

inductive RI where
  | addi | andi | ori | xori | slti | sltiu | addiw
  deriving Repr, BEq

inductive Shift where
  | slli | srli | srai | slliw | srliw
  deriving Repr, BEq

inductive Load where
  | ld | lw | lwu | lh | lhu | lb | lbu
  deriving Repr, BEq

inductive Store where
  | sd | sw | sh | sb
  deriving Repr, BEq

inductive Branch where
  | eq | ne | lt | ge | ltu | geu
  deriving Repr, BEq

inductive Line where
  | rr (op : RR) (rd rs1 rs2 : Reg)
  | ri (op : RI) (rd rs : Reg) (imm : Int)
  | shift (op : Shift) (rd rs : Reg) (amount : Nat)
  | load (op : Load) (rd base : Reg) (offset : Int)
  | store (op : Store) (src base : Reg) (offset : Int)
  | mv (rd rs : Reg)
  | li (rd : Reg) (value : Int)
  | branch (op : Branch) (rs1 rs2 : Reg) (target : String)
  | jump (target : String)
  | call (target : String)
  | la (rd : Reg) (symbol : String)
  | ret
  | label (name : String)
  | function (name : String)
  | endFunction (name : String)
  | text
  | rodata
  | align (power : Nat)
  | word (value : UInt32)
  | bytes (values : List UInt8)
  deriving Repr

abbrev Program := List Line

private def emitRR : RR → String
  | .bitAnd => "and" | .bitOr => "or" | .bitXor => "xor"
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .div => "div" | .divu => "divu" | .rem => "rem" | .remu => "remu"
  | .sltu => "sltu" | .slt => "slt"
  | .sll => "sll" | .srl => "srl" | .sra => "sra"
  | .addw => "addw" | .subw => "subw"

private def emitRI : RI → String
  | .addi => "addi" | .andi => "andi" | .ori => "ori"
  | .xori => "xori" | .slti => "slti" | .sltiu => "sltiu"
  | .addiw => "addiw"

private def emitShift : Shift → String
  | .slli => "slli" | .srli => "srli" | .srai => "srai"
  | .slliw => "slliw" | .srliw => "srliw"

private def emitLoad : Load → String
  | .ld => "ld" | .lw => "lw" | .lwu => "lwu"
  | .lh => "lh" | .lhu => "lhu" | .lb => "lb" | .lbu => "lbu"

private def emitStore : Store → String
  | .sd => "sd" | .sw => "sw" | .sh => "sh" | .sb => "sb"

private def emitBranch : Branch → String
  | .eq => "beq" | .ne => "bne" | .lt => "blt"
  | .ge => "bge" | .ltu => "bltu" | .geu => "bgeu"

def validSymbol (s : String) : Bool :=
  let chars := s.toList
  !chars.isEmpty &&
    chars.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_')) &&
    !(chars.head!).isDigit

private def symbol (s : String) : Except String String :=
  if validSymbol s then .ok s else .error "invalid assembly symbol"

private def immediate (n : Int) : Except String String :=
  if -2048 ≤ n && n ≤ 2047 then .ok (toString n)
  else .error "instruction immediate is outside the signed 12-bit range"

private def emitMemory (op : String) (r base : Reg) (off : Int) :
    Except String String := do
  return s!"  {op} {r}, {← immediate off}({base})"

def emitLine : Line → Except String String
  | .rr op d a b => .ok s!"  {emitRR op} {d}, {a}, {b}"
  | .ri op d s n => do return s!"  {emitRI op} {d}, {s}, {← immediate n}"
  | .shift op d s n =>
      if n < (if op == .slliw || op == .srliw then 32 else 64) then
        .ok s!"  {emitShift op} {d}, {s}, {n}"
      else .error "shift amount is outside the instruction range"
  | .load op d b n => emitMemory (emitLoad op) d b n
  | .store op s b n => emitMemory (emitStore op) s b n
  | .mv d s => .ok s!"  mv {d}, {s}"
  | .li d n =>
      if -(2 ^ 63 : Int) ≤ n && n < 2 ^ 64 then .ok s!"  li {d}, {n}"
      else .error "constant does not fit in a 64-bit register"
  | .branch op a b label => do
      return s!"  {emitBranch op} {a}, {b}, {← symbol label}"
  | .jump label => do return s!"  j {← symbol label}"
  | .call label => do return s!"  call {← symbol label}"
  | .la d label => do return s!"  la {d}, {← symbol label}"
  | .ret => .ok "  ret"
  | .label label => do return s!"{← symbol label}:"
  | .function label => do
      let name ← symbol label
      return s!".text\n.balign 4\n.globl {name}\n.type {name}, @function\n{name}:"
  | .endFunction label => do
      let name ← symbol label
      return s!".size {name}, . - {name}"
  | .text => .ok ".text"
  | .rodata => .ok ".section .rodata"
  | .align n =>
      if n ≤ 16 then .ok s!".p2align {n}" else .error "alignment is too large"
  | .word n => .ok s!"  .word {n.toNat}"
  | .bytes [] => .ok ""
  | .bytes values =>
      .ok ("  .byte " ++ String.intercalate ", " (values.map (toString ·.toNat)))

def emit (program : Program) : Except String String := do
  let lines ← program.mapM emitLine
  return ".option norvc\n.option norelax\n.attribute arch, \"rv64im\"\n" ++
    String.intercalate "\n" lines ++
    "\n.section .note.GNU-stack,\"\",@progbits\n"

end LeanAsm.Symbolic
