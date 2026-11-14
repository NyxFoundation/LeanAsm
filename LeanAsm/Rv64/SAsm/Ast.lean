import LeanAsm.Rv64.Program

/-!
# RV64 structured assembly syntax

This is the reusable control-flow core inspired by evm-asm's SAsm. Verification
annotations and project-specific control-flow forms are intentionally separate
from this syntax.
-/

namespace LeanAsm.Rv64.SAsm

open LeanAsm.Rv64

inductive Cond where
  | beq (rs1 rs2 : Reg)
  | bne (rs1 rs2 : Reg)
  | blt (rs1 rs2 : Reg)
  | bge (rs1 rs2 : Reg)
  | bltu (rs1 rs2 : Reg)
  | bgeu (rs1 rs2 : Reg)
  deriving DecidableEq, Repr

namespace Cond

def neg : Cond → Cond
  | .beq a b => .bne a b
  | .bne a b => .beq a b
  | .blt a b => .bge a b
  | .bge a b => .blt a b
  | .bltu a b => .bgeu a b
  | .bgeu a b => .bltu a b

@[simp] theorem neg_neg (c : Cond) : c.neg.neg = c := by
  cases c <;> rfl

def toInstr : Cond → BitVec 13 → Instr
  | .beq a b, off => .BEQ a b off
  | .bne a b, off => .BNE a b off
  | .blt a b, off => .BLT a b off
  | .bge a b, off => .BGE a b off
  | .bltu a b, off => .BLTU a b off
  | .bgeu a b, off => .BGEU a b off

end Cond

inductive Stmt where
  | block (label : String) (code : Program)
  | seq (first second : Stmt)
  | ite (label : String) (guard : Cond) (yes no : Stmt)
  | when (label : String) (guard : Cond) (body : Stmt)
  | «while» (label : String) (guard : Cond) (body : Stmt)
  | call (label : String) (target : Word)
  | ret (label : String)
  deriving Repr

def Stmt.size : Stmt → Nat
  | .block _ code => code.length
  | .seq a b => a.size + b.size
  | .ite _ _ yes no => yes.size + no.size + 2
  | .when _ _ body => body.size + 1
  | .while _ _ body => body.size + 2
  | .call .. => 1
  | .ret .. => 1

end LeanAsm.Rv64.SAsm
