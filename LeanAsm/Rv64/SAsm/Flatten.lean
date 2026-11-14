import LeanAsm.Rv64.SAsm.Ast

/-! Position-aware lowering of structured assembly to fixed-width instructions. -/

namespace LeanAsm.Rv64.SAsm

open LeanAsm.Rv64
namespace Stmt

def brOfs (instructions : Nat) : BitVec 13 :=
  BitVec.ofNat 13 (4 * instructions)

def jFwd (instructions : Nat) : BitVec 21 :=
  BitVec.ofNat 21 (4 * instructions)

def jBack (instructions : Nat) : BitVec 21 :=
  BitVec.ofInt 21 (-Int.ofNat (4 * instructions))

def flatten (addr : Word) : Stmt → Program
  | .block _ code => code
  | .seq a b =>
      a.flatten addr ++ b.flatten (addr + BitVec.ofNat 64 (4 * a.size))
  | .ite _ guard yes no =>
      guard.neg.toInstr (brOfs (yes.size + 2)) ::
        (yes.flatten (addr + 4) ++
          .JAL .x0 (jFwd (no.size + 1)) ::
          no.flatten (addr + BitVec.ofNat 64 (4 * (yes.size + 2))))
  | .when _ guard body =>
      guard.neg.toInstr (brOfs (body.size + 1)) ::
        body.flatten (addr + 4)
  | .while _ guard body =>
      guard.neg.toInstr (brOfs (body.size + 2)) ::
        (body.flatten (addr + 4) ++
          [.JAL .x0 (jBack (body.size + 1))])
  | .call _ target =>
      [.JAL .x1 (BitVec.setWidth 21 (target - addr))]
  | .ret _ =>
      [.JALR .x0 .x1 0]

@[simp] theorem flatten_length (s : Stmt) (addr : Word) :
    (s.flatten addr).length = s.size := by
  induction s generalizing addr with
  | block _ code => rfl
  | seq a b ha hb => simp [flatten, size, ha, hb]
  | ite _ guard yes no hy hn =>
      simp [flatten, size, hy, hn]
      omega
  | «when» _ guard body hb => simp [flatten, size, hb]
  | «while» _ guard body hb => simp [flatten, size, hb]
  | call _ _ => rfl
  | ret _ => rfl

private def blockOk (code : Program) : Bool :=
  code.all (fun i => !i.isControl)

private def callOffsetOk (addr target : Word) : Bool :=
  let delta := (target - addr).toInt
  decide (-(2 ^ 20 : Int) ≤ delta ∧ delta < 2 ^ 20 ∧ delta % 2 = 0)

def offsetsOk (addr : Word) : Stmt → Bool
  | .block _ code => blockOk code
  | .seq a b =>
      a.offsetsOk addr &&
        b.offsetsOk (addr + BitVec.ofNat 64 (4 * a.size))
  | .ite _ _ yes no =>
      decide (4 * (yes.size + 2) < 2 ^ 12) &&
        decide (4 * (no.size + 1) < 2 ^ 20) &&
        yes.offsetsOk (addr + 4) &&
        no.offsetsOk (addr + BitVec.ofNat 64 (4 * (yes.size + 2)))
  | .when _ _ body =>
      decide (4 * (body.size + 1) < 2 ^ 12) &&
        body.offsetsOk (addr + 4)
  | .while _ _ body =>
      decide (4 * (body.size + 2) < 2 ^ 12) &&
        decide (4 * (body.size + 1) ≤ 2 ^ 20) &&
        body.offsetsOk (addr + 4)
  | .call _ target => callOffsetOk addr target
  | .ret _ => true

inductive LowerError where
  | notLowerable
  deriving DecidableEq, BEq, Repr

def lower (addr : Word) (stmt : Stmt) : Except LowerError (Array Instr) :=
  if stmt.offsetsOk addr then .ok (stmt.flatten addr).toArray
  else .error .notLowerable

end Stmt
end LeanAsm.Rv64.SAsm
