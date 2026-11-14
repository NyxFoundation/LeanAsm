import LeanAsm
import LeanAsm.Rv64.SAsm.Flatten

/-! Structured RV64 lowering checks. Run with `lake env lean Tests/Rv64/SAsm.lean`. -/

open LeanAsm LeanAsm.Rv64 LeanAsm.Rv64.SAsm

private def increment : Stmt := .block "increment" [.ADDI .x10 .x10 1]
private def decrement : Stmt := .block "decrement" [.ADDI .x10 .x10 (-1)]
private def countdown : Stmt := .while "countdown" (.bne .x10 .x0) decrement

private def lowersTo (statement : Stmt) (expected : Program) (base : Word := 0) : Bool :=
  (statement.lower base).toOption == some expected.toArray

-- should preserve instruction order when lowering blocks and sequences
#guard lowersTo increment [.ADDI .x10 .x10 1]
#guard lowersTo (.seq increment decrement) [.ADDI .x10 .x10 1, .ADDI .x10 .x10 (-1)]

-- should emit the correct branch distances when lowering conditionals and loops
#guard lowersTo (.ite "choice" (.beq .x10 .x0) increment decrement)
  [.BNE .x10 .x0 12, .ADDI .x10 .x10 1, .JAL .x0 8, .ADDI .x10 .x10 (-1)]
#guard lowersTo (.when "bounded" (.bltu .x10 .x11) increment)
  [.BGEU .x10 .x11 8, .ADDI .x10 .x10 1]
#guard lowersTo countdown [.BEQ .x10 .x0 12, .ADDI .x10 .x10 (-1), .JAL .x0 (-8)]

-- should relocate calls from their actual position when lowering a sequence
#guard lowersTo (.seq increment (.call "callee" 0x1010))
  [.ADDI .x10 .x10 1, .JAL .x1 12] 0x1000
#guard lowersTo (.ret "return") [.JALR .x0 .x1 0]

private def callSource : LeanAsm.Rv64.SAsm.Source :=
  { base := 0x1000, statement := .call "callee" 0x1010 }

-- should honor the source base when using the shared lowering and emission APIs
#guard (lowerRv64 callSource).toOption == some [.JAL .x1 16]
#guard (lowerRv64 { callSource with base := 0x1004 }).toOption == some [.JAL .x1 12]
#guard (emitAsm "call_at_base" callSource).toOption ==
  some (emitProgram "call_at_base" [.JAL .x1 16])

private def countdownResult (start : Word) : Option (Word × Word × Nat) := do
  let source : LeanAsm.Rv64.SAsm.Source := { base := 0x2000, statement := countdown }
  let code ← (lowerRv64 source).toOption
  let initial : State := ({ pc := source.base } : State).setReg .x10 start
  let result ← (runUntil (image source.base code) 0x200c 32 initial).toOption
  return (result.state.getReg .x10, result.state.pc, result.steps)

-- should follow the lowered loop's control flow when executing at a nonzero base
#guard countdownResult 0 == some (0, 0x200c, 1)
#guard countdownResult 1 == some (0, 0x200c, 4)
#guard countdownResult 5 == some (0, 0x200c, 16)

private def guardedPadding (count : Nat) : Stmt :=
  .when "guarded" (.bge .x10 .x0) (.block "padding" (List.replicate count (.ADDI .x0 .x0 0)))

-- should reject the first out-of-range displacement when a conditional body grows
#guard ((guardedPadding 1022).lower 0).isOk
#guard ((guardedPadding 1023).lower 0).toOption.isNone
#guard ((Stmt.call "too_far" (2^20)).lower 0).toOption.isNone
#guard ((Stmt.call "odd_offset" 3).lower 0).toOption.isNone

private def invalidSource : LeanAsm.Rv64.SAsm.Source :=
  { base := 0, statement := .block "hidden_jump" [.JAL .x0 4] }

-- should reject control instructions inside blocks through both frontend capabilities
#guard (invalidSource.statement.lower invalidSource.base).toOption.isNone
#guard (lowerRv64 invalidSource).toOption.isNone
#guard (emitAsm "invalid" invalidSource).toOption.isNone
