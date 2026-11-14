import LeanAsm.X64.Basic

namespace LeanAsm.ABI.SysVAMD64

open X64

/-- Integer/pointer arguments only; aggregate, vector, and variadic argument
    classification are not provided by these helpers. -/
def argumentRegisters : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

def returnRegisters : List Reg := [.rax, .rdx]

def calleeSaved : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

def callerSaved : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- Entry RSP is 8 mod 16. Six saved registers consume 48 bytes; the
    allocation is 8 mod 16 so RSP is aligned before a nested CALL. No red zone. -/
def localAllocation (locals : Nat) : Nat := ((locals + 23) / 16) * 16 - 8

def frameSize (locals : Nat) : Nat := 8 * calleeSaved.length + localAllocation locals

private def allocation (locals : Nat) : Except Error (BitVec 32) :=
  let bytes := localAllocation locals
  if bytes < 2 ^ 31 then .ok (BitVec.ofNat 32 bytes) else .error .invalidOperand

def enter (locals : Nat := 0) : Except Error Program := do
  let bytes ← allocation locals
  return calleeSaved.map Instr.push ++ [.aluImm .sub .b64 .rsp bytes]

def leave (locals : Nat := 0) : Except Error Program := do
  let bytes ← allocation locals
  return [.aluImm .add .b64 .rsp bytes] ++ calleeSaved.reverse.map Instr.pop ++ [.ret]

def functionBody (body : Program) (locals : Nat := 0) : Except Error Program := do
  return (← enter locals) ++ body ++ (← leave locals)

end LeanAsm.ABI.SysVAMD64
