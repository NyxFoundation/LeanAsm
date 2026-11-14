import LeanAsm.X64.Multiply

namespace LeanAsm.X64

private def execAlu (op : AluOp) (size : Size) (dst : Reg) (rhs : Word)
    (state : State) : Except Error State := do
  let lhs := state.getReg dst
  let carry ← if op == .adc || op == .sbb then requireFlag state.flags.cf else pure false
  let (value, flags) := match op with
    | .add | .adc => arithmetic size false lhs rhs carry
    | .sub | .sbb | .cmp => arithmetic size true lhs rhs carry
    | .bitAnd | .test => logical size (lhs &&& rhs)
    | .bitOr => logical size (lhs ||| rhs)
    | .bitXor => logical size (lhs ^^^ rhs)
  let updated := if op == .cmp || op == .test then state else state.writeReg size dst value
  return { updated with flags := flags }

private def execUnary (op : UnaryOp) (size : Size) (dst : Reg) (state : State) : State :=
  let lhs := state.getReg dst
  if op == .bitNot then state.writeReg size dst (~~~lhs)
  else
    let (value, flags) := match op with
      | .neg => arithmetic size true 0 lhs false
      | .inc => arithmetic size false lhs 1 false
      | _ => arithmetic size true lhs 1 false
    { state.writeReg size dst value with
      flags := if op == .neg then flags else { flags with cf := state.flags.cf } }

private def execShift (op : ShiftOp) (size : Size) (dst : Reg)
    (count : ShiftCount) (state : State) : State :=
  let n := match count with
    | .imm n => n.toNat
    | .cl => (state.getReg .rcx).toNat % 256
  let (value, flags) := shiftResult op size (state.getReg dst) n state.flags
  { state.writeReg size dst value with flags := flags }

private def execData (instruction : Instr) (state : State) : Except Error State := do
  match instruction with
  | .mov size dst src => return state.writeReg size dst (← src.read size state state.rip)
  | .store size dst src =>
      let memory ← state.memory.store size (dst.eval state state.rip) (state.getReg src)
      return { state with memory := memory }
  | .movImm size dst value => return state.writeReg size dst (value.zeroExtend 64)
  | .lea dst address => return state.setReg dst (address.eval state state.rip)
  | .extend signed srcSize dstSize dst src =>
      let value ← src.read srcSize state state.rip
      return state.writeReg dstSize dst (if signed then BitVec.ofInt 64 (srcSize.signed value) else value)
  | .alu op size dst src => execAlu op size dst (← src.read size state state.rip) state
  | .aluImm op size dst value => execAlu op size dst (value.signExtend 64) state
  | .unary op size dst => return execUnary op size dst state
  | .shift op size dst count => return execShift op size dst count state
  | _ => throw .invalidOperand

private def execMath (instruction : Instr) (state : State) : Except Error State := do
  match instruction with
  | .mul signed size src => execMultiply signed size src state
  | .imul size dst src => execImul size dst src state
  | .div signed size src => execDivide signed size src state
  | .signExtend size =>
      return state.writeReg size .rdx (if size.signed (state.getReg .rax) < 0 then ~~~0 else 0)
  | .bswap size dst =>
      let value := state.getReg dst
      let swapped := (List.range size.bytes).foldl (fun acc i =>
        acc ||| (((value >>> (8 * i)) &&& 255) <<< (8 * (size.bytes - 1 - i)))) 0
      return state.writeReg size dst swapped
  | .setcc cond dst => return state.writeReg .b8 dst (if ← cond.eval state.flags then 1 else 0)
  | .cmov cond size dst src =>
      let value ← src.read size state state.rip
      let taken ← cond.eval state.flags
      return state.writeReg size dst (if taken then value else state.getReg dst)
  | _ => throw .invalidOperand

private def pushValue (value : Word) (state : State) : Except Error State := do
  let sp := state.getReg .rsp - 8
  let memory ← state.memory.store .b64 sp value
  return { state.setReg .rsp sp with memory := memory }

private def popValue (state : State) : Except Error (Word × State) := do
  let value ← state.memory.load .b64 (state.getReg .rsp)
  return (value, state.setReg .rsp (state.getReg .rsp + 8))

private def execControl (instruction : Instr) (state : State) : Except Error State := do
  match instruction with
  | .jmp disp => return { state with rip := state.rip + disp.signExtend 64 }
  | .jcc cond disp => return if ← cond.eval state.flags then
      { state with rip := state.rip + disp.signExtend 64 } else state
  | .call disp =>
      let saved ← pushValue state.rip state
      return { saved with rip := state.rip + disp.signExtend 64 }
  | .jmpReg target => return { state with rip := state.getReg target }
  | .callReg target =>
      let saved ← pushValue state.rip state
      return { saved with rip := state.getReg target }
  | .push src => pushValue (state.getReg src) state
  | .pop dst =>
      let (value, updated) ← popValue state
      return updated.setReg dst value
  | .ret =>
      let (target, updated) ← popValue state
      return { updated with rip := target }
  | .nop => return state
  | .clc => return { state with flags := { state.flags with cf := some false } }
  | .stc => return { state with flags := { state.flags with cf := some true } }
  | .cmc => return { state with flags := { state.flags with cf := some (!(← requireFlag state.flags.cf)) } }
  | _ => throw .invalidOperand

def execInstr (instruction : Instr) (state : State) : Except Error State := do
  let size ← instruction.byteSize
  let advanced := { state with rip := state.rip + BitVec.ofNat 64 size }
  match instruction with
  | .mov .. | .store .. | .movImm .. | .lea .. | .extend .. | .alu ..
  | .aluImm .. | .unary .. | .shift .. => execData instruction advanced
  | .mul .. | .imul .. | .div .. | .signExtend .. | .bswap .. | .setcc .. | .cmov .. =>
      execMath instruction advanced
  | .jmp .. | .jcc .. | .call .. | .jmpReg .. | .callReg .. | .push .. | .pop ..
  | .ret | .nop | .clc | .stc | .cmc => execControl instruction advanced

/-- Execute a supplied sequence, without fetching. Control flow still updates RIP. -/
def execSequence (code : Program) (state : State) : Except Error State :=
  code.foldlM (fun state instruction => execInstr instruction state) state

def step (image : Image) (state : State) : Except Error State := do
  execInstr (← image.fetch state.rip) state

structure Completed where
  state : State
  steps : Nat
  deriving Repr

private def runLoop (image : Image) (stop : Word) :
    Nat → State → Nat → Except Error Completed
  | 0, state, count =>
      if state.rip == stop then .ok ⟨state, count⟩ else .error .fuelExhausted
  | fuel + 1, state, count => do
      if state.rip == stop then return ⟨state, count⟩
      runLoop image stop fuel (← step image state) (count + 1)

def runUntil (image : Image) (stop : Word) (fuel : Nat) (state : State) :
    Except Error Completed :=
  if image.valid state.memory then runLoop image stop fuel state 0
  else .error .invalidProgram

end LeanAsm.X64
