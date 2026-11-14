import LeanAsm.Rv64.Program

/-!
# Executable RV64IM semantics

The semantics operate on finite region memory and return explicit traps. Code
memory is immutable and separate from data memory.
-/

namespace LeanAsm.Rv64

def writeReg (s : State) (rd : Reg) (value : Word) : Except Trap State :=
  .ok (s.setReg rd value).advance

def loadReg (s : State) (width : Nat) (rd rs1 : Reg)
    (offset : BitVec 12) (extend : Word → Word := id) : Except Trap State := do
  let value ← s.memory.load width (s.getReg rs1 + offset.signExtend 64)
  writeReg s rd (extend value)

def storeReg (s : State) (width : Nat) (rs1 rs2 : Reg)
    (offset : BitVec 12) : Except Trap State := do
  let memory ← s.memory.store width
    (s.getReg rs1 + offset.signExtend 64) (s.getReg rs2)
  return { s.advance with memory := memory }

def jump (s : State) (rd : Reg) (target : Word) : Except Trap State :=
  if target.toNat % 4 == 0 then
    .ok { s.setReg rd (s.pc + 4) with pc := target }
  else
    .error .instructionMisaligned

def branch (s : State) (taken : Bool) (offset : BitVec 13) :
    Except Trap State :=
  if taken then jump s .x0 (s.pc + offset.signExtend 64)
  else .ok s.advance

def execInstr (i : Instr) (s : State) : Except Trap State :=
  let get := s.getReg
  match i with
  | .ADD rd a b => writeReg s rd (get a + get b)
  | .SUB rd a b => writeReg s rd (get a - get b)
  | .SLL rd a b => writeReg s rd (get a <<< ((get b).toNat % 64))
  | .SRL rd a b => writeReg s rd (get a >>> ((get b).toNat % 64))
  | .SRA rd a b => writeReg s rd ((get a).sshiftRight ((get b).toNat % 64))
  | .AND rd a b => writeReg s rd (get a &&& get b)
  | .OR rd a b => writeReg s rd (get a ||| get b)
  | .XOR rd a b => writeReg s rd (get a ^^^ get b)
  | .SLT rd a b => writeReg s rd (if BitVec.slt (get a) (get b) then 1 else 0)
  | .SLTU rd a b => writeReg s rd (if get a < get b then 1 else 0)
  | .ADDW rd a b => writeReg s rd (((get a + get b).truncate 32).signExtend 64)
  | .SUBW rd a b => writeReg s rd (((get a - get b).truncate 32).signExtend 64)
  | .ADDI rd a imm => writeReg s rd (get a + imm.signExtend 64)
  | .ANDI rd a imm => writeReg s rd (get a &&& imm.signExtend 64)
  | .ORI rd a imm => writeReg s rd (get a ||| imm.signExtend 64)
  | .XORI rd a imm => writeReg s rd (get a ^^^ imm.signExtend 64)
  | .SLTI rd a imm =>
      writeReg s rd (if BitVec.slt (get a) (imm.signExtend 64) then 1 else 0)
  | .SLTIU rd a imm =>
      writeReg s rd (if BitVec.ult (get a) (imm.signExtend 64) then 1 else 0)
  | .SLLI rd a n => writeReg s rd (get a <<< n.toNat)
  | .SRLI rd a n => writeReg s rd (get a >>> n.toNat)
  | .SRAI rd a n => writeReg s rd ((get a).sshiftRight n.toNat)
  | .ADDIW rd a imm =>
      let result : BitVec 32 := (get a).truncate 32 + (imm.signExtend 32)
      writeReg s rd (result.signExtend 64)
  | .SLLIW rd a n =>
      let result : BitVec 32 := (get a).truncate 32 <<< n.toNat
      writeReg s rd (result.signExtend 64)
  | .SRLIW rd a n =>
      let result : BitVec 32 := (get a).truncate 32 >>> n.toNat
      writeReg s rd (result.signExtend 64)
  | .LUI rd imm =>
      let value : BitVec 32 := imm.zeroExtend 32 <<< 12
      writeReg s rd (value.signExtend 64)
  | .AUIPC rd imm =>
      let value : BitVec 32 := imm.zeroExtend 32 <<< 12
      writeReg s rd (s.pc + value.signExtend 64)
  | .LB rd a off => loadReg s 1 rd a off (fun x => (x.truncate 8).signExtend 64)
  | .LH rd a off => loadReg s 2 rd a off (fun x => (x.truncate 16).signExtend 64)
  | .LW rd a off => loadReg s 4 rd a off (fun x => (x.truncate 32).signExtend 64)
  | .LD rd a off => loadReg s 8 rd a off
  | .LBU rd a off => loadReg s 1 rd a off
  | .LHU rd a off => loadReg s 2 rd a off
  | .LWU rd a off => loadReg s 4 rd a off
  | .SB a b off => storeReg s 1 a b off
  | .SH a b off => storeReg s 2 a b off
  | .SW a b off => storeReg s 4 a b off
  | .SD a b off => storeReg s 8 a b off
  | .BEQ a b off => branch s (get a == get b) off
  | .BNE a b off => branch s (get a != get b) off
  | .BLT a b off => branch s (BitVec.slt (get a) (get b)) off
  | .BGE a b off => branch s (!BitVec.slt (get a) (get b)) off
  | .BLTU a b off => branch s (decide (get a < get b)) off
  | .BGEU a b off => branch s (decide (get b ≤ get a)) off
  | .JAL rd off => jump s rd (s.pc + off.signExtend 64)
  | .JALR rd a off => jump s rd ((get a + off.signExtend 64) &&& (~~~(1 : Word)))
  | .MUL rd a b => writeReg s rd (get a * get b)
  | .MULH rd a b =>
      writeReg s rd
        (((((get a).signExtend 128 * (get b).signExtend 128) >>> 64).truncate 64))
  | .MULHSU rd a b =>
      writeReg s rd
        (((((get a).signExtend 128 * (get b).zeroExtend 128) >>> 64).truncate 64))
  | .MULHU rd a b =>
      writeReg s rd
        (((((get a).zeroExtend 128 * (get b).zeroExtend 128) >>> 64).truncate 64))
  | .DIV rd a b =>
      writeReg s rd
        (if get b == 0 then BitVec.allOnes 64 else BitVec.sdiv (get a) (get b))
  | .DIVU rd a b =>
      writeReg s rd
        (if get b == 0 then BitVec.allOnes 64 else get a / get b)
  | .REM rd a b =>
      writeReg s rd
        (if get b == 0 then get a else BitVec.srem (get a) (get b))
  | .REMU rd a b => writeReg s rd (get a % get b)
  | .FENCE => .ok s.advance

def step (p : Image) (s : State) : Except Trap State := do
  execInstr (← p.fetch s.pc) s

/-- Execute a supplied sequence without fetching. Branch and jump instructions
    still update the program counter according to their machine semantics. -/
def execSequence (code : Program) (s : State) : Except Trap State :=
  code.foldlM (fun state instruction => execInstr instruction state) s

abbrev execProgram := execSequence

structure Completed where
  state : State
  steps : Nat
  deriving Repr

def runLoop (p : Image) (stop : Word) : Nat → State → Nat → Except Trap Completed
  | 0, s, count =>
      if s.pc == stop then .ok ⟨s, count⟩ else .error .fuelExhausted
  | remaining + 1, s, count => do
      if s.pc == stop then return ⟨s, count⟩
      runLoop p stop remaining (← step p s) (count + 1)

def runUntil (p : Image) (stop : Word) (fuel : Nat) (s : State) :
    Except Trap Completed :=
  if p.valid s.memory then runLoop p stop fuel s 0
  else .error .invalidProgram

end LeanAsm.Rv64
