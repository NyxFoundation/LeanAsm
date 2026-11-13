import LeanAsm.Rv64.Program

/-! Encoding of the portable `Instr` subset to little-endian RV64 machine code. -/

namespace LeanAsm.Rv64

inductive EncodeError where
  | oddDisplacement
  deriving DecidableEq, BEq, Repr

private def regBits (r : Reg) (shift : Nat) : Nat :=
  r.toNat <<< shift

private def rType (op f7 f3 : Nat) (rd a b : Reg) : UInt32 :=
  ((f7 <<< 25) ||| regBits b 20 ||| regBits a 15 ||| (f3 <<< 12) |||
    regBits rd 7 ||| op).toUInt32

private def iType (op f3 : Nat) (rd a : Reg) (imm : Nat) : UInt32 :=
  ((imm <<< 20) ||| regBits a 15 ||| (f3 <<< 12) ||| regBits rd 7 ||| op).toUInt32

private def sType (f3 : Nat) (a b : Reg) (off : BitVec 12) : UInt32 :=
  let n := off.toNat
  (((n >>> 5) <<< 25) ||| regBits b 20 ||| regBits a 15 ||| (f3 <<< 12) |||
    ((n &&& 31) <<< 7) ||| 0x23).toUInt32

private def bType (f3 : Nat) (a b : Reg) (off : BitVec 13) :
    Except EncodeError UInt32 :=
  let n := off.toNat
  if n % 2 != 0 then .error .oddDisplacement else .ok
    ((((n >>> 12) &&& 1) <<< 31) ||| (((n >>> 5) &&& 63) <<< 25) |||
      regBits b 20 ||| regBits a 15 ||| (f3 <<< 12) |||
      (((n >>> 1) &&& 15) <<< 8) ||| (((n >>> 11) &&& 1) <<< 7) |||
      0x63).toUInt32

private def jType (rd : Reg) (off : BitVec 21) : Except EncodeError UInt32 :=
  let n := off.toNat
  if n % 2 != 0 then .error .oddDisplacement else .ok
    ((((n >>> 20) &&& 1) <<< 31) ||| (((n >>> 1) &&& 1023) <<< 21) |||
      (((n >>> 11) &&& 1) <<< 20) ||| (((n >>> 12) &&& 255) <<< 12) |||
      regBits rd 7 ||| 0x6f).toUInt32

def encode : Instr → Except EncodeError UInt32
  | .ADD rd a b => .ok (rType 0x33 0 0 rd a b)
  | .SUB rd a b => .ok (rType 0x33 32 0 rd a b)
  | .SLL rd a b => .ok (rType 0x33 0 1 rd a b)
  | .SLT rd a b => .ok (rType 0x33 0 2 rd a b)
  | .SLTU rd a b => .ok (rType 0x33 0 3 rd a b)
  | .XOR rd a b => .ok (rType 0x33 0 4 rd a b)
  | .SRL rd a b => .ok (rType 0x33 0 5 rd a b)
  | .SRA rd a b => .ok (rType 0x33 32 5 rd a b)
  | .OR rd a b => .ok (rType 0x33 0 6 rd a b)
  | .AND rd a b => .ok (rType 0x33 0 7 rd a b)
  | .ADDW rd a b => .ok (rType 0x3b 0 0 rd a b)
  | .SUBW rd a b => .ok (rType 0x3b 32 0 rd a b)
  | .ADDI rd a imm => .ok (iType 0x13 0 rd a imm.toNat)
  | .SLTI rd a imm => .ok (iType 0x13 2 rd a imm.toNat)
  | .SLTIU rd a imm => .ok (iType 0x13 3 rd a imm.toNat)
  | .XORI rd a imm => .ok (iType 0x13 4 rd a imm.toNat)
  | .ORI rd a imm => .ok (iType 0x13 6 rd a imm.toNat)
  | .ANDI rd a imm => .ok (iType 0x13 7 rd a imm.toNat)
  | .SLLI rd a n => .ok (iType 0x13 1 rd a n.toNat)
  | .SRLI rd a n => .ok (iType 0x13 5 rd a n.toNat)
  | .SRAI rd a n => .ok (iType 0x13 5 rd a (0x400 + n.toNat))
  | .ADDIW rd a imm => .ok (iType 0x1b 0 rd a imm.toNat)
  | .SLLIW rd a n => .ok (iType 0x1b 1 rd a n.toNat)
  | .SRLIW rd a n => .ok (iType 0x1b 5 rd a n.toNat)
  | .LUI rd imm =>
      .ok ((imm.toNat <<< 12 ||| regBits rd 7 ||| 0x37).toUInt32)
  | .AUIPC rd imm =>
      .ok ((imm.toNat <<< 12 ||| regBits rd 7 ||| 0x17).toUInt32)
  | .LB rd a off => .ok (iType 0x03 0 rd a off.toNat)
  | .LH rd a off => .ok (iType 0x03 1 rd a off.toNat)
  | .LW rd a off => .ok (iType 0x03 2 rd a off.toNat)
  | .LD rd a off => .ok (iType 0x03 3 rd a off.toNat)
  | .LBU rd a off => .ok (iType 0x03 4 rd a off.toNat)
  | .LHU rd a off => .ok (iType 0x03 5 rd a off.toNat)
  | .LWU rd a off => .ok (iType 0x03 6 rd a off.toNat)
  | .SB a b off => .ok (sType 0 a b off)
  | .SH a b off => .ok (sType 1 a b off)
  | .SW a b off => .ok (sType 2 a b off)
  | .SD a b off => .ok (sType 3 a b off)
  | .BEQ a b off => bType 0 a b off
  | .BNE a b off => bType 1 a b off
  | .BLT a b off => bType 4 a b off
  | .BGE a b off => bType 5 a b off
  | .BLTU a b off => bType 6 a b off
  | .BGEU a b off => bType 7 a b off
  | .JAL rd off => jType rd off
  | .JALR rd a off => .ok (iType 0x67 0 rd a off.toNat)
  | .MUL rd a b => .ok (rType 0x33 1 0 rd a b)
  | .MULH rd a b => .ok (rType 0x33 1 1 rd a b)
  | .MULHSU rd a b => .ok (rType 0x33 1 2 rd a b)
  | .MULHU rd a b => .ok (rType 0x33 1 3 rd a b)
  | .DIV rd a b => .ok (rType 0x33 1 4 rd a b)
  | .DIVU rd a b => .ok (rType 0x33 1 5 rd a b)
  | .REM rd a b => .ok (rType 0x33 1 6 rd a b)
  | .REMU rd a b => .ok (rType 0x33 1 7 rd a b)
  | .FENCE => .ok 0x0ff0000f

private def appendWord (bytes : ByteArray) (word : UInt32) : ByteArray :=
  (List.range 4).foldl
    (fun out i => out.push (word >>> (8 * i).toUInt32).toUInt8)
    bytes

def encodeArray (code : Array Instr) : Except EncodeError ByteArray := do
  let words ← code.mapM encode
  return words.foldl appendWord ByteArray.empty

def encodeProgram (code : Program) : Except EncodeError ByteArray := do
  let words ← code.mapM encode
  return words.foldl appendWord ByteArray.empty

end LeanAsm.Rv64
