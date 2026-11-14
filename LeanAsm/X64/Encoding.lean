import LeanAsm.X64.Basic

namespace LeanAsm.X64

private def byte (value : Nat) : UInt8 := value.toUInt8

private def littleEndian (count value : Nat) : Array UInt8 :=
  (List.range count).toArray.map fun i => byte (value / 2 ^ (8 * i))

private def fits8 (value : BitVec 32) : Bool :=
  decide (-128 ≤ value.toInt ∧ value.toInt ≤ 127)

private structure OperandEncoding where
  bytes : Array UInt8
  b : Bool := false
  x : Bool := false

private def memoryOperand (field : Nat) (base : Option Reg)
    (index : Option (Reg × Scale)) (disp : BitVec 32) : Except Error OperandEncoding := do
  if index.any (fun pair => pair.1 == .rsp) then throw .invalidAddress
  let lowBase := base.map (fun r => r.toNat % 8)
  let mode := if base.isNone then 0 else
    if disp == 0 && lowBase != some 5 then 0 else if fits8 disp then 1 else 2
  let displacement := if base.isNone || mode == 2 then littleEndian 4 disp.toNat
    else if mode == 1 then littleEndian 1 disp.toNat else #[]
  let sib := index.isSome || lowBase == some 4 || base.isNone
  let rm := if sib then 4 else lowBase.getD 5
  let head := #[byte (64 * mode + 8 * (field % 8) + rm)]
  let addressing := if sib then
    #[byte (64 * (index.map (fun p => p.2.code)).getD 0 +
      8 * (index.map (fun p => p.1.toNat % 8)).getD 4 + lowBase.getD 5)] else #[]
  return { bytes := head ++ addressing ++ displacement
           b := base.any (fun r => r.toNat ≥ 8)
           x := index.any (fun p => p.1.toNat ≥ 8) }

private def operand (field : Nat) : RM → Except Error OperandEncoding
  | .reg reg => .ok {
      bytes := #[byte (0xc0 + 8 * (field % 8) + reg.toNat % 8)]
      b := reg.toNat ≥ 8 }
  | .mem (.base reg disp) => memoryOperand field (some reg) none disp
  | .mem (.indexed base index scale disp) => memoryOperand field base (some (index, scale)) disp
  | .mem (.rip disp) => .ok { bytes := #[byte (8 * (field % 8) + 5)] ++ littleEndian 4 disp.toNat }

private def encodePrefix (size : Size) (r x b force : Bool) : Array UInt8 :=
  let rex := 0x40 + (if size == .b64 then 8 else 0) +
    (if r then 4 else 0) + (if x then 2 else 0) + (if b then 1 else 0)
  (if size == .b16 then #[0x66] else #[]) ++
    (if rex != 0x40 || force then #[byte rex] else #[])

private def byteRex : RM → Bool
  | .reg reg => reg.toNat ≥ 4
  | .mem _ => false

private def form (size : Size) (opcodes : Array UInt8) (field : Nat)
    (rm : RM) (byteField : Bool := false) : Except Error (Array UInt8) := do
  let encoded ← operand field rm
  let force := size == .b8 && (byteField || byteRex rm)
  return encodePrefix size (field ≥ 8) encoded.x encoded.b force ++ opcodes ++ encoded.bytes

private def regOpcode (size : Size) (opcode : Nat) (reg : Reg) : Array UInt8 :=
  encodePrefix size false false (reg.toNat ≥ 8) (size == .b8 && reg.toNat ≥ 4) ++
    #[byte (opcode + reg.toNat % 8)]

private def wideOpcode (size : Size) (base : Nat) : Array UInt8 :=
  #[byte (base + if size == .b8 then 0 else 1)]

private def aluGroup : AluOp → Nat
  | .add => 0 | .bitOr => 1 | .adc => 2 | .sbb => 3
  | .bitAnd => 4 | .sub => 5 | .bitXor => 6 | .cmp => 7 | .test => 0

private def encodeAlu (op : AluOp) (size : Size) (dst : Reg) (src : RM) :
    Except Error (Array UInt8) :=
  if op == .test then
    match src with
    | .reg reg => form size (wideOpcode size 0x84) reg.toNat (.reg dst) (reg.toNat ≥ 4)
    | .mem _ => form size (wideOpcode size 0x84) dst.toNat src (dst.toNat ≥ 4)
  else match src with
    | .reg reg => form size (wideOpcode size (8 * aluGroup op)) reg.toNat
        (.reg dst) (reg.toNat ≥ 4)
    | .mem _ => form size (wideOpcode size (8 * aluGroup op + 2)) dst.toNat src (dst.toNat ≥ 4)

private def encodeAluImm (op : AluOp) (size : Size) (dst : Reg)
    (value : BitVec size.immBits) : Except Error (Array UInt8) := do
  let small := size != .b8 && op != .test && decide (-128 ≤ value.toInt ∧ value.toInt ≤ 127)
  let count := if small then 1 else size.immBits / 8
  let tail := littleEndian count value.toNat
  if dst == .rax && !small then
    let opcode := if op == .test then 0xa8 else 8 * aluGroup op + 4
    return encodePrefix size false false false false ++ wideOpcode size opcode ++ tail
  let opcode := if op == .test then wideOpcode size 0xf6
    else if small then #[0x83] else wideOpcode size 0x80
  return (← form size opcode (aluGroup op) (.reg dst)) ++ tail

private def encodeExtend (signed : Bool) (srcSize dstSize : Size) (dst : Reg) (src : RM) :
    Except Error (Array UInt8) := do
  unless srcSize.bits < dstSize.bits do throw .invalidOperand
  if srcSize == .b32 then
    unless signed && dstSize == .b64 do throw .invalidOperand
    form dstSize #[0x63] dst.toNat src
  else
    let code := (if signed then 0xbe else 0xb6) + (if srcSize == .b16 then 1 else 0)
    let encoded ← operand dst.toNat src
    return encodePrefix dstSize (dst.toNat ≥ 8) encoded.x encoded.b
      (srcSize == .b8 && byteRex src) ++ #[0x0f, byte code] ++ encoded.bytes

private def shiftGroup : ShiftOp → Nat
  | .rol => 0 | .ror => 1 | .shl => 4 | .shr => 5 | .sar => 7

private def encodeShift (op : ShiftOp) (size : Size) (dst : Reg) (count : ShiftCount) :
    Except Error (Array UInt8) := do
  let (base, tail) := match count with
    | .cl => (0xd2, #[])
    | .imm n => if n == 1 then (0xd0, #[]) else (0xc0, #[byte n.toNat])
  return (← form size (wideOpcode size base) (shiftGroup op) (.reg dst)) ++ tail

private def encodeUnary (op : UnaryOp) (size : Size) (dst : Reg) :
    Except Error (Array UInt8) :=
  let (opcode, group) := match op with
    | .bitNot => (0xf6, 2) | .neg => (0xf6, 3)
    | .inc => (0xfe, 0) | .dec => (0xfe, 1)
  form size (wideOpcode size opcode) group (.reg dst)

private def encodeData : Instr → Except Error (Array UInt8)
  | .mov size dst (.reg src) =>
      form size (wideOpcode size 0x88) src.toNat (.reg dst) (src.toNat ≥ 4)
  | .mov size dst src => form size (wideOpcode size 0x8a) dst.toNat src (dst.toNat ≥ 4)
  | .store size dst src => form size (wideOpcode size 0x88) src.toNat (.mem dst) (src.toNat ≥ 4)
  | .movImm size dst value => .ok
      (regOpcode size (if size == .b8 then 0xb0 else 0xb8) dst ++ littleEndian size.bytes value.toNat)
  | .lea dst address => form .b64 #[0x8d] dst.toNat (.mem address)
  | .extend signed srcSize dstSize dst src => encodeExtend signed srcSize dstSize dst src
  | .alu op size dst src => encodeAlu op size dst src
  | .aluImm op size dst value => encodeAluImm op size dst value
  | .unary op size dst => encodeUnary op size dst
  | .shift op size dst count => encodeShift op size dst count
  | _ => .error .invalidOperand

private def encodeMath : Instr → Except Error (Array UInt8)
  | .mul signed size src => form size (wideOpcode size 0xf6) (if signed then 5 else 4) src
  | .div signed size src => form size (wideOpcode size 0xf6) (if signed then 7 else 6) src
  | .imul size dst src => if size == .b8 then .error .invalidOperand
      else form size #[0x0f, 0xaf] dst.toNat src
  | .signExtend size => if size == .b8 then .error .invalidOperand
      else .ok (encodePrefix size false false false false ++ #[0x99])
  | .bswap size dst => if size == .b8 || size == .b16 then .error .invalidOperand
      else .ok (encodePrefix size false false (dst.toNat ≥ 8) false ++ #[0x0f, byte (0xc8 + dst.toNat % 8)])
  | .setcc cond dst => form .b8 #[0x0f, byte (0x90 + cond.code)] 0 (.reg dst)
  | .cmov cond size dst src => if size == .b8 then .error .invalidOperand
      else form size #[0x0f, byte (0x40 + cond.code)] dst.toNat src
  | _ => .error .invalidOperand

/-- Canonical encodings use rel32 for all direct branches and imm64 for MOV r64.
    Lengths are derived from these bytes throughout layout and execution. -/
def encode : Instr → Except Error (Array UInt8)
  | .jmp disp => .ok (#[0xe9] ++ littleEndian 4 disp.toNat)
  | .jcc cond disp => .ok (#[0x0f, byte (0x80 + cond.code)] ++ littleEndian 4 disp.toNat)
  | .call disp => .ok (#[0xe8] ++ littleEndian 4 disp.toNat)
  | .jmpReg target => form .b32 #[0xff] 4 (.reg target)
  | .callReg target => form .b32 #[0xff] 2 (.reg target)
  | .push src => .ok (regOpcode .b32 0x50 src)
  | .pop dst => .ok (regOpcode .b32 0x58 dst)
  | .ret => .ok #[0xc3] | .nop => .ok #[0x90]
  | .clc => .ok #[0xf8] | .stc => .ok #[0xf9] | .cmc => .ok #[0xf5]
  | i@(.mov ..) | i@(.store ..) | i@(.movImm ..) | i@(.lea ..)
  | i@(.extend ..) | i@(.alu ..) | i@(.aluImm ..) | i@(.unary ..)
  | i@(.shift ..) => encodeData i
  | i@(.mul ..) | i@(.div ..) | i@(.imul ..) | i@(.signExtend ..)
  | i@(.bswap ..) | i@(.setcc ..) | i@(.cmov ..) => encodeMath i

def Instr.byteSize (instruction : Instr) : Except Error Nat :=
  (encode instruction).map Array.size

def encodeProgram (program : Program) : Except Error (Array UInt8) :=
  program.foldlM (fun bytes instruction => return bytes ++ (← encode instruction)) #[]

end LeanAsm.X64
