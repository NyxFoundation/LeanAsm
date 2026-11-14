import Std

/-! A scalar subset of x86-64 long mode. Operands name physical registers;
    byte registers are the low bytes only, never AH/BH/CH/DH. -/

namespace LeanAsm.X64

abbrev Word := BitVec 64

inductive Size where
  | b8 | b16 | b32 | b64
  deriving DecidableEq, BEq, Repr

def Size.bits : Size → Nat
  | .b8 => 8 | .b16 => 16 | .b32 => 32 | .b64 => 64

def Size.bytes (size : Size) : Nat := size.bits / 8

def Size.immBits (size : Size) : Nat := min size.bits 32

def Size.mask (size : Size) : Word := BitVec.ofNat 64 (2 ^ size.bits - 1)

def Size.trim (size : Size) (value : Word) : Word := value &&& size.mask

def Size.signed (size : Size) (value : Word) : Int :=
  let n := (size.trim value).toNat
  if n < 2 ^ (size.bits - 1) then Int.ofNat n else Int.ofNat n - 2 ^ size.bits

inductive Reg where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, BEq, Repr

def Reg.toNat : Reg → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3
  | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

theorem Reg.toNat_lt (reg : Reg) : reg.toNat < 16 := by
  cases reg <;> decide

inductive Scale where
  | one | two | four | eight
  deriving DecidableEq, BEq, Repr

def Scale.code : Scale → Nat
  | .one => 0 | .two => 1 | .four => 2 | .eight => 3

def Scale.factor (scale : Scale) : Nat := 2 ^ scale.code

inductive Address where
  | base (reg : Reg) (disp : BitVec 32 := 0)
  | indexed (base : Option Reg) (index : Reg) (scale : Scale) (disp : BitVec 32 := 0)
  | rip (disp : BitVec 32)
  deriving DecidableEq, BEq, Repr

inductive RM where
  | reg (reg : Reg)
  | mem (address : Address)
  deriving DecidableEq, BEq, Repr

inductive AluOp where
  | add | bitOr | adc | sbb | bitAnd | sub | bitXor | cmp | test
  deriving DecidableEq, BEq, Repr

inductive UnaryOp where
  | bitNot | neg | inc | dec
  deriving DecidableEq, BEq, Repr

inductive ShiftOp where
  | rol | ror | shl | shr | sar
  deriving DecidableEq, BEq, Repr

inductive ShiftCount where
  | imm (count : BitVec 8)
  | cl
  deriving DecidableEq, BEq, Repr

/-- The ordering is the architectural condition-code nibble. -/
inductive Cond where
  | o | no | b | ae | e | ne | be | a
  | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, BEq, Repr

def Cond.code : Cond → Nat
  | .o => 0 | .no => 1 | .b => 2 | .ae => 3
  | .e => 4 | .ne => 5 | .be => 6 | .a => 7
  | .s => 8 | .ns => 9 | .p => 10 | .np => 11
  | .l => 12 | .ge => 13 | .le => 14 | .g => 15

/-- Each accepted value encodes one real instruction. Invalid size combinations
    are rejected by `encode`, `emitInstr`, and execution, never approximated. -/
inductive Instr where
  | mov (size : Size) (dst : Reg) (src : RM)
  | store (size : Size) (dst : Address) (src : Reg)
  | movImm (size : Size) (dst : Reg) (value : BitVec size.bits)
  | lea (dst : Reg) (address : Address)
  | extend (signed : Bool) (srcSize dstSize : Size) (dst : Reg) (src : RM)
  | alu (op : AluOp) (size : Size) (dst : Reg) (src : RM)
  | aluImm (op : AluOp) (size : Size) (dst : Reg) (value : BitVec size.immBits)
  | unary (op : UnaryOp) (size : Size) (dst : Reg)
  | shift (op : ShiftOp) (size : Size) (dst : Reg) (count : ShiftCount)
  | mul (signed : Bool) (size : Size) (src : RM)
  | imul (size : Size) (dst : Reg) (src : RM)
  | div (signed : Bool) (size : Size) (src : RM)
  | signExtend (size : Size)
  | bswap (size : Size) (dst : Reg)
  | setcc (cond : Cond) (dst : Reg)
  | cmov (cond : Cond) (size : Size) (dst : Reg) (src : RM)
  | jmp (disp : BitVec 32)
  | jcc (cond : Cond) (disp : BitVec 32)
  | call (disp : BitVec 32)
  | jmpReg (target : Reg)
  | callReg (target : Reg)
  | push (src : Reg)
  | pop (dst : Reg)
  | ret | nop | clc | stc | cmc
  deriving DecidableEq, Repr

abbrev Program := List Instr

inductive Error where
  | invalidOperand | invalidAddress
  | memoryBounds | readOnlyMemory | invalidMemory
  | undefinedFlag | divisionError
  | instructionBounds | invalidProgram | fuelExhausted
  | invalidSymbol | duplicateSymbol | undefinedSymbol
  | displacementOutOfRange | unsupportedRelocation
  deriving DecidableEq, BEq, Repr

end LeanAsm.X64
