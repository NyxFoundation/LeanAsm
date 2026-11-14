import LeanAsm.X64.Encoding

namespace LeanAsm.X64

def regName (size : Size) (reg : Reg) : String :=
  let names : Array String := match size with
    | .b8 => #["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil",
        "r8b", "r9b", "r10b", "r11b", "r12b", "r13b", "r14b", "r15b"]
    | .b16 => #["ax", "cx", "dx", "bx", "sp", "bp", "si", "di",
        "r8w", "r9w", "r10w", "r11w", "r12w", "r13w", "r14w", "r15w"]
    | .b32 => #["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi",
        "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"]
    | .b64 => #["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
        "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
  names[reg.toNat]!

def Cond.mnemonic : Cond → String
  | .o => "o" | .no => "no" | .b => "b" | .ae => "ae"
  | .e => "e" | .ne => "ne" | .be => "be" | .a => "a"
  | .s => "s" | .ns => "ns" | .p => "p" | .np => "np"
  | .l => "l" | .ge => "ge" | .le => "le" | .g => "g"

def addressText : Address → String
  | .base reg disp => s!"[{regName .b64 reg} + {disp.toInt}]"
  | .indexed base index scale disp =>
      s!"[{(base.map (regName .b64)).getD "0"} + {regName .b64 index} * {scale.factor} + {disp.toInt}]"
  | .rip disp => s!"[rip + {disp.toInt}]"

private def memoryText (size : Size) (address : Address) : String :=
  let width := match size with
    | .b8 => "byte" | .b16 => "word" | .b32 => "dword" | .b64 => "qword"
  s!"{width} ptr {addressText address}"

private def operandText (size : Size) : RM → String
  | .reg reg => regName size reg
  | .mem address => memoryText size address

private def aluName : AluOp → String
  | .add => "add" | .bitOr => "or" | .adc => "adc" | .sbb => "sbb"
  | .bitAnd => "and" | .sub => "sub" | .bitXor => "xor" | .cmp => "cmp" | .test => "test"

private def unaryName : UnaryOp → String
  | .bitNot => "not" | .neg => "neg" | .inc => "inc" | .dec => "dec"

private def shiftName : ShiftOp → String
  | .rol => "rol" | .ror => "ror" | .shl => "shl" | .shr => "shr" | .sar => "sar"

private def dataText : Instr → Except Error String
  | .mov size dst src => .ok s!"mov {regName size dst}, {operandText size src}"
  | .store size dst src => .ok s!"mov {memoryText size dst}, {regName size src}"
  | .movImm size dst value =>
      .ok s!"{if size == .b64 then "movabs" else "mov"} {regName size dst}, {value.toNat}"
  | .lea dst address => .ok s!"lea {regName .b64 dst}, {addressText address}"
  | .extend signed srcSize dstSize dst src =>
      let mnemonic := if !signed then "movzx" else if srcSize == .b32 then "movsxd" else "movsx"
      .ok s!"{mnemonic} {regName dstSize dst}, {operandText srcSize src}"
  | .alu .test size dst (.mem address) => .ok s!"test {memoryText size address}, {regName size dst}"
  | .alu op size dst src => .ok s!"{aluName op} {regName size dst}, {operandText size src}"
  | .aluImm op size dst value => .ok s!"{aluName op} {regName size dst}, {value.toInt}"
  | .unary op size dst => .ok s!"{unaryName op} {regName size dst}"
  | .shift op size dst count =>
      let amount := match count with | .imm n => toString n.toNat | .cl => "cl"
      .ok s!"{shiftName op} {regName size dst}, {amount}"
  | _ => .error .invalidOperand

private def mathText : Instr → Except Error String
  | .mul signed size src => .ok s!"{if signed then "imul" else "mul"} {operandText size src}"
  | .div signed size src => .ok s!"{if signed then "idiv" else "div"} {operandText size src}"
  | .imul size dst src => .ok s!"imul {regName size dst}, {operandText size src}"
  | .signExtend size => .ok (if size == .b16 then "cwd" else if size == .b32 then "cdq" else "cqo")
  | .bswap size dst => .ok s!"bswap {regName size dst}"
  | .setcc cond dst => .ok s!"set{cond.mnemonic} {regName .b8 dst}"
  | .cmov cond size dst src => .ok s!"cmov{cond.mnemonic} {regName size dst}, {operandText size src}"
  | _ => .error .invalidOperand

/-- The GNU disp32 pseudo-prefix prevents relaxation from changing modeled lengths. -/
private def controlText : Instr → Except Error String
  | .jmp disp => .ok ("{disp32} " ++ s!"jmp . + {disp.toInt + 5}")
  | .jcc cond disp => .ok ("{disp32} " ++ s!"j{cond.mnemonic} . + {disp.toInt + 6}")
  | .call disp => .ok s!"call . + {disp.toInt + 5}"
  | .jmpReg target => .ok s!"jmp {regName .b64 target}"
  | .callReg target => .ok s!"call {regName .b64 target}"
  | .push src => .ok s!"push {regName .b64 src}"
  | .pop dst => .ok s!"pop {regName .b64 dst}"
  | .ret => .ok "ret" | .nop => .ok "nop" | .clc => .ok "clc"
  | .stc => .ok "stc" | .cmc => .ok "cmc"
  | _ => .error .invalidOperand

def emitInstr (instruction : Instr) : Except Error String := do
  let _ ← encode instruction
  let text ← match instruction with
    | .mov .. | .store .. | .movImm .. | .lea .. | .extend .. | .alu ..
    | .aluImm .. | .unary .. | .shift .. => dataText instruction
    | .mul .. | .imul .. | .div .. | .signExtend .. | .bswap .. | .setcc .. | .cmov .. =>
        mathText instruction
    | .jmp .. | .jcc .. | .call .. | .jmpReg .. | .callReg .. | .push .. | .pop ..
    | .ret | .nop | .clc | .stc | .cmc => controlText instruction
  return "  " ++ text

def validSymbol (name : String) : Bool :=
  match name.toList with
  | [] => false
  | head :: tail =>
      let start := fun c : Char => c.toNat < 128 && (c.isAlpha || c == '_')
      start head && tail.all (fun c => start c || (c.toNat < 128 && c.isDigit))

def checkSymbol (name : String) : Except Error String :=
  if validSymbol name then .ok name else .error .invalidSymbol

def assemblyHeader : String := ".intel_syntax noprefix\n.text\n"
def assemblyFooter : String := "\n.section .note.GNU-stack,\"\",@progbits\n"

def emitProgram (name : String) (program : Program) : Except Error String := do
  let name ← checkSymbol name
  let lines ← program.mapM emitInstr
  return assemblyHeader ++ s!".globl {name}\n.type {name}, @function\n{name}:\n" ++
    String.intercalate "\n" lines ++ s!"\n.size {name}, . - {name}\n" ++ assemblyFooter

end LeanAsm.X64
