import LeanAsm.X64.Emit

namespace LeanAsm.X64.Symbolic

inductive Line where
  | instr (instruction : Instr)
  | label (name : String)
  | function (name : String)
  | endFunction (name : String)
  | jump (target : String)
  | branch (condition : Cond) (target : String)
  | call (target : String)
  | leaSymbol (dst : Reg) (target : String)
  | text | rodata
  | align (power : Nat)
  | bytes (values : Array UInt8)
  | quad (value : Word)
  deriving Repr

abbrev Program := List Line

private def definedName : Line → Option String
  | .label name | .function name => some name
  | _ => none

private def validateNames (program : Program) : Except Error Unit := do
  let names ← program.foldlM (fun names line => do
    match definedName line with
    | none => return names
    | some name =>
        let _ ← checkSymbol name
        if names.contains name then throw .duplicateSymbol
        return name :: names) ([] : List String)
  for line in program do
    if let .endFunction name := line then
      let _ ← checkSymbol name
      unless names.contains name do throw .undefinedSymbol

def emitLine : Line → Except Error String
  | .instr instruction => emitInstr instruction
  | .label name => do return s!"{← checkSymbol name}:"
  | .function name => do
      let name ← checkSymbol name
      return s!".text\n.globl {name}\n.type {name}, @function\n{name}:"
  | .endFunction name => do
      let name ← checkSymbol name
      return s!".size {name}, . - {name}"
  | .jump name => do return "  {disp32} jmp \"" ++ (← checkSymbol name) ++ "\""
  | .branch cond name => do return "  {disp32} " ++ s!"j{cond.mnemonic} \"{← checkSymbol name}\""
  | .call name => do return s!"  call \"{← checkSymbol name}\""
  | .leaSymbol dst name => do return s!"  lea {regName .b64 dst}, [rip + \"{← checkSymbol name}\"]"
  | .text => .ok ".text"
  | .rodata => .ok ".section .rodata"
  | .align power => if power ≤ 16 then .ok s!".p2align {power}" else .error .invalidOperand
  | .quad value => .ok s!"  .quad {value.toNat}"
  | .bytes values => .ok (if values.isEmpty then "" else
      "  .byte " ++ String.intercalate ", " (values.toList.map (toString ·.toNat)))

def emit (program : Program) : Except Error String := do
  validateNames program
  let lines ← program.mapM emitLine
  return assemblyHeader ++ String.intercalate "\n" lines ++ assemblyFooter

private def lineSize : Line → Except Error Nat
  | .instr instruction => instruction.byteSize
  | .jump _ => (Instr.jmp 0).byteSize
  | .branch condition _ => (Instr.jcc condition 0).byteSize
  | .call _ => (Instr.call 0).byteSize
  | .leaSymbol dst _ => (Instr.lea dst (.rip 0)).byteSize
  | .label _ | .function _ | .endFunction _ | .text => .ok 0
  | .rodata | .align _ | .bytes _ | .quad _ => .error .unsupportedRelocation

private def symbolOffsets (program : Program) : Except Error (List (String × Nat)) := do
  let (_, symbols) ← program.foldlM (fun (offset, symbols) line => do
    let size ← lineSize line
    let symbols := match definedName line with
      | none => symbols
      | some name => (name, offset) :: symbols
    return (offset + size, symbols)) (0, [])
  return symbols

def displacement (next target : Nat) : Except Error (BitVec 32) :=
  let delta := Int.ofNat target - Int.ofNat next
  if -(2 ^ 31 : Int) ≤ delta && delta < 2 ^ 31 then .ok (BitVec.ofInt 32 delta)
  else .error .displacementOutOfRange

private def resolve (symbols : List (String × Nat)) (next : Nat) (name : String) :
    Except Error (BitVec 32) := do
  let _ ← checkSymbol name
  match symbols.lookup name with
  | none => throw .undefinedSymbol
  | some target => displacement next target

private def lowerLine (symbols : List (String × Nat)) (next : Nat) :
    Line → Except Error (Option Instr)
  | .instr instruction => .ok (some instruction)
  | .jump name => do return some (.jmp (← resolve symbols next name))
  | .branch cond name => do return some (.jcc cond (← resolve symbols next name))
  | .call name => do return some (.call (← resolve symbols next name))
  | .leaSymbol dst name => do return some (.lea dst (.rip (← resolve symbols next name)))
  | .label _ | .function _ | .endFunction _ | .text => .ok none
  | .rodata | .align _ | .bytes _ | .quad _ => .error .unsupportedRelocation

/-- Resolve a closed code-only program. Data sections, padding, and external
    symbols belong to GNU assembly/linking and are explicitly rejected here. -/
def lower (program : Program) : Except Error X64.Program := do
  validateNames program
  let symbols ← symbolOffsets program
  let (_, reversed) ← program.foldlM (fun (offset, code) line => do
    let next := offset + (← lineSize line)
    let instruction ← lowerLine symbols next line
    return (next, match instruction with | none => code | some i => i :: code)) (0, [])
  return reversed.reverse

end LeanAsm.X64.Symbolic
