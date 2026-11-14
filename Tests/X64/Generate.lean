import LeanAsm
import Lean

open LeanAsm.X64
open Lean

private def sizes : List Size := [.b8, .b16, .b32, .b64]
private def regs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]
private def conditions : List Cond := [.o, .no, .b, .ae, .e, .ne, .be, .a, .s, .ns, .p, .np, .l, .ge, .le, .g]
private def operations : List AluOp := [.add, .adc, .sub, .sbb, .bitAnd, .bitOr, .bitXor, .cmp, .test]
private def displacements : List Int := [-129, -128, -1, 0, 127, 128, 0x12345678]

private def registerEncodings : Array Instr := Id.run do
  let mut cases := #[]
  for size in sizes do
    for dst in regs do
      for src in regs do
        cases := cases ++ #[.mov size dst (.reg src), .alu .test size dst (.reg src),
          .alu .add size dst (.reg src)]
      for op in operations do
        for imm in [-2147483648, -129, -128, -1, 0, 1, 127, 128, 255, 32768, 2147483647] do
          cases := cases.push (.aluImm op size dst (BitVec.ofInt size.immBits imm))
      for value in [0, 128, 65535, 0x80000000, 0xfedcba9876543210] do
        cases := cases.push (.movImm size dst (BitVec.ofNat size.bits value))
      for op in [UnaryOp.bitNot, .neg, .inc, .dec] do
        cases := cases.push (.unary op size dst)
      for op in [ShiftOp.shl, .shr, .sar, .rol, .ror] do
        for count in [ShiftCount.cl, .imm 0, .imm 1, .imm 8, .imm 31, .imm 64, .imm 255] do
          cases := cases.push (.shift op size dst count)
      for signed in [false, true] do
        cases := cases ++ #[.mul signed size (.reg dst), .div signed size (.reg dst)]
      if size != .b8 then
        cases := cases.push (.imul size dst (.reg .r15))
        for cond in conditions do cases := cases.push (.cmov cond size dst (.reg .r8))
      if size == .b32 || size == .b64 then cases := cases.push (.bswap size dst)
  return cases

private def addresses : Array Address := Id.run do
  let mut result := #[]
  for base in regs do
    for disp in displacements do result := result.push (.base base (BitVec.ofInt 32 disp))
  for base in [none, some Reg.rax, some .rsp, some .r13] do
    for index in regs.filter (· != .rsp) do
      for scale in [Scale.one, .two, .four, .eight] do
        for disp in displacements do
          result := result.push (.indexed base index scale (BitVec.ofInt 32 disp))
  for disp in displacements do result := result.push (.rip (BitVec.ofInt 32 disp))
  return result

private def memoryEncodings : Array Instr := Id.run do
  let mut cases := #[]
  for address in addresses do
    for size in sizes do
      cases := cases ++ #[.mov size .r9 (.mem address), .store size address .rdi,
        .alu .test size .r8 (.mem address)]
    cases := cases.push (.lea .r12 address)
  for srcSize in [Size.b8, .b16, .b32] do
    for dstSize in sizes.filter (fun s => s.bits > srcSize.bits) do
      for signed in [false, true] do
        if signed || srcSize != .b32 then
          for src in regs.map RM.reg ++ [.mem (.base .rsp), .mem (.base .r13 128)] do
            cases := cases.push (.extend signed srcSize dstSize .r9 src)
  return cases

private def controlEncodings : Array Instr := Id.run do
  let mut cases := #[Instr.ret, .nop, .clc, .stc, .cmc,
    .signExtend .b16, .signExtend .b32, .signExtend .b64]
  for reg in regs do
    cases := cases ++ #[.jmpReg reg, .callReg reg, .push reg, .pop reg]
    for cond in conditions do cases := cases.push (.setcc cond reg)
  for disp in [-2147483648, -129, -1, 0, 1, 127, 2147483647] do
    cases := cases ++ #[.jmp (BitVec.ofInt 32 disp), .call (BitVec.ofInt 32 disp)]
    for cond in conditions do cases := cases.push (.jcc cond (BitVec.ofInt 32 disp))
  return cases

private def flagsFrom (value : Nat) : Flags :=
  let bit := fun n => some (value / 2 ^ n % 2 == 1)
  ⟨bit 0, bit 1, bit 2, bit 3, bit 4, bit 5⟩

private def flagBits (flags : Flags) : Nat × Nat :=
  [(flags.cf, 0), (flags.pf, 2), (flags.af, 4), (flags.zf, 6), (flags.sf, 7), (flags.of, 11)].foldl
    (fun (mask, value) (flag, bit) => match flag with
      | none => (mask, value)
      | some b => (mask + 2 ^ bit, value + if b then 2 ^ bit else 0)) (0, 0)

private def seed (a b : Word) (flags : Nat := 0) : State :=
  { ({} : State).setReg .rax a |>.setReg .r8 b |>.setReg .rdx 0x123456789abcdef0
      |>.setReg .r9 0x4000 with flags := flagsFrom flags }

private def values (size : Size) : List Word :=
  [0, 1, 15, 16, 2 ^ (size.bits - 1) - 1, 2 ^ (size.bits - 1),
    2 ^ size.bits - 1, 0x123456789abcdef0].map
    (fun n => BitVec.ofNat 64 n ||| (~~~size.mask &&& 0xfedcba9876543210))

private structure NativeCase where
  code : Program
  state : State
  memory : Bool := false

private def arithmeticCases : Array NativeCase := Id.run do
  let mut cases := #[]
  for size in sizes do
    for a in values size do
      for b in values size do
        for carry in [0, 63] do
          for op in operations do
            cases := cases.push ⟨[.alu op size .rax (.reg .r8)], seed a b carry, false⟩
            cases := cases.push ⟨[.aluImm op size .rax (BitVec.ofNat size.immBits b.toNat)], seed a b carry, false⟩
        for signed in [false, true] do
          cases := cases.push ⟨[.mul signed size (.reg .r8)], seed a b, false⟩
        if size != .b8 then cases := cases.push ⟨[.imul size .rax (.reg .r8)], seed a b, false⟩
      for op in [UnaryOp.bitNot, .neg, .inc, .dec] do
        for flags in [0, 63] do cases := cases.push ⟨[.unary op size .rax], seed a 1 flags, false⟩
      for op in [ShiftOp.shl, .shr, .sar, .rol, .ror] do
        for n in [0, 1, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 255] do
          let state := (seed a 1 63).setReg .rcx (BitVec.ofNat 64 n)
          cases := cases.push ⟨[.shift op size .rax (.imm (BitVec.ofNat 8 n))], state, false⟩
          cases := cases.push ⟨[.shift op size .rax .cl], state, false⟩
  return cases

private def moveAndConditionCases : Array NativeCase := Id.run do
  let mut cases := #[]
  for size in sizes do
    for a in values size do
      cases := cases ++ #[⟨[.mov size .rax (.reg .r8)], seed a (-1), false⟩,
        ⟨[.movImm size .rax (BitVec.ofNat size.bits 42)], seed a 0, false⟩]
      if size == .b32 || size == .b64 then cases := cases.push ⟨[.bswap size .rax], seed a 0, false⟩
      for dstSize in sizes.filter (fun s => s.bits > size.bits) do
        for signed in [false, true] do
          if signed || size != .b32 then
            cases := cases.push ⟨[.extend signed size dstSize .r8 (.reg .rax)], seed a (-1), false⟩
  for flags in List.range 64 do
    for cond in conditions do
      cases := cases.push ⟨[.setcc cond .r8], seed (-1) (-1) flags, false⟩
      for size in [Size.b16, .b32, .b64] do
        cases := cases.push ⟨[.cmov cond size .rax (.reg .r8)], seed (-1) 0x12345678 flags, false⟩
    for op in [Instr.clc, .stc, .cmc, .nop] do cases := cases.push ⟨[op], seed 0 0 flags, false⟩
  return cases

private def divisionCases : Array NativeCase := Id.run do
  let mut cases := #[]
  for size in sizes do
    for a in [0, 1, 7, 127] do
      for b in [1, 3, 17, 127] do
        cases := cases.push ⟨[.div false size (.reg .r8)], (seed a b).setReg .rdx 0, false⟩
        for sign in [false, true] do
          let n := if sign then -Int.ofNat a.toNat else Int.ofNat a.toNat
          let state := (seed (BitVec.ofInt 64 n) b).setReg .rdx (if n < 0 then -1 else 0)
          cases := cases.push ⟨[.div true size (.reg .r8)], state, false⟩
    if size != .b8 then
      for a in values size do cases := cases.push ⟨[.signExtend size], seed a 0, false⟩
  return cases

private def memoryCases : Array NativeCase := Id.run do
  let memory : Memory := { regions := #[{
    base := 0x4000, bytes := (List.range 256).toArray.map Nat.toUInt8, writable := true }] }
  let state := { seed 0xfedcba9876543210 0x8877665544332211 63 with memory := memory }
  let mut cases := #[]
  for size in sizes do
    for offset in [0, 1, 7, 15, 127, 128, 248] do
      let addr := Address.base .r9 (BitVec.ofNat 32 offset)
      cases := cases ++ #[⟨[.mov size .rax (.mem addr)], state, true⟩,
        ⟨[.store size addr .r8, .mov .b64 .rax (.mem addr)], state, true⟩,
        ⟨[.alu .adc size .rax (.mem addr)], state, true⟩]
  return cases

private def unwrap [Repr α] (value : Except Error α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"x64 fixture rejected: {repr error}")

private def emitEncodingCases (directory : System.FilePath) : IO Nat := do
  let cases := registerEncodings ++ memoryEncodings ++ controlEncodings
  let mut lines := #[assemblyHeader]
  let mut expected := #[]
  for (instruction, i) in cases.toList.zipIdx do
    let source ← unwrap (emitInstr instruction)
    let bytes ← unwrap (encode instruction)
    lines := lines.push s!"enc_{i}:\n{source}\n"
    expected := expected.push (Json.mkObj [("source", toJson source), ("bytes", toJson (bytes.map UInt8.toNat))])
  lines := lines.push "enc_end:\n"
  IO.FS.writeFile (directory / "encodings.s") (String.join lines.toList)
  IO.FS.writeFile (directory / "encodings.json") (toJson expected).compress
  return cases.size

private def nativeFunction (name : String) (case : NativeCase) (raw : Bool) : IO String := do
  let mut source := s!".text\n.globl {name}\n{name}:\n"
  for reg in [Reg.rax, .rdx, .r8, .r9, .rcx] do
    source := source ++ s!"  movabs {regName .b64 reg}, {(case.state.getReg reg).toNat}\n"
  if case.memory then source := source ++ s!"  lea r9, [rip + {name}_memory]\n"
  source := source ++ s!"  push {2 + (flagBits case.state.flags).2}\n  popfq\n"
  for instruction in case.code do
    let line ← if raw then do
      let bytes ← unwrap (encode instruction)
      pure ("  .byte " ++ String.intercalate ", " (bytes.toList.map (toString ·.toNat)))
      else unwrap (emitInstr instruction)
    source := source ++ line ++ "\n"
  source := source ++ "  pushfq\n  pop r10\n  mov [rdi], rax\n  mov [rdi+8], rdx\n" ++
    "  mov [rdi+16], r8\n  mov [rdi+24], r10\n  ret\n"
  if case.memory then
    source := source ++ s!".data\n{name}_memory:\n  .byte " ++
      String.intercalate ", " ((List.range 256).map toString) ++ "\n"
  return source

private def emitNativeCases (directory : System.FilePath) : IO Nat := do
  let cases := arithmeticCases ++ moveAndConditionCases ++ divisionCases ++ memoryCases
  let mut source := #[assemblyHeader]
  let mut expected := #[]
  for (case, i) in cases.toList.zipIdx do
    let result ← match execSequence case.code case.state with
      | .ok state => pure state
      | .error error => throw (IO.userError s!"native case {i}: {repr case.code}: {repr error}")
    source := source.push (← nativeFunction s!"native_{i}" case false)
    source := source.push (← nativeFunction s!"encoded_{i}" case true)
    let (mask, flags) := flagBits result.flags
    expected := expected.push (Json.mkObj [("rax", toJson (result.getReg .rax).toNat),
      ("rdx", toJson (result.getReg .rdx).toNat), ("r8", toJson (result.getReg .r8).toNat),
      ("mask", toJson mask), ("flags", toJson flags), ("code", toJson (reprStr case.code))])
  IO.FS.writeFile (directory / "native.s") (String.join source.toList ++ assemblyFooter)
  IO.FS.writeFile (directory / "native.json") (toJson expected).compress
  return cases.size

private def fixtures : Symbolic.Program :=
  [.function "sum_to_n", .instr (.movImm .b64 .rax 0), .label "sum_loop",
   .instr (.aluImm .cmp .b64 .rdi 0), .branch .e "sum_done",
   .instr (.alu .add .b64 .rax (.reg .rdi)), .instr (.aluImm .sub .b64 .rdi 1),
   .jump "sum_loop", .label "sum_done", .instr .ret, .endFunction "sum_to_n",
   .function "copy_bytes", .label "copy_loop", .instr (.aluImm .cmp .b64 .rdx 0),
   .branch .e "copy_done", .instr (.mov .b8 .rax (.mem (.base .rsi))),
   .instr (.store .b8 (.base .rdi) .rax), .instr (.unary .inc .b64 .rsi),
   .instr (.unary .inc .b64 .rdi), .instr (.unary .dec .b64 .rdx), .jump "copy_loop",
   .label "copy_done", .instr .ret, .endFunction "copy_bytes",
   .function "add128", .instr (.mov .b64 .rax (.mem (.base .rsi))),
   .instr (.alu .add .b64 .rax (.mem (.base .rdx))), .instr (.store .b64 (.base .rdi) .rax),
   .instr (.mov .b64 .rax (.mem (.base .rsi 8))), .instr (.alu .adc .b64 .rax (.mem (.base .rdx 8))),
   .instr (.store .b64 (.base .rdi 8) .rax), .instr (.setcc .b .rax),
   .instr (.extend false .b8 .b64 .rax (.reg .rax)), .instr .ret, .endFunction "add128",
   .function "indirect", .instr (.push .rbx), .leaSymbol .r11 "rax", .instr (.callReg .r11),
   .instr (.pop .rbx), .instr .ret, .label "rax", .instr (.movImm .b64 .rax 73), .instr .ret,
   .endFunction "indirect", .function "sum_six", .instr (.mov .b64 .rax (.reg .rdi))] ++
  ([Reg.rsi, .rdx, .rcx, .r8, .r9].map fun r => .instr (.alu .add .b64 .rax (.reg r))) ++
  [.instr .ret, .endFunction "sum_six", .function "alignment_probe",
   .instr (.mov .b64 .rax (.reg .rsp)), .instr (.aluImm .bitAnd .b64 .rax 15),
   .instr (.aluImm .cmp .b64 .rax 8), .instr (.setcc .e .rax), .instr .ret,
   .endFunction "alignment_probe"]

private def emitFixtures (directory : System.FilePath) : IO Unit := do
  let enter ← unwrap (LeanAsm.ABI.SysVAMD64.enter 23)
  let leave ← unwrap (LeanAsm.ABI.SysVAMD64.leave 23)
  let body := [.function "abi_body"] ++ enter.map Symbolic.Line.instr ++
    (LeanAsm.ABI.SysVAMD64.calleeSaved.map fun r => .instr (.movImm .b64 r 0xdeadbeef)) ++
    [.call "alignment_probe"] ++ leave.map Symbolic.Line.instr ++ [.endFunction "abi_body"]
  let source := fixtures ++ body
  let code ← unwrap (Symbolic.lower source)
  IO.FS.writeFile (directory / "fixtures.s") (← unwrap (Symbolic.emit source))
  IO.FS.writeBinFile (directory / "fixtures.expected") ⟨← unwrap (encodeProgram code)⟩
  let data : Symbolic.Program := [.function "constant", .leaSymbol .rax "constant_data",
    .instr (.mov .b64 .rax (.mem (.base .rax))), .instr .ret, .endFunction "constant",
    .rodata, .align 3, .label "constant_data", .quad 0x123456789abcdef0]
  IO.FS.writeFile (directory / "data.s") (← unwrap (Symbolic.emit data))

def main (args : List String) : IO UInt32 := do
  let [directory] := args | throw (IO.userError "expected an output directory")
  let directory : System.FilePath := directory
  IO.FS.createDirAll directory
  let encoded ← emitEncodingCases directory
  let native ← emitNativeCases directory
  emitFixtures directory
  IO.println s!"Generated {encoded} encoding cases and {native} native/model cases"
  return 0
