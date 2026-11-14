import LeanAsm

open LeanAsm.X64

local instance : BEq Instr where
  beq a b := decide (a = b)

local instance [BEq α] : BEq (Except Error α) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false

private def initial : State :=
  ({} : State).setReg .rax 0xffffffffffffffff |>.setReg .r8 1

private def regAfter (instruction : Instr) (state : State := initial) (reg : Reg := .rax) :=
  (execInstr instruction state).map (·.getReg reg)

-- should preserve upper bits for byte/word writes and clear them for dword writes
#guard regAfter (.movImm .b8 .rax 0x12) == .ok 0xffffffffffffff12
#guard regAfter (.movImm .b16 .rax 0x1234) == .ok 0xffffffffffff1234
#guard regAfter (.movImm .b32 .rax 0x12345678) == .ok 0x12345678
#guard regAfter (.mov .b8 .rsp (.reg .r8)) initial .rsp == .ok 1
#guard (encode (.mov .b8 .rsp (.reg .rax))) == .ok #[0x40, 0x88, 0xc4]
#guard (encode (.mov .b64 .r9 (.mem (.base .r13)))) == .ok #[0x4d, 0x8b, 0x4d, 0]
#guard (encode (.mov .b64 .r8 (.mem (.indexed (some .r13) .r12 .eight (-129))))) ==
  .ok #[0x4f, 0x8b, 0x84, 0xe5, 0x7f, 0xff, 0xff, 0xff]

-- should reject unencodable operands in both the encoder and execution
#guard (encode (.mov .b64 .rax (.mem (.indexed none .rsp .two)))) == .error .invalidAddress
#guard (encode (.cmov .e .b8 .rax (.reg .r8))) == .error .invalidOperand
#guard (encode (.extend false .b32 .b64 .rax (.reg .r8))) == .error .invalidOperand
#guard (encode (.extend true .b64 .b64 .rax (.reg .r8))) == .error .invalidOperand
#guard (encode (.imul .b8 .rax (.reg .r8))) == .error .invalidOperand
#guard (encode (.signExtend .b8)) == .error .invalidOperand
#guard (regAfter (.bswap .b16 .rax)) == .error .invalidOperand
#guard (emitInstr (.cmov .e .b8 .rax (.reg .r8))) == .error .invalidOperand

-- should calculate carry, borrow, signed overflow, and auxiliary carry independently
#guard (execInstr (.alu .add .b64 .rax (.reg .r8)) initial).map (·.flags) ==
  .ok { cf := some true, pf := some true, af := some true, zf := some true }
#guard (execInstr (.aluImm .adc .b8 .rax 0) { initial with flags := { cf := some true } }).map
  (fun s => (s.getReg .rax, s.flags.cf, s.flags.af)) ==
  .ok (0xffffffffffffff00, some true, some true)
#guard (execInstr (.aluImm .sbb .b8 .rax 255)
    { initial with flags := { cf := some true } }).map
  (fun s => (s.getReg .rax, s.flags.cf)) == .ok (0xffffffffffffffff, some true)
#guard (execInstr (.aluImm .add .b8 .rax 1) (initial.setReg .rax 127)).map
  (·.flags.of) == .ok (some true)
#guard (regAfter (.aluImm .cmp .b32 .rax 0)) == .ok 0xffffffffffffffff
#guard (regAfter (.aluImm .test .b32 .rax 0)) == .ok 0xffffffffffffffff
#guard (execInstr (.unary .inc .b64 .rax) { initial with flags := Flags.undefined }).map
  (·.flags.cf) == .ok none
#guard regAfter (.aluImm .adc .b64 .rax 0) { initial with flags := Flags.undefined } ==
  .error .undefinedFlag
#guard (Cond.e.eval Flags.undefined) == .error .undefinedFlag

-- should preserve flags on masked-zero shifts and mark architecturally undefined flags
#guard (execInstr (.shift .shl .b32 .rax (.imm 32)) initial).map
  (fun s => (s.getReg .rax, s.flags)) == .ok (0xffffffff, initial.flags)
#guard (execInstr (.shift .shr .b8 .rax (.imm 8)) initial).map
  (fun s => (s.flags.cf, s.flags.of, s.flags.af)) == .ok (none, none, none)
#guard (regAfter (.shift .sar .b8 .rax (.imm 7))) == .ok 0xffffffffffffffff
#guard (execInstr (.shift .rol .b8 .rax (.imm 8)) initial).map
  (fun s => (s.flags.cf, s.flags.of)) == .ok (some true, none)
#guard (execInstr (.shift .ror .b8 .rax (.imm 9)) initial).map
  (·.flags.of) == .ok none
#guard regAfter (.cmov .e .b32 .rax (.reg .r8)) initial == .ok 0xffffffff

-- should implement the implicit accumulator pairs and trap on divide overflow
#guard (execInstr (.mul false .b64 (.reg .r8)) (initial.setReg .r8 2)).map
  (fun s => (s.getReg .rax, s.getReg .rdx, s.flags.cf)) ==
  .ok (0xfffffffffffffffe, 1, some true)
#guard regAfter (.mul false .b8 (.reg .r8)) (initial.setReg .r8 2) ==
  .ok 0xffffffffffff01fe
#guard regAfter (.div false .b8 (.reg .r8)) (initial.setReg .rax 512 |>.setReg .r8 2) ==
  .error .divisionError
#guard regAfter (.div false .b64 (.reg .r8)) (initial.setReg .r8 0) == .error .divisionError
#guard regAfter (.div true .b64 (.reg .r8))
  (initial.setReg .rax (2^63) |>.setReg .rdx 0xffffffffffffffff |>.setReg .r8 0xffffffffffffffff) ==
  .error .divisionError
#guard (execSequence [.signExtend .b64, .div true .b64 (.reg .r8)]
    (initial.setReg .rax (-7) |>.setReg .r8 3)).map
  (fun s => (s.getReg .rax, s.getReg .rdx, s.flags)) ==
  .ok (-2, -1, Flags.undefined)

private def memory : Memory :=
  { regions := #[{ base := 0x1000, bytes := (List.range 64).toArray.map Nat.toUInt8, writable := true }] }
private def withMemory : State :=
  { initial.setReg .r9 0x1000 |>.setReg .rsp 0x1040 with memory := memory, rip := 0x2000 }

-- should allow unaligned accesses but reject bounds, overlapping regions, and writes to read-only data
#guard memory.load .b32 0x1001 == .ok 0x04030201
#guard memory.load .b64 0x1039 == .error .memoryBounds
#guard memory.load .b8 0xffffffffffffffff == .error .memoryBounds
#guard (memory.store .b64 0x1001 0x8877665544332211 >>= (·.load .b64 0x1001)) ==
  .ok 0x8877665544332211
#guard (Memory.load { regions := memory.regions ++ memory.regions } .b8 0x1000) == .error .invalidMemory
#guard (Memory.store { regions := memory.regions.map (fun r => { r with writable := false }) }
  .b8 0x1000 0).map (fun _ => ()) == .error .readOnlyMemory
#guard regAfter (.mov .b32 .rax (.mem (.base .r9 1))) withMemory == .ok 0x04030201
#guard regAfter (.cmov .e .b64 .rax (.mem (.base .rax))) withMemory == .error .memoryBounds
#guard regAfter (.lea .rax (.rip 3)) withMemory == .ok 0x200a
#guard regAfter (.lea .rax (.indexed (some .r9) .r8 .eight (-4))) withMemory == .ok 0x1004

-- should use next RIP and a real stack for calls and returns
#guard (execInstr (.jcc .ne (-6)) withMemory).map (·.rip) == .ok 0x2000
#guard (execInstr (.call 10) withMemory).map
  (fun s => (s.rip, s.getReg .rsp, s.memory.load .b64 0x1038)) == .ok (0x200f, 0x1038, .ok 0x2005)
#guard (execSequence [.call 10, .ret] withMemory).map
  (fun s => (s.rip, s.getReg .rsp)) == .ok (0x2005, 0x1040)
#guard (execInstr (.callReg .rsp) withMemory).map (·.rip) == .ok 0x1040
#guard (execSequence [.push .rsp, .pop .rax] withMemory).map (·.getReg .rax) == .ok 0x1040
#guard (execSequence [.push .r9, .pop .rsp] withMemory).map (·.getReg .rsp) == .ok 0x1000
#guard regAfter .ret initial == .error .memoryBounds

private def loopSource : Symbolic.Program :=
  [.function "sum_to_n", .instr (.movImm .b64 .rax 0), .label "again",
   .instr (.aluImm .cmp .b64 .rdi 0), .branch .e "done",
   .instr (.alu .add .b64 .rax (.reg .rdi)), .instr (.aluImm .sub .b64 .rdi 1),
   .jump "again", .label "done", .instr .nop, .endFunction "sum_to_n"]

private def runSum : Except Error (Word × Nat) := do
  let code ← LeanAsm.lowerX64 loopSource
  let bytes ← encodeProgram code
  let image : Image := ⟨0x2000, code⟩
  let result ← runUntil image (0x2000 + BitVec.ofNat 64 bytes.size) 100 (withMemory.setReg .rdi 5)
  return (result.state.getReg .rax, result.steps)

-- should lay out variable-length code consistently and reject unresolved or malformed programs
#guard runSum == .ok (15, 29)
#guard (Image.fetch ⟨0x2000, [.movImm .b64 .rax 0, .ret]⟩ 0x2001) == .error .instructionBounds
#guard !(Image.valid ⟨0x1000, [.nop]⟩ memory)
#guard (runUntil ⟨0x2000, [.jmp (-5)]⟩ 0x2005 5 withMemory).map (fun _ => ()) ==
  .error .fuelExhausted
#guard Symbolic.lower [.label "same", .label "same"] == .error .duplicateSymbol
#guard Symbolic.lower [.jump "missing"] == .error .undefinedSymbol
#guard Symbolic.lower [.rodata, .quad 0] == .error .unsupportedRelocation
#guard Symbolic.displacement 0 (2^31) == .error .displacementOutOfRange
#guard Symbolic.displacement (2^31) 0 == .ok (BitVec.ofNat 32 (2^31))
#guard (Symbolic.emit [.jump "foo\nret"]) == .error .invalidSymbol
#guard (emitProgram "rax;ret" []) == .error .invalidSymbol
#guard (Symbolic.emit [.label "x", .label "x"]) == .error .duplicateSymbol
#guard (LeanAsm.emitAsm "identity" ([.mov .b64 .rax (.reg .rdi), .ret] : Program)).isOk

-- should reserve sufficient local storage and align nested calls for every small frame size
#guard (List.range 128).all (fun n =>
  let allocation := LeanAsm.ABI.SysVAMD64.localAllocation n
  allocation ≥ n && (allocation + 48 + 8) % 16 == 0)
#guard (LeanAsm.ABI.SysVAMD64.enter (2^31)).toOption.isNone
