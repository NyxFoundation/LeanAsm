import LeanAsm.Rv64.Execution

/-! Execution-level checks for load extension, M-extension, and division
    edge cases. Run with `lake env lean Tests/Execution.lean`. -/

open LeanAsm.Rv64

namespace Tests

private def seeded (regs : List (Reg × Word)) : State :=
  regs.foldl (fun s (r, w) => s.setReg r w) { pc := 0 }

private def okEq {ε α} [BEq α] (result : Except ε α) (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

/-- Execute without fetching and observe the listed register values. -/
def run (code : List Instr) (regs : List (Reg × Word)) (observe : List Reg) :
    Except Trap (List Word) :=
  match execProgram code (seeded regs) with
  | .ok s => .ok (observe.map s.getReg)
  | .error e => .error e

private def oneByteMemory : Memory :=
  { regions := #[{ base := 0x1000, bytes := #[0xFF], writable := false }] }

private def twoByteMemory : Memory :=
  { regions := #[{ base := 0x1000, bytes := #[0xFF, 0x80, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06], writable := false }] }

private def withMemory (source : Memory) : State :=
  { seeded [(.x10, 0x1000)] with memory := source }

/-- Load into `x11` from byte 0 of the region based at 0x1000. -/
def load (source : Memory) (code : List Instr) : Except Trap Word :=
  match execProgram code (withMemory source) with
  | .ok s => .ok (s.getReg .x11)
  | .error e => .error e

end Tests

#guard Tests.okEq (Tests.run [.REMU .x11 .x10 .x0] [(.x10, 7)] [.x10, .x11]) [7, 7]
#guard Tests.okEq (Tests.run [.DIVU .x11 .x10 .x0] [(.x10, 7)] [.x10, .x11])
  [7, BitVec.allOnes 64]
#guard Tests.okEq
  (Tests.run [.MULHU .x11 .x10 .x1] [(.x10, 1 <<< 63), (.x1, 2)]
    [.x10, .x1, .x11]) [1 <<< 63, 2, 1]
#guard Tests.okEq
  (Tests.run [.MUL .x11 .x10 .x1] [(.x10, 1 <<< 63), (.x1, 2)] [.x11]) [0]
#guard Tests.okEq
  (Tests.run [.MULHSU .x11 .x10 .x1] [(.x10, 1 <<< 63), (.x1, 2)] [.x11])
  [BitVec.allOnes 64]
#guard Tests.okEq
  (Tests.run [.MULH .x11 .x10 .x1] [(.x10, 1 <<< 63), (.x1, 2)] [.x11])
  [BitVec.allOnes 64]
#guard Tests.okEq
  (Tests.run [.ADDIW .x11 .x10 1] [(.x10, 0x7FFFFFFF)] [.x11])
  [(0x80000000 : BitVec 32).signExtend 64]
#guard Tests.okEq
  (Tests.run [.SRLI .x11 .x10 63] [(.x10, BitVec.allOnes 64)] [.x11]) [1]
#guard Tests.okEq
  (Tests.run [.SRAI .x11 .x10 63] [(.x10, BitVec.allOnes 64)] [.x11])
  [BitVec.allOnes 64]
#guard Tests.okEq
  (Tests.run [.SLTU .x11 .x10 .x1] [(.x10, 7), (.x1, 8)] [.x11]) [1]

#guard Tests.okEq (Tests.load Tests.oneByteMemory [.LBU .x11 .x10 0]) 0xFF
#guard Tests.okEq (Tests.load Tests.oneByteMemory [.LB .x11 .x10 0])
  (BitVec.allOnes 64)
#guard Tests.okEq (Tests.load Tests.twoByteMemory [.LHU .x11 .x10 0]) 0x80FF
#guard Tests.okEq (Tests.load Tests.twoByteMemory [.LWU .x11 .x10 0]) 0x020180FF
#guard Tests.okEq (Tests.load Tests.twoByteMemory [.LH .x11 .x10 0])
  (0x80FF ||| (BitVec.allOnes 64 <<< 16))
