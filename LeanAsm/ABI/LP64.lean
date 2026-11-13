import LeanAsm.Rv64.Basic

/-! Minimal LP64 integer calling-convention helpers. -/

namespace LeanAsm.ABI.LP64

open LeanAsm.Rv64

def calleeSaved : List Reg :=
  [.ra, .s0, .s1, .s2, .s3, .s4, .s5, .s6,
    .s7, .s8, .s9, .s10, .s11]

def localSize (locals : Nat) : Nat :=
  (locals + 15) / 16 * 16

def frameSize (locals : Nat) : Nat :=
  localSize locals + 112

def frameFits (locals : Nat) : Bool :=
  decide (frameSize locals ≤ 2047)

def enter (locals : Nat := 0) : Except String (List Instr) := do
  unless frameFits locals do
    throw "LP64 frame does not fit signed 12-bit stack adjustments"
  let localBytes := localSize locals
  return [.ADDI .sp .sp (BitVec.ofInt 12 (-(Int.ofNat (frameSize locals))))] ++
    calleeSaved.zipIdx.map (fun (r, i) =>
      .SD .sp r (BitVec.ofNat 12 (localBytes + 8 * i)))

def leave (locals : Nat := 0) : Except String (List Instr) := do
  unless frameFits locals do
    throw "LP64 frame does not fit signed 12-bit stack adjustments"
  let localBytes := localSize locals
  return calleeSaved.zipIdx.map (fun (r, i) =>
      .LD r .sp (BitVec.ofNat 12 (localBytes + 8 * i))) ++
    [.ADDI .sp .sp (BitVec.ofNat 12 (frameSize locals)),
     .JALR .x0 .ra 0]

end LeanAsm.ABI.LP64
