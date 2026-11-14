import LeanAsm.Rv64.Encoding
import LeanAsm.Rv64.Emit

/- Byte-level agreement of `Rv64.encode` with the GNU RISC-V assembler.
    Run with `lake env lean --run Tests/EmitBytes.lean`; requires
    `riscv64-unknown-elf-as` and `riscv64-unknown-elf-objcopy` on PATH. -/

open LeanAsm.Rv64

/-- One machine word per instruction, in listing order. -/
def samples : Array Instr :=
  #[.ADD .x5 .x10 .x5, .SUB .x7 .x0 .x5, .SLL .x5 .x10 .x6, .SRL .x5 .x10 .x6,
    .SRA .x5 .x10 .x6, .AND .x29 .x29 .x31, .OR .x30 .x30 .x2,
    .XOR .x31 .x31 .x16, .SLT .x5 .x5 .x6, .SLTU .x5 .x5 .x6,
    .ADDW .x14 .x15 .x16, .SUBW .x14 .x15 .x16,
    .ADDI .x5 .x5 4095, .ANDI .x5 .x5 15, .ORI .x28 .x28 2,
    .XORI .x5 .x5 1, .SLTI .x5 .x5 7, .SLTIU .x5 .x5 1,
    .SLLI .x5 .x10 1, .SRLI .x31 .x30 63, .SRAI .x5 .x30 47,
    .ADDIW .x14 .x15 2047, .SLLIW .x5 .x10 16, .SRLIW .x28 .x28 31,
    .LUI .x28 0x3B9AD, .AUIPC .x28 0x3B9AD,
    .LB .x15 .x10 2047, .LH .x15 .x10 2047, .LW .x15 .x10 2047,
    .LD .x5 .x10 4095, .LBU .x15 .x10 3, .LHU .x15 .x10 2,
    .LWU .x15 .x10 4, .SB .x10 .x5 2047, .SH .x10 .x5 2047,
    .SW .x10 .x5 2047, .SD .x10 .x5 32,
    .BEQ .x10 .x5 8, .BNE .x29 .x0 12, .BLT .x10 .x5 8,
    .BGE .x10 .x5 8, .BLTU .x10 .x5 8, .BGEU .x10 .x5 8,
    .JAL .x0 60, .JALR .x0 .x1 0,
    .MUL .x5 .x10 .x5, .MULH .x5 .x10 .x5, .MULHSU .x5 .x10 .x5,
    .MULHU .x5 .x10 .x5, .DIV .x5 .x10 .x5, .DIVU .x5 .x10 .x5,
    .REM .x5 .x10 .x5, .REMU .x5 .x10 .x5, .FENCE]

/-- Same assembly prologue that `Rv64.emitProgram` emits, followed by one
    rendered instruction per line. -/
def gnuSource : String :=
  ".option norvc\n.option norelax\n.attribute arch, \"rv64im\"\n" ++
    ".text\n.balign 4\n" ++
    String.join (samples.toList.map (fun instruction =>
      s!"  {emitInstr instruction}\n"))

def main : IO UInt32 := do
  let directory : System.FilePath := ".build"
  IO.FS.createDirAll directory
  let source := directory / "emit-bytes.s"
  let object := directory / "emit-bytes.o"
  let raw := directory / "emit-bytes.bin"
  IO.FS.writeFile source gnuSource
  let assembleSpec : IO.Process.SpawnArgs :=
    { cmd := "riscv64-unknown-elf-as", args := #["-march=rv64im", "-mno-relax",
      "--fatal-warnings", "-o", object.toString, source.toString] }
  let assemble ← IO.Process.output assembleSpec
  unless assemble.exitCode == 0 do
    IO.eprintln s!"GNU as failed:\n{assemble.stderr}"
    return 1
  let extract : IO.Process.SpawnArgs :=
    { cmd := "riscv64-unknown-elf-objcopy",
      args := #["-O", "binary", object.toString, raw.toString] }
  let extracted ← IO.Process.output extract
  unless extracted.exitCode == 0 do
    IO.eprintln s!"objcopy failed:\n{extracted.stderr}"
    return 1
  let bytes ← IO.FS.readBinFile raw
  if bytes.size != 4 * samples.size then
    IO.eprintln s!"GNU encoded {bytes.size} bytes, expected {4 * samples.size}"
    return 1
  let mut failures := 0
  for h : index in [0:samples.size] do
    let word := samples[index]
    match encode word with
    | .error error => do
      IO.eprintln s!"#{index}: encoding rejected: {repr error}"
      failures := failures + 1
    | .ok encoded =>
      let gnu := bytes[4 * index]!.toUInt32.toNat +
        bytes[4 * index + 1]!.toUInt32.toNat * 256 +
        bytes[4 * index + 2]!.toUInt32.toNat * 65536 +
        bytes[4 * index + 3]!.toUInt32.toNat * 16777216
      unless encoded.toNat == gnu do
        IO.eprintln (s!"#{index}: {emitInstr word}: LeanAsm {encoded.toNat} " ++
          s!"vs GNU {gnu}")
        failures := failures + 1
  IO.println
    (if failures == 0
     then s!"encode agrees with GNU as on {samples.size} instructions"
     else s!"{failures} of {samples.size} instruction encodings disagree")
  return if failures == 0 then 0 else 1
