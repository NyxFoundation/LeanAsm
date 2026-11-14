# LeanAsm agent guidance

## Build surface

- Repository-declared default build target: the `LeanAsm` library in
  `lakefile.toml` (`lake build`), using the `lean-toolchain` pin.
- No separate Lake test, lint, or executable target or CI workflow is checked in.
- After `lake build`, run the standalone RV64 checks with `lake env lean` on
  `Tests/Execution.lean`, `Tests/Emit.lean`, and `Tests/Rv64/SAsm.lean`.
  `lake env lean --run Tests/EmitBytes.lean` also needs GNU RISC-V binutils.
- On Linux x86-64, `python3 Tests/X64/check.py` builds the library and checks
  Lean semantics, GNU encoding agreement, native execution, and the C ABI.

## Change boundaries

- Keep `Rv64.Instr` fixed-width: one real 32-bit instruction per value.
  Labels, data, and GNU pseudo-instructions belong in `LeanAsm.Symbolic`,
  outside execution and binary encoding. The core has no ECALL or zkVM operations.
- Instruction additions span `LeanAsm/Rv64/Basic.lean`, `Profile.lean`,
  `Execution.lean`, `Encoding.lean`, and `Emit.lean`. In `Profile.lean`, update
  `Opcode`, `Opcode.all`, and `Instr.opcode`; also check `Instr.isControl`
  in `Basic.lean`, whose catch-all otherwise classifies new instructions as non-control.
- Express consumer ISA subsets with `IsaProfile.allowed`, not another instruction
  type. Explicit allow-lists reject unlisted opcodes; `IsaProfile.rv64im` uses
  `Opcode.all` instead.
- Keep structured RV64 assembly in `LeanAsm.Rv64.SAsm`; its registers,
  conditions, and fixed-width lowering are RISC-V-specific.
- `LeanAsm/Frontend.lean` separates `EmitAsm` from `LowerRv64` and `LowerX64`.
  `LeanAsm.Symbolic.Program` has emission only; do not equate assembly emission
  with fixed-width lowering. `Rv64.SAsm.Source.base` matters because lowering
  is position-dependent.

## Semantic pitfalls

- Use `Stmt.lower` in `LeanAsm/Rv64/SAsm/Flatten.lean` for checked RV64 lowering.
  `offsetsOk` checks displacement ranges and rejects control instructions inside
  `.block`; raw `Stmt.flatten` can truncate out-of-range offsets.
  Preserve `flatten_length` when changing statement sizes or lowering layouts.
- `execProgram` / `execSequence` in `LeanAsm/Rv64/Execution.lean` fold over the
  supplied list even when branches change the PC. Use image-based `runUntil`
  for PC-directed instruction fetching, validity checks, and fuel-limited execution.
- RV64 encoding rejects odd branch/JAL displacements, but execution requires jump
  targets aligned to four bytes. Successful encoding does not establish runtime alignment.
- RV64 data accesses must fit entirely within one valid region; regions are disjoint,
  supported widths are 1/2/4/8 bytes, accesses are naturally aligned, and stores
  require write permission. Executable code is separate from data memory.

## Proof scope

- `flatten_length` proves instruction count, not execution correctness.
  `docs/design.md` records outstanding whole-program lowering soundness and
  hardware/toolchain equivalence obligations. `NOTICE.md` records source
  provenance, not inherited correctness theorems.
