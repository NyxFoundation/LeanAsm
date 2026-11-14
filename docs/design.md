---
title: LeanAsm design
last_updated: 2026-11-15
tags:
  - architecture
  - assembly
  - semantics
---

# LeanAsm design

## Goal

Provide one runtime-neutral Lean 4 foundation for the three assembly projects,
using evm-asm as the reference architecture but without depending on or
modifying evm-asm and without depending on riscv-zkvm.

## Layers

```text
project specifications and routines
              |
      LeanAsm.Rv64.SAsm
              |
   LeanAsm.Rv64.Execution
       /              \
Encoding / Emit    Region Memory
```

The diagram describes the existing RV64 path. `LeanAsm.X64` supplies a
separate scalar x86-64 instruction, encoding, and execution path, with
`X64.Symbolic` for labels and data and `ABI.SysVAMD64` for C calls.
The shared frontend capabilities select the target explicitly.
`LeanAsm.Rv64.SAsm` is an RV64 layer, not a target-neutral representation.

### Fixed-width ISA

`Rv64.Instr` is the semantic and binary-encoding boundary. Every value is one
32-bit instruction. This prevents assembler pseudo expansion from silently
changing proved instruction counts or branch offsets.

### Variable-length ISA

`X64.Instr` represents real instructions with physical registers and explicit
operand widths. Encoding validates operand combinations and defines byte
lengths used by execution and layout. Conditions consume explicit flags;
architecturally undefined flags are not assigned arbitrary Boolean values.
See [x86-64 foundation](x64.md) for the supported subset and execution limits.

### Symbolic assembly

Symbols, data sections, and pseudo instructions remain separate from the
machine instruction types. The RV64 symbolic layer is source-emission-only;
a future relocation pass can lower it to fixed-width instructions and data.
`X64.Symbolic.lower` resolves closed code using fixed rel32 branches, while
external references and data placement remain the assembler/linker's job.

### Memory

Both backends use finite disjoint regions. The RV64 memory model remains
unchanged to preserve consumers' existing proof definitions. Each RV64 access
checks:

- memory validity,
- supported width,
- full-byte-range containment,
- natural alignment,
- write permission.

X64 has a separate unaligned-access model. Its scalar width type restricts
access widths; containment and write-permission checks remain mandatory.
Code is immutable and checked separately from writable data regions in both.

### RV64 structured assembly

`LeanAsm.Rv64.SAsm` contains blocks, sequences, conditionals, loops, direct
calls, and returns. Conditions and blocks use RV64 registers and instructions;
lowering uses fixed four-byte instruction sizes. Verification annotations are
not stored in the core AST. A later proof layer can attach invariants and
contracts without making syntax and lowering depend on one project's assertion
language.

After `lake build`, run the structured lowering regression checks with:

```sh
lake env lean Tests/Rv64/SAsm.lean
```

## Trust boundary

The present implementation supplies an executable model and encoder, but does
not yet prove:

- encoder/decoder round trips,
- equivalence with physical RISC-V or x86-64 hardware,
- equivalence with GNU binutils or QEMU,
- correctness of symbolic pseudo-instruction expansion,
- whole-program RV64 SAsm lowering soundness,
- operating-system or MMU behavior.

These are explicit future proof obligations rather than inherited claims.
The x86-64 differential and C ABI tests provide runtime evidence, not
formal proofs or automatic transfer of the RV64 verification results.
