# LeanAsm design

## Goal

Provide one runtime-neutral Lean 4 foundation for the three assembly projects,
using evm-asm as the reference architecture but without depending on or
modifying evm-asm and without depending on riscv-zkvm.

## Layers

```text
project specifications and routines
              |
        LeanAsm.SAsm
              |
   LeanAsm.Rv64.Execution
       /              \
Encoding / Emit    Region Memory
```

### Fixed-width ISA

`Rv64.Instr` is the semantic and binary-encoding boundary. Every value is one
32-bit instruction. This prevents assembler pseudo expansion from silently
changing proved instruction counts or branch offsets.

### Symbolic assembly

Symbols, data sections, and pseudo instructions remain useful for generated
libraries. They are represented separately. A future relocation pass will
lower this layer deterministically to fixed-width instructions and data.

### Memory

The first concrete memory model uses finite disjoint regions. Each access
checks:

- memory validity,
- supported width,
- full-byte-range containment,
- natural alignment,
- write permission.

Code is immutable and checked separately from writable data regions.

### SAsm

The initial common denominator contains block, sequence, conditional, loop,
direct call, and return. Verification annotations are deliberately not stored
in the core AST. A later proof layer can attach invariants and contracts without
making syntax and lowering depend on one project's assertion language.

## Trust boundary

The present implementation supplies an executable model and encoder, but does
not yet prove:

- encoder/decoder round trips,
- equivalence with physical RISC-V hardware,
- equivalence with GNU binutils or QEMU,
- correctness of symbolic pseudo-instruction expansion,
- whole-program SAsm lowering soundness,
- operating-system or MMU behavior.

These are explicit future proof obligations rather than inherited claims.
