# LeanAsm

LeanAsm is a reusable Lean 4 foundation for typed RV64IM assembly, executable
machine semantics, structured assembly lowering, encoding, and source emission.

It is intended to be shared by:

- `ssz-asm`
- `cl-asm`
- `p2p-asm`

The architecture follows the verified macro-assembly approach demonstrated by
[Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm), while
remaining independent of EVM, zkVM execution, and `riscv-zkvm`.

## Modules

| Module | Purpose |
| --- | --- |
| `LeanAsm.Rv64.Basic` | Registers and real, fixed-width RV64IM instructions |
| `LeanAsm.Rv64.Memory` | Finite disjoint byte regions and write permissions |
| `LeanAsm.Rv64.State` | Register state and placed executable images |
| `LeanAsm.Rv64.Program` | Flat instruction programs and composition |
| `LeanAsm.Rv64.Execution` | Trap-aware execution and instruction fetch |
| `LeanAsm.Rv64.Encoding` | Little-endian 32-bit machine-code encoding |
| `LeanAsm.Rv64.Emit` | GNU-as output for real instructions |
| `LeanAsm.SAsm.Ast` | Minimal structured control-flow syntax |
| `LeanAsm.SAsm.Flatten` | Position-aware lowering and offset checks |
| `LeanAsm.Symbolic` | Labels, data, relocations, and GNU pseudo instructions |
| `LeanAsm.ABI.LP64` | Integer ABI register and stack-frame helpers |

## Design boundaries

- `Rv64.Instr` contains only one-word real instructions.
- Pseudo instructions such as `li`, `la`, `call symbol`, and `ret` are
  represented by `LeanAsm.Symbolic`, not by the execution semantics.
- Code and data memory are separate. Data memory is a finite list of disjoint
  regions with explicit write permission.
- No zkVM input/output, commit operation, custom ECALL, or accelerator is part
  of the portable core.
- The current SAsm layer proves lowering size and checks offset ranges. Full
  Hoare/separation-logic extraction is a later milestone.

## Dependency

```toml
[[require]]
name = "LeanAsm"
git = "https://github.com/NyxFoundation/LeanAsm"
rev = "<commit>"
```

```lean
import LeanAsm.Rv64.Execution
import LeanAsm.SAsm.Flatten

open LeanAsm.Rv64
```

## Migration order

1. Share the portable RV64 vocabulary and encoders with `p2p-asm` while
   preserving its deliberately finite proof profile.
2. Move `ssz-asm`'s symbolic assembly and ABI helpers to LeanAsm.
3. Port `cl-asm` programs and proofs from their current machine model.
4. Extract reusable Hoare, frame, separation, and SAsm soundness infrastructure.

See [docs/design.md](docs/design.md) and [NOTICE.md](NOTICE.md).
