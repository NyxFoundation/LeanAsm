# LeanAsm

LeanAsm is a reusable Lean 4 foundation for typed RV64IM and scalar x86-64
assembly, executable machine semantics, encoding, and source emission.
The structured SAsm lowering layer currently targets RV64IM.

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
| `LeanAsm.Rv64.Profile` | Stable opcode tags and consumer ISA allow-lists |
| `LeanAsm.Rv64.Execution` | Trap-aware execution and instruction fetch |
| `LeanAsm.Rv64.Encoding` | Little-endian 32-bit machine-code encoding |
| `LeanAsm.Rv64.Emit` | GNU-as output for real instructions |
| `LeanAsm.SAsm.Ast` | Minimal structured control-flow syntax |
| `LeanAsm.SAsm.Flatten` | Position-aware lowering and offset checks |
| `LeanAsm.Symbolic` | Labels, data, relocations, and GNU pseudo instructions |
| `LeanAsm.Frontend` | `EmitAsm`, `LowerRv64`, and `LowerX64` capability APIs |
| `LeanAsm.ABI.LP64` | RISC-V integer ABI register and stack-frame helpers |
| `LeanAsm.X64` | Scalar x86-64 instructions, flags, memory, encoding, and execution |
| `LeanAsm.X64.Symbolic` | Labels, closed-code relocation, and GNU assembly/data output |
| `LeanAsm.ABI.SysVAMD64` | System V AMD64 integer registers and aligned stack frames |

## Design boundaries

- `Rv64.Instr` contains only one-word real instructions.
- Consumers restrict that shared instruction type with `IsaProfile`; they do
  not introduce another instruction inductive merely to obtain a subset.
- Source languages integrate through `EmitAsm`, `LowerRv64`, and `LowerX64`.
  A source may provide assembly emission without instruction lowering.
- `X64.Instr` models real, variable-length instructions. Encoding determines
  instruction lengths; undefined flags remain explicit and trap when consumed.
- RISC-V pseudo instructions such as `li`, `la`, `call symbol`, and `ret`
  are represented by `LeanAsm.Symbolic`, not by RV64 execution semantics.
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

## x86-64

On Linux x86-64, generate and run the C-callable example:

```sh
lake build
mkdir -p build
lake env lean --run Examples/X64.lean > build/x64.s
gcc -Wall -Wextra -Werror Examples/X64.c build/x64.s -o build/x64-example
./build/x64-example
python3 Tests/X64/check.py
```

The example prints `5050`. See [x86-64 foundation](docs/x64.md) for prerequisites,
supported operand forms, model boundaries, and the System V AMD64 ABI.

## Consumer integration

These consumers still target RISC-V. The x86-64 foundation does not migrate
their routines or proofs automatically.

- `p2p-asm` lowers structured code to `Rv64.Instr` and states its accepted
  opcodes with an `IsaProfile`.
- `cl-asm` retains `riscv-zkvm` as its proof frontend and provides a partial
  `LowerRv64` adapter for portable code generation.
- `ssz-asm` uses `LeanAsm.Symbolic` directly and provides assembly emission,
  without claiming fixed-width lowering for labels and pseudo instructions.

See [docs/design.md](docs/design.md) and [NOTICE.md](NOTICE.md).
