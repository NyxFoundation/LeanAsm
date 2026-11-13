# Third-party provenance

LeanAsm's architecture and structured-assembly lowering are adapted from:

- Verified-zkEVM/evm-asm,
  commit `7e65e4d024718f704226cd795f3d03d4e9aafe13`,
  copyright (c) 2026 ZkSecurity, MIT license.

The initial region-memory, executable-state, encoder, and compact structured
assembly implementation were adapted from:

- adust09/libp2p-asm,
  commit `f44d410b73aae7ed67d98b1b929fb25d96aa3a3a`.

That implementation records its RV64 register/instruction representation as
adapted from:

- Verified-zkEVM/riscv-zkvm,
  commit `afcbc45e1c74c2d296e032b5606dd977a304e8ad`,
  with the retained BSD-2-Clause notice in `LICENSES/riscv-zkvm.txt`.

The symbolic GNU assembly representation and LP64 frame helpers are adapted
from:

- NyxFoundation/ssz-asm,
  commit `42ada4ea1e814fa96fce42ada2d0e19ca990eafc`,
  with its retained MIT notice in `LICENSES/ssz-asm.txt`; that project itself
  records adaptation from evm-asm.

LeanAsm does not import the Sail model, riscv-zkvm package, evm-asm package, or
their correctness theorems. These notices record source provenance only.
