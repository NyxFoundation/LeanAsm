import LeanAsm.Rv64.Emit

/- GNU-as rendering checks, including unsigned shift amounts at range
    boundaries. Run with `lake env lean Tests/Emit.lean`. -/

open LeanAsm.Rv64

#guard emitInstr (.SRLI .x31 .x30 63) == "srli x31, x30, 63"
#guard emitInstr (.SLLI .x5 .x10 63) == "slli x5, x10, 63"
#guard emitInstr (.SRAI .x5 .x30 47) == "srai x5, x30, 47"
#guard emitInstr (.SRLI .x5 .x5 31) == "srli x5, x5, 31"
#guard emitInstr (.SRLIW .x28 .x28 31) == "srliw x28, x28, 31"
#guard emitInstr (.SLLIW .x5 .x10 16) == "slliw x5, x10, 16"
#guard emitInstr (.ADDI .x5 .x5 4095) == "addi x5, x5, -1"
#guard emitInstr (.LD .x5 .x10 4095) == "ld x5, -1(x10)"
#guard emitInstr (.SD .x10 .x5 32) == "sd x5, 32(x10)"
#guard emitInstr (.LUI .x28 0x3B9AD) == "lui x28, 244141"
#guard emitInstr (.AUIPC .x28 0x3B9AD) == "auipc x28, 244141"
#guard emitInstr (.BEQ .x10 .x5 8) == "beq x10, x5, . + 8"
#guard emitInstr (.JAL .x0 60) == "jal x0, . + 60"
