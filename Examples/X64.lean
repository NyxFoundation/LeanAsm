import LeanAsm.X64

open LeanAsm.X64

def sumToN : Symbolic.Program :=
  [.function "sum_to_n",
   .instr (.movImm .b64 .rax 0),
   .label "loop",
   .instr (.aluImm .cmp .b64 .rdi 0),
   .branch .e "done",
   .instr (.alu .add .b64 .rax (.reg .rdi)),
   .instr (.aluImm .sub .b64 .rdi 1),
   .jump "loop",
   .label "done",
   .instr .ret,
   .endFunction "sum_to_n"]

def main : IO Unit := do
  match Symbolic.emit sumToN with
  | .ok source => IO.print source
  | .error error => throw (IO.userError s!"assembly generation failed: {repr error}")
