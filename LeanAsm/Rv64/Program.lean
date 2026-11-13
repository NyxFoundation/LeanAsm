import LeanAsm.Rv64.State

/-! Flat instruction programs and macro-assembler composition. -/

namespace LeanAsm.Rv64

abbrev Program := List Instr

instance : Append Program := ⟨List.append⟩

def progSkip : Program := []
def single (instruction : Instr) : Program := [instruction]
def seq (first second : Program) : Program := first ++ second

infixr:50 " ;; " => seq

@[simp] theorem Program.length_append {first second : Program} :
    (first ++ second).length = first.length + second.length :=
  List.length_append (as := first) (bs := second)

def image (base : Word) (program : Program) : Image :=
  { base, code := program.toArray }

end LeanAsm.Rv64
