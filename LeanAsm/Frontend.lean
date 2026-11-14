import LeanAsm.Rv64.Profile
import LeanAsm.Rv64.Emit
import LeanAsm.Rv64.SAsm.Flatten
import LeanAsm.Symbolic
import LeanAsm.X64.Symbolic

/-!
# Common frontend capabilities

Source languages remain free to differ. Consumers call the same capability
methods, and unsupported capabilities are absent rather than simulated.
-/

namespace LeanAsm

class LowerRv64 (α : Type) where
  lower : α → Except String Rv64.Program

class LowerX64 (α : Type) where
  lower : α → Except X64.Error X64.Program

class EmitAsm (α : Type) where
  emit : String → α → Except String String

def lowerRv64 [LowerRv64 α] (source : α) : Except String Rv64.Program :=
  LowerRv64.lower source

def lowerX64 [LowerX64 α] (source : α) : Except X64.Error X64.Program :=
  LowerX64.lower source

def emitAsm [EmitAsm α] (name : String) (source : α) : Except String String :=
  EmitAsm.emit name source

instance : LowerRv64 Rv64.Program where
  lower program := .ok program

instance : EmitAsm Rv64.Program where
  emit name program := .ok (Rv64.emitProgram name program)

instance : EmitAsm Symbolic.Program where
  emit _ program := Symbolic.emit program

instance : LowerX64 X64.Program where
  lower program := do
    let _ ← X64.encodeProgram program
    return program

instance : LowerX64 X64.Symbolic.Program where
  lower := X64.Symbolic.lower

instance : EmitAsm X64.Program where
  emit name program := (X64.emitProgram name program).mapError (fun error => s!"x64: {repr error}")

instance : EmitAsm X64.Symbolic.Program where
  emit _ program := (X64.Symbolic.emit program).mapError (fun error => s!"x64: {repr error}")

namespace Rv64.SAsm

structure Source where
  base : Rv64.Word
  statement : Stmt

instance : LowerRv64 Source where
  lower source :=
    match source.statement.lower source.base with
    | .ok code => .ok code.toList
    | .error .notLowerable => .error "structured assembly is not lowerable"

instance : EmitAsm Source where
  emit name source := do
    let program ← lowerRv64 source
    return Rv64.emitProgram name program

end Rv64.SAsm
end LeanAsm
