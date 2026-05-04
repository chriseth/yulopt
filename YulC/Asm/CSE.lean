import YulC.Codegen.Asm
import YulC.Asm.Rules

/-!
# Per-basic-block CSE (assembly level)

Symbolic stack/memory/storage interpreter using shared rewrite rules,
re-emitting minimal code from the resulting expression DAG and
side-effect list. Mirrors solc's `CommonSubexpressionEliminator`.
-/
namespace YulC.Asm.CSE
open YulC.Codegen

def run (a : Asm) : Asm := a  -- TODO

end YulC.Asm.CSE
