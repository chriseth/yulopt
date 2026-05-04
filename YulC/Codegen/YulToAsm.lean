import YulC.Syntax.Yul
import YulC.Codegen.Asm

/-!
# Yul → Asm code generator

Naive code generator (Phase A) and later the Phase H optimizing
codegen. See `PLAN.md` §5/§6.
-/
namespace YulC.Codegen

def compile (_p : YulC.Syntax.Program) : Asm := default  -- TODO

end YulC.Codegen
