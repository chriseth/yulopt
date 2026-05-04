import YulC.Codegen.Asm

/-!
# Simple Inliner (assembly level)

Replaces `PUSHTAG t; JUMP` with the body of the basic block at `t`
when small and ending in `JUMP "out"`. See `PLAN.md` §5.
-/
namespace YulC.Asm.Inliner
open YulC.Codegen

def run (a : Asm) : Asm := a  -- TODO

end YulC.Asm.Inliner
