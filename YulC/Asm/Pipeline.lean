import YulC.Codegen.Asm
import YulC.Asm.JumpdestRemover
import YulC.Asm.Peephole
import YulC.Asm.Inliner
import YulC.Asm.CSE
import YulC.Asm.BlockDeduplicator
import YulC.Asm.ConstantOptimiser

/-!
# Assembly optimizer pipeline

Runs JumpdestRemover, Peephole, Inliner, CSE, BlockDeduplicator,
ConstantOptimiser to fixpoint. Heuristics use `--optimize-runs`.
-/
namespace YulC.Asm.Pipeline
open YulC.Codegen

partial def run (runs : Nat) (a : Asm) : Asm :=
  let a := JumpdestRemover.run a
  let a := Peephole.run a
  let a := Inliner.run a
  let a := CSE.run a
  let a := BlockDeduplicator.run a
  let a := ConstantOptimiser.run runs a
  a  -- TODO: outer fixpoint

end YulC.Asm.Pipeline
