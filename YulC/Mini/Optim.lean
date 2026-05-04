import YulC.Mini.Syntax
import YulC.Mini.Semantics
import YulC.Mini.Compiler
import YulC.Mini.Correctness
import YulC.Mini.Optim.ConstFold
import YulC.Mini.Optim.Algebraic
import YulC.Mini.Optim.Flatten
import YulC.Mini.Optim.Peephole

/-!
# Composed optimizer pipeline (verified, end-to-end)

Two entry points:

* `optimize : Program → Program` chains the verified Yul-level passes.
  Each pass preserves `Program.exec`, so their composition does too.

* `compileOptimized : Program → Option (List Op × Layout)` runs the
  full pipeline:

      Yul source
        → optimize           (flatten, fold, algebraic)
        → Program.compile    (codegen)
        → Bytecode.peephole  (PUSH; POP cancellation)

  The headline correctness theorem `compileOptimized_correct` states
  that the final bytecode produces a stack matching the source
  semantics — i.e. the optimised pipeline is observationally
  indistinguishable from `Program.compile_correct` on the unoptimised
  program.

Pipeline order (top-down, semantically equivalent to the identity at
the Yul level):

1. **Flatten** — splice nested `block`s into the surrounding sequence
   so subsequent passes see a flat statement list.
2. **Constant folding** — collapse `op(lit, …, lit)` to a literal.
3. **Algebraic simplification** — apply identities like
   `add(x, 0) → x`, `mul(x, 1) → x`, etc.
4. **Codegen + peephole** — at the bytecode level, drop adjacent
   `PUSH n; POP` pairs the optimised codegen may have produced.
-/

namespace YulC.Mini

/-! ## Yul-level pipeline -/

/-- Composed Yul-level optimiser. -/
def optimize (p : Program) : Program :=
  progAlg (progFold (progFlatten p))

/-- The Yul-level pipeline preserves program semantics. -/
theorem optimize_exec (p : Program) (env : Env) :
    (optimize p).exec env = p.exec env := by
  unfold optimize
  rw [progAlg_exec, progFold_exec, progFlatten_exec]

/-! ## End-to-end pipeline (Yul → optimised bytecode) -/

/-- Optimise, compile, then peephole-rewrite the resulting bytecode. -/
def compileOptimized (p : Program) : Option (List Op × Layout) :=
  match Program.compile (optimize p) [] with
  | some (ops, layout') => some (Bytecode.peephole ops, layout')
  | none                => none

/-- End-to-end correctness: a successful source run produces a
bytecode that, when peephole-optimised and executed on the empty
stack, terminates with a stack matching the source environment. -/
theorem compileOptimized_correct (p : Program) (env' : Env)
    (hexec : Program.exec p [] = some env') :
    ∃ ops layout' stack',
      compileOptimized p = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches env' layout' stack' := by
  -- The Yul-level optimiser preserves semantics, so the optimised
  -- program also runs to `env'`. Apply `compile_correct` to it,
  -- then commute through the bytecode-level peephole pass.
  have hexec' : Program.exec (optimize p) [] = some env' := by
    rw [optimize_exec]; exact hexec
  obtain ⟨ops, layout', stack', hcomp, hrun, hM⟩ :=
    Program.compile_correct (optimize p) env' hexec'
  refine ⟨Bytecode.peephole ops, layout', stack', ?_, ?_, hM⟩
  · simp [compileOptimized, hcomp]
  · rw [Bytecode.peephole_run]; exact hrun

end YulC.Mini
