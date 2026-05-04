import YulC.Mini.Syntax
import YulC.Mini.Semantics
import YulC.Mini.Optim.ConstFold
import YulC.Mini.Optim.Algebraic
import YulC.Mini.Optim.Flatten

/-!
# Composed Yul-level optimizer pipeline (verified)

Chains the three verified Yul-level passes into a single function
`optimize : Program → Program`, with `optimize_exec` showing it
preserves `Program.exec`.

The end-to-end *bytecode* pipeline (Yul source → optimise → codegen →
bytecode peephole) and its correctness theorem live in
`YulC.Mini.Correctness`, alongside the headline `Program.compile_correct`.

Pipeline order (semantically equivalent to the identity):

1. **Flatten** — splice nested `block`s into the surrounding sequence.
2. **Constant folding** — collapse `op(lit, …, lit)` to a literal.
3. **Algebraic simplification** — apply identities like
   `add(x, 0) → x`, `mul(x, 1) → x`, etc.
-/

namespace YulC.Mini

/-- Composed Yul-level optimiser. -/
def optimize (p : Program) : Program :=
  progAlg (progFold (progFlatten p))

/-- The Yul-level pipeline preserves program semantics. -/
theorem optimize_exec (p : Program) (env : Env) :
    (optimize p).exec env = p.exec env := by
  unfold optimize
  rw [progAlg_exec, progFold_exec, progFlatten_exec]

end YulC.Mini
