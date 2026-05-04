import YulC.Mini.Evm

/-!
# Peephole optimisation on mini-EVM bytecode

A first, deliberately small bytecode-level pass: drop adjacent
`PUSH n; POP` pairs anywhere in a bytecode stream. Both opcodes are
total in this position (`PUSH` always succeeds, and the immediately
following `POP` always succeeds because the stack is non-empty by
construction), so the rewrite preserves both the success/failure shape
and the resulting stack of `Bytecode.run`.

Why so few rules? Most "obvious" cancellation patterns
(`SWAP1; SWAP1 → ε`, `DUPi; POP → ε`) are *unsafe* in our model
because the original sequence can fail on an under-sized stack while
the empty replacement cannot — any such rewrite would change the
failure shape. The `PUSH; POP` rule is the unique pair where the first
opcode places its own input on the stack and the second removes
exactly that input.

Future extensions will need either a static stack-depth analysis or
explicit side conditions; that is left to a follow-up pass.
-/

namespace YulC.Mini

namespace Bytecode

/-- Single-pass peephole rewriter: collapses adjacent `PUSH n; POP`. -/
@[simp] def peephole : List Op → List Op
  | .push _ :: .pop :: rest => peephole rest
  | op :: rest              => op :: peephole rest
  | []                      => []

/-- The peephole pass preserves bytecode behaviour exactly. -/
theorem peephole_run (p : List Op) (s : Stack) :
    Bytecode.run (peephole p) s = Bytecode.run p s := by
  induction p using peephole.induct generalizing s with
  | case1 _ rest ih =>
    simp [Bytecode.run, Op.step, ih]
  | case2 op rest _ ih =>
    simp only [peephole, Bytecode.run]
    cases hstep : op.step s with
    | none    => rfl
    | some s' => simp [ih]
  | case3 => rfl

end Bytecode

end YulC.Mini
