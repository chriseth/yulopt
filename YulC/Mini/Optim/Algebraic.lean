import YulC.Mini.Syntax
import YulC.Mini.Semantics

/-!
# Algebraic simplification (verified)

A second verified Yul-level optimizer pass. Where constant folding
collapses `op(lit, lit)` to a literal, this pass collapses `op(e, lit)`
or `op(lit, e)` patterns whose result equals one of the operands.

Only rules that hold *unconditionally on `Word`* are included.
Crucially we avoid:

* `mul(x, 0) → 0` (and the symmetric `and(x, 0) → 0`): they require
  `x.eval env = some _`, which is **not** guaranteed in our model
  (`var x` may evaluate to `none` if `x` is out of scope). Folding
  them to `lit 0` would change the result from `none` to `some 0`.

* `iszero(iszero(x)) → x`: `iszero(iszero(x))` normalises to a `0/1`
  boolean, not to `x` itself.

The supported rules (each preserves `Expr.eval` in any environment):

| Pattern                  | Rewrites to | Justification (BitVec lemma) |
|--------------------------|-------------|------------------------------|
| `add(x, 0)`, `add(0, x)` | `x`         | `add_zero` / `zero_add`      |
| `sub(x, 0)`              | `x`         | `sub_zero`                   |
| `mul(x, 1)`, `mul(1, x)` | `x`         | `mul_one` / `one_mul`        |
| `div(x, 1)`              | `x`         | `div_one`                    |
| `or(x, 0)`,  `or(0, x)`  | `x`         | `or_zero` / `zero_or`        |
| `xor(x, 0)`, `xor(0, x)` | `x`         | `xor_zero` / `zero_xor`      |
-/

namespace YulC.Mini

namespace Expr

/-- Smart binary constructor that applies the algebraic identities
listed in the module docstring. Falls through to `bin op a b` otherwise. -/
def algBin : BinOp → Expr → Expr → Expr
  | .add, .lit 0, b      => b
  | .add, a,      .lit 0 => a
  | .sub, a,      .lit 0 => a
  | .mul, .lit 1, b      => b
  | .mul, a,      .lit 1 => a
  | .div, a,      .lit 1 => a
  | .or,  .lit 0, b      => b
  | .or,  a,      .lit 0 => a
  | .xor, .lit 0, b      => b
  | .xor, a,      .lit 0 => a
  | op,   a,      b      => .bin op a b

/-- Apply algebraic simplification to every sub-expression. -/
def alg : Expr → Expr
  | .lit n      => .lit n
  | .var x      => .var x
  | .un  op a   => .un op a.alg
  | .bin op a b => algBin op a.alg b.alg

/-! ## Correctness -/

@[simp] theorem algBin_eval (op : BinOp) (a b : Expr) (env : Env) :
    (algBin op a b).eval env = (Expr.bin op a b).eval env := by
  -- Fully unfold `algBin`, split on every literal-shape case, then
  -- discharge each surviving goal by reducing the `match` on
  -- `a.eval env` / `b.eval env` and applying a single `BitVec`
  -- identity (`add_zero`, `mul_one`, …) from the core simp set.
  unfold algBin
  split <;> first
    | rfl
    | (simp [Expr.eval, BinOp.apply]; cases a.eval env <;> simp)
    | (simp [Expr.eval, BinOp.apply]; cases b.eval env <;> simp)

/-- Algebraic simplification preserves expression evaluation. -/
@[simp] theorem alg_eval (e : Expr) (env : Env) :
    (e.alg).eval env = e.eval env := by
  induction e with
  | lit _ => rfl
  | var _ => rfl
  | un  _ _ iha       => simp [alg, Expr.eval, iha]
  | bin _ _ _ iha ihb => simp [alg, Expr.eval, iha, ihb]

end Expr

namespace Stmt

/-- Apply algebraic simplification to every expression in a statement. -/
def alg : Stmt → Stmt
  | .letDecl x e => .letDecl x e.alg
  | .assign  x e => .assign  x e.alg
  | .iff cond body => .iff cond.alg (body.map alg)
  | .block body  => .block (body.map alg)
termination_by s => sizeOf s

end Stmt

/-- Apply algebraic simplification to every statement of a program. -/
def progAlg (p : Program) : Program := p.map Stmt.alg

mutual

theorem Stmt.alg_exec (s : Stmt) (env : Env) :
    (s.alg).exec env = s.exec env := by
  match s with
  | .letDecl _ _ | .assign _ _ => simp [Stmt.alg, Stmt.exec]
  | .iff cond body =>
    simp only [Stmt.alg, Stmt.exec, Expr.alg_eval]
    cases hc : cond.eval env with
    | none   => rfl
    | some c =>
      by_cases h0 : c = 0
      · simp [h0, Program.alg_exec body env]
      · simp only [h0, if_false, Program.alg_exec body env]
  | .block body =>
    simp only [Stmt.alg, Stmt.exec, Program.alg_exec body env]
termination_by sizeOf s

theorem Program.alg_exec (p : Program) (env : Env) :
    Program.exec (p.map Stmt.alg) env = Program.exec p env := by
  match p with
  | [] => rfl
  | s :: rest =>
    simp only [List.map_cons, Program.exec]
    rw [Stmt.alg_exec]
    cases Stmt.exec s env with
    | none      => rfl
    | some env' => exact Program.alg_exec rest env'
termination_by sizeOf p

end

/-- Lifted form: `progAlg` preserves `Program.exec`. -/
theorem progAlg_exec (p : Program) (env : Env) :
    (progAlg p).exec env = p.exec env :=
  Program.alg_exec p env

end YulC.Mini
