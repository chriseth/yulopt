import YulC.Mini.Syntax
import YulC.Mini.Semantics

/-!
# Constant folding (verified)

A first verified optimizer pass on Yul ASTs. The transformation is
purely local on `Expr`: any sub-expression with no free variables is
replaced by its evaluated literal. The pass is then lifted to `Stmt`
and `Program` componentwise.

Correctness statements:

* `Expr.fold_eval`        — folding preserves expression evaluation
                            in every environment.
* `Stmt.fold_exec`        — folding preserves statement semantics.
* `Program.fold_exec`     — folding preserves program semantics.
-/

namespace YulC.Mini

namespace Expr

/-- Smart constructor for unary ops that folds a literal argument. -/
def smartUn (op : UnOp) : Expr → Expr
  | .lit av => .lit (op.apply av)
  | a'      => .un op a'

/-- Smart constructor for binary ops that folds two literal arguments. -/
def smartBin (op : BinOp) : Expr → Expr → Expr
  | .lit av, .lit bv => .lit (op.apply av bv)
  | a',      b'      => .bin op a' b'

/-- Fold constant subexpressions to literals. -/
def fold : Expr → Expr
  | .lit n      => .lit n
  | .var x      => .var x
  | .un  op a   => smartUn  op a.fold
  | .bin op a b => smartBin op a.fold b.fold

@[simp] theorem smartUn_eval (op : UnOp) (a : Expr) (env : Env) :
    (smartUn op a).eval env = (Expr.un op a).eval env := by
  cases a <;> simp [smartUn, Expr.eval]

@[simp] theorem smartBin_eval (op : BinOp) (a b : Expr) (env : Env) :
    (smartBin op a b).eval env = (Expr.bin op a b).eval env := by
  cases a <;> cases b <;> simp [smartBin, Expr.eval]

/-- Constant folding preserves evaluation in every environment. -/
@[simp] theorem fold_eval (e : Expr) (env : Env) :
    (e.fold).eval env = e.eval env := by
  induction e with
  | lit _ => rfl
  | var _ => rfl
  | un  _ _ iha       => simp [fold, Expr.eval, iha]
  | bin _ _ _ iha ihb => simp [fold, Expr.eval, iha, ihb]

end Expr

namespace Stmt

/-- Apply constant folding to every expression in a statement. Recurses
into nested blocks. -/
def fold : Stmt → Stmt
  | .letDecl x e => .letDecl x e.fold
  | .assign  x e => .assign  x e.fold
  | .block body  => .block (body.map fold)
termination_by s => sizeOf s

end Stmt

/-- Apply constant folding to every statement of a program. -/
def progFold (p : Program) : Program := p.map Stmt.fold

/-! ## Correctness -/

mutual

theorem Stmt.fold_exec (s : Stmt) (env : Env) :
    (s.fold).exec env = s.exec env := by
  match s with
  | .letDecl _ _ | .assign _ _ => simp [Stmt.fold, Stmt.exec]
  | .block body =>
    simp only [Stmt.fold, Stmt.exec]
    exact Program.fold_exec body env
termination_by sizeOf s

theorem Program.fold_exec (p : Program) (env : Env) :
    Program.exec (p.map Stmt.fold) env = Program.exec p env := by
  match p with
  | [] => rfl
  | s :: rest =>
    simp only [List.map_cons, Program.exec]
    rw [Stmt.fold_exec]
    cases Stmt.exec s env with
    | none      => rfl
    | some env' => exact Program.fold_exec rest env'
termination_by sizeOf p

end

/-- Lifted form: `progFold` preserves `Program.exec`. -/
theorem progFold_exec (p : Program) (env : Env) :
    (progFold p).exec env = p.exec env :=
  Program.fold_exec p env

end YulC.Mini
