import YulC.Mini.Syntax
import YulC.Mini.Semantics

/-!
# Block flattening (verified)

Under the post-disambiguator "block as syntactic grouping" semantics
(see `Stmt.exec` for `.block`), nested blocks add nothing: a `block`
just runs its body in the enclosing scope.

This pass exploits that to clean up the AST:

* `flatten (block body)`  flattens any inner blocks of `body` and
  splices the result into the surrounding sequence;
* the program-level pass `progFlatten` removes outer `block` wrappers
  entirely, so a top-level `block { s₁; s₂ }` becomes `s₁; s₂`.

This makes downstream passes simpler — they can assume an
already-flat statement sequence.
-/

namespace YulC.Mini

namespace Stmt

/-- Flatten one level of nested blocks inside a statement. The
non-`block` cases are unchanged; for `block body` we recursively
flatten every sub-statement and concatenate any inner blocks. -/
def flatten : Stmt → Stmt
  | .letDecl x e => .letDecl x e
  | .assign  x e => .assign  x e
  | .iff cond body  => .iff cond (body.flatMap flattenOne)
  | .block body  => .block (body.flatMap flattenOne)
where
  /-- A single statement after flattening, exposed as the list of
  statements that should be spliced into the parent block. -/
  flattenOne : Stmt → List Stmt
    | .letDecl x e => [.letDecl x e]
    | .assign  x e => [.assign  x e]
    | .iff cond body => [.iff cond (body.flatMap flattenOne)]
    | .block body  => body.flatMap flattenOne
termination_by s => sizeOf s

end Stmt

/-- Program-level flattening: also drops outer `block` wrappers,
since a `block` at the program top is pure grouping. -/
def progFlatten (p : Program) : Program :=
  p.flatMap Stmt.flatten.flattenOne

/-! ## Correctness

The proof exploits the `block` semantics directly: executing a
`block body` is the same as executing `body` in the enclosing
environment. So splicing a block's contents into the surrounding
sequence is a no-op semantically.
-/

namespace Stmt

/-- Pivot lemma: a list of statements concatenated with another runs
left-to-right — so `Program.exec (l₁ ++ l₂)` matches `Program.exec l₂`
on the result of `l₁`. -/
theorem _root_.YulC.Mini.Program.exec_append (l₁ l₂ : Program) (env : Env) :
    Program.exec (l₁ ++ l₂) env =
      (Program.exec l₁ env).bind (Program.exec l₂) := by
  induction l₁ generalizing env with
  | nil => simp [Program.exec]
  | cons s rest ih =>
    simp only [List.cons_append, Program.exec]
    cases Stmt.exec s env with
    | none      => rfl
    | some env' => simpa using ih env'

/-- Singleton programs reduce to the underlying statement. -/
private theorem singleton_exec (s : Stmt) (env : Env) :
    Program.exec [s] env = Stmt.exec s env := by
  simp only [Program.exec]
  cases Stmt.exec s env <;> rfl

mutual

/-- The list returned by `flattenOne` runs identically to the original
single statement under `Program.exec`. -/
theorem flattenOne_exec (s : Stmt) (env : Env) :
    Program.exec (flatten.flattenOne s) env = Stmt.exec s env := by
  match s with
  | .letDecl _ _ | .assign _ _ =>
    simp only [flatten.flattenOne]; exact singleton_exec _ env
  | .iff cond body =>
    simp only [flatten.flattenOne]
    rw [singleton_exec]
    show Stmt.exec (.iff cond (body.flatMap flatten.flattenOne)) env =
         Stmt.exec (.iff cond body) env
    simp only [Stmt.exec]
    cases hc : cond.eval env with
    | none   => rfl
    | some c =>
      by_cases h0 : c = 0
      · simp [h0]
      · simp only [h0, if_false]
        rw [flatMap_flattenOne_exec body env]
  | .block body =>
    simp only [flatten.flattenOne, Stmt.exec]
    exact flatMap_flattenOne_exec body env
termination_by sizeOf s

theorem flatMap_flattenOne_exec (p : Program) (env : Env) :
    Program.exec (p.flatMap flatten.flattenOne) env = Program.exec p env := by
  match p with
  | [] => rfl
  | s :: rest =>
    rw [List.flatMap_cons, Program.exec_append, flattenOne_exec]
    show (Stmt.exec s env).bind _ = Program.exec (s :: rest) env
    simp only [Program.exec]
    cases Stmt.exec s env with
    | none      => rfl
    | some env' => simpa using flatMap_flattenOne_exec rest env'
termination_by sizeOf p

end

/-- Statement-level flattening preserves semantics. -/
theorem flatten_exec (s : Stmt) (env : Env) :
    (s.flatten).exec env = s.exec env := by
  match s with
  | .letDecl _ _ | .assign _ _ => simp [Stmt.flatten, Stmt.exec]
  | .iff cond body =>
    simp only [Stmt.flatten, Stmt.exec]
    cases hc : cond.eval env with
    | none   => rfl
    | some c =>
      by_cases h0 : c = 0
      · simp [h0]
      · simp only [h0, if_false]
        rw [flatMap_flattenOne_exec body env]
  | .block body =>
    simp only [Stmt.flatten, Stmt.exec]
    exact flatMap_flattenOne_exec body env

end Stmt

/-- Program-level flattening preserves semantics. -/
theorem progFlatten_exec (p : Program) (env : Env) :
    (progFlatten p).exec env = p.exec env :=
  Stmt.flatMap_flattenOne_exec p env

end YulC.Mini
