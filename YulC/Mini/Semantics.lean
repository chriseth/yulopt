import YulC.Mini.Syntax

/-!
# Yul subset: dynamic semantics

Big-step evaluator for `Expr`, `Stmt` and `Program`, plus
purely-arithmetic lemmas about `Env.update` that the correctness
proof depends on.

Built-in operators are evaluated using `BitVec 256` arithmetic so the
semantics matches real EVM behaviour: addition / subtraction /
multiplication wrap mod 2²⁵⁶, division and modulo are *unsigned* and
return zero on divisor zero, and `lt`/`gt`/`eq` produce the boolean
encoding `1`/`0` as a 256-bit word.
-/

namespace YulC.Mini

/-- Yul boolean encoding: `1` for true, `0` for false. -/
@[simp] def Word.ofBool (b : Bool) : Word := if b then 1 else 0

@[simp] def BinOp.apply : BinOp → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .and, a, b => a &&& b
  | .or,  a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .lt,  a, b => Word.ofBool (a < b)
  | .gt,  a, b => Word.ofBool (a > b)
  | .eq,  a, b => Word.ofBool (a = b)

@[simp] def UnOp.apply : UnOp → Word → Word
  | .iszero, a => Word.ofBool (a = 0)

@[simp] def Expr.eval : Expr → Env → Option Word
  | .lit n,      _   => some n
  | .var x,      env => Env.lookup env x
  | .un  op a,   env => (a.eval env).map op.apply
  | .bin op a b, env =>
    match a.eval env, b.eval env with
    | some av, some bv => some (op.apply av bv)
    | _, _ => none

mutual

@[simp] def Stmt.exec : Stmt → Env → Option Env
  | .letDecl x e, env =>
    match e.eval env, env.lookup x with
    | some v, none => some ((x, v) :: env)
    | _,      _    => none
  | .assign x e, env =>
    match e.eval env with
    | some v => Env.update env x v
    | none   => none
  | .block body, env =>
    -- Block as syntactic grouping (post-disambiguator semantics): the
    -- no-shadowing `letDecl` rule already prevents accidental capture,
    -- so a block contributes nothing beyond running its body in the
    -- enclosing scope.
    Program.exec body env
  | .iff cond body, env =>
    -- `if cond { body }`. Falsely-conditioned: env unchanged.
    -- Truly-conditioned: run body, then *require* the body to be
    -- layout-preserving (same env length out as in). This rules out
    -- `letDecl`s inside the body and matches the bytecode's
    -- structured `Op.iff` constraint.
    match cond.eval env with
    | none   => none
    | some c =>
      if c = 0 then some env
      else match Program.exec body env with
           | some env' => if env'.length = env.length then some env' else none
           | none      => none

@[simp] def Program.exec : Program → Env → Option Env
  | [],        env => some env
  | s :: rest, env =>
    match Stmt.exec s env with
    | some env' => Program.exec rest env'
    | none      => none

end

/-! ## Lemmas about `Env.update`

These are the only properties of the source semantics needed by the
compiler's correctness proof. Each proof is a structural induction on
the environment whose `cons` step splits on whether the head key
matches the target name; both sides are then dispatched by `simp`
plus the inductive hypothesis.
-/

namespace Env

variable {x y : Ident} {v : Word}

/-- Updating an unbound name fails. -/
theorem update_eq_none_of_lookup_eq_none (env : Env) :
    Env.lookup env x = none → Env.update env x v = none := by
  induction env with
  | nil => intro _; rfl
  | cons head _ ih =>
    obtain ⟨k, _⟩ := head
    intro h
    by_cases hkx : k = x
    · simp [hkx] at h
    · simp [hkx] at h ⊢; exact ih h

/-- The updated slot reads back the new value. -/
theorem update_lookup_self {env env' : Env}
    (h : Env.update env x v = some env') : Env.lookup env' x = some v := by
  induction env generalizing env' with
  | nil => simp at h
  | cons head _ ih =>
    obtain ⟨k, _⟩ := head
    by_cases hkx : k = x
    · simp [hkx] at h; subst h; simp
    · simp [hkx] at h; obtain ⟨_, hrest, rfl⟩ := h
      simpa [hkx] using ih hrest

/-- Other names are unaffected by an update. -/
theorem update_lookup_other {env env' : Env}
    (h : Env.update env x v = some env') (hxy : x ≠ y) :
    Env.lookup env' y = Env.lookup env y := by
  induction env generalizing env' with
  | nil => simp at h
  | cons head _ ih =>
    obtain ⟨k, _⟩ := head
    by_cases hkx : k = x
    · subst hkx
      simp at h; subst h
      have : k ≠ y := hxy
      simp [this]
    · simp [hkx] at h; obtain ⟨_, hrest, rfl⟩ := h
      by_cases hky : k = y
      · simp [hky]
      · simp [hky]; exact ih hrest

/-- `update` preserves length. -/
theorem update_length {env env' : Env}
    (h : Env.update env x v = some env') : env'.length = env.length := by
  induction env generalizing env' with
  | nil => simp at h
  | cons head _ ih =>
    obtain ⟨k, _⟩ := head
    by_cases hkx : k = x
    · simp [hkx] at h; subst h; simp
    · simp [hkx] at h; obtain ⟨_, hrest, rfl⟩ := h
      simpa using ih hrest

end Env

end YulC.Mini
