/-!
# `List` utilities

Generic, Yul-agnostic list operations and lemmas used by the mini
compiler. Kept separate so the rest of the development reads like a
domain-specific story.
-/

namespace YulC.Mini

/-- Replace the `i`-th element of a list (0-based). Returns `none`
when the index is out of bounds. -/
def List.setOpt {α} : List α → Nat → α → Option (List α)
  | [],      _,     _ => none
  | _ :: xs, 0,     y => some (y :: xs)
  | x :: xs, n + 1, y => (List.setOpt xs n y).map (x :: ·)

namespace List

variable {α : Type _}

/-! ## Definitional simp lemmas

These three rewrite rules unfold `setOpt` one constructor at a time.
They are tagged `@[simp]` so subsequent proofs only need bare `simp`. -/

@[simp] theorem setOpt_nil (n : Nat) (y : α) :
    List.setOpt ([] : List α) n y = none := by cases n <;> rfl

@[simp] theorem setOpt_cons_zero (x : α) (xs : List α) (y : α) :
    List.setOpt (x :: xs) 0 y = some (y :: xs) := rfl

@[simp] theorem setOpt_cons_succ (x : α) (xs : List α) (n : Nat) (y : α) :
    List.setOpt (x :: xs) (n + 1) y = (List.setOpt xs n y).map (x :: ·) := rfl

/-! ## Behavioural lemmas -/

/-- `setOpt` succeeds iff the index is in range. -/
theorem exists_setOpt (xs : List α) (n : Nat) (y : α) :
    n < xs.length → ∃ xs', List.setOpt xs n y = some xs' := by
  induction xs generalizing n with
  | nil => simp
  | cons head _ ih =>
    cases n with
    | zero => exact fun _ => ⟨y :: _, rfl⟩
    | succ k =>
      intro h
      have ⟨ys, h'⟩ := ih k (Nat.lt_of_succ_lt_succ (by simpa using h))
      refine ⟨head :: ys, ?_⟩; simp [h']

/-- The slot we updated reads back as the new value. -/
theorem getElem?_setOpt_self {xs : List α} {n : Nat} {y : α} {xs' : List α}
    (h : List.setOpt xs n y = some xs') : xs'[n]? = some y := by
  induction xs generalizing n xs' with
  | nil => simp at h
  | cons _ _ ih =>
    cases n with
    | zero => simp at h; subst h; rfl
    | succ _ =>
      simp at h; obtain ⟨_, hrest, rfl⟩ := h
      simpa using ih hrest

/-- `setOpt` preserves length. -/
theorem length_setOpt {xs : List α} {n : Nat} {y : α} {xs' : List α}
    (h : List.setOpt xs n y = some xs') : xs'.length = xs.length := by
  induction xs generalizing n xs' with
  | nil => simp at h
  | cons _ _ ih =>
    cases n with
    | zero => simp at h; subst h; rfl
    | succ _ =>
      simp at h; obtain ⟨_, hrest, rfl⟩ := h
      simpa using ih hrest

/-- Other slots are unchanged by a `setOpt`. -/
theorem getElem?_setOpt_other {xs : List α} {n : Nat} {y : α} {xs' : List α}
    {m : Nat} (h : List.setOpt xs n y = some xs') (hmn : m ≠ n) :
    xs'[m]? = xs[m]? := by
  induction xs generalizing n xs' m with
  | nil => simp at h
  | cons _ _ ih =>
    cases n with
    | zero =>
      simp at h; subst h
      cases m with
      | zero => exact absurd rfl hmn
      | succ _ => simp
    | succ _ =>
      simp at h; obtain ⟨_, hrest, rfl⟩ := h
      cases m with
      | zero => simp
      | succ _ =>
        simpa using ih hrest (fun heq => hmn (by simp [heq]))

end List

end YulC.Mini
