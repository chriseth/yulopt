import YulC.Mini.Util
import YulC.Mini.Syntax
import YulC.Mini.Evm

/-!
# Compiler: Yul subset → Mini-EVM

A `Layout` records the *static* shape of the stack at a program
point: each entry is either `some x` (a named binder) or `none` (an
anonymous intermediate). Position 0 is the top of the stack.

The compiler is a total function on the layout that returns:

* `none` if the source program is ill-formed (variable out of scope,
  or `assign` to an unbound name);
* `some (ops, layout')` otherwise, where `ops` is the emitted
  bytecode and `layout'` describes the stack after running it.

Codegen pattern:

* `lit n`            ↦ `PUSH n`
* `var x`            ↦ `DUP (depth + 1)`
* `un op e`          ↦ `<e>; UN op`
* `bin op a b`       ↦ `<a>; <b'>; BIN op`     (b' compiled with `none :: layout`)
* `let x := e`       ↦ `<e>`                   (layout grows by `some x`)
* `x := e`           ↦ `<e>; SWAP (d+1); POP`  (in-place update at depth d)
-/

namespace YulC.Mini

/-- Static description of the stack: head is the top. `none`
marks an anonymous intermediate value. -/
abbrev Layout := List (Option Ident)

namespace Layout

/-- Depth of a binder in the layout (0 = top of stack). Returns
`none` if `x` is not in scope. -/
@[simp] def depth : Layout → Ident → Option Nat
  | [],              _ => none
  | none :: rest,    x => (depth rest x).map (· + 1)
  | some y :: rest,  x =>
    if y = x then some 0 else (depth rest x).map (· + 1)

/-- A reachable depth is a valid stack index. -/
theorem depth_lt_length {l : Layout} {x : Ident} {d : Nat}
    (h : Layout.depth l x = some d) : d < l.length := by
  induction l generalizing d with
  | nil => simp at h
  | cons head _ ih =>
    cases head with
    | none =>
      simp at h; obtain ⟨d', hd', rfl⟩ := h
      simpa using ih hd'
    | some y =>
      simp at h
      by_cases hyx : y = x
      · simp [hyx] at h; subst h; simp
      · simp [hyx] at h; obtain ⟨d', hd', rfl⟩ := h
        simpa using ih hd'

/-- Different binders that are present in the layout map to different
depths (i.e. `depth` is injective on its domain). -/
theorem depth_inj {l : Layout} {x y : Ident} {d : Nat}
    (hx : Layout.depth l x = some d) (hy : Layout.depth l y = some d) :
    x = y := by
  induction l generalizing d with
  | nil => simp at hx
  | cons head tail ih =>
    cases head with
    | none =>
      cases hdx : Layout.depth tail x with
      | none => simp [hdx] at hx
      | some dx =>
        cases hdy : Layout.depth tail y with
        | none => simp [hdy] at hy
        | some dy =>
          simp [hdx] at hx
          simp [hdy] at hy
          have : dy = dx := by omega
          exact ih hdx (this ▸ hdy)
    | some z =>
      by_cases hzx : z = x
      · simp [hzx] at hx; subst hx
        by_cases hzy : z = y
        · subst hzx; exact hzy
        · simp [hzy] at hy
      · cases hdx : Layout.depth tail x with
        | none => simp [hzx, hdx] at hx
        | some dx =>
          simp [hzx, hdx] at hx; subst hx
          by_cases hzy : z = y
          · simp [hzy] at hy
          · cases hdy : Layout.depth tail y with
            | none => simp [hzy, hdy] at hy
            | some dy =>
              simp [hzy, hdy] at hy
              have : dy = dx := by omega
              exact ih hdx (this ▸ hdy)

end Layout

@[simp] def Expr.compile : Expr → Layout → Option (List Op)
  | .lit n,      _ => some [Op.push n]
  | .var x,      l => (Layout.depth l x).map fun d => [Op.dup (d + 1)]
  | .un op a,    l => (a.compile l).map fun ca => ca ++ [Op.un op]
  | .bin op a b, l =>
    match a.compile l, b.compile (none :: l) with
    | some ca, some cb => some (ca ++ cb ++ [Op.bin op])
    | _, _ => none

mutual

@[simp] def Stmt.compile : Stmt → Layout → Option (List Op × Layout)
  | .letDecl x e, l =>
    match e.compile l with
    | some c => some (c, some x :: l)
    | none   => none
  | .assign x e, l =>
    match e.compile l, Layout.depth l x with
    | some c, some d => some (c ++ [Op.swap (d + 1), Op.pop], l)
    | _, _ => none
  | .block body, l =>
    -- Block introduces a fresh scope: compile the body in the current
    -- layout, then emit `POP` for each new binding to restore the
    -- enclosing layout/stack.
    match Program.compile body l with
    | none           => none
    | some (cb, lb)  =>
      let k := lb.length - l.length
      some (cb ++ List.replicate k Op.pop, l)
  | .iff cond body, l =>
    match cond.compile l with
    | none    => none
    | some cc =>
      match Program.compile body l with
      | none           => none
      | some (cb, lb)  =>
        -- The body's own scope: trailing POPs balance the stack so the
        -- `Op.iff` body is self-contained (length-preserving).
        let k := lb.length - l.length
        let body_ops := cb ++ List.replicate k Op.pop
        some (cc ++ [Op.iff body_ops], l)

@[simp] def Program.compile : Program → Layout → Option (List Op × Layout)
  | [],        l => some ([], l)
  | s :: rest, l =>
    match Stmt.compile s l with
    | some (c1, l1) =>
      match Program.compile rest l1 with
      | some (c2, l2) => some (c1 ++ c2, l2)
      | none          => none
    | none => none

end

/-! ## Layout-extension structural lemmas

The compiler only ever *prepends* fresh slots to the layout: every
statement either preserves it (`assign`, `block`, `iff`) or pushes
exactly one named slot on top (`letDecl`). Below we expose this
invariant so downstream proofs can recover the inner-vs-outer shape. -/

theorem Stmt.compile_layout_extends :
    ∀ {s : Stmt} {l ops l'},
      Stmt.compile s l = some (ops, l') → ∃ ext, l' = ext ++ l := by
  intro s l ops l' h
  match s with
  | .letDecl x e =>
    simp only [Stmt.compile] at h
    cases hc : Expr.compile e l with
    | none   => rw [hc] at h; simp at h
    | some c => rw [hc] at h; simp at h; exact ⟨[some x], by simp [h.2]⟩
  | .assign x e =>
    simp only [Stmt.compile] at h
    cases hc : Expr.compile e l with
    | none   => rw [hc] at h; simp at h
    | some c =>
      cases hd : Layout.depth l x with
      | none   => rw [hc, hd] at h; simp at h
      | some d => rw [hc, hd] at h; simp at h; exact ⟨[], by simp [h.2]⟩
  | .block body =>
    simp only [Stmt.compile] at h
    split at h
    next => simp at h
    next => simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact ⟨[], by simp [h.2]⟩
  | .iff cond body =>
    simp only [Stmt.compile] at h
    split at h
    next => simp at h
    next =>
      split at h
      next => simp at h
      next => simp only [Option.some.injEq, Prod.mk.injEq] at h
              exact ⟨[], by simp [h.2]⟩

theorem Program.compile_layout_extends :
    ∀ {p : Program} {l ops l'},
      Program.compile p l = some (ops, l') → ∃ ext, l' = ext ++ l := by
  intro p
  induction p with
  | nil =>
    intro l ops l' h
    simp at h; exact ⟨[], by simp [h.2]⟩
  | cons s rest ih =>
    intro l ops l' h
    simp only [Program.compile] at h
    split at h
    next hs =>
      split at h
      next hr =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨ext1, hext1⟩ := Stmt.compile_layout_extends hs
        obtain ⟨ext2, hext2⟩ := ih hr
        exact ⟨ext2 ++ ext1, by rw [← h.2, hext2, hext1, List.append_assoc]⟩
      next => simp at h
    next => simp at h

end YulC.Mini
