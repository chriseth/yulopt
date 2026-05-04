# Lean4 Yul → EVM Optimizing Compiler — Plan (annotated)

For every pass we list, in addition to a short description:

- **Lean impl** — concrete implementation strategy in Lean 4
  (data structures, monads, helpers).
- **Proof difficulty** — how hard correctness (semantic preservation) is
  to formalise against the Yul / EVM small-step semantics, with a short
  justification. Scale: **trivial / easy / medium / hard / very hard / research-grade**.

Throughout, `⟦·⟧` denotes the small-step semantics; "correctness" of a
pass `f` means `∀ p. ⟦f p⟧ ≈ ⟦p⟧` for an appropriate observational
equivalence (same final return data, storage, logs, gas-modulo-spec).

---

## 1. Problem statement

Build, in Lean 4, an optimizing compiler from Yul to EVM bytecode that
mirrors a meaningful subset of the two optimizer modules used by `solc`:

1. **Yul-based optimizer** — AST→AST passes.
2. **Opcode-based ("assembly") optimizer** — operates on the EVM
   assembly produced from Yul; also active under
   `solc --strict-assembly --optimize`.

## 2. High-level architecture

```
Yul source ─► Parser ─► Yul AST ─► Yul-optimizer ─► Yul AST'
                                    │
                                    ▼
                                 Codegen ─► Asm IR ─► Asm-optimizer
                                                       │
                                                       ▼
                                                   Assembler ─► EVM bytecode
```

Each stage has a typed Lean IR; passes are pure `IR → IR` (or
`StateM Ctx IR`) functions whose correctness is stated against the
small-step semantics of that IR.

## 3. Lean module layout

(unchanged from before — see §6.)

```
YulC/
├── Syntax/{Yul.lean, Parser.lean}
├── Semantics/{YulSem.lean, EvmSem.lean}
├── Yul/{Disambiguator, Normalize, SSA, Simplify, DCE, CSE,
│        LoadResolver, LICM, Inline, Rules, Pipeline}.lean
├── Codegen/{Asm.lean, YulToAsm.lean}
├── Asm/{Cfg, JumpdestRemover, Peephole, Inliner, CSE,
│        BlockDeduplicator, ConstantOptimiser, Rules, Pipeline}.lean
├── Assembler/Link.lean
├── Driver/Main.lean
└── Test/…
```

---

## 4. Yul-level optimizer passes

### 4.1 Preprocessing / normal form

#### Disambiguator
- **What.** Rename every binder so all identifiers are globally unique.
- **Lean impl.** A `StateM NameGen` traversal of the AST; environment
  `HashMap String String` mapping old → new name, pushed/popped at
  scopes. New names from `Lean.Name.mkSimple` + counter.
- **Proof difficulty.** **Easy.** α-renaming preserves semantics by
  standard substitution lemmas; the only subtlety is shadowing in `for`
  init blocks, which we already handle with the scope stack. Reusable
  `α_equiv` lemma over the Yul evaluator.

#### FunctionHoister (`h`)
- **What.** Move every function definition to the end of the topmost
  block.
- **Lean impl.** Two-pass traversal: collect all `FunctionDefinition`
  nodes (after disambiguation they cannot capture), erase them in place,
  append at the top.
- **Proof difficulty.** **Easy.** Functions in Yul have no side effects
  on definition; their meaning is purely the resulting environment. Once
  names are globally unique, moving a `FunctionDefinition` does not
  change which call resolves to which body. Direct lemma against the
  evaluator's function-environment construction.

#### FunctionGrouper (`g`)
- **What.** Reorganise top block into normal form `{ I F… }`.
- **Lean impl.** Partition the top-block statement list into
  non-function-defs and function-defs while preserving order of each.
- **Proof difficulty.** **Easy.** Same argument as Hoister.

#### ForLoopInitRewriter (`o`)
- **What.** `for { Init } C { Post } { Body }` → `Init; for {} C { Post } { Body }`.
- **Lean impl.** AST rewrite at every `For` node; relies on Disambiguator
  so `Init`'s names don't clash with the surrounding scope.
- **Proof difficulty.** **Easy.** Direct from the operational rule for
  `For`: the spec already evaluates `Init` once before entering the loop.

#### ForLoopConditionIntoBody (`I`) / ForLoopConditionOutOfBody (`O`)
- **What.** Move loop condition between header and `if iszero(C) break`
  at top of body.
- **Lean impl.** Pattern-match `For` nodes; insert/remove the
  `if iszero(C) { break }` prefix.
- **Proof difficulty.** **Easy.** Equivalence is one unfolding of the
  loop semantics; no aliasing concerns. A few-line bisimulation.

#### VarDeclInitializer (`d`)
- **What.** Split `let x, y` and add `:= 0` initializers.
- **Lean impl.** Replace each multi-decl with a sequence of single
  decls, all initialized to `0`.
- **Proof difficulty.** **Trivial.** Yul spec already zero-initialises
  uninitialised variables; this is a syntactic rewrite into the
  reference form.

#### BlockFlattener (`f`)
- **What.** Flatten nested `{ … }` where the inner block introduces no
  binders that escape (after disambiguation, this is always safe for
  pure-statement nesting except where a block delimits a function body
  or loop body).
- **Lean impl.** Recursive walk: replace `Block (xs ++ [Block ys] ++ zs)`
  with `Block (xs ++ ys ++ zs)` outside loop/function/if scopes.
- **Proof difficulty.** **Easy.** After Disambiguator the scope is just
  a name-uniqueness tag; the evaluator is already an `Env →` function
  with no scope-boundary effects to preserve.

### 4.2 Pseudo-SSA layer

#### ExpressionSplitter (`x`)
- **What.** Bind every non-trivial sub-expression to a fresh `let`.
- **Lean impl.** A recursive traversal returning
  `(List Statement, Expression)`; for each function call argument,
  generate `let _i := arg` and replace with `_i`. Skip loop iteration
  conditions.
- **Proof difficulty.** **Easy → Medium.** Pure expressions: trivial.
  With side effects, must show the new evaluation order is identical to
  the original (Yul evaluates arguments left-to-right, which matches our
  letting). Need a "let-binding correspondence" lemma.

#### SSATransform (`a`)
- **What.** Pseudo-SSA: every reassignment is replaced by a fresh
  variable; a phi-replacement `let b := <previous-version>` is inserted
  at control-flow merges.
- **Lean impl.** Per-block dataflow analysis; maintain
  `HashMap Var Var` (current SSA version), join at merges by emitting an
  explicit `let b_n := b` after the branch.
- **Proof difficulty.** **Medium.** SSA correctness is a classic
  bisimulation — straightforward in principle but requires careful
  invariants about which environment binding is "live" after each
  statement. Proven in CompCert / Vellvm; we can follow that recipe.

#### SSAReverser (`V`)
- **What.** Inverse of SSATransform — collapse SSA copies before final
  emission.
- **Lean impl.** Detect `let v := w` chains where `w` is dead after the
  copy and rewrite to direct assignment.
- **Proof difficulty.** **Medium.** Same family as SSATransform; a
  liveness-based argument suffices.

#### Rematerialiser (`m`)
- **What.** Replace uses of variables whose defining expression is
  cheap/pure by that expression.
- **Lean impl.** Build def-use chains; for each `let v := e` with `e`
  pure & cheap (literal, single arithmetic op, identifier), substitute
  uses, then let DCE remove `v`.
- **Proof difficulty.** **Medium.** Safety predicate: `e` must be pure
  AND its free vars are not reassigned between def and use. Side-effect
  classifier (§7) is a prerequisite. Proof is by induction over the
  trace, swapping a value lookup for a re-evaluation.

#### LiteralRematerialiser (`T`)
- **What.** Same as Rematerialiser but only for literals.
- **Lean impl.** Specialisation of Rematerialiser with predicate
  `isLiteral`.
- **Proof difficulty.** **Easy.** Literals are pure and deterministic;
  no aliasing or reassignment concerns.

#### ExpressionJoiner (`j`)
- **What.** Inverse of ExpressionSplitter — fold `let _i := e` back into
  use sites when `_i` is used exactly once and order permits.
- **Lean impl.** Single-use analysis; pattern `let _i := e; … use(_i) …`
  with no intervening side-effect on `e`.
- **Proof difficulty.** **Medium.** Needs an effect-commutation lemma:
  moving `e`'s evaluation to its single use is safe if no statement in
  between conflicts. Same machinery as Rematerialiser.

### 4.3 Simplification

#### Rules.lean (shared)
- **What.** Set of algebraic rewrite rules
  (`x+0 → x`, `mul(x,1) → x`, `iszero(iszero(b)) → b` when boolean,
  `and(x, ~0) → x`, comparison normalisations, …). Mirrors
  `libsolutil`/`libevmasm` `RuleList.h`.
- **Lean impl.** A `structure Rule where lhs : Pat; rhs : Pat;
  side : Pat → Bool` indexed by head opcode. Pattern matcher with
  `HashMap` lookup. Unit tests per rule.
- **Proof difficulty.** **Per-rule, easy.** Each rule is a 256-bit
  arithmetic identity; prove once with `decide` / `Nat`/`BitVec` tactics,
  then the simplifier is sound by structural induction over rule
  application. The scale (hundreds of rules) is the cost, not difficulty.

#### ExpressionSimplifier (`s`)
- **What.** Apply `Rules` bottom-up to expressions, with constant
  folding.
- **Lean impl.** Recursive `simpExpr : Expr → Expr` that first folds
  literal-only sub-expressions (use `BitVec 256` arithmetic) then
  attempts each rule.
- **Proof difficulty.** **Easy** given Rules are proven; correctness is
  a fold over rule-soundness lemmas.

#### ConditionalSimplifier (`C`) / ConditionalUnsimplifier (`U`)
- **What.** Inside `if cond { … }` and `switch`, replace uses of `cond`
  by the literal it must equal in that branch (and inverse).
- **Lean impl.** Track per-branch facts in a small assertion env;
  substitute when a tracked variable appears.
- **Proof difficulty.** **Medium.** Soundness depends on the asserted
  fact actually holding at runtime — direct from `if` semantics. The
  Unsimplifier needs liveness so the substitution is reversed only when
  it does not enlarge live ranges.

#### StructuralSimplifier (`t`)
- **What.** Collapse `if 0 { … }`, `if 1 { S } → S`, single-branch
  `switch`, etc.
- **Lean impl.** Pattern matches on AST.
- **Proof difficulty.** **Trivial.** One-step semantics rules.

#### ControlFlowSimplifier (`n`)
- **What.** Drop empty `for`, drop `continue` at end of body, simplify
  `switch` with one case, etc.
- **Lean impl.** AST patterns; small library of CFG-shape rewrites.
- **Proof difficulty.** **Easy.** Each rewrite is a local equivalence on
  the operational rules.

#### DeadCodeEliminator (`D`)
- **What.** Remove statements after `return`/`revert`/`stop`/`break`/
  `continue`/`leave`.
- **Lean impl.** Scan each block; once a terminator is seen, drop the
  rest. Builtin classifier flags `revert`/`return`/`stop` etc.
- **Proof difficulty.** **Easy.** Direct: terminators reduce to a halt
  configuration, suffix unreachable.

### 4.4 Data flow

#### UnusedPruner (`u`)
- **What.** Remove variables and functions with no uses (always run,
  even with `:` empty sequence).
- **Lean impl.** Compute global use set; drop unreferenced bindings
  whose defining expression is pure.
- **Proof difficulty.** **Easy** for pure defs, **medium** when removing
  `let v := e` with `e` having only "benign" effects (e.g. `mload` of a
  fresh location). Need conservative purity.

#### UnusedAssignEliminator (`r`)
- **What.** Drop `x := e` whose value is never read before next
  reassignment / end of scope.
- **Lean impl.** Backward liveness analysis per function; remove dead
  stores when `e` is pure.
- **Proof difficulty.** **Medium.** Standard dead-store removal proof
  via backward simulation, parameterised on liveness invariant.

#### UnusedStoreEliminator (`S`)
- **What.** Same idea for `mstore`/`sstore`/`tstore` killed by later
  stores to the same location with no intervening read.
- **Lean impl.** Symbolic location tracking inside a basic block;
  alias predicate `mayAlias` from the docs (`sub(l,m)` analysis).
- **Proof difficulty.** **Hard.** Memory aliasing is the crux; we need a
  precise model of EVM memory + the `sub(l,m)` decision procedure proven
  correct (or at least conservatively sound). Comparable to CompCert's
  memory model proofs.

#### EqualStoreEliminator (`E`)
- **What.** Drop `sstore(k, v)` (or memory equivalent) when the cell is
  already known to equal `v`.
- **Lean impl.** Forward abstract interpretation maintaining a partial
  map `Loc → Value`.
- **Proof difficulty.** **Hard.** Same memory model as above, plus a
  store/load equality argument. Easier for storage than for memory
  because storage cells are word-sized and key-addressed.

#### UnusedFunctionParameterPruner (`p`)
- **What.** Drop params/return-vars never used; rewrite call sites.
- **Lean impl.** Per-function use analysis; rewrite `FunctionDefinition`
  + every `FunctionCall`; introduce wrapper for external entry points.
- **Proof difficulty.** **Medium.** Need to argue that erased argument
  expressions are pure (or that their effects are kept by reordering).

#### CircularReferencesPruner (`l`)
- **What.** Remove functions only reachable via cycles among themselves.
- **Lean impl.** Build call graph; SCC; mark SCCs with no entry from
  outside as dead.
- **Proof difficulty.** **Easy.** Removing definitions never called
  from observable code is trivially semantics-preserving once
  reachability is correctly computed.

#### LoadResolver (`L`)
- **What.** Replace `mload(k)` / `sload(k)` with the known value when
  alias analysis allows.
- **Lean impl.** Forward abstract-interp tracking a `Loc ⇀ SymVal` map;
  invalidate on writes per `sub(l,m)` rule.
- **Proof difficulty.** **Hard.** Same memory-model overhead as
  UnusedStoreEliminator; the proof is the dual (load, not store).

#### LoopInvariantCodeMotion (`M`)
- **What.** Hoist `let v := e` out of a loop when `e`'s free variables
  are not assigned in the loop and `e` is pure.
- **Lean impl.** Liveness + purity check; move statement before the
  `for`.
- **Proof difficulty.** **Medium.** Classic LICM proof; bisimulation
  shows hoisted evaluation produces the same value because the
  invariants hold across iterations.

#### CommonSubexpressionEliminator (`c`)
- **What.** Replace repeated pure expressions by a single computation +
  reference.
- **Lean impl.** Hash-cons sub-expressions per block; substitute later
  occurrences with the bound variable, provided no clobbering operation
  intervened.
- **Proof difficulty.** **Medium.** For purely arithmetic expressions:
  direct. For expressions involving `mload`/`sload`: requires the same
  alias-aware model as LoadResolver. Plan to ship CSE in two tiers
  (pure-only first, memory-aware later).

### 4.5 Inlining / specialisation

#### ExpressionInliner (`e`)
- **What.** Inline tiny pure functions whose body is a single
  expression at call sites.
- **Lean impl.** Detect `function f(x…) -> r { r := <expr in x…> }`;
  substitute at call sites.
- **Proof difficulty.** **Medium.** β-reduction lemma over the function
  environment; needs argument-evaluation order matched.

#### FullInliner (`i`)
- **What.** Inline whole function bodies under a size/runs heuristic.
- **Lean impl.** For each call: α-rename body with fresh names
  (Disambiguator-style), substitute parameters, splice in. Heuristic
  uses AST size + call count + `--optimize-runs`.
- **Proof difficulty.** **Hard.** Inlining a multi-statement body
  including its own control flow requires care around `leave` (function
  return) which does not directly match `break`/`continue`. A correct
  encoding wraps the inlined body in a labelled construct or uses a
  fresh return-flag variable. Proof is a CompCert-style inlining
  simulation (well-known but non-trivial).

#### FunctionSpecializer (`F`)
- **What.** Generate specialised copies of a function for call sites
  with constant arguments.
- **Lean impl.** Detect call with literal args; clone function with
  params replaced by literals; rewrite call.
- **Proof difficulty.** **Medium.** Composition of α-renaming +
  literal-substitution proofs; smaller than FullInliner because
  control flow is unchanged.

#### EquivalentFunctionCombiner (`v`)
- **What.** Merge α-equivalent functions into one.
- **Lean impl.** Canonicalise function bodies (rename params to
  positional indices); hash; merge equal hashes; rewrite calls.
- **Proof difficulty.** **Easy/Medium.** Boils down to: equal
  α-classes denote equal functions. The α-equivalence lemma is reused
  from Disambiguator's correctness; the rewrite of call sites is a
  straightforward congruence.

### 4.6 Pipeline driver

- **What.** Parse step-letter sequences (`"dhfo[...]u"`), with
  bracket-loop fixpoint capped at 12 rounds, mandatory pre/post cleanup
  sequences, default sequence, `--yul-optimizations` override.
- **Lean impl.** `inductive Step | … (one ctor per pass)`; parser
  `String → List (Step ⊕ Loop (List Step))`; driver
  `Pipeline → YulAST → YulAST` with a fuel argument and an "unchanged"
  check (structural equality on the AST).
- **Proof difficulty.** **Trivial** for the driver itself given each
  pass is correct: composition of equivalences is an equivalence.
  Proving the fixpoint terminates is `decreasing_by` on fuel; proving
  it reaches a real fixpoint is not necessary for correctness.

---

## 5. Assembly-level optimizer passes

We need an Asm IR first:

```
inductive Op
  | push (n : BitVec 256)
  | pushTag (t : TagId)
  | pushSubSize (s : SubId) | pushSubData …
  | dup (i : Fin 16) | swap (i : Fin 16)
  | jump | jumpi | jumpdest (t : TagId)
  | opcode (e : EvmOp)         -- ADD, MUL, MLOAD, …
structure Asm := (ops : Array Op) (subs : Array Asm)
```

### JumpdestRemover
- **What.** Drop `JUMPDEST tag` nodes whose tag is not pushed anywhere.
- **Lean impl.** Compute set of referenced tags; filter `ops`.
- **Proof difficulty.** **Easy.** A `JUMPDEST` is a no-op except as a
  jump target; if unreachable it's dead code.

### PeepholeOptimizer
- **What.** Local rewrites:
  - `PUSH x POP → ε`
  - `SWAP1 SWAP1 → ε`, `DUPi POP → ε`
  - `tag JUMP JUMPDEST(tag) → JUMPDEST(tag)`
  - `JUMP <unreachable> → JUMP`
  - `ISZERO ISZERO ISZERO → ISZERO`
  - `PUSH 0 NOT → PUSH ~0`
  - … (port from `PeepholeOptimiser.cpp`).
- **Lean impl.** A list of `Pattern → Pattern` rewrites applied in a
  single linear pass; loop until fixpoint.
- **Proof difficulty.** **Per-rule easy, aggregate medium.** Each
  rewrite is a local stack-machine identity. The harder ones involve
  tag-aware reasoning (jump elimination), which needs a per-block CFG
  invariant. Aim to prove maybe 80% of the rewrites and leave
  control-flow rewrites until the assembly semantics is solid.

### Inliner (Simple Inliner)
- **What.** Replace `PUSHTAG t; JUMP` with the body of the basic block
  starting at `t` when that body is small and ends in `JUMP "out"`.
- **Lean impl.** Detect blocks ending in tagged out-jumps; substitute
  at call sites; let JumpdestRemover/PeepholeOptimizer mop up.
- **Proof difficulty.** **Hard.** Requires reasoning about the
  control-flow graph and ensuring no other code path observes the
  inlined block. Proof is similar to Yul's FullInliner but at a
  lower level (unstructured jumps), which is genuinely harder. Plan
  to prove only under the assumption "tags annotated `in`/`out`
  faithfully reflect callsites" (which the codegen guarantees).

### CommonSubexpressionEliminator (assembly)
- **What.** Per basic block, run a symbolic stack/memory/storage
  interpreter using the shared `Rules`; re-emit minimal code from the
  resulting expression DAG + side-effect list (memory/storage writes
  in original order, dropped if dead).
- **Lean impl.**
  1. `inductive SymExpr | const | input i | op : EvmOp → List SymExpr`
     hash-consed.
  2. Symbolic interpreter `Op → State Sym Unit` updating stack /
     memory map / storage map / log list, keyed by `SymExpr` with the
     `mayAlias` decision from the docs.
  3. Code generator that reconstructs minimum-length opcode sequence
     to realise the final stack and side-effect list (this is itself
     a small NP-ish problem; use the same heuristic Solidity uses).
- **Proof difficulty.** **Hard → Very hard.** Two intertwined parts:
  (a) the symbolic interpreter is an abstract interpretation of EVM
  semantics — proof of soundness is a standard simulation but with
  many cases (every opcode), and (b) the code re-emission must produce
  a sequence equivalent to the abstract state — proof is by induction
  on the emission order, but plumbing stack scheduling correctness is
  non-trivial. Realistically, prove (a), validate (b) by translation
  validation (per-call comparing concrete vs symbolic execution on
  random inputs) rather than full proof.

### ConstantOptimiser
- **What.** Replace expensive literal pushes with cheaper computations
  (`PUSH 32 SHL`, `NOT`, etc.) when smaller in bytes / cheaper in gas.
- **Lean impl.** For each literal, enumerate candidate encodings, score
  by `bytes + runs * gas`, pick minimum.
- **Proof difficulty.** **Easy.** Each candidate is a pure-arithmetic
  identity proven once with `decide`/`BitVec` tactics.

### BlockDeduplicator
- **What.** Merge identical basic blocks behind a single tag.
- **Lean impl.** Hash basic blocks (after canonical tag-renaming);
  merge equal hashes; redirect all references to the survivor.
- **Proof difficulty.** **Medium.** Similar to EquivalentFunctionCombiner
  but at the assembly level. Equal blocks have equal observational
  semantics; redirection of jumps is justified by the CFG semantics.

### Assembly Pipeline driver
- **What.** Run the above to fixpoint; outer heuristic uses
  `--optimize-runs`.
- **Lean impl.** Same `Step | Loop` machinery as Yul pipeline.
- **Proof difficulty.** **Trivial** given each pass is correct.

---

## 6. Phased work breakdown (incremental milestones)

1. **Phase A — Foundations.** Yul AST/parser/printer; Yul interpreter;
   EVM opcode + interpreter; naive Yul→EVM codegen; assembler;
   end-to-end test harness (interpret Yul vs interpret bytecode).
   *Proof bar:* none; tests only.
2. **Phase B — Yul preprocessing & normal form** (§4.1).
   *Proof bar:* prove Disambiguator, Hoister, Grouper, BlockFlattener,
   VarDeclInitializer (all easy); leave ForLoop rewriters with tests.
3. **Phase C — Pseudo-SSA layer** (§4.2).
   *Proof bar:* prove LiteralRematerialiser; SSATransform/SSAReverser
   with tests + invariants.
4. **Phase D — Local simplification** (§4.3).
   *Proof bar:* prove `Rules.lean` rule-by-rule; lift to
   ExpressionSimplifier, StructuralSimplifier, DeadCodeEliminator.
5. **Phase E — Data-flow passes** (§4.4).
   *Proof bar:* easy ones (UnusedPruner, CircularReferencesPruner)
   proven; hard memory-aliasing ones (UnusedStoreEliminator,
   LoadResolver, EqualStoreEliminator) deferred; ship with tests +
   contract-level differential testing.
6. **Phase F — Inlining** (§4.5).
   *Proof bar:* EquivalentFunctionCombiner proven; FullInliner with
   tests, plan a CompCert-style inlining proof later.
7. **Phase G — Yul pipeline driver** (§4.6).
8. **Phase H — Assembly IR + non-naive codegen.**
9. **Phase I — Assembly optimizer** (§5).
   *Proof bar:* JumpdestRemover, ConstantOptimiser, peephole
   arithmetic rewrites proven; CSE shipped with translation
   validation; Inliner with tests.
10. **Phase J — Assembler.** Iterative push-size resolution; emit
    bytecode + auxdata.
11. **Phase K — CLI + parity testing.** Mirror
    `solc --strict-assembly --optimize`. Differential test against
    `solc` corpus on observable EVM behaviour.
12. **Phase L — Verification (stretch).** Top-level theorem
    `∀ p, ⟦compile p⟧_EVM ≈ ⟦p⟧_Yul`. Strategy: each pass has a
    semantic-preservation lemma (where proven); compose them through
    the pipeline; codegen + assembler proven separately.

---

## 7. Cross-cutting concerns

- **Side-effect classifier (`Yul/Builtins.lean`).** Per-builtin record:
  `reads_memory`, `writes_memory`, `reads_storage`, `writes_storage`,
  `can_revert`, `can_terminate`, `msize_sensitive`. Used by every DCE,
  inliner and motion pass. *Proof:* state once, reuse everywhere.
- **Dialect parameterisation.** AST parameterised over a `Dialect`
  typeclass providing builtin set + semantics.
- **Memory model.** A single `Mem` structure used by both Yul and EVM
  semantics, implemented as a finite map `BitVec 256 → BitVec 8` (or
  a sparse word map). Aliasing predicates proven against this model
  once; reused by every memory-touching pass.
- **Determinism and fresh names.** A `NameGen` reader-state monad;
  Disambiguator establishes the invariant other passes assume.
- **`UnusedPruner` always runs**, even with `:`. Encoded as part of
  the cleanup sequence.
- **Translation validation.** For passes too costly to fully verify
  (assembly CSE, FullInliner), implement a checker that runs a small
  symbolic execution on inputs and outputs and certifies equivalence
  per call. This is the same trade-off CompCert makes for some
  passes.

## 8. Open questions

- Target EVM version (Cancun?).
- Object/sub-object support in v1 (constructor + runtime layout)?
- Bit-for-bit parity with `solc` or only behavioural parity? (Hard
  passes will be much easier with only behavioural parity.)
- Is verification (Phase L) in scope for v1, or shipped pass-by-pass?
- Do we use Mathlib's `BitVec` or a hand-rolled `Word256`?

---

## 9. Proof-difficulty summary table

| Pass | Difficulty |
|---|---|
| Disambiguator | easy |
| FunctionHoister | easy |
| FunctionGrouper | easy |
| ForLoopInitRewriter | easy |
| ForLoopConditionInto/OutOfBody | easy |
| VarDeclInitializer | trivial |
| BlockFlattener | easy |
| ExpressionSplitter | easy/medium |
| SSATransform / SSAReverser | medium |
| Rematerialiser | medium |
| LiteralRematerialiser | easy |
| ExpressionJoiner | medium |
| Algebraic Rules (each) | easy |
| ExpressionSimplifier | easy (given Rules) |
| Conditional{,Un}Simplifier | medium |
| StructuralSimplifier | trivial |
| ControlFlowSimplifier | easy |
| DeadCodeEliminator | easy |
| UnusedPruner | easy/medium |
| UnusedAssignEliminator | medium |
| UnusedStoreEliminator | hard |
| EqualStoreEliminator | hard |
| UnusedFunctionParameterPruner | medium |
| CircularReferencesPruner | easy |
| LoadResolver | hard |
| LoopInvariantCodeMotion | medium |
| CommonSubexpressionEliminator (Yul) | medium (pure) / hard (memory) |
| ExpressionInliner | medium |
| FullInliner | hard |
| FunctionSpecializer | medium |
| EquivalentFunctionCombiner | easy/medium |
| Yul Pipeline driver | trivial |
| Asm JumpdestRemover | easy |
| Asm Peephole | easy per rule, medium aggregate |
| Asm Inliner | hard |
| Asm CSE | hard / very hard |
| Asm ConstantOptimiser | easy |
| Asm BlockDeduplicator | medium |
| Asm Pipeline driver | trivial |
| Codegen Yul→Asm | medium |
| Assembler/Linker | medium |

---

## 10. Verified mini compiler (current status)

A working, end-to-end verified compiler for a meaningful Yul subset
lives in `YulC/Mini/`. It is intentionally separate from the
optimizer pipeline above so the proof effort is self-contained and
the design can be iterated without breaking the wider tree.

### Subset covered

| Construct          | Source                                  | Codegen                          |
|--------------------|-----------------------------------------|----------------------------------|
| Literal            | `lit n`                                 | `PUSH n`                         |
| Variable           | `var x`                                 | `DUP (depth + 1)`                |
| Unary builtin      | `iszero`                                | `<a>; UN op`                     |
| Binary builtins    | `add sub mul div mod and or xor lt gt eq` | `<a>; <b'>; BIN op`            |
| `let`              | `let x := e`                            | `<e>` (layout grows)             |
| Assignment         | `x := e`                                | `<e>; SWAP (d+1); POP`           |
| Block              | `{ … }`                                 | grouping (no codegen overhead)   |

Restrictions: distinct binders only (no shadowing), no control flow
(`if`/`for`/`switch`), no function definitions or calls, no
memory/storage/logs, no gas accounting. Word arithmetic now uses
`BitVec 256` (matches real EVM semantics, including wrap and unsigned
div/mod returning zero on divisor zero).

### Verified optimizer passes

| Pass             | Module                          | What it does                                |
|------------------|---------------------------------|---------------------------------------------|
| Constant folding | `Optim/ConstFold.lean`          | `op(lit, lit)` → `lit`                      |
| Algebraic simp   | `Optim/Algebraic.lean`          | `add(x, 0) → x`, `mul(x, 1) → x`, …         |
| Block flattening | `Optim/Flatten.lean`            | splice nested `block`s; drop outer wrappers |
| EVM peephole     | `Optim/Peephole.lean`           | drop adjacent `PUSH n; POP` on bytecode     |
| Composed         | `Optim.lean` (`optimize`)       | the three Yul-level passes, in order        |

Each Yul-level pass has a per-pass `*_exec` theorem proving
`Program.exec` preservation; `optimize_exec` chains them. The
bytecode-level peephole pass has its own `peephole_run` theorem
preserving `Bytecode.run`.

### Module layout (post-cleanup)

```
YulC/Mini.lean              -- thin re-export and overview
YulC/Mini/
  Util.lean                 -- generic List.setOpt + lemmas
  Syntax.lean               -- AST, Env.lookup/update
  Semantics.lean            -- big-step evaluator + Env.update lemmas
  Evm.lean                  -- mini-EVM Op, Stack, run, run_append
  Compiler.lean             -- Layout, codegen, depth lemmas
  Correctness.lean          -- Matches invariant + compile_correct
  Parser.lean               -- recursive-descent Yul parser
  Examples.lean             -- worked examples discharged by `decide`
  Optim.lean                -- composed `optimize` + `optimize_exec`
  Optim/
    ConstFold.lean          -- constant subexpression folding
    Algebraic.lean          -- safe algebraic identities
    Flatten.lean            -- nested-block flattening
```

Dependency DAG (strictly layered): Util → Syntax → Semantics  Evm →
Compiler → Correctness → Parser; Optim/* depend on Syntax + Semantics
only; Optim composes them; Examples depends on everything.

### Main theorems

* `YulC.Mini.Program.compile_correct`:

  ```
  Program.exec p [] = some env'
    → ∃ ops layout' stack',
         Program.compile p [] = some (ops, layout')
       ∧ Bytecode.run ops [] = some stack'
       ∧ Matches env' layout' stack'
  ```

* `YulC.Mini.compileOptimized_correct` lifts the same guarantee to the
  full optimised pipeline (`optimize` → `Program.compile` →
  `Bytecode.peephole`).

`Matches env layout stack` ties the source environment to the target
stack via the static layout (lengths agree; every name reads back
through the layout to the matching slot).

### Roadmap from here

**Reality check (updated 2026-05-01).** Sections 4–9 above describe the
*aspirational* full-parity pipeline (mirrors `solc`'s Yul + assembly
optimizers, ~30+ passes, full EVM model). The verified mini compiler
is intentionally a different, much smaller artefact: a self-contained
end-to-end proof that the *architecture* works. We have:

- a full source semantics → target semantics correctness theorem;
- three verified optimizer passes composed into `optimize`;
- a parser, examples, and zero `sorry`s.

What we are **not** on track for is feature parity with §4–§9 — that
remains a multi-year ambition. The mini compiler's restricted Yul
subset (no `if`/`for`/`switch`/`function`, no memory, no storage, no
side effects, no gas) and toy EVM (no JUMP, no memory) put a hard
ceiling on what optimizations are even *expressible*, let alone
provable. Adding more "shallow" passes on this base is a diminishing
return.

**Revised priorities.** Two tracks, in dependency order:

#### Track A — Fidelity (unlocks future passes)

Each item below is foundation work that the §4–§9 passes will need;
without these, those passes cannot be even stated against our model.

1. **`BitVec 256` arithmetic.** ✅ *Done.* `Word := BitVec 256`;
   `BinOp.apply` uses native `+ - * / % &&& ||| ^^^` and `<` on
   `BitVec`. All existing proofs (constant folding, algebraic, flatten)
   ported with zero extra lemmas — the core `BitVec` simp set already
   knows `add_zero`, `mul_one`, etc.
2. **Control flow: `if cond { body }` and `for`.** Add `Op.jumpdest`,
   `Op.jumpi`, `Op.jump` to the EVM, plus a position-resolution pass.
   Require *balanced* code blocks (net stack change = 0) so the
   `Matches` invariant survives across branches. This is the hardest
   single jump in the roadmap — see "scope cleanup" notes from earlier
   block-stmt attempts. *Difficulty: hard.*
3. **Function definitions and calls.** Adds a calling-frame layout
   invariant on top of the basic `Matches`. Builds on (2).
   *Difficulty: hard.*
4. **Memory model.** A `Mem := BitVec 256 → BitVec 8` finite map (or
   sparse word map). Adds `Op.mload/mstore` and a `MemMatches`
   invariant. Necessary to talk about any side-effecting builtin.
   *Difficulty: medium–hard.*
5. **Storage and gas (later).** Symmetric to memory but persistent;
   gas as an explicit running counter. Likely deferred to v2.

#### Track B — More breadth on the *current* base (cheap wins)

These can be added without touching the model. Each is a small,
self-contained verified pass.

1. **Dead `let` elimination (closed RHS).** Drop `letDecl x e` when
   `x` is unmentioned in the rest of the program *and* `e` has no
   `var` (so it cannot fail). The closed-RHS condition is what makes
   the proof go through without a global "well-scoped" hypothesis.
   *Difficulty: easy. ~80 lines.*
2. **Adjacent-let coalescing.** `let x := e₁; let y := e₂` where
   `e₂` doesn't use `x` and they're independent — purely cosmetic
   normalisation; probably not worth it without control flow.
3. **Boolean canonicalisation under `iszero`.** `iszero(eq(a, b))`
   etc., once `if` exists. Defer until after Track A.2.
4. **Peephole on the *current* EVM ops.** ✅ *Done* (initial rule).
   `Optim/Peephole.lean` ships `PUSH n; POP → ε` with a one-line
   `fun_induction`-based proof. Additional rules
   (`SWAP1; SWAP1`, `DUPi; POP`, …) need a static stack-depth analysis
   to avoid changing the failure shape of `Bytecode.run`; deferred.

#### Scope of solc-parity work (§4–§9 above)

To set expectations: each major item in §4–§9 (e.g. `FullInliner`,
`UnusedStoreEliminator`, `LoadResolver`, `BlockDeduplicator`) is a
multi-week project on its own *given* a real EVM model. Until Track A
items 1, 2, 4 are done, those passes remain in the "future work"
backlog.

**Recommended next step:** Track A.2 (control flow: `if` / `for` with
`JUMP`/`JUMPI`). With both `BitVec 256` and the bytecode-level
peephole infrastructure in place, control flow is the next foundation
needed to unlock §4–§9 passes that touch branches or loops.
