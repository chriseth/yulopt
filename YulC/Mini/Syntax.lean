/-!
# Yul subset: abstract syntax

Datatypes describing the (verified) subset of Yul this compiler
handles:

* `Word` — machine words (`BitVec 256`, matching the EVM).
* `Ident` — variable names.
* `BinOp`, `UnOp` — built-in operators. Reused by the EVM target as a
  shortcut: rather than introducing 12 separate opcodes, the mini-EVM
  has `Op.bin` / `Op.un` parameterised by the same operator tags.
* `Expr` — pure expressions.
* `Stmt` — statements (`let`, assignment).
* `Program` — a flat sequence of statements.
* `Env` — runtime environment for the source semantics.
-/

namespace YulC.Mini

/-- Machine word: a 256-bit unsigned bit vector, matching the EVM. -/
abbrev Word  := BitVec 256
abbrev Ident := String

/-- Built-in binary operators (Yul names). -/
inductive BinOp where
  | add | sub | mul | div | mod
  | and | or  | xor
  | lt  | gt  | eq
  deriving Repr, DecidableEq, Inhabited

/-- Built-in unary operators (Yul names). -/
inductive UnOp where
  | iszero
  deriving Repr, DecidableEq, Inhabited

inductive Expr where
  | lit (n : Word)
  | var (x : Ident)
  | un  (op : UnOp)  (a : Expr)
  | bin (op : BinOp) (a b : Expr)
  deriving Repr, Inhabited, DecidableEq

inductive Stmt where
  | letDecl (x : Ident) (rhs : Expr)
  | assign  (x : Ident) (rhs : Expr)
  | block   (body : List Stmt)
  deriving Repr, Inhabited

mutual

/-- Structural equality on `Stmt`. Hand-rolled because the nested
inductive `block (body : List Stmt)` blocks the auto-derivation. -/
def Stmt.beq : Stmt → Stmt → Bool
  | .letDecl x e, .letDecl x' e' => x == x' && e == e'
  | .assign x e,  .assign x' e'  => x == x' && e == e'
  | .block b,     .block b'      => Program.beq b b'
  | _, _ => false

/-- Structural equality on `Program` (a list of statements). -/
def Program.beq : List Stmt → List Stmt → Bool
  | [],      []      => true
  | s :: r,  s' :: r' => Stmt.beq s s' && Program.beq r r'
  | _,       _       => false

end

instance : BEq Stmt := ⟨Stmt.beq⟩

abbrev Program := List Stmt

/-- A source-level environment is an association list. The most
recently bound variable is at the head; `lookup` finds the first
binding (lexical scoping). -/
abbrev Env := List (Ident × Word)

namespace Env

@[simp] def lookup : Env → Ident → Option Word
  | [],            _ => none
  | (k, v) :: rest, x => if k = x then some v else lookup rest x

/-- Replace the *first* (most recent) binding of `x` with `w`.
Returns `none` if `x` is unbound, mirroring Yul's static guarantee
that `assign` targets must already be in scope. -/
@[simp] def update : Env → Ident → Word → Option Env
  | [],              _, _ => none
  | (k, v) :: rest, x, w =>
    if k = x then some ((k, w) :: rest)
    else (update rest x w).map (fun rest' => (k, v) :: rest')

end Env

end YulC.Mini
