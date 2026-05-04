import YulC.Mini.Syntax
import YulC.Mini.Evm
import YulC.Mini.Compiler

/-!
# Yul concrete-syntax parser

A tiny recursive-descent parser for the supported Yul subset.

```
program ::= "{" stmt* "}" | stmt*
stmt    ::= "let" ident ":=" expr
          | ident ":=" expr
          | "if" expr "{" stmt* "}"
          | "{" stmt* "}"
expr    ::= literal
          | ident
          | builtin "(" (expr ("," expr)*)? ")"
literal ::= [0-9]+ | "0x" [0-9a-fA-F]+
ident   ::= [A-Za-z_$][A-Za-z0-9_$.]*
```

`//` line comments and `/* … */` block comments are skipped. Whitespace
is insignificant (Yul has no statement separators). Builtin names map
to `BinOp` / `UnOp` constructors.
-/

namespace YulC.Mini

abbrev ParseError := String

namespace Parser

abbrev Stream := List Char

private def isWS (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def isIdStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '$'

private def isIdCont (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '$' || c == '.'

private def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c ∧ c ≤ 'f') || ('A' ≤ c ∧ c ≤ 'F')

/-- Skip whitespace and `//` / `/* */` comments. -/
private partial def skipWS : Stream → Stream
  | [] => []
  | '/' :: '/' :: rest =>
    skipWS (rest.dropWhile (· ≠ '\n'))
  | '/' :: '*' :: rest =>
    skipBlock rest
  | c :: rest =>
    if isWS c then skipWS rest else c :: rest
where
  skipBlock : Stream → Stream
    | [] => []
    | '*' :: '/' :: rest => skipWS rest
    | _ :: rest => skipBlock rest

private def takeWhile (p : Char → Bool) (s : Stream) : String × Stream :=
  let taken := s.takeWhile p
  let rest  := s.dropWhile p
  (String.ofList taken, rest)

/-- Try to consume the literal string `tok` (after skipping whitespace),
returning the new stream on success. Used for keywords and punctuation. -/
private def consume (tok : String) (s : Stream) : Option Stream :=
  let s := skipWS s
  let rec go : List Char → Stream → Option Stream
    | [],      rest      => some rest
    | t :: ts, c :: rest => if t = c then go ts rest else none
    | _ :: _,  []        => none
  go tok.toList s

private def expect (tok : String) (s : Stream) : Except ParseError Stream :=
  match consume tok s with
  | some rest => .ok rest
  | none      => .error s!"expected '{tok}'"

/-- Parse an identifier (and return it together with the remaining stream).
Reserved words like `let` are *not* rejected here — callers handle that. -/
private def parseIdentRaw (s : Stream) : Except ParseError (String × Stream) :=
  let s := skipWS s
  match s with
  | c :: _ =>
    if isIdStart c then
      let (name, rest) := takeWhile isIdCont s
      .ok (name, rest)
    else
      .error s!"expected identifier, got '{c}'"
  | [] => .error "expected identifier, got end of input"

private def hexDigitVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseHexNat (digs : String) : Option Nat :=
  digs.toList.foldlM (fun acc c => (hexDigitVal c).map (acc * 16 + ·)) 0

/-- Parse an unsigned numeric literal (decimal or `0x…` hex). -/
private def parseLiteral (s : Stream) : Except ParseError (Word × Stream) :=
  let s := skipWS s
  match s with
  | '0' :: 'x' :: rest =>
    let (digs, rest') := takeWhile isHexDigit rest
    if digs.isEmpty then .error "expected hex digits after '0x'"
    else
      match parseHexNat digs with
      | some n => .ok (n, rest')
      | none   => .error s!"invalid hex literal '0x{digs}'"
  | c :: _ =>
    if c.isDigit then
      let (digs, rest) := takeWhile (·.isDigit) s
      match digs.toNat? with
      | some n => .ok (n, rest)
      | none   => .error s!"invalid decimal literal '{digs}'"
    else .error s!"expected literal, got '{c}'"
  | [] => .error "expected literal, got end of input"

/-- Map a builtin name + argument list to an expression. -/
private def builtinExpr (name : String) (args : List Expr) :
    Except ParseError Expr :=
  match name, args with
  | "add",    [a, b] => .ok (.bin .add a b)
  | "sub",    [a, b] => .ok (.bin .sub a b)
  | "mul",    [a, b] => .ok (.bin .mul a b)
  | "div",    [a, b] => .ok (.bin .div a b)
  | "mod",    [a, b] => .ok (.bin .mod a b)
  | "and",    [a, b] => .ok (.bin .and a b)
  | "or",     [a, b] => .ok (.bin .or a b)
  | "xor",    [a, b] => .ok (.bin .xor a b)
  | "lt",     [a, b] => .ok (.bin .lt a b)
  | "gt",     [a, b] => .ok (.bin .gt a b)
  | "eq",     [a, b] => .ok (.bin .eq a b)
  | "iszero", [a]    => .ok (.un .iszero a)
  | _, _ =>
    .error s!"unknown builtin or wrong arity: {name}({args.length} args)"

/-- Mutually recursive expression / argument-list parser. -/
private partial def parseExpr (s : Stream) : Except ParseError (Expr × Stream) := do
  let s := skipWS s
  match s with
  | c :: _ =>
    if c.isDigit then
      let (n, s') ← parseLiteral s
      return (.lit n, s')
    else if isIdStart c then
      let (name, s1) ← parseIdentRaw s
      if name = "let" then .error "unexpected keyword 'let' in expression" else
      if name = "if"  then .error "unexpected keyword 'if' in expression"  else
      -- Might be a variable reference, or a builtin call `name(...)`.
      match consume "(" s1 with
      | some s2 =>
        let (args, s3) ← parseArgs s2
        let s4 ← expect ")" s3
        let e ← builtinExpr name args
        return (e, s4)
      | none =>
        return (.var name, s1)
    else
      .error s!"unexpected character '{c}' in expression"
  | [] => .error "expected expression, got end of input"
where
  parseArgs (s : Stream) : Except ParseError (List Expr × Stream) := do
    -- Empty argument list?
    match consume ")" s with
    | some _ => return ([], s)
    | none =>
      let (a, s1) ← parseExpr s
      parseArgsTail [a] s1
  parseArgsTail (acc : List Expr) (s : Stream) :
      Except ParseError (List Expr × Stream) := do
    match consume "," s with
    | some s1 =>
      let (a, s2) ← parseExpr s1
      parseArgsTail (a :: acc) s2
    | none =>
      return (acc.reverse, s)

mutual

/-- Parse a single statement. -/
private partial def parseStmt (s : Stream) : Except ParseError (Stmt × Stream) := do
  let s := skipWS s
  match s with
  | '{' :: rest =>
    let (stmts, rest') ← parseStmts [] rest
    let rest' := skipWS rest'
    match rest' with
    | '}' :: tail => return (.block stmts, tail)
    | _ => .error "expected '}' to close block"
  | _ =>
  match consume "if" s with
  | some s1 =>
    match s1 with
    | c :: _ =>
      if isIdCont c then
        -- "if" was a prefix of a longer identifier; fall through.
        parseLetOrAssign s
      else
        let (cond, s2) ← parseExpr s1
        let s3 := skipWS s2
        match s3 with
        | '{' :: rest =>
          let (body, rest') ← parseStmts [] rest
          let rest' := skipWS rest'
          match rest' with
          | '}' :: tail => return (.iff cond body, tail)
          | _ => .error "expected '}' to close `if` body"
        | _ => .error "expected '{' after `if` condition"
    | [] => .error "unexpected end of input after 'if'"
  | none => parseLetOrAssign s

private partial def parseLetOrAssign (s : Stream) :
    Except ParseError (Stmt × Stream) := do
  match consume "let" s with
  | some s1 =>
    -- Make sure "let" wasn't actually the prefix of a longer ident.
    match s1 with
    | c :: _ =>
      if isIdCont c then
        -- Not the keyword; fall through to assignment.
        parseAssign s
      else
        let (x, s2) ← parseIdentRaw s1
        let s3 ← expect ":=" s2
        let (e, s4) ← parseExpr s3
        return (.letDecl x e, s4)
    | [] => .error "unexpected end of input after 'let'"
  | none => parseAssign s

/-- Parse zero or more statements until end of input or a closing `}`. -/
private partial def parseStmts (acc : List Stmt) (s : Stream) :
    Except ParseError (List Stmt × Stream) := do
  let s := skipWS s
  match s with
  | [] | '}' :: _ => return (acc.reverse, s)
  | _ =>
    let (st, s') ← parseStmt s
    parseStmts (st :: acc) s'

private partial def parseAssign (s : Stream) :
    Except ParseError (Stmt × Stream) := do
  let (x, s1) ← parseIdentRaw s
  if x = "let" then .error "unexpected keyword 'let'" else
  if x = "if"  then .error "unexpected keyword 'if'"  else
  let s2 ← expect ":=" s1
  let (e, s3) ← parseExpr s2
  return (.assign x e, s3)

end

/-- Parse a complete program. Accepts either `stmt*` or `{ stmt* }`. -/
def parseProgram (s : Stream) : Except ParseError Program := do
  let s := skipWS s
  let expectBrace := (consume "{" s).isSome
  let inner := match consume "{" s with | some s' => s' | none => s
  let (stmts, rest) ← parseStmts [] inner
  let rest := skipWS rest
  if expectBrace then
    match rest with
    | '}' :: tail =>
      let tail := skipWS tail
      if tail.isEmpty then .ok stmts
      else .error s!"unexpected trailing input: {String.ofList (tail.take 20)}…"
    | _ => .error "expected '}' to close program"
  else
    if rest.isEmpty then .ok stmts
    else .error s!"unexpected trailing input: {String.ofList (rest.take 20)}…"

end Parser

/-- Parse a Yul source string into a `Program`. -/
def Program.parse (src : String) : Except ParseError Program :=
  Parser.parseProgram src.toList

/-- End-to-end pipeline: parse Yul source, then compile to mini-EVM
bytecode (starting from an empty layout). -/
def Program.compileSource (src : String) :
    Except ParseError (Option (List Op × Layout)) := do
  let p ← Program.parse src
  return Program.compile p []

end YulC.Mini
