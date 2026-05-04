
/-!
# Assembly IR

Mid-level IR between Yul and EVM bytecode: a list of opcodes with
symbolic tags (jump targets) and sub-assemblies (constructor / runtime
/ data sections). See `PLAN.md` §5.
-/
namespace YulC.Codegen

abbrev TagId := Nat
abbrev SubId := Nat

inductive EvmOp
  | add | mul | sub | div | sdiv | mod | smod | exp
  | lt | gt | slt | sgt | eq | iszero | and | or | xor | not | byte
  | shl | shr | sar
  | keccak256
  | address | balance | origin | caller | callvalue
  | calldataload | calldatasize | calldatacopy
  | codesize | codecopy | gasprice
  | extcodesize | extcodecopy | returndatasize | returndatacopy
  | extcodehash | blockhash | coinbase | timestamp | number
  | prevrandao | gaslimit | chainid | selfbalance | basefee
  | blobhash | blobbasefee
  | pop | mload | mstore | mstore8 | sload | sstore
  | tload | tstore | mcopy | msize
  | gas
  | log0 | log1 | log2 | log3 | log4
  | create | call | callcode | return_ | delegatecall | create2
  | staticcall | revert | invalid | selfdestruct | stop
  deriving Repr, DecidableEq

inductive Op
  | push       (n : Nat)             -- literal value 0 ≤ n < 2^256
  | pushTag    (t : TagId)           -- to be resolved by linker
  | pushSubSize (s : SubId)
  | pushSubData (s : SubId)
  | dup        (i : Fin 16)
  | swap       (i : Fin 16)
  | jump | jumpi
  | jumpdest   (t : TagId)
  | op         (e : EvmOp)
  deriving Repr

structure Asm where
  ops  : Array Op
  subs : Array Asm
  deriving Inhabited

end YulC.Codegen
