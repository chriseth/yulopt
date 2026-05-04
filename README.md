# YulC

An optimizing compiler from [Yul](https://docs.soliditylang.org/en/latest/yul.html)
to EVM bytecode, written in Lean 4.

The design and per-pass implementation/proof-difficulty notes live in
[`PLAN.md`](./PLAN.md). The source tree mirrors that plan:

```
YulC/
 Syntax/      -- Yul AST + parser
 Semantics/   -- small-step semantics for Yul and EVM (specs)
 Yul/         -- Yul-level optimizer passes + pipeline driver
 Codegen/     -- Asm IR + Yul → Asm code generator
 Asm/         -- assembly-level optimizer passes + pipeline driver
 Assembler/   -- tag resolution + bytecode emission
 Driver/      -- CLI
```

## Build

```sh
lake build
```

## Status

Skeleton only — every pass is a stub returning its input unchanged.
