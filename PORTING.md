# Porting notes

OpenAI's formalization (https://github.com/openai/math, commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`) targets Lean v4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and its Catalan files are not modules. Palomar
requires Lean v4.35.0-rc2 or later, with every imported file a module. The vendored files in
`OAI/` and `PrimeNumberTheoremAnd/` were therefore changed as follows.

## 1. Module conversion (mechanical, all 506 Lean files of the development)

Each file received:

- a `module` header after its leading comments;
- `public import` in place of `import`;
- `@[expose] public section` directly after the imports, so that every declaration stays
  public and definitions keep their bodies visible to later files, as before.

Nothing else in these files was changed. On the original toolchain (Lean v4.34.1, OpenAI's
Mathlib pin), the converted development builds without errors.

## 2. Toolchain update to Lean v4.35.0-rc2

Mathlib moves from `d13f23b` (master as of 2026-09-15, plus the v4.34.1 bump) to the
`v4.35.0-rc2` tag (`065356127b1dc0016f66b7283ce0ce2c4055aa55`, 2026-09-16), 69 commits later.
Source changes needed for this update are listed below.

Status: in progress.
