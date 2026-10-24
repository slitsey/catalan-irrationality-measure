module

public import CatalanCore.NV.Hybrid.Bordered
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# The Schur step of DO Proposition 1.3 (pure algebra)

Index types: `A` (low nodes `a < K`), `c` (the high nodes in `C`), `m` (the borders `X'`, `Y'`).
The reduced matrix (after scaling the high rows/columns by `ℓ`) is
`Zmat = [[X - Aa, -¼Wc, -¼Wy], [-¼Wcᵀ, -I, 0], [-¼Wxᵀ, 0, 0]]` on `(A ⊕ c) ⊕ m`.

The determinant identity under the harmonic hypothesis is `det_ZmatN` (`Mod3.lean`).
-/

@[expose] public section

open Matrix

namespace CatalanFrames.LambdaHybrid.NV

variable {F : Type*} [Field F] {A c m g : Type*}
  [Fintype A] [DecidableEq A] [Fintype c] [DecidableEq c] [Fintype m] [DecidableEq m]
  [Fintype g] [DecidableEq g]

/-- The reduced matrix on `(A ⊕ c) ⊕ m`, with cross coefficient `t` and high diagonal `d`
(`t = -1/4`, `d = -1` for λ). -/
def Zmat (x t d : F) (Aa : Matrix A A F) (Wc : Matrix A c F) (Wx Wy : Matrix A m F) :
    Matrix ((A ⊕ c) ⊕ m) ((A ⊕ c) ⊕ m) F :=
  fromBlocks (fromBlocks (x • (1 : Matrix A A F) - Aa) (t • Wc) (t • Wcᵀ) (d • (1 : Matrix c c F)))
    (fromRows (t • Wy) 0) (fromCols (t • Wxᵀ) 0) 0

/-- Reindexing `(A ⊕ c) ⊕ m ≃ (A ⊕ m) ⊕ c`. -/
def zEquiv (A c m : Type*) : (A ⊕ c) ⊕ m ≃ (A ⊕ m) ⊕ c where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr j) => Sum.inr j
    | Sum.inr i => Sum.inl (Sum.inr i)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr i) => Sum.inr i
    | Sum.inr j => Sum.inl (Sum.inr j)
  left_inv := by rintro ((a | j) | i) <;> rfl
  right_inv := by rintro ((a | i) | j) <;> rfl

end CatalanFrames.LambdaHybrid.NV
