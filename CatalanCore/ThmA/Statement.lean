module

public import CatalanCore.ThmA.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Frozen statements for Theorem A at `θ = 0`

**STATUS: statements only; proofs are in progress.**  Every `sorry` in this file is a placeholder
for work being done elsewhere in `CatalanCore`; do not rely on them as proved.  The signatures are
frozen so that other packages (P6 nonvanishing, the λ upgrade) can build against them.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

/-- `krylovDet`: the Krylov determinant `u(A, v)`. -/
abbrev krylovDet {F : Type*} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) : F :=
  kdet A v

/-- Triangular number `T(m) = m (m+1)/2`. -/
def triNum (m : ℕ) : ℕ := m * (m + 1) / 2

/-- `A_K(s) = ∏_{c=1}^{K-1} [(s+c)(s+1-c)]^{T(K-c)}`. -/
def AK (K s : ℕ) : ℚ :=
  ∏ c ∈ Finset.Icc 1 (K - 1), (((s : ℚ) + c) * ((s : ℚ) + 1 - c)) ^ triNum (K - c)

/-- `B_K = ∏_{i=1}^{K-1} i^{2 i (K-i)}`. -/
def BK (K : ℕ) : ℚ := ∏ i ∈ Finset.Icc 1 (K - 1), (i : ℚ) ^ (2 * i * (K - i))

/-- `C_K(s) = ∏_{c=1}^{K} (s+c)^{β_c}`, `β_c = 2c(K+1-c) - K`. -/
def CK (K s : ℕ) : ℚ :=
  ∏ c ∈ Finset.Icc 1 K, ((s : ℚ) + c) ^ ((2 * (c : ℤ) * ((K : ℤ) + 1 - c)) - K)

/-- `κ_K^+ = ∏_{m=1}^{K-1} m^{2 (K-m)(K-2m)}`. -/
def kappaPlus (K : ℕ) : ℚ :=
  ∏ m ∈ Finset.Icc 1 (K - 1), (m : ℚ) ^ (2 * ((K : ℤ) - m) * ((K : ℤ) - 2 * m))

/-- The closed form `F(K, s) = (-1)^{⌊K/2⌋} κ_K^+ A_K(s) / (B_K C_K(s))`. -/
def Fcl (K s : ℕ) : ℚ := (-1) ^ (K / 2) * kappaPlus K * AK K s / (BK K * CK K s)

/-- **Theorem A at `θ = 0`** (STATEMENT ONLY): `u(K,s) = F(K,s)` for `s ≥ K - 1`. -/
theorem closed_form (K s : ℕ) (hK : 1 ≤ K) (hs : K - 1 ≤ s) : uK ℚ K s = Fcl K s := by
  sorry

/-- **Unit-ratio lemma** (STATEMENT ONLY). -/
theorem unit_of_lt (l : ℕ) [Fact l.Prime] (K s : ℕ) (hK : 1 ≤ K) (hs : K - 1 ≤ s)
    (hlt : s + K < l) : uK (ZMod l) K s ≠ 0 := by
  sorry

/-- **Lemma CC, shortcut (i)** (STATEMENT ONLY): over `𝔽_ℓ`, `ℓ ≡ 3 (mod 4)`,
`K = (ℓ+1)/4`, `s ∈ {K, K+1}`. -/
theorem uK_ne_zero_CC (l : ℕ) [Fact l.Prime] (K s : ℕ) (hl : l % 4 = 3) (hl7 : 7 ≤ l)
    (hK : K = (l + 1) / 4) (hs : s = K ∨ s = K + 1) : uK (ZMod l) K s ≠ 0 := by
  sorry

/-- **Corollary kr** (STATEMENT ONLY): if `u(A, v) ≠ 0` ... the two Gram matrices `N_s`, `N_{s+1}`
have no common eigenvalue (for every `z`, one of `det(z + N_s)`, `det(z + N_{s+1})` is nonzero). -/
theorem no_common_root_of_krylov {F : Type*} [Field F] (K s : ℕ)
    (hF : ∀ n : ℕ, 0 < n → n ≤ K + s + 1 → (n : F) ≠ 0) (hu : uK F K s ≠ 0) (z : F) :
    (z • (1 : Matrix (Fin K) (Fin K) F) + Nmat F K s).det ≠ 0 ∨
      (z • (1 : Matrix (Fin K) (Fin K) F) + Nmat F K (s + 1)).det ≠ 0 := by
  sorry

/-- **Cauchy determinant, two-family form** (STATEMENT ONLY). -/
theorem cauchy_det {F : Type*} [Field F] {n : ℕ} (x y : Fin n → F)
    (hxy : ∀ i j, x i + y j ≠ 0) :
    (Matrix.of fun i j => 1 / (x i + y j)).det =
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j - x i) * (y j - y i))) /
        ∏ i : Fin n, ∏ j : Fin n, (x i + y j) := by
  sorry

end CatalanCore.ThmA
