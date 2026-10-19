module

public import CatalanFrames.LambdaHybrid.NV.Pair
public import CatalanFrames.LambdaHybrid.NV.Schur

/-!
# WP-H7 deliverable: both members vanish ⟹ `k_R ≡ 0` or `k_L ≡ 0`

`nv_pair`: for the member pair of DO §3 (member 2 = member 1 with the last absent node `g` moved
into `C`, same borders), if both determinants `det Full(r₀)` vanish and the mod-`ℓ` reduction
`ReductionHyp` (DO Prop 1.3: `det Full = 0 ⟹ B(Y₀) = 0`) holds for each member with the common
`Y₀ = H2_{K-1} - 16 r₀`, then `k_R = 0 ∨ k_L = 0` in `𝔽_ℓ`.

The two Cauchy determinants `det[G Y]`, `det[G X]` (`K × K`, nonzero by `CatalanCore.cauchy_det_mul`
since all node sums/differences lie in `[1, 2K+m-1] ⊂ [1, ℓ-1]`) are hypotheses here and are
discharged at the frame instance.  `k_R, k_L ≠ 0` (WP-H4) is NOT used: the conclusion is the
disjunction, the contrapositive of the hybrid nonvanishing.
-/

@[expose] public section

open Matrix

namespace CatalanFrames.LambdaHybrid.NV

variable {F : Type*} [Field F] {A : Type*} [Fintype A] [DecidableEq A] {s m : ℕ}

/-- The mod-`ℓ` reduction statement for one member (DO Prop 1.3, shape only): the vanishing of the
rational determinant `D` at `r₀` forces the bordered determinant `B(Y₀)` to vanish. -/
def ReductionHyp (D : Prop) (G : Matrix A (Fin s) F) (X Y : Matrix A (Fin m) F) (Y₀ : F) : Prop :=
  D → (bordered Y₀ G X Y).det = 0

/-- **Deliverable.** -/
theorem nv_pair (G : Matrix A (Fin (s + 1)) F) (X Y : Matrix A (Fin m) F)
    (e : Fin (s + 1) ⊕ Fin m ≃ A)
    (hY : ((fromCols G Y).submatrix e id).det ≠ 0) (hX : ((fromCols G X).submatrix e id).det ≠ 0)
    (Y₀ : F) (D₁ D₂ : Prop) (r₁ : ReductionHyp D₁ G X Y Y₀)
    (r₂ : ReductionHyp D₂ (dropLast G) X Y Y₀) (h₁ : D₁) (h₂ : D₂) :
    kR (gramHat G X Y) (Fin.last s) = 0 ∨ kL (gramHat G X Y) (Fin.last s) = 0 :=
  pair_krylov G X Y e hY hX Y₀ (r₁ h₁) (r₂ h₂)

/-- Contrapositive form: if `k_R, k_L ≠ 0` (WP-H4), one of the two members is nonvanishing. -/
theorem nv_pair_of_kne (G : Matrix A (Fin (s + 1)) F) (X Y : Matrix A (Fin m) F)
    (e : Fin (s + 1) ⊕ Fin m ≃ A)
    (hY : ((fromCols G Y).submatrix e id).det ≠ 0) (hX : ((fromCols G X).submatrix e id).det ≠ 0)
    (hkR : kR (gramHat G X Y) (Fin.last s) ≠ 0) (hkL : kL (gramHat G X Y) (Fin.last s) ≠ 0)
    (Y₀ : F) (D₁ D₂ : Prop) (r₁ : ReductionHyp D₁ G X Y Y₀)
    (r₂ : ReductionHyp D₂ (dropLast G) X Y Y₀) : ¬ D₁ ∨ ¬ D₂ := by
  by_contra h
  push Not at h
  rcases nv_pair G X Y e hY hX Y₀ D₁ D₂ r₁ r₂ h.1 h.2 with h' | h'
  exacts [hkR h', hkL h']

end CatalanFrames.LambdaHybrid.NV
