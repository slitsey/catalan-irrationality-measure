module

public import CatalanCore.Linalg.Telescope
public import Mathlib.Tactic.LinearCombination

/-!
# Telescoping for an intertwiner defect `X N_s - N'_{s+1} X` (package H5, (K4))

`N_s = Σ_{y=1}^{s} c_y c_yᵀ`, `N'_s = Σ_{y=1}^s c'_y c'_yᵀ`.  If, modulo `W₂` resp. `W₁`,
`X c_y ≡ a_y c'_y + b_y c'_{y+1}` and `Xᵀ c'_y ≡ a_y c_y + b_{y-1} c_{y-1}`, with `b_0 = 0`,
`a_{s+1} = 0`, then `X N_s x - N'_{s+1} X x ∈ W₂` for every `x` orthogonal to `W₁`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {K1 K2 : ℕ}

theorem telescopeX (X : Matrix (Fin K2) (Fin K1) F) (c : ℕ → Fin K1 → F) (c' : ℕ → Fin K2 → F)
    (a b : ℕ → F) (W1 : Submodule F (Fin K1 → F)) (W2 : Submodule F (Fin K2 → F))
    (x : Fin K1 → F) (hx : ∀ w ∈ W1, w ⬝ᵥ x = 0) (hb0 : b 0 = 0) :
    ∀ s : ℕ,
      (∀ y, 1 ≤ y → y ≤ s → X *ᵥ c y - a y • c' y - b y • c' (y + 1) ∈ W2) →
      (∀ y, 1 ≤ y → y ≤ s → Xᵀ *ᵥ c' y - a y • c y - b (y - 1) • c (y - 1) ∈ W1) →
      X *ᵥ (Nsum c s *ᵥ x) - Nsum c' s *ᵥ (X *ᵥ x) - (b s * (c s ⬝ᵥ x)) • c' (s + 1) ∈ W2 := by
  intro s
  induction s with
  | zero => intro _ _; simp [Nsum, hb0]
  | succ s ih =>
    intro hcol hrow
    have ih' := ih (fun y h1 h2 => hcol y h1 (by omega)) (fun y h1 h2 => hrow y h1 (by omega))
    have hc := hcol (s + 1) (by omega) le_rfl
    have hr := hrow (s + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hr
    have hxr := hx _ hr
    have hxr' : (Xᵀ *ᵥ c' (s + 1)) ⬝ᵥ x = a (s + 1) * (c (s + 1) ⬝ᵥ x) + b s * (c s ⬝ᵥ x) := by
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul] at hxr
      linear_combination hxr
    have e1 : c' (s + 1) ⬝ᵥ (X *ᵥ x) = (Xᵀ *ᵥ c' (s + 1)) ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have key : X *ᵥ (Nsum c (s + 1) *ᵥ x) - Nsum c' (s + 1) *ᵥ (X *ᵥ x)
        - (b (s + 1) * (c (s + 1) ⬝ᵥ x)) • c' (s + 1 + 1) =
        (X *ᵥ (Nsum c s *ᵥ x) - Nsum c' s *ᵥ (X *ᵥ x) - (b s * (c s ⬝ᵥ x)) • c' (s + 1))
          + (c (s + 1) ⬝ᵥ x) • (X *ᵥ c (s + 1) - a (s + 1) • c' (s + 1) - b (s + 1) • c' (s + 1 + 1)) := by
      rw [Nsum_mulVec_succ, Nsum_mulVec_succ, Matrix.mulVec_add, Matrix.mulVec_smul, e1, hxr']
      module
    rw [key]
    exact Submodule.add_mem _ ih' (Submodule.smul_mem _ _ hc)

end CatalanCore
