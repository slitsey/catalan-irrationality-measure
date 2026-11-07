module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3I

@[expose] public section

/-!
# Lemma E, class 3: the solution `V` of `A V = B`, `C V = 0` and the rank bound

`V1 c y = [c = c'_y] τ'` on `Pt` and `V2 w y = Q(w, y)` on `Wt` (`τ' = 16⁻¹ s`, `s = 1 - 4/5`);
the equation `C V = 0` is the antisymmetry `(z - y)⁻¹ + (y - z)⁻¹ = 0` of DQ Theorem 2.2.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {o p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

variable (S : ESetup3 o p r m k1)

include S

/-- The partner `c'_y = y' - p` of the zone column `y' = r + 2y + 1`. -/
def e0 (y : Fin m) : Pt3 p r m :=
  ⟨⟨r + 2 * (y : ℕ) + 1 - p, by have := y.2; have := S.hN; have := S.hpr; omega⟩,
   by have := y.2; have := S.hN; have := S.hpr; show ¬ isCz p r m (r + 2 * (y : ℕ) + 1 - p); unfold isCz; omega⟩

/-- The partner `c_x = z - p` of the zone row `z = r + 2x`. -/
def ww (x : Fin m) : Wt3 p r m :=
  ⟨⟨r + 2 * (x : ℕ) - p, by have := x.2; have := S.hN; have := S.hpr; omega⟩,
   by have := x.2; have := S.hN; have := S.hpr; show isCz p r m (r + 2 * (x : ℕ) - p); unfold isCz; omega⟩

noncomputable def V1 (c : Pt3 p r m) (y : Fin m) : RatFunc (ZMod p) :=
  if c = e0 S y then rfC p ((16 : ZMod p)⁻¹ * s3 p) else 0

noncomputable def V2 (w : Wt3 p r m) (y : Fin m) : RatFunc (ZMod p) :=
  rfC p ((16 * (((r + 2 * (y : ℕ) + 1 : ℕ) : ZMod p) - (w.1 : ℕ)))⁻¹ * s3 p)

lemma e0_val (y : Fin m) : ((e0 S y).1 : ℕ) = r + 2 * (y : ℕ) + 1 - p := rfl
lemma ww_val (x : Fin m) : ((ww S x).1 : ℕ) = r + 2 * (x : ℕ) - p := rfl

lemma wC_bounds (w : Wt3 p r m) : k1 ≤ (w.1 : ℕ) ∧ (w.1 : ℕ) < p ∧ r - p ≤ (w.1 : ℕ) := by
  have := S.hk2r; have := S.hN; have := S.hpr; have := w.2; have := w.1.2
  unfold isCz at *; omega

lemma e0_bounds (y : Fin m) : k1 ≤ ((e0 S y).1 : ℕ) ∧ ((e0 S y).1 : ℕ) < p := by
  have := S.hk2r; have := S.hN; have := S.hpr; have := y.2
  rw [e0_val]; omega

lemma TE3_WP0 (w : Wt3 p r m) (y : Fin m) : TEw3 p r m (sd3 S) w.1 (e0 S y).1 = 0 := by
  obtain ⟨hw1, hw2, hw3⟩ := wC_bounds S w
  obtain ⟨he1, he2⟩ := e0_bounds S y
  have hwC := w.2
  have hew := (e0 S y).2
  have hwc : wr p r m (w.1 : ℕ) + wc p r m ((e0 S y).1 : ℕ) = 1 := by
    rw [wr_Wt, wc_Pt]
  have hne : (w.1 : ℕ) ≠ (e0 S y).1 := by
    intro h
    apply hew
    rw [← h]; exact hwC
  have hpar : ((e0 S y).1 : ℕ) - (w.1 : ℕ) ≠ p ∧ (w.1 : ℕ) - ((e0 S y).1 : ℕ) ≠ p := by
    constructor <;> omega
  rcases lt_or_gt_of_ne hne with h | h
  · rw [TEw3_lt _ h, hwc, TEoG_one _ hpar.1, singG_in S hw1 he2]; simp
  · rw [TEw3_gt _ h, hwc, TEoG_one _ hpar.2, singG_in S he1 hw2]; simp

end

end CatalanCore.Arith.Hybrid
