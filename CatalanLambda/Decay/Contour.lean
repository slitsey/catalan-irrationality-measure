import CatalanLambda.Decay.RayFTC
import CatalanLambda.Decay.Atoms
import CatalanLambda.Decay.Reflect

/-!
# The contour identity

For `N0 : ℕ`, `x* = -N0 - 3/8`, `φ = 3π/5` and `Γ` the two rays `x* + r e^{±iφ}` traversed downward,
`16 · T_{ab} = - ∑_{m < N0} atomTerm a b m + (1/2πi) ∫_Γ E(z) (z-a)⁻¹ (z-b)⁻¹ dz`.
-/

open Complex MeasureTheory Filter Topology Set

namespace CatalanLambda.Decay

/-- The opening angle `φ = 3π/5`. -/
noncomputable def phiC : ℝ := 3 * Real.pi / 5

/-- The vertex `x* = -N0 - 3/8`. -/
noncomputable def xstar (N0 : ℕ) : ℝ := -(N0 : ℝ) - 3 / 8

lemma phiC_gt : Real.pi / 2 < phiC := by
  unfold phiC; linarith [Real.pi_pos]

lemma phiC_lt : phiC < Real.pi := by
  unfold phiC; linarith [Real.pi_pos]

/-- The integrand `g_p(z) = (z-p)⁻¹ (z-a)⁻¹ (z-b)⁻¹`. -/
noncomputable def g3 (p a b : ℝ) (z : ℂ) : ℂ := (z - p)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹

lemma contL_sub_g3 (p q a b x φ : ℝ) (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : p ≠ x) (hq : q ≠ x) (ha : a ≠ x) (hb : b ≠ x) :
    contL x φ (fun z => g3 p a b z - g3 q a b z) = contL x φ (g3 p a b) - contL x φ (g3 q a b) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have hf : (fun z => g3 p a b z - g3 q a b z) = fun z => g3 p a b z + (-1 : ℂ) * g3 q a b z := by
    funext z; ring
  have hR : ∀ θ : ℝ, Real.sin θ ≠ 0 → rayI x θ (fun z => g3 p a b z - g3 q a b z)
      = rayI x θ (g3 p a b) - rayI x θ (g3 q a b) := by
    intro θ hs
    have i1 : IntegrableOn (fun r : ℝ => g3 p a b (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0) :=
      integrableOn_ray3 p a b hp ha hb hs
    have i2 : IntegrableOn (fun r : ℝ => g3 q a b (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0) :=
      integrableOn_ray3 q a b hq ha hb hs
    have hh := rayI_add_smul (x := x) (θ := θ) (g3 p a b) (g3 q a b) (-1) i1 i2
    rw [hf, hh]
    ring
  unfold contL
  rw [hR φ hsφ, hR (-φ) hsφ']
  ring

lemma eterm_eq_g3 (n : ℤ) (a b : ℕ) (z : ℂ) :
    eterm z n * ((z - a)⁻¹ * (z - b)⁻¹)
      = g3 ((n : ℝ) + 1 / 4) a b z - g3 (n : ℝ) a b z := by
  unfold eterm g3
  push_cast
  simp only [one_div]
  ring

/-- Poles of `e_n` to the right of `x*` (`n ≥ -N0`): no contribution. -/
theorem contL_eterm_east (N0 a b : ℕ) (n : ℤ) (hn : -(N0 : ℤ) ≤ n) :
    contL (xstar N0) phiC (fun z => eterm z n * ((z - a)⁻¹ * (z - b)⁻¹)) = 0 := by
  have hn' : -(N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hx : xstar N0 = -(N0 : ℝ) - 3 / 8 := rfl
  have hfun : (fun z : ℂ => eterm z n * ((z - a)⁻¹ * (z - b)⁻¹))
      = fun z => g3 ((n : ℝ) + 1 / 4) a b z - g3 (n : ℝ) a b z := by
    funext z; exact eterm_eq_g3 n a b z
  rw [hfun, contL_sub_g3 _ _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith) (by rw [hx]; linarith)]
  unfold g3
  rw [contL_tri_east _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith),
    contL_tri_east _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith)]
  ring

/-- Poles of `e_{-(m+1)}` to the left of `x*` (`m ≥ N0`): the atom term. -/
theorem contL_eterm_west (N0 a b m : ℕ) (hm : N0 ≤ m) :
    contL (xstar N0) phiC (fun z => eterm z (-((m : ℤ) + 1)) * ((z - a)⁻¹ * (z - b)⁻¹))
      = -(2 * Real.pi * I) * (atomTerm a b m : ℝ) := by
  have hm' : (N0 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hx : xstar N0 = -(N0 : ℝ) - 3 / 8 := rfl
  have hfun : (fun z : ℂ => eterm z (-((m : ℤ) + 1)) * ((z - a)⁻¹ * (z - b)⁻¹))
      = fun z => g3 ((((-((m : ℤ) + 1) : ℤ)) : ℝ) + 1 / 4) a b z
          - g3 ((((-((m : ℤ) + 1) : ℤ)) : ℝ)) a b z := by
    funext z; exact eterm_eq_g3 _ a b z
  have e1 : ((((-((m : ℤ) + 1) : ℤ)) : ℝ)) = -(m : ℝ) - 1 := by push_cast; ring
  rw [hfun, e1]
  rw [contL_sub_g3 _ _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith) (by rw [hx]; linarith)]
  unfold g3
  rw [contL_tri_west _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith),
    contL_tri_west _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith)]
  have hR : (1 / (((-(m : ℝ) - 1 + 1 / 4) - a) * ((-(m : ℝ) - 1 + 1 / 4) - b))
      - 1 / (((-(m : ℝ) - 1) - a) * ((-(m : ℝ) - 1) - b))) = atomTerm a b m := by
    have e1 : (-(m : ℝ) - 1 + 1 / 4 - a) * (-(m : ℝ) - 1 + 1 / 4 - b)
        = ((a : ℝ) + m + 3 / 4) * ((b : ℝ) + m + 3 / 4) := by ring
    have e2 : (-(m : ℝ) - 1 - a) * (-(m : ℝ) - 1 - b) = ((a : ℝ) + m + 1) * ((b : ℝ) + m + 1) := by ring
    rw [e1, e2, atomTerm_eq]
  have key := congrArg (fun t : ℝ => (t : ℂ)) hR
  push_cast at key ⊢
  linear_combination (-(2 * (Real.pi : ℂ) * I)) * key

end CatalanLambda.Decay
