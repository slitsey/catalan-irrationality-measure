module

public import CatalanCore.Star.Leonard.DeltaCB

/-!
# Positivity: Cauchy–Gram determinants do not vanish for positive data

For `θ > 0` real (in particular rational `θ ∈ (0,1)`, the only range needed by the `θ → 0`
continuity argument), `det(C_Xᵀ C_Y)` with `a + x_i, a + y_i > 0` is `V(x)V(y)` times a sum of
squares-times-positive-weights (Cauchy–Binet, `delta_CB`), hence nonzero.  This is the nondegeneracy
mechanism for `hD2` (`det([R|W_X]ᵀ [R|W_Y]) ≠ 0`) and for cyclicity statements, avoiding any
closed form.
-/

@[expose] public section

open Finset Matrix CatalanCore

namespace CatalanCore.Star.Leonard

theorem Vprod_ne_zero_of_injective {m : ℕ} (v : Fin m → ℚ) (hv : StrictMono v) : Vprod v ≠ 0 := by
  unfold Vprod
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have : v i < v j := hv (Finset.mem_Ioi.1 hj)
  exact sub_ne_zero.2 (ne_of_gt this)

/-- **Cauchy–Gram determinants of positive data are nonzero.** -/
theorem det_CmCm_ne_zero_pos {K m : ℕ} (hmK : m ≤ K) (xs ys : Fin m → ℚ)
    (hx : ∀ (a : Fin K) (i : Fin m), 0 < ((a : ℕ) : ℚ) + xs i)
    (hy : ∀ (a : Fin K) (i : Fin m), 0 < ((a : ℕ) : ℚ) + ys i)
    (hVx : Vprod xs ≠ 0) (hVy : Vprod ys ≠ 0) :
    ((Cm K xs)ᵀ * Cm K ys).det ≠ 0 := by
  rw [delta_CB xs ys (fun a i => (hx a i).ne') (fun a i => (hy a i).ne')]
  refine mul_ne_zero (mul_ne_zero hVx hVy) (ne_of_gt ?_)
  have hex : ∃ P : Finset (Fin K), P.card = m := by
    obtain ⟨P, -, hP⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin K)))
      (n := m) (by simpa using hmK)
    exact ⟨P, hP⟩
  obtain ⟨P0, hP0⟩ := hex
  set P0' : {P : Finset (Fin K) // P.card = m} := ⟨P0, hP0⟩ with hP0'
  refine Finset.sum_pos' (fun P _ => ?_) ⟨P0', Finset.mem_univ _, ?_⟩
  · refine mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ => ?_)
    unfold rho
    refine inv_nonneg.2 (Finset.prod_nonneg fun j _ => ?_)
    exact (mul_pos (hx _ j) (hy _ j)).le
  · have hne : Vprod (fun i : Fin m => (((colsOf P0' i : Fin K) : ℕ) : ℚ)) ≠ 0 := by
      refine Vprod_ne_zero_of_injective _ fun i j hij => ?_
      have := (colsOf P0').strictMono hij
      exact_mod_cast Fin.lt_def.1 this
    refine mul_pos (sq_pos_of_ne_zero hne) (Finset.prod_pos fun i _ => ?_)
    unfold rho
    exact inv_pos.2 (Finset.prod_pos fun j _ => mul_pos (hx _ j) (hy _ j))

end CatalanCore.Star.Leonard
