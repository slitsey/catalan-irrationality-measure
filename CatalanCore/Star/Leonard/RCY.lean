module

public import CatalanCore.Star.Leonard.CCY

/-!
# (RC) at the border points `x ∈ X`: `T~ᵀ` preserves `span WX` (package H2, (T1))
-/

@[expose] public section

open Polynomial Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma Qh2_eval_int_ne' [CharZero F] (m S : ℕ) (c : ℤ)
    (h : ∀ j < m, c + S + 2 * ((j : ℤ) + 1) ≠ 0) : (Qh2 m (S : F)).eval (c : F) ≠ 0 := by
  unfold Qh2 PPf
  rw [eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hj' := h j (Finset.mem_range.1 hj)
  rw [eval_lin]
  have : (1 : F) * (c : F) + ((S : F) + 2 * ((j : F) + 1)) = ((c + S + 2 * ((j : ℤ) + 1) : ℤ) : F) := by
    push_cast; ring
  rw [this]
  exact_mod_cast hj'

/-- **(RC) polynomial form, border case.** -/
theorem RC_polyY [CharZero F] (K m : ℕ) (hm : 1 ≤ m) (S θ y : F)
    (hQ1 : (Qh2 m S).eval (1 - y) ≠ 0) (hQ3 : (Qh2 m S).eval (-y - 1) ≠ 0) :
    ∃ N : F[X], N.natDegree < m ∧
      Hz2 K m S θ y (S - K + m + 1)
        (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)
        - Qh2 m S * (C ((aP2 K m S θ).eval (1 - y) / (Qh2 m S).eval (1 - y)) * (lin 1 y * lin 1 (y + 1))
            + C ((Dz K m S θ (S - K + m + 1)
                (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)).eval (-y))
              * (lin 1 (y - 1) * lin 1 (y + 1))
            + C ((bP2 K m S θ).eval (-y - 1) / (Qh2 m S).eval (-y - 1))
              * (lin 1 (y - 1) * lin 1 y))
      = (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N := by
  set g : F := S - K + m + 1 with hg
  set c0 : F := -2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2 with hc0
  set ℓ := (aP2 K m S θ).eval (1 - y) / (Qh2 m S).eval (1 - y) with hℓ
  set d := (Dz K m S θ g c0).eval (-y) with hd
  set r := (bP2 K m S θ).eval (-y - 1) / (Qh2 m S).eval (-y - 1) with hr
  have e1 : lin 1 (y - 1) = X - C (1 - y) := by rw [lin_one]; congr 2; ring
  have e2 : lin 1 y = X - C (-y) := lin_one y
  have e3 : lin 1 (y + 1) = X - C (-y - 1) := by rw [lin_one]; congr 2; ring
  obtain ⟨N, hN⟩ := three_div (aP2 K m S θ - C ℓ * Qh2 m S) (Dt2 K m S θ g c0 - C d * Qh2 m S)
    (bP2 K m S θ - C r * Qh2 m S) (1 - y) (-y) (-y - 1)
    (by rw [eval_sub, eval_mul, eval_C, hℓ, div_mul_cancel₀ _ hQ1, sub_self])
    (by
      unfold Dt2
      rw [eval_sub, eval_mul, eval_mul, eval_C]
      unfold Qh2
      rw [hd]; ring)
    (by rw [eval_sub, eval_mul, eval_C, hr, div_mul_cancel₀ _ hQ3, sub_self])
  have heq : Hz2 K m S θ y g c0 - Qh2 m S * (C ℓ * (lin 1 y * lin 1 (y + 1))
      + C d * (lin 1 (y - 1) * lin 1 (y + 1)) + C r * (lin 1 (y - 1) * lin 1 y))
      = (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N := by
    rw [e1, e2, e3, ← hN, Hz2_eq, e1, e2, e3]; ring
  refine ⟨N, ?_, heq⟩
  have hdeg : ((lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N).natDegree ≤ m + 2 := by
    rw [← heq]
    refine (natDegree_sub_le _ _).trans (max_le (Hz2_natDegree_le K m S θ y) ?_)
    refine (natDegree_mul_le).trans ?_
    have h1 : (C ℓ * (lin 1 y * lin 1 (y + 1))).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h2 : (C d * (lin 1 (y - 1) * lin 1 (y + 1))).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h3 : (C r * (lin 1 (y - 1) * lin 1 y)).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h12 := (natDegree_add_le _ _).trans (max_le h1 h2)
    have h123 := (natDegree_add_le _ _).trans (max_le h12 h3)
    have hQ : (Qh2 m S).natDegree ≤ m := natDegree_PPf_le _ _
    omega
  by_cases hN0 : N = 0
  · subst hN0; simp; omega
  · have hU : (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)).natDegree = 3 := by
      rw [e1, e2, e3]; exact natDegree_three _ _ _
    have hUne : (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) ≠ 0 := by
      intro h0; rw [h0] at hU; simp at hU
    rw [natDegree_mul hUne hN0, hU] at hdeg
    omega


/-- **(T1) for one border column.**  For `x = S + 2j + 2 ∈ X`: `T~ᵀ c_x = d c_x + Σ_{x'∈X} κ_{x'} c_{x'}`.
Symbolic `m`. -/
theorem TtilT_colY [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (j : ℕ)
    (hj : j < m) :
    ∃ (d : F) (κ : ℕ → F), (Ttil K m S θ)ᵀ *ᵥ wcol K θ ((S + 2 * j + 2 : ℕ) : ℤ) =
      d • wcol K θ ((S + 2 * j + 2 : ℕ) : ℤ)
        + ∑ i ∈ Finset.range m, κ i • wcol K θ ((S + 2 * i + 2 : ℕ) : ℤ) := by
  set y : F := ((S + 2 * j + 2 : ℕ) : F) with hy
  have hQ1 : (Qh2 m (S : F)).eval (1 - y) ≠ 0 := by
    have := Qh2_eval_int_ne' (F := F) m S (1 - ((S + 2 * j + 2 : ℕ) : ℤ))
      (fun i _ => by push_cast; omega)
    push_cast at this; rw [hy]; push_cast; exact this
  have hQ3 : (Qh2 m (S : F)).eval (-y - 1) ≠ 0 := by
    have := Qh2_eval_int_ne' (F := F) m S (-((S + 2 * j + 2 : ℕ) : ℤ) - 1)
      (fun i _ => by push_cast; omega)
    push_cast at this; rw [hy]; push_cast; exact this
  obtain ⟨N, hNd, heq⟩ := RC_polyY K m hm (S : F) θ y hQ1 hQ3
  have hQQ : Qh m ((S : F) + 1) = Qh2 m (S : F) := by simp [Qh, Qh2]
  obtain ⟨κ, hκ⟩ := partial_frac m ((S : F) + 1) N hNd
  rw [hQQ] at hκ
  have hl : (aP2 K m (S : F) θ).eval (1 - y) = 0 := by
    unfold aP2
    simp only [eval_neg, eval_mul]
    have : (PPf ((S : F) - 1) m).eval (1 - y) = 0 := by
      unfold PPf; rw [eval_prod]
      refine Finset.prod_eq_zero (i := j) (by simp; omega) ?_
      rw [eval_lin, hy]; push_cast; ring
    rw [this]; ring
  have hr : (bP2 K m (S : F) θ).eval (-y - 1) = 0 := by
    unfold bP2
    simp only [eval_neg, eval_mul]
    by_cases hjm : j + 1 < m
    · have : (PPf ((S : F) - 1) m).eval (-y - 1) = 0 := by
        unfold PPf; rw [eval_prod]
        refine Finset.prod_eq_zero (i := j + 1) (by simp; omega) ?_
        rw [eval_lin, hy]; push_cast; ring
      rw [this]; ring
    · have hjm' : j + 1 = m := by omega
      have : (lin 1 ((S : F) + 2 * m + 1)).eval (-y - 1) = 0 := by
        rw [eval_lin, hy, ← hjm']; push_cast; ring
      rw [this]; ring
  refine ⟨(Dz K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (-y), κ, ?_⟩
  funext a
  have hrow := TtilT_row K m S θ y a
  have hGa : GenAt θ ((a : ℕ) : F) := genAt_nat hθ a
  have hGa1 : GenAt θ (((a : ℕ) : F) - 1) := genAt_nat_sub_one hθ a
  have hPz : Pe m S θ ((a : ℕ) : F) ≠ 0 := Pe_ne_zero m S hGa
  have hQz : (Qh2 m (S : F)).eval (θ + ((a : ℕ) : F)) ≠ 0 := by rw [eval_Qh2]; exact hPz
  have hA : (aP2 K m (S : F) θ).eval (θ + ((a : ℕ) : F)) =
      -sigma K m S θ (((a : ℕ) : F) - 1) * (Qh2 m (S : F)).eval (θ + ((a : ℕ) : F)) := by
    rw [eval_aP2, eval_Qh2]
    have key := sigma_pred_mul_Pe K m S θ ((a : ℕ) : F) hm (Qo_ne_zero m S hGa1)
    linear_combination key
  have hB : (bP2 K m (S : F) θ).eval (θ + ((a : ℕ) : F)) =
      -tau K m S θ ((a : ℕ) : F) * (Qh2 m (S : F)).eval (θ + ((a : ℕ) : F)) := by
    rw [eval_bP2, eval_Qh2]
    have key := tau_mul_Pe K m S θ ((a : ℕ) : F) hm hPz
    linear_combination key
  have hK : (K : F) - ((a : ℕ) : F) ≠ 0 := natsub_ne (by have := a.2; omega)
  have hDt : (Dt2 K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (θ + ((a : ℕ) : F)) =
      Dd K m S θ ((a : ℕ) : F) * (Qh2 m (S : F)).eval (θ + ((a : ℕ) : F)) := by
    unfold Dt2 Qh2
    rw [eval_mul, eval_Dz, ← Dd_eq K m S θ ((a : ℕ) : F) hm hGa1 hK]
  simp only [gg, cc0] at hDt
  have hE := congrArg (Polynomial.eval (θ + ((a : ℕ) : F))) heq
  rw [Hz2_eq] at hE
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_lin] at hE
  rw [hA, hB, hDt, hl, hr, zero_div] at hE
  have hSum := hκ (θ + ((a : ℕ) : F)) hQz
  have hSum' : ∑ i ∈ Finset.range m, κ i / (θ + ((a : ℕ) : F) + (S + 2 * (i : F) + 2)) =
      N.eval (θ + ((a : ℕ) : F)) / (Qh2 m (S : F)).eval (θ + ((a : ℕ) : F)) := by
    rw [hSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold vY; ring_nf
  have hum : θ + ((a : ℕ) : F) + y - 1 ≠ 0 := by
    have := hθ (((a : ℕ) : ℤ) + (S + 2 * j + 2 : ℕ) - 1); rw [hy]; push_cast at this ⊢
    intro h0; apply this; linear_combination h0
  have hu : θ + ((a : ℕ) : F) + y ≠ 0 := by
    have := hθ (((a : ℕ) : ℤ) + (S + 2 * j + 2 : ℕ)); rw [hy]; push_cast at this ⊢
    intro h0; apply this; linear_combination h0
  have hup : θ + ((a : ℕ) : F) + y + 1 ≠ 0 := by
    have := hθ (((a : ℕ) : ℤ) + (S + 2 * j + 2 : ℕ) + 1); rw [hy]; push_cast at this ⊢
    intro h0; apply this; linear_combination h0
  have key := cc_alg (θ + ((a : ℕ) : F) + y - 1) (θ + ((a : ℕ) : F) + y)
    (θ + ((a : ℕ) : F) + y + 1) ((Qh2 m (S : F)).eval (θ + ((a : ℕ) : F)))
    (N.eval (θ + ((a : ℕ) : F))) (sigma K m S θ (((a : ℕ) : F) - 1)) (Dd K m S θ ((a : ℕ) : F))
    (tau K m S θ ((a : ℕ) : F)) 0
    ((Dz K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (-y)) 0 hum hu hup hQz
    (by simp only [gg, cc0]; linear_combination hE)
  have hw : wcol K θ ((S + 2 * j + 2 : ℕ) : ℤ) =
      fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + y) := by
    funext b; simp [wcol, hy]
  rw [hw, hrow]
  simp only [wcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  rw [← hSum'] at key
  have hs : ∑ x ∈ Finset.range m, κ x / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 2)) =
      ∑ x ∈ Finset.range m, κ x * (1 / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 2))) := by
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  linear_combination key + hs

end CatalanCore.Star.Leonard
