module

public import CatalanCore.Star.Leonard.Ttil

/-!
# (CC) at the border points `y ∈ Y`: `T~` preserves `span WY` (package H2, (T2))

For `y = t = S + 2j + 1` the residues `l(t), r(t)` vanish and the pole at `z = -t` of `D̃/u` is
cancelled by `Q̂(-t) = 0`.  The same polynomial argument as `CC_poly`, with `d := D̃(-y)` taken as a
polynomial value (no division by `Q̂(-y)`), gives `T~ c_t = d c_t + Σ κ c_{t'}`.
-/

@[expose] public section

open Polynomial Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma Qh_eval_int_ne' [CharZero F] (m S : ℕ) (c : ℤ) (h : ∀ j < m, c + S + 2 * (j : ℤ) + 1 ≠ 0) :
    (Qh m (S : F)).eval (c : F) ≠ 0 := by
  unfold Qh PPf
  rw [eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hj' := h j (Finset.mem_range.1 hj)
  rw [eval_lin]
  have : (1 : F) * (c : F) + ((S : F) - 1 + 2 * ((j : F) + 1)) = ((c + S + 2 * (j : ℤ) + 1 : ℤ) : F) := by
    push_cast; ring
  rw [this]
  exact_mod_cast hj'

/-- **(CC) polynomial form, border case.** -/
theorem CC_polyY [CharZero F] (K m : ℕ) (hm : 1 ≤ m) (S θ y : F)
    (hQ1 : (Qh m S).eval (1 - y) ≠ 0)
    (hr3 : (bP K m S θ).eval (-y - 1) =
      (bP K m S θ).eval (-y - 1) / (Qh m S).eval (-y - 1) * (Qh m S).eval (-y - 1)) :
    ∃ N : F[X], N.natDegree < m ∧
      Hz K m S θ y (S - K + m + 1)
        (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)
        - Qh m S * (C ((aP K m S θ).eval (1 - y) / (Qh m S).eval (1 - y)) * (lin 1 y * lin 1 (y + 1))
            + C ((Dz K m S θ (S - K + m + 1)
                (-2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2)).eval (-y))
              * (lin 1 (y - 1) * lin 1 (y + 1))
            + C ((bP K m S θ).eval (-y - 1) / (Qh m S).eval (-y - 1))
              * (lin 1 (y - 1) * lin 1 y))
      = (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N := by
  set g : F := S - K + m + 1 with hg
  set c0 : F := -2 * ((K : F) - 1) * (θ + (S - K + m + 1)) - 2 * K ^ 2 + 2 * K - m ^ 2 with hc0
  set ℓ := (aP K m S θ).eval (1 - y) / (Qh m S).eval (1 - y) with hℓ
  set d := (Dz K m S θ g c0).eval (-y) with hd
  set r := (bP K m S θ).eval (-y - 1) / (Qh m S).eval (-y - 1) with hr
  have e1 : lin 1 (y - 1) = X - C (1 - y) := by rw [lin_one]; congr 2; ring
  have e2 : lin 1 y = X - C (-y) := lin_one y
  have e3 : lin 1 (y + 1) = X - C (-y - 1) := by rw [lin_one]; congr 2; ring
  obtain ⟨N, hN⟩ := three_div (aP K m S θ - C ℓ * Qh m S) (Dt K m S θ g c0 - C d * Qh m S)
    (bP K m S θ - C r * Qh m S) (1 - y) (-y) (-y - 1)
    (by rw [eval_sub, eval_mul, eval_C, hℓ, div_mul_cancel₀ _ hQ1, sub_self])
    (by
      unfold Dt
      rw [eval_sub, eval_mul, eval_mul, eval_C]
      unfold Qh
      rw [hd]; ring)
    (by rw [eval_sub, eval_mul, eval_C, hr]; exact sub_eq_zero.2 hr3)
  have heq : Hz K m S θ y g c0 - Qh m S * (C ℓ * (lin 1 y * lin 1 (y + 1))
      + C d * (lin 1 (y - 1) * lin 1 (y + 1)) + C r * (lin 1 (y - 1) * lin 1 y))
      = (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N := by
    rw [e1, e2, e3, ← hN, Hz_eq, e1, e2, e3]; ring
  refine ⟨N, ?_, heq⟩
  have hdeg : ((lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) * N).natDegree ≤ m + 2 := by
    rw [← heq]
    refine (natDegree_sub_le _ _).trans (max_le (Hz_natDegree_le K m S θ y) ?_)
    refine (natDegree_mul_le).trans ?_
    have h1 : (C ℓ * (lin 1 y * lin 1 (y + 1))).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h2 : (C d * (lin 1 (y - 1) * lin 1 (y + 1))).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h3 : (C r * (lin 1 (y - 1) * lin 1 y)).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (natDegree_lin_mul_lin_le _ _ _ _)
    have h12 := (natDegree_add_le _ _).trans (max_le h1 h2)
    have h123 := (natDegree_add_le _ _).trans (max_le h12 h3)
    have hQ : (Qh m S).natDegree ≤ m := natDegree_PPf_le _ _
    omega
  by_cases hN0 : N = 0
  · subst hN0; simp; omega
  · have hU : (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)).natDegree = 3 := by
      rw [e1, e2, e3]; exact natDegree_three _ _ _
    have hUne : (lin 1 (y - 1) * lin 1 y * lin 1 (y + 1)) ≠ 0 := by
      intro h0; rw [h0] at hU; simp at hU
    rw [natDegree_mul hUne hN0, hU] at hdeg
    omega


/-- **(T2) for one border column.**  For `t = S + 2j + 1 ∈ Y`: `T~ c_t = d c_t + Σ_{t'∈Y} κ_{t'} c_{t'}`
(the neighbours `c_{t±1}` do not occur: `l(t) = r(t) = 0`). Symbolic `m`. -/
theorem Ttil_colY [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (j : ℕ)
    (hj : j < m) :
    ∃ (d : F) (κ : ℕ → F), Ttil K m S θ *ᵥ wcol K θ ((S + 2 * j + 1 : ℕ) : ℤ) =
      d • wcol K θ ((S + 2 * j + 1 : ℕ) : ℤ)
        + ∑ i ∈ Finset.range m, κ i • wcol K θ ((S + 2 * i + 1 : ℕ) : ℤ) := by
  set y : F := ((S + 2 * j + 1 : ℕ) : F) with hy
  have hQ1 : (Qh m (S : F)).eval (1 - y) ≠ 0 := by
    have := Qh_eval_int_ne' (F := F) m S (1 - ((S + 2 * j + 1 : ℕ) : ℤ))
      (fun i _ => by push_cast; omega)
    push_cast at this; rw [hy]; push_cast; exact this
  have hQ3 : (Qh m (S : F)).eval (-y - 1) ≠ 0 := by
    have := Qh_eval_int_ne' (F := F) m S (-((S + 2 * j + 1 : ℕ) : ℤ) - 1)
      (fun i _ => by push_cast; omega)
    push_cast at this; rw [hy]; push_cast; exact this
  obtain ⟨N, hNd, heq⟩ := CC_polyY K m hm (S : F) θ y hQ1 (div_mul_cancel₀ _ hQ3).symm
  obtain ⟨κ, hκ⟩ := partial_frac m (S : F) N hNd
  have hl : (aP K m (S : F) θ).eval (1 - y) = 0 := by
    unfold aP
    simp only [eval_neg, eval_mul, eval_lin]
    have : (1 * (1 - y) + (S : F)) * (PPf (S : F) m).eval (1 - y) = 0 := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        have : (1 * (1 - y) + (S : F)) = 0 := by rw [hy]; push_cast; ring
        rw [this, zero_mul]
      · have : (PPf (S : F) m).eval (1 - y) = 0 := by
          unfold PPf; rw [eval_prod]
          refine Finset.prod_eq_zero (i := j - 1) (by simp; omega) ?_
          rw [eval_lin, hy]; push_cast
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this, mul_zero]
    linear_combination (-(pmz K θ).eval (1 - y)) * this
  have hr : (bP K m (S : F) θ).eval (-y - 1) = 0 := by
    unfold bP
    simp only [eval_neg, eval_mul, eval_lin]
    have : (PPf (S : F) m).eval (-y - 1) = 0 := by
      unfold PPf; rw [eval_prod]
      refine Finset.prod_eq_zero (i := j) (by simp; omega) ?_
      rw [eval_lin, hy]; push_cast; ring
    rw [this]; ring
  refine ⟨(Dz K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (-y), κ, ?_⟩
  funext a
  have hrow := Ttil_row K m S θ y a
  have hGa : GenAt θ ((a : ℕ) : F) := genAt_nat hθ a
  have hGa1 : GenAt θ (((a : ℕ) : F) - 1) := genAt_nat_sub_one hθ a
  have hQhat : Qhat m S θ ((a : ℕ) : F) ≠ 0 := by
    rw [Qhat_eq m S θ _ hm]
    refine mul_ne_zero ?_ (Qo_ne_zero m S hGa)
    have := hGa (S + 1); push_cast at this; intro h0; apply this; linear_combination h0
  have hQz : (Qh m (S : F)).eval (θ + ((a : ℕ) : F)) ≠ 0 := by rw [eval_Qh]; exact hQhat
  have hA : (aP K m (S : F) θ).eval (θ + ((a : ℕ) : F)) =
      -tau K m S θ (((a : ℕ) : F) - 1) * (Qh m (S : F)).eval (θ + ((a : ℕ) : F)) := by
    rw [eval_aP, eval_Qh]
    have key := tau_pred_mul_Qhat K m S θ ((a : ℕ) : F) hm (Pe_ne_zero m S hGa1)
    linear_combination key
  have hB : (bP K m (S : F) θ).eval (θ + ((a : ℕ) : F)) =
      -sigma K m S θ ((a : ℕ) : F) * (Qh m (S : F)).eval (θ + ((a : ℕ) : F)) := by
    rw [eval_bP, eval_Qh]
    have key := sigma_mul_Qhat K m S θ ((a : ℕ) : F) hm (Qo_ne_zero m S hGa)
    linear_combination key
  have hK : (K : F) - ((a : ℕ) : F) ≠ 0 := natsub_ne (by have := a.2; omega)
  have hDt : (Dt K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (θ + ((a : ℕ) : F)) =
      Dd K m S θ ((a : ℕ) : F) * (Qh m (S : F)).eval (θ + ((a : ℕ) : F)) := by
    unfold Dt
    rw [eval_mul, eval_Dz, ← Dd_eq K m S θ ((a : ℕ) : F) hm hGa1 hK]
    rfl
  simp only [gg, cc0] at hDt
  have hE := congrArg (Polynomial.eval (θ + ((a : ℕ) : F))) heq
  rw [Hz_eq] at hE
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_lin] at hE
  rw [hA, hB, hDt, hl, hr, zero_div] at hE
  have hSum := hκ (θ + ((a : ℕ) : F)) hQz
  have hSum' : ∑ i ∈ Finset.range m, κ i / (θ + ((a : ℕ) : F) + (S + 2 * (i : F) + 1)) =
      N.eval (θ + ((a : ℕ) : F)) / (Qh m (S : F)).eval (θ + ((a : ℕ) : F)) := by
    rw [hSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold vY; ring_nf
  have hum : θ + ((a : ℕ) : F) + y - 1 ≠ 0 := by
    have := hθ (((a : ℕ) : ℤ) + (S + 2 * j + 1 : ℕ) - 1); rw [hy]; push_cast at this ⊢
    intro h0; apply this; linear_combination h0
  have hu : θ + ((a : ℕ) : F) + y ≠ 0 := by
    have := hθ (((a : ℕ) : ℤ) + (S + 2 * j + 1 : ℕ)); rw [hy]; push_cast at this ⊢
    intro h0; apply this; linear_combination h0
  have hup : θ + ((a : ℕ) : F) + y + 1 ≠ 0 := by
    have := hθ (((a : ℕ) : ℤ) + (S + 2 * j + 1 : ℕ) + 1); rw [hy]; push_cast at this ⊢
    intro h0; apply this; linear_combination h0
  have key := cc_alg (θ + ((a : ℕ) : F) + y - 1) (θ + ((a : ℕ) : F) + y)
    (θ + ((a : ℕ) : F) + y + 1) ((Qh m (S : F)).eval (θ + ((a : ℕ) : F)))
    (N.eval (θ + ((a : ℕ) : F))) (tau K m S θ (((a : ℕ) : F) - 1)) (Dd K m S θ ((a : ℕ) : F))
    (sigma K m S θ ((a : ℕ) : F)) 0
    ((Dz K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (-y)) 0 hum hu hup hQz
    (by simp only [gg, cc0]; linear_combination hE)
  have hw : wcol K θ ((S + 2 * j + 1 : ℕ) : ℤ) =
      fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + y) := by
    funext b; simp [wcol, hy]
  rw [hw, hrow]
  simp only [wcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  have e1 : θ + ((a : ℕ) : F) - 1 + y = θ + ((a : ℕ) : F) + y - 1 := by ring
  have e2 : θ + ((a : ℕ) : F) + 1 + y = θ + ((a : ℕ) : F) + y + 1 := by ring
  rw [← hSum'] at key
  have hs : ∑ x ∈ Finset.range m, κ x / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 1)) =
      ∑ x ∈ Finset.range m, κ x * (1 / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 1))) := by
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  linear_combination key + hs

end CatalanCore.Star.Leonard
