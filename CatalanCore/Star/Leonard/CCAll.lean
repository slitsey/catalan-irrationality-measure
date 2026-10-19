module

public import CatalanCore.Star.Leonard.RCY

/-!
# (CC) and (RC) for every `0 ≤ n ≤ S` with a uniform polynomial `d` (package H2/H4)

`Ttil_col_all`: `T~ c_n = l(n) c_{n-1} + d(n) c_n + r'(n) c_{n+1} + Σ κ_t c_t`, `n ≤ S`, with
`l(n) = -τ(-θ-n)`, `d(n) = D̃(-n)` (polynomial value, no division), `r'(n) = b(-n-1)/Q̂(-n-1)`
(which is `-σ(-θ-n-1)` for `n < S` and `0` at `n = S`, where `c_{S+1} ∈ range WY`).
`TtilT_col_all`: the row chain with the same `d(n)`.
-/

@[expose] public section

open Polynomial Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

section Res

variable [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (n : ℤ) (hn : n ≤ (S : ℤ))

include hm hn in
lemma res_l' : (aP K m (S : F) θ).eval (1 - (n : F)) / (Qh m (S : F)).eval (1 - (n : F)) =
    -tau K m S θ (-θ - n) := by
  have hQ1 : (Qh m (S : F)).eval (((1 - n : ℤ)) : F) ≠ 0 :=
    Qh_eval_int_ne m S (1 - n) (fun j _ => by omega)
  push_cast at hQ1
  set a1 : F := 1 - (n : F) - θ with ha1
  have e : (1 : F) - n = θ + a1 := by rw [ha1]; ring
  rw [e] at hQ1 ⊢
  rw [eval_Qh] at hQ1
  have hP : Pe m S θ (a1 - 1) ≠ 0 := by rw [Pe_pred_eq_Qhat]; exact hQ1
  have key := tau_pred_mul_Qhat K m S θ a1 hm hP
  have e2 : a1 - 1 = -θ - n := by rw [ha1]; ring
  rw [eval_aP, eval_Qh, div_eq_iff hQ1, ← e2]
  linear_combination key

include hm hn in
lemma res2_l' : (aP2 K m (S : F) θ).eval (1 - (n : F)) / (Qh2 m (S : F)).eval (1 - (n : F)) =
    -sigma K m S θ (-θ - n) := by
  have hQ1 : (Qh2 m (S : F)).eval (((1 - n : ℤ)) : F) ≠ 0 :=
    Qh2_eval_int_ne m S (1 - n) (fun j _ => by omega)
  push_cast at hQ1
  set a1 : F := 1 - (n : F) - θ with ha1
  have e : (1 : F) - n = θ + a1 := by rw [ha1]; ring
  rw [e] at hQ1 ⊢
  rw [eval_Qh2] at hQ1
  have hc : θ + (a1 - 1) = ((-n : ℤ) : F) := by rw [ha1]; push_cast; ring
  have hQo : Qo m S θ (a1 - 1) ≠ 0 := Qo_ne_zero_int m S θ _ (-n) hc (fun i _ => by omega)
  have key := sigma_pred_mul_Pe K m S θ a1 hm hQo
  have e2 : a1 - 1 = -θ - n := by rw [ha1]; ring
  rw [eval_aP2, eval_Qh2, div_eq_iff hQ1, ← e2]
  linear_combination key

end Res


/-- **(CC), all `n ≤ S`.** -/
theorem Ttil_col_all [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (n : ℕ)
    (hn : n ≤ S) :
    ∃ κ : ℕ → F, Ttil K m S θ *ᵥ wcol K θ (n : ℤ) =
      (-tau K m S θ (-θ - (n : ℤ))) • wcol K θ ((n : ℤ) - 1)
        + (Dz K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (-((n : ℤ) : F)) •
            wcol K θ (n : ℤ)
        + ((bP K m (S : F) θ).eval (-((n : ℤ) : F) - 1) /
            (Qh m (S : F)).eval (-((n : ℤ) : F) - 1)) • wcol K θ ((n : ℤ) + 1)
        + ∑ j ∈ Finset.range m, κ j • wcol K θ ((S + 2 * j + 1 : ℕ) : ℤ) := by
  set y : F := ((n : ℤ) : F) with hy
  have hQ1 : (Qh m (S : F)).eval (1 - y) ≠ 0 := by
    have := Qh_eval_int_ne (F := F) m S (1 - (n : ℤ)) (fun j _ => by omega)
    push_cast at this ⊢; rw [hy]; push_cast; exact this
  have hr3 : (bP K m (S : F) θ).eval (-y - 1) =
      (bP K m (S : F) θ).eval (-y - 1) / (Qh m (S : F)).eval (-y - 1) *
        (Qh m (S : F)).eval (-y - 1) := by
    rcases Nat.lt_or_ge n S with hlt | hge
    · have hQ3 : (Qh m (S : F)).eval (-y - 1) ≠ 0 := by
        have := Qh_eval_int_ne (F := F) m S (-(n : ℤ) - 1) (fun j _ => by omega)
        push_cast at this ⊢; rw [hy]; push_cast; exact this
      rw [div_mul_cancel₀ _ hQ3]
    · have hnS : n = S := le_antisymm hn hge
      have hb : (bP K m (S : F) θ).eval (-y - 1) = 0 := by
        unfold bP
        simp only [eval_neg, eval_mul, eval_lin]
        have : (1 : F) * (-y - 1) + ((S : F) + 1) = 0 := by rw [hy, hnS]; push_cast; ring
        rw [this]; ring
      rw [hb]; simp
  obtain ⟨N, hNd, heq⟩ := CC_polyY K m hm (S : F) θ y hQ1 hr3
  obtain ⟨κ, hκ⟩ := partial_frac m (S : F) N hNd
  have hl := res_l' K m S hm θ (n : ℤ) (by omega)
  refine ⟨κ, ?_⟩
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
  rw [hA, hB, hDt, hl] at hE
  have hSum := hκ (θ + ((a : ℕ) : F)) hQz
  have hSum' : ∑ i ∈ Finset.range m, κ i / (θ + ((a : ℕ) : F) + (S + 2 * (i : F) + 1)) =
      N.eval (θ + ((a : ℕ) : F)) / (Qh m (S : F)).eval (θ + ((a : ℕ) : F)) := by
    rw [hSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold vY; ring_nf
  have hum : θ + ((a : ℕ) : F) + y - 1 ≠ 0 := by
    have := hθ (((a : ℕ) : ℤ) + n - 1); rw [hy]; push_cast at this ⊢
    intro h0; apply this; linear_combination h0
  have hu : θ + ((a : ℕ) : F) + y ≠ 0 := by
    have := hθ (((a : ℕ) : ℤ) + n); rw [hy]; push_cast at this ⊢
    intro h0; apply this; linear_combination h0
  have hup : θ + ((a : ℕ) : F) + y + 1 ≠ 0 := by
    have := hθ (((a : ℕ) : ℤ) + n + 1); rw [hy]; push_cast at this ⊢
    intro h0; apply this; linear_combination h0
  have key := cc_alg (θ + ((a : ℕ) : F) + y - 1) (θ + ((a : ℕ) : F) + y)
    (θ + ((a : ℕ) : F) + y + 1) ((Qh m (S : F)).eval (θ + ((a : ℕ) : F)))
    (N.eval (θ + ((a : ℕ) : F))) (tau K m S θ (((a : ℕ) : F) - 1)) (Dd K m S θ ((a : ℕ) : F))
    (sigma K m S θ ((a : ℕ) : F)) (-tau K m S θ (-θ - (n : ℤ)))
    ((Dz K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (-y))
    ((bP K m (S : F) θ).eval (-y - 1) / (Qh m (S : F)).eval (-y - 1)) hum hu hup hQz
    (by simp only [gg, cc0]; linear_combination hE)
  have hw : wcol K θ (n : ℤ) = fun b : Fin K => 1 / (θ + ((b : ℕ) : F) + y) := by
    funext b; simp [wcol, hy]
  rw [hw, hrow]
  simp only [wcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  rw [← hSum'] at key
  have hs : ∑ x ∈ Finset.range m, κ x / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 1)) =
      ∑ x ∈ Finset.range m, κ x * (1 / (θ + ((a : ℕ) : F) + ((S : F) + 2 * (x : F) + 1))) := by
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  rw [hy] at key ⊢
  push_cast at key ⊢
  linear_combination key + hs

end CatalanCore.Star.Leonard
