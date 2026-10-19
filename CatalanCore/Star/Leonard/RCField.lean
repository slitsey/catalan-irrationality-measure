module

public import CatalanCore.Star.Leonard.RCPoly
public import CatalanCore.Star.Leonard.CCField

/-!
# (RC) at the nodes (package H2): the row chain `T~ᵀ c_y ≡ l(y+1) c_{y+1} + d(y) c_y + r(y-1) c_{y-1}`
modulo `span{c_x : x ∈ X}`, for symbolic `m`.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma eval_Qh2 (S : ℕ) (m : ℕ) (θ a : F) : (Qh2 m (S : F)).eval (θ + a) = Pe m S θ a := by
  unfold Qh2; exact eval_PPf S m θ a

lemma Qh2_eval_int_ne [CharZero F] (m S : ℕ) (c : ℤ) (h : ∀ j < m, 0 < c + S + 2 * ((j : ℤ) + 1)) :
    (Qh2 m (S : F)).eval (c : F) ≠ 0 := by
  unfold Qh2 PPf
  rw [eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hj' := h j (Finset.mem_range.1 hj)
  rw [eval_lin]
  have : (1 : F) * (c : F) + ((S : F) + 2 * ((j : F) + 1)) = ((c + S + 2 * ((j : ℤ) + 1) : ℤ) : F) := by
    push_cast; ring
  rw [this]
  exact_mod_cast hj'.ne'

lemma eval_aP2 (K m S : ℕ) (θ a : F) :
    (aP2 K m (S : F) θ).eval (θ + a) = -(pp K θ (a - 1) * (θ + S + 2 * m + a) * Qhat m S θ a) := by
  unfold aP2
  simp only [eval_neg, eval_mul, eval_lin, eval_pmz]
  have : (PPf ((S : F) - 1) m).eval (θ + a) = Qhat m S θ a := eval_Qh S m θ a
  rw [this]; ring

lemma eval_bP2 (K m S : ℕ) (θ a : F) :
    (bP2 K m (S : F) θ).eval (θ + a) = -(pp K θ a * (θ + S + 2 * m + 1 + a) * Qhat m S θ a) := by
  unfold bP2
  simp only [eval_neg, eval_mul, eval_lin, eval_pz]
  have : (PPf ((S : F) - 1) m).eval (θ + a) = Qhat m S θ a := eval_Qh S m θ a
  rw [this]; ring

lemma Pe_eq_Qo_pred (m S : ℕ) (θ a : F) (hm : 1 ≤ m) :
    Pe m S θ a = Qo m S θ (a - 1) * (θ + S + 2 * m + a) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold Pe Qo
  rw [Finset.prod_range_succ, Nat.add_sub_cancel]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by ring
  · push_cast; ring

lemma sigma_pred_mul_Pe (K m S : ℕ) (θ a : F) (hm : 1 ≤ m) (hQo : Qo m S θ (a - 1) ≠ 0) :
    sigma K m S θ (a - 1) * Pe m S θ a = pp K θ (a - 1) * (θ + S + 2 * m + a) * Qhat m S θ a := by
  rw [Pe_eq_Qo_pred m S θ a hm, ← Pe_pred_eq_Qhat]
  unfold sigma; field_simp

lemma tau_mul_Pe (K m S : ℕ) (θ a : F) (hm : 1 ≤ m) (hP : Pe m S θ a ≠ 0) :
    tau K m S θ a * Pe m S θ a = pp K θ a * (θ + S + 2 * m + 1 + a) * Qhat m S θ a := by
  rw [Qhat_eq m S θ a hm]
  unfold tau; rw [Qf_eq m S θ a hm]; field_simp


section Res2

variable [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (n : ℤ) (hn : n + 1 ≤ (S : ℤ))

include hm hn in
lemma res2_l : (aP2 K m (S : F) θ).eval (1 - (n : F)) / (Qh2 m (S : F)).eval (1 - (n : F)) =
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

include hm hn in
lemma res2_r : (bP2 K m (S : F) θ).eval (-(n : F) - 1) / (Qh2 m (S : F)).eval (-(n : F) - 1) =
    -tau K m S θ (-θ - n - 1) := by
  have hQ3 : (Qh2 m (S : F)).eval (((-n - 1 : ℤ)) : F) ≠ 0 :=
    Qh2_eval_int_ne m S (-n - 1) (fun j _ => by omega)
  push_cast at hQ3
  set a3 : F := -(n : F) - 1 - θ with ha3
  have e : -(n : F) - 1 = θ + a3 := by rw [ha3]; ring
  rw [e] at hQ3 ⊢
  rw [eval_Qh2] at hQ3
  have key := tau_mul_Pe K m S θ a3 hm hQ3
  have e2 : a3 = -θ - n - 1 := by rw [ha3]; ring
  rw [eval_bP2, eval_Qh2, div_eq_iff hQ3, ← e2]
  linear_combination key

include hm hn in
lemma res2_d (hθ : Gen θ) :
    (Dt2 K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (-(n : F)) /
      (Qh2 m (S : F)).eval (-(n : F)) = Dd K m S θ (-θ - n) := by
  have hQ2 : (Qh2 m (S : F)).eval (((-n : ℤ)) : F) ≠ 0 :=
    Qh2_eval_int_ne m S (-n) (fun j _ => by omega)
  push_cast at hQ2
  set a2 : F := -(n : F) - θ with ha2
  have e : -(n : F) = θ + a2 := by rw [ha2]; ring
  rw [e] at hQ2 ⊢
  have hQ2' := hQ2
  have hc : θ + (a2 - 1) = ((-n - 1 : ℤ) : F) := by rw [ha2]; push_cast; ring
  have hP : Pe m S θ (a2 - 1) ≠ 0 :=
    Pe_ne_zero_int m S θ _ (-n - 1) hc (fun i _ => by omega)
  have hQo : Qo m S θ (a2 - 1) ≠ 0 :=
    Qo_ne_zero_int m S θ _ (-n - 1) hc (fun i _ => by omega)
  have h1 : θ + (S : F) + 1 + (a2 - 1) ≠ 0 := by
    have : θ + (S : F) + 1 + (a2 - 1) = (((S : ℤ) - n : ℤ) : F) := by rw [ha2]; push_cast; ring
    rw [this]; exact cast_ne_zero_of_pos (by omega)
  have h2 : θ + (S : F) + 2 * m + 1 + (a2 - 1) ≠ 0 := by
    have : θ + (S : F) + 2 * m + 1 + (a2 - 1) = (((S : ℤ) + 2 * m - n : ℤ) : F) := by
      rw [ha2]; push_cast; ring
    rw [this]; exact cast_ne_zero_of_pos (by omega)
  have hK : (K : F) - a2 ≠ 0 := by
    have := hθ ((K : ℤ) + n)
    push_cast at this
    intro h0; apply this; rw [ha2] at h0; linear_combination h0
  have hD := Dd_eq' K m S θ a2 hm hP hQo h1 h2 hK
  unfold Dt2 Qh2
  rw [eval_mul, mul_div_assoc, div_self (by simpa [Qh2] using hQ2'), mul_one]
  have := eval_Dz K m S θ a2
  rw [this, ← hD, ha2]
  congr 1; ring

end Res2


/-- **(RC).**  Row chain identity at the nodes (the transpose of (CC), with the roles of `σ, τ`
and of `X, Y` exchanged): symbolic `m`. -/
theorem RC_field [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (n : ℤ)
    (hn : n + 1 ≤ (S : ℤ)) :
    ∃ κ : ℕ → F, ∀ i : ℕ, i < K →
      -sigma K m S θ ((i : F) - 1) / (θ + i - 1 + n) + Dd K m S θ i / (θ + i + n)
        + -tau K m S θ i / (θ + i + 1 + n) =
      -sigma K m S θ (-θ - n) / (θ + i + n - 1) + Dd K m S θ (-θ - n) / (θ + i + n)
        + -tau K m S θ (-θ - n - 1) / (θ + i + n + 1)
        + ∑ j ∈ Finset.range m, κ j / (θ + i + (S + 2 * (j : F) + 2)) := by
  have hQ1 : (Qh2 m (S : F)).eval (((1 - n : ℤ)) : F) ≠ 0 :=
    Qh2_eval_int_ne m S (1 - n) (fun j _ => by omega)
  have hQ2 : (Qh2 m (S : F)).eval (((-n : ℤ)) : F) ≠ 0 :=
    Qh2_eval_int_ne m S (-n) (fun j _ => by omega)
  have hQ3 : (Qh2 m (S : F)).eval (((-n - 1 : ℤ)) : F) ≠ 0 :=
    Qh2_eval_int_ne m S (-n - 1) (fun j _ => by omega)
  push_cast at hQ1 hQ2 hQ3
  obtain ⟨N, hNd, heq⟩ := RC_poly K m hm (S : F) θ (n : F) hQ1 hQ2 hQ3
  have hQQ : Qh m ((S : F) + 1) = Qh2 m (S : F) := by simp [Qh, Qh2]
  obtain ⟨κ, hκ⟩ := partial_frac m ((S : F) + 1) N hNd
  rw [hQQ] at hκ
  refine ⟨κ, fun i hi => ?_⟩
  have hl := res2_l K m S hm θ n hn
  have hr := res2_r K m S hm θ n hn
  have hd := res2_d K m S hm θ n hn hθ
  simp only [gg, cc0] at hd
  rw [Hz2_eq] at heq
  have hE := congrArg (Polynomial.eval (θ + (i : F))) heq
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_lin] at hE
  have hGa : GenAt θ (i : F) := genAt_nat hθ i
  have hGa1 : GenAt θ ((i : F) - 1) := genAt_nat_sub_one hθ i
  have hPz : Pe m S θ i ≠ 0 := Pe_ne_zero m S hGa
  have hQz : (Qh2 m (S : F)).eval (θ + (i : F)) ≠ 0 := by rw [eval_Qh2]; exact hPz
  have hA : (aP2 K m (S : F) θ).eval (θ + (i : F)) =
      -sigma K m S θ ((i : F) - 1) * (Qh2 m (S : F)).eval (θ + (i : F)) := by
    rw [eval_aP2, eval_Qh2]
    have key := sigma_pred_mul_Pe K m S θ (i : F) hm (Qo_ne_zero m S hGa1)
    linear_combination key
  have hB : (bP2 K m (S : F) θ).eval (θ + (i : F)) =
      -tau K m S θ i * (Qh2 m (S : F)).eval (θ + (i : F)) := by
    rw [eval_bP2, eval_Qh2]
    have key := tau_mul_Pe K m S θ (i : F) hm hPz
    linear_combination key
  have hK : (K : F) - i ≠ 0 := natsub_ne (by omega)
  have hDt : (Dt2 K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (θ + (i : F)) =
      Dd K m S θ i * (Qh2 m (S : F)).eval (θ + (i : F)) := by
    unfold Dt2 Qh2
    rw [eval_mul, eval_Dz, ← Dd_eq K m S θ i hm hGa1 hK]
  simp only [gg, cc0] at hDt
  have hSum := hκ (θ + (i : F)) hQz
  have hSum' : ∑ j ∈ Finset.range m, κ j / (θ + i + (S + 2 * (j : F) + 2)) =
      N.eval (θ + (i : F)) / (Qh2 m (S : F)).eval (θ + (i : F)) := by
    rw [hSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold vY; ring_nf
  rw [hA, hB, hDt, hl, hd, hr] at hE
  rw [hSum']
  have hum : θ + (i : F) + n - 1 ≠ 0 := by
    have := hθ ((i : ℤ) + n - 1); push_cast at this
    intro h0; apply this; linear_combination h0
  have hu : θ + (i : F) + n ≠ 0 := by
    have := hθ ((i : ℤ) + n); push_cast at this
    intro h0; apply this; linear_combination h0
  have hup : θ + (i : F) + n + 1 ≠ 0 := by
    have := hθ ((i : ℤ) + n + 1); push_cast at this
    intro h0; apply this; linear_combination h0
  have e1 : θ + (i : F) - 1 + n = θ + i + n - 1 := by ring
  have e2 : θ + (i : F) + 1 + n = θ + i + n + 1 := by ring
  rw [e1, e2]
  exact cc_alg _ _ _ _ _ _ _ _ _ _ _ hum hu hup hQz (by linear_combination hE)

end CatalanCore.Star.Leonard
