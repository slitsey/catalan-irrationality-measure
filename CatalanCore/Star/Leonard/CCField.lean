module

public import CatalanCore.Star.Leonard.PartialFrac
public import CatalanCore.Star.Leonard.Defs

/-!
# (CC) at the nodes (package H2)

Evaluation of the polynomial data at `z = θ + a` in terms of `Pe, Qhat, pp, Dd`, and the column
chain identity for the tridiagonal `T~`.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma eval_PPf (S : ℕ) (m : ℕ) (θ a : F) : (PPf (S : F) m).eval (θ + a) = Pe m S θ a := by
  unfold PPf Pe
  rw [eval_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [eval_lin]; ring

lemma eval_Qh (S : ℕ) (m : ℕ) (θ a : F) : (Qh m (S : F)).eval (θ + a) = Qhat m S θ a := by
  unfold Qh PPf Qhat
  rw [eval_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [eval_lin]; ring

lemma eval_pz (K : ℕ) (θ a : F) : (pz K θ).eval (θ + a) = pp K θ a := by
  unfold pz pp; simp only [eval_mul, eval_lin]; ring

lemma eval_pmz (K : ℕ) (θ a : F) : (pmz K θ).eval (θ + a) = pp K θ (a - 1) := by
  unfold pmz pp; simp only [eval_mul, eval_lin]; ring

lemma eval_aP (K m S : ℕ) (θ a : F) :
    (aP K m (S : F) θ).eval (θ + a) = -(pp K θ (a - 1) * (θ + S + a) * Pe m S θ a) := by
  unfold aP; simp only [eval_neg, eval_mul, eval_lin, eval_pmz, eval_PPf]; ring

lemma eval_bP (K m S : ℕ) (θ a : F) :
    (bP K m (S : F) θ).eval (θ + a) = -(pp K θ a * (θ + S + 1 + a) * Pe m S θ a) := by
  unfold bP; simp only [eval_neg, eval_mul, eval_lin, eval_pz, eval_PPf]; ring

lemma eval_Dz (K m S : ℕ) (θ a : F) :
    (Dz K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (θ + a) =
      mu K m S θ a - (a * (a + θ)) ^ 2 + gg K m S * (gg K m S + 1) * a ^ 2
        + gg K m S * cc0 K m θ (gg K m S) * a := by
  unfold Dz mu; simp only [eval_add, eval_sub, eval_neg, eval_mul, eval_lin]; ring


lemma Qh_eval_int_ne [CharZero F] (m S : ℕ) (c : ℤ) (h : ∀ j < m, 0 < c + S + 2 * (j : ℤ) + 1) :
    (Qh m (S : F)).eval (c : F) ≠ 0 := by
  unfold Qh PPf
  rw [eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hj' := h j (Finset.mem_range.1 hj)
  rw [eval_lin]
  have : (1 : F) * (c : F) + ((S : F) - 1 + 2 * ((j : F) + 1)) = ((c + S + 2 * (j : ℤ) + 1 : ℤ) : F) := by
    push_cast; ring
  rw [this]
  exact_mod_cast hj'.ne'


/-! ### Nonvanishing at integer points -/

lemma Pe_ne_zero_int [CharZero F] (m S : ℕ) (θ a : F) (c : ℤ) (hc : θ + a = c)
    (h : ∀ i < m, 0 < c + S + 2 * ((i : ℤ) + 1)) : Pe m S θ a ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have hi' := h i (Finset.mem_range.1 hi)
  have : θ + (S : F) + 2 * ((i : F) + 1) + a = ((c + S + 2 * ((i : ℤ) + 1) : ℤ) : F) := by
    push_cast; rw [← hc]; ring
  rw [this]; exact_mod_cast hi'.ne'

lemma Qo_ne_zero_int [CharZero F] (m S : ℕ) (θ a : F) (c : ℤ) (hc : θ + a = c)
    (h : ∀ i < m - 1, 0 < c + S + 2 * ((i : ℤ) + 1) + 1) : Qo m S θ a ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have hi' := h i (Finset.mem_range.1 hi)
  have : θ + (S : F) + 2 * ((i : F) + 1) + 1 + a = ((c + S + 2 * ((i : ℤ) + 1) + 1 : ℤ) : F) := by
    push_cast; rw [← hc]; ring
  rw [this]; exact_mod_cast hi'.ne'

lemma cast_ne_zero_of_pos [CharZero F] {c : ℤ} (h : 0 < c) : ((c : ℤ) : F) ≠ 0 := by
  exact_mod_cast h.ne'


/-! ### Residues at the three poles -/

section Res

variable [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (n : ℤ) (hn : n + 1 ≤ (S : ℤ))

include hm hn in
lemma res_l : (aP K m (S : F) θ).eval (1 - (n : F)) / (Qh m (S : F)).eval (1 - (n : F)) =
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
lemma res_r : (bP K m (S : F) θ).eval (-(n : F) - 1) / (Qh m (S : F)).eval (-(n : F) - 1) =
    -sigma K m S θ (-θ - n - 1) := by
  have hQ3 : (Qh m (S : F)).eval (((-n - 1 : ℤ)) : F) ≠ 0 :=
    Qh_eval_int_ne m S (-n - 1) (fun j _ => by omega)
  push_cast at hQ3
  set a3 : F := -(n : F) - 1 - θ with ha3
  have e : -(n : F) - 1 = θ + a3 := by rw [ha3]; ring
  rw [e] at hQ3 ⊢
  rw [eval_Qh] at hQ3
  have hQo : Qo m S θ a3 ≠ 0 := by
    rw [Qhat_eq m S θ a3 hm] at hQ3; exact right_ne_zero_of_mul hQ3
  have key := sigma_mul_Qhat K m S θ a3 hm hQo
  have e2 : a3 = -θ - n - 1 := by rw [ha3]; ring
  rw [eval_bP, eval_Qh, div_eq_iff hQ3, ← e2]
  linear_combination key


include hm hn in
lemma res_d (hθ : Gen θ) :
    (Dt K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (-(n : F)) /
      (Qh m (S : F)).eval (-(n : F)) = Dd K m S θ (-θ - n) := by
  have hQ2 : (Qh m (S : F)).eval (((-n : ℤ)) : F) ≠ 0 :=
    Qh_eval_int_ne m S (-n) (fun j _ => by omega)
  push_cast at hQ2
  set a2 : F := -(n : F) - θ with ha2
  have e : -(n : F) = θ + a2 := by rw [ha2]; ring
  rw [e] at hQ2 ⊢
  have hQ2' := hQ2
  rw [eval_Qh] at hQ2
  have hP : Pe m S θ (a2 - 1) ≠ 0 := by rw [Pe_pred_eq_Qhat]; exact hQ2
  have hc : θ + (a2 - 1) = ((-n - 1 : ℤ) : F) := by rw [ha2]; push_cast; ring
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
  unfold Dt Qh
  rw [eval_mul, mul_div_assoc, div_self (by simpa [Qh] using hQ2'), mul_one]
  have := eval_Dz K m S θ a2
  rw [this, ← hD, ha2]
  congr 1; ring

end Res


/-- The final clearing of denominators, with abstract atoms. -/
lemma cc_alg (um u up Q Nv τa Da σa Lv dv Rv : F) (hum : um ≠ 0) (hu : u ≠ 0) (hup : up ≠ 0)
    (hQ : Q ≠ 0)
    (hE : (-τa * Q) * (u * up) + (-σa * Q) * (um * u) + (Da * Q) * (um * up)
      - Q * (Lv * (u * up) + dv * (um * up) + Rv * (um * u)) = um * u * up * Nv) :
    -τa / um + Da / u + -σa / up = Lv / um + dv / u + Rv / up + Nv / Q := by
  field_simp
  linear_combination hE

/-! ### The column chain identity (CC) at the nodes -/

/-- **(CC).**  For `y = n ≤ S - 1` and every node `a = i < K`:
`-τ(a-1)/(θ+a-1+y) + D(a)/(θ+a+y) - σ(a)/(θ+a+1+y) = l(y)/(θ+a+y-1) + d(y)/(θ+a+y) +
r(y)/(θ+a+y+1) + Σ_{j<m} κ_j/(θ+a+t_j)`, with `l(y) = -τ(-θ-y)`, `d(y) = D(-θ-y)`,
`r(y) = -σ(-θ-y-1)` and `t_j = S + 2j + 1`.  Symbolic `m`. -/
theorem CC_field [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (n : ℤ)
    (hn : n + 1 ≤ (S : ℤ)) :
    ∃ κ : ℕ → F, ∀ i : ℕ, i < K →
      -tau K m S θ ((i : F) - 1) / (θ + i - 1 + n) + Dd K m S θ i / (θ + i + n)
        + -sigma K m S θ i / (θ + i + 1 + n) =
      -tau K m S θ (-θ - n) / (θ + i + n - 1) + Dd K m S θ (-θ - n) / (θ + i + n)
        + -sigma K m S θ (-θ - n - 1) / (θ + i + n + 1)
        + ∑ j ∈ Finset.range m, κ j / (θ + i + (S + 2 * (j : F) + 1)) := by
  have hQ1 : (Qh m (S : F)).eval (((1 - n : ℤ)) : F) ≠ 0 :=
    Qh_eval_int_ne m S (1 - n) (fun j _ => by omega)
  have hQ2 : (Qh m (S : F)).eval (((-n : ℤ)) : F) ≠ 0 :=
    Qh_eval_int_ne m S (-n) (fun j _ => by omega)
  have hQ3 : (Qh m (S : F)).eval (((-n - 1 : ℤ)) : F) ≠ 0 :=
    Qh_eval_int_ne m S (-n - 1) (fun j _ => by omega)
  push_cast at hQ1 hQ2 hQ3
  obtain ⟨N, hNd, heq⟩ := CC_poly K m hm (S : F) θ (n : F) hQ1 hQ2 hQ3
  obtain ⟨κ, hκ⟩ := partial_frac m (S : F) N hNd
  refine ⟨κ, fun i hi => ?_⟩
  have hl := res_l K m S hm θ n hn
  have hr := res_r K m S hm θ n hn
  have hd := res_d K m S hm θ n hn hθ
  simp only [gg, cc0] at hd
  rw [Hz_eq] at heq
  have hE := congrArg (Polynomial.eval (θ + (i : F))) heq
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_lin] at hE
  have hGa : GenAt θ (i : F) := genAt_nat hθ i
  have hGa1 : GenAt θ ((i : F) - 1) := genAt_nat_sub_one hθ i
  have hQhat : Qhat m S θ i ≠ 0 := by
    rw [Qhat_eq m S θ i hm]
    refine mul_ne_zero ?_ (Qo_ne_zero m S hGa)
    have := hGa (S + 1); push_cast at this; intro h0; apply this; linear_combination h0
  have hQz : (Qh m (S : F)).eval (θ + (i : F)) ≠ 0 := by rw [eval_Qh]; exact hQhat
  have hA : (aP K m (S : F) θ).eval (θ + (i : F)) =
      -tau K m S θ ((i : F) - 1) * (Qh m (S : F)).eval (θ + (i : F)) := by
    rw [eval_aP, eval_Qh]
    have key := tau_pred_mul_Qhat K m S θ (i : F) hm (Pe_ne_zero m S hGa1)
    linear_combination key
  have hB : (bP K m (S : F) θ).eval (θ + (i : F)) =
      -sigma K m S θ i * (Qh m (S : F)).eval (θ + (i : F)) := by
    rw [eval_bP, eval_Qh]
    have key := sigma_mul_Qhat K m S θ (i : F) hm (Qo_ne_zero m S hGa)
    linear_combination key
  have hK : (K : F) - i ≠ 0 := natsub_ne (by omega)
  have hDt : (Dt K m (S : F) θ (gg K m S) (cc0 K m θ (gg K m S))).eval (θ + (i : F)) =
      Dd K m S θ i * (Qh m (S : F)).eval (θ + (i : F)) := by
    unfold Dt
    rw [eval_mul, eval_Dz, ← Dd_eq K m S θ i hm hGa1 hK]
    rfl
  simp only [gg, cc0] at hDt
  have hSum := hκ (θ + (i : F)) hQz
  have hSum' : ∑ j ∈ Finset.range m, κ j / (θ + i + (S + 2 * (j : F) + 1)) =
      N.eval (θ + (i : F)) / (Qh m (S : F)).eval (θ + (i : F)) := by
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
