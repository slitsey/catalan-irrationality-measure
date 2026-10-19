module

public import CatalanCore.Star.Leonard.KStepPoly
public import CatalanCore.Star.Leonard.RCField

/-!
# K-step relations (K4a/K4b) at the nodes (package H5)

For the Darboux map `X = diag(D)·U` of the `g = 0` instance `(K, m, S)` (`K = S+m+1`):
* `K4a_field`: `(X c_y)_i = D_i μ_i c_y(i) - D_i σ_i c_y(i+1) = 𝒜(y) c'_y(i) + ℬ(y) c'_{y+1}(i)
  + Σ_{x∈X} ℰ_x(y) c'_x(i)`;
* `K4b_field`: `(Xᵀ c'_y)_j = D_j μ_j c_y(j) - D_{j-1}σ_{j-1} c_y(j-1) = 𝒜(y) c_y(j) + ℬ'(y) c_{y-1}(j)
  + Σ_{x∈X} ℱ_x(y) c_x(j)`.
Symbolic `m`.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- The constant `c₀ = (K-1) P(0)/Q_o(0)` of the Darboux normalisation. -/
noncomputable def cK (K m S : ℕ) (θ : F) : F := ((K : F) - 1) * Pe m S θ 0 / Qo m S θ 0

lemma Dfac_sigma (K m S : ℕ) (θ a : F) (hP : Pe m S θ a ≠ 0) (hQ : Qo m S θ a ≠ 0)
    (hQ0 : Qo m S θ 0 ≠ 0) (hK : (K : F) - 1 - a ≠ 0) :
    Dfac K m S θ a * sigma K m S θ a = cK K m S θ * ((a + 1) * (a + 1 + θ)) := by
  unfold Dfac sigma pp cK
  field_simp

lemma Dfac_mu_Pe (K m S : ℕ) (θ a : F) (hm : 1 ≤ m) (hP : Pe m S θ a ≠ 0)
    (hQ0 : Qo m S θ 0 ≠ 0) (hQ : Qo m S θ a ≠ 0) :
    Dfac K m S θ a * mu K m S θ a * Pe m S θ a =
      -(cK K m S θ * (((K : F) - 1 - a) * (θ + S + 2 * m + 1 + a) * Qhat m S θ a)) := by
  by_cases hK : (K : F) - 1 - a = 0
  · unfold Dfac mu; rw [hK]; simp
  · by_cases h1 : θ + S + 1 + a = 0
    · rw [Qhat_eq m S θ a hm, h1]
      unfold Dfac mu; rw [h1]; simp
    · rw [Qhat_eq m S θ a hm]
      unfold Dfac mu cK
      field_simp

/-- Abstract clearing of denominators for the `K`-step relations. -/
lemma kstep_alg (u up P Nv Fa Fb Aa Bb : F) (hu : u ≠ 0) (hup : up ≠ 0) (hP : P ≠ 0)
    (hE : Fa * P * up - Fb * P * u - P * (Aa * up + Bb * u) = u * up * Nv) :
    Fa / u - Fb / up = Aa / u + Bb / up + Nv / P := by
  field_simp
  linear_combination hE


lemma eval_pK1 (K m S : ℕ) (θ a : F) :
    (pK1 K m (S : F) θ).eval (θ + a) = ((K : F) - 1 - a) * (θ + S + 2 * m + 1 + a) := by
  unfold pK1; simp only [eval_mul, eval_lin]; ring

lemma eval_p2 (θ a : F) : (lin 1 (1 - θ) * lin 1 1).eval (θ + a) = (a + 1) * (a + 1 + θ) := by
  simp only [eval_mul, eval_lin]; ring

lemma eval_p2' (θ a : F) : (lin 1 (-θ) * lin 1 0).eval (θ + a) = a * (a + θ) := by
  simp only [eval_mul, eval_lin]; ring

lemma eval_PPf_S (K m S : ℕ) (θ a : F) : (PPf (S : F) m).eval (θ + a) = Pe m S θ a := eval_PPf S m θ a

lemma eval_PPf_pred (m S : ℕ) (θ a : F) : (PPf ((S : F) - 1) m).eval (θ + a) = Qhat m S θ a :=
  eval_Qh S m θ a

lemma Qh2_eval_ne_of_ne [CharZero F] (m S : ℕ) (c : ℤ)
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

section K4field

variable [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
  (n : ℤ) (hn : n ≤ (S : ℤ) + 1)

include hm hθ hKS hn in
/-- Identification of the `A` coefficient with `(Dμ)(-θ-n)`. -/
lemma coefA_eq : coefA K m (S : F) θ (n : F) (cK K m S θ) =
    Dfac K m S θ (-θ - n) * mu K m S θ (-θ - n) := by
  set a2 : F := -θ - n with ha2
  have hc : θ + a2 = ((-n : ℤ) : F) := by rw [ha2]; push_cast; ring
  have hPe : Pe m S θ a2 ≠ 0 := Pe_ne_zero_int m S θ _ (-n) hc (fun i _ => by omega)
  have hQo : Qo m S θ a2 ≠ 0 := Qo_ne_zero_int m S θ _ (-n) hc (fun i _ => by omega)
  have hQ0 : Qo m S θ 0 ≠ 0 := by simpa using Qo_ne_zero m S (genAt_nat hθ 0)
  have key := Dfac_mu_Pe K m S θ a2 hm hPe hQ0 hQo
  have e : (-(n : F)) = θ + a2 := by rw [ha2]; ring
  unfold coefA
  rw [e, eval_PPf_S K m S θ a2, eval_PPf_pred, eval_pK1]
  rw [div_eq_iff hPe]
  linear_combination (-1 : F) * key

include hm hθ hKS hn in
lemma coefB_eq (hn' : n ≤ (S : ℤ)) : coefB θ (n : F) (cK K m S θ) =
    -(Dfac K m S θ (-θ - n - 1) * sigma K m S θ (-θ - n - 1)) := by
  set a3 : F := -θ - n - 1 with ha3
  have hc : θ + a3 = ((-n - 1 : ℤ) : F) := by rw [ha3]; push_cast; ring
  have hPe : Pe m S θ a3 ≠ 0 := Pe_ne_zero_int m S θ _ (-n - 1) hc (fun i _ => by omega)
  have hQo : Qo m S θ a3 ≠ 0 := Qo_ne_zero_int m S θ _ (-n - 1) hc (fun i _ => by omega)
  have hQ0 : Qo m S θ 0 ≠ 0 := by simpa using Qo_ne_zero m S (genAt_nat hθ 0)
  have hK : (K : F) - 1 - a3 ≠ 0 := by
    have := hθ ((K : ℤ) + n)
    push_cast at this
    intro h0; apply this; rw [ha3] at h0; linear_combination h0
  have key := Dfac_sigma K m S θ a3 hPe hQo hQ0 hK
  have e : (-(n : F) - 1) = θ + a3 := by rw [ha3]; ring
  unfold coefB
  rw [e, eval_p2, key]; ring

include hm hθ hKS hn in
lemma coefB'_eq : coefB' θ (n : F) (cK K m S θ) =
    -(Dfac K m S θ (-θ - n) * sigma K m S θ (-θ - n)) := by
  set a2 : F := -θ - n with ha2
  have hc : θ + a2 = ((-n : ℤ) : F) := by rw [ha2]; push_cast; ring
  have hPe : Pe m S θ a2 ≠ 0 := Pe_ne_zero_int m S θ _ (-n) hc (fun i _ => by omega)
  have hQo : Qo m S θ a2 ≠ 0 := Qo_ne_zero_int m S θ _ (-n) hc (fun i _ => by omega)
  have hQ0 : Qo m S θ 0 ≠ 0 := by simpa using Qo_ne_zero m S (genAt_nat hθ 0)
  have hK : (K : F) - 1 - a2 ≠ 0 := by
    have := hθ ((K : ℤ) - 1 + n)
    push_cast at this
    intro h0; apply this; rw [ha2] at h0; linear_combination h0
  have key := Dfac_sigma K m S θ a2 hPe hQo hQ0 hK
  have e : (1 - (n : F)) = θ + (a2 + 1) := by rw [ha2]; ring
  unfold coefB'
  rw [e, eval_p2', key]; ring


end K4field

/-- **(K4a).**  Column relation of the Darboux map, at `g = 0` (`K = S+m+1`), symbolic `m`:
`(X c_y)_i = 𝒜(y) c'_y(i) + ℬ(y) c'_{y+1}(i) + Σ_{x∈X} ℰ_x(y) c'_x(i)`, with
`𝒜(y) = (Dμ)(-θ-y)`, `ℬ(y) = -(Dσ)(-θ-y-1)`. -/
theorem K4a_gen [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
    (n : ℤ) (hn : ∀ j : ℕ, j < m → (S : ℤ) + 2 * j + 2 ≠ n) :
    ∃ ℰ : ℕ → F, ∀ i : ℕ, i + 1 < K →
      Dfac K m S θ i * mu K m S θ i / (θ + i + n)
        - Dfac K m S θ i * sigma K m S θ i / (θ + i + 1 + n) =
      coefA K m (S : F) θ (n : F) (cK K m S θ) / (θ + i + n)
        + coefB θ (n : F) (cK K m S θ) / (θ + i + 1 + n)
        + ∑ j ∈ Finset.range m, ℰ j / (θ + i + (S + 2 * (j : F) + 2)) := by
  have hKF : (K : F) = (S : F) + m + 1 := by rw [hKS]; push_cast; ring
  have hP : (PPf (S : F) m).eval (-(n : F)) ≠ 0 := by
    have := Qh2_eval_ne_of_ne (F := F) m S (-n) (fun j hj => by have := hn j hj; omega)
    push_cast at this; exact this
  obtain ⟨N, hNd, heq⟩ := K4a_poly K m hm (S : F) θ (n : F) (cK K m S θ) hKF hP
  have hQQ : Qh m ((S : F) + 1) = Qh2 m (S : F) := by simp [Qh, Qh2]
  obtain ⟨κ, hκ⟩ := partial_frac m ((S : F) + 1) N hNd
  rw [hQQ] at hκ
  refine ⟨κ, fun i hi => ?_⟩
  have hGa : GenAt θ (i : F) := genAt_nat hθ i
  have hPz : Pe m S θ i ≠ 0 := Pe_ne_zero m S hGa
  have hQoi : Qo m S θ i ≠ 0 := Qo_ne_zero m S hGa
  have hQ0 : Qo m S θ 0 ≠ 0 := by simpa using Qo_ne_zero m S (genAt_nat hθ 0)
  have h1 : θ + (S : F) + 1 + i ≠ 0 := by
    have := hGa (S + 1); push_cast at this; intro h0; apply this; linear_combination h0
  have hKi : (K : F) - 1 - i ≠ 0 := by
    have := natsub_ne (F := F) (a := K - 1) (b := i) (by omega)
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this; exact this
  have hFa := Dfac_mu_Pe K m S θ (i : F) hm hPz hQ0 hQoi
  have hFb := Dfac_sigma K m S θ (i : F) hPz hQoi hQ0 hKi
  have hE := congrArg (Polynomial.eval (θ + (i : F))) heq
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_lin, MainA, A3a, B3a, pK1, eval_PPf_S,
    eval_PPf_pred] at hE
  have hQz : (PPf (S : F) m).eval (θ + (i : F)) ≠ 0 := by rw [eval_PPf_S K m S θ i]; exact hPz
  have hSum := hκ (θ + (i : F)) (by simpa [Qh2] using hQz)
  have hSum' : ∑ j ∈ Finset.range m, κ j / (θ + i + (S + 2 * (j : F) + 2)) =
      N.eval (θ + (i : F)) / (PPf (S : F) m).eval (θ + (i : F)) := by
    rw [show (PPf (S : F) m) = Qh2 m (S : F) from rfl, hSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold vY; ring_nf
  rw [hSum']
  have hu : θ + (i : F) + n ≠ 0 := by
    have := hθ ((i : ℤ) + n); push_cast at this
    intro h0; apply this; linear_combination h0
  have hup : θ + (i : F) + 1 + n ≠ 0 := by
    have := hθ ((i : ℤ) + n + 1); push_cast at this
    intro h0; apply this; linear_combination h0
  rw [eval_PPf_S K m S θ i] at hE hQz ⊢
  refine kstep_alg _ _ _ _ _ _ _ _ hu hup hQz ?_
  linear_combination hE + (θ + (i : F) + 1 + n) * hFa - (Pe m S θ i * (θ + (i : F) + n)) * hFb



/-- **(K4a).** -/
theorem K4a_field [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
    (n : ℤ) (hn : n ≤ (S : ℤ)) :
    ∃ ℰ : ℕ → F, ∀ i : ℕ, i + 1 < K →
      Dfac K m S θ i * mu K m S θ i / (θ + i + n)
        - Dfac K m S θ i * sigma K m S θ i / (θ + i + 1 + n) =
      Dfac K m S θ (-θ - n) * mu K m S θ (-θ - n) / (θ + i + n)
        + -(Dfac K m S θ (-θ - n - 1) * sigma K m S θ (-θ - n - 1)) / (θ + i + 1 + n)
        + ∑ j ∈ Finset.range m, ℰ j / (θ + i + (S + 2 * (j : F) + 2)) := by
  obtain ⟨ℰ, h⟩ := K4a_gen K m S hm θ hθ hKS n (fun j _ => by omega)
  refine ⟨ℰ, fun i hi => ?_⟩
  rw [h i hi, coefA_eq K m S hm θ hθ hKS n (by omega), coefB_eq K m S hm θ hθ hKS n (by omega) hn]

/-- **(K4b).**  Row relation of the Darboux map at `g = 0`, symbolic `m`:
`(Xᵀ c'_y)_j = D_j μ_j c_y(j) - D_{j-1}σ_{j-1} c_y(j-1) = 𝒜(y) c_y(j) + ℬ'(y) c_{y-1}(j)
+ Σ_{x∈X} ℱ_x(y) c_x(j)` with `ℬ'(y) = -(Dσ)(-θ-y)`. -/
theorem K4b_gen [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
    (n : ℤ) (hn : ∀ j : ℕ, j < m → (S : ℤ) + 2 * j + 2 ≠ n) :
    ∃ ℱ : ℕ → F, ∀ j : ℕ, j < K →
      Dfac K m S θ j * mu K m S θ j / (θ + j + n)
        - Dfac K m S θ ((j : F) - 1) * sigma K m S θ ((j : F) - 1) / (θ + j - 1 + n) =
      coefA K m (S : F) θ (n : F) (cK K m S θ) / (θ + j + n)
        + coefB' θ (n : F) (cK K m S θ) / (θ + j + n - 1)
        + ∑ i ∈ Finset.range m, ℱ i / (θ + j + (S + 2 * (i : F) + 2)) := by
  have hKF : (K : F) = (S : F) + m + 1 := by rw [hKS]; push_cast; ring
  have hP : (PPf (S : F) m).eval (-(n : F)) ≠ 0 := by
    have := Qh2_eval_ne_of_ne (F := F) m S (-n) (fun j hj => by have := hn j hj; omega)
    push_cast at this; exact this
  obtain ⟨N, hNd, heq⟩ := K4b_poly K m hm (S : F) θ (n : F) (cK K m S θ) hKF hP
  have hQQ : Qh m ((S : F) + 1) = Qh2 m (S : F) := by simp [Qh, Qh2]
  obtain ⟨κ, hκ⟩ := partial_frac m ((S : F) + 1) N hNd
  rw [hQQ] at hκ
  refine ⟨κ, fun j hj => ?_⟩
  have hGa : GenAt θ (j : F) := genAt_nat hθ j
  have hGa1 : GenAt θ ((j : F) - 1) := genAt_nat_sub_one hθ j
  have hPz : Pe m S θ j ≠ 0 := Pe_ne_zero m S hGa
  have hQoj : Qo m S θ j ≠ 0 := Qo_ne_zero m S hGa
  have hQ0 : Qo m S θ 0 ≠ 0 := by simpa using Qo_ne_zero m S (genAt_nat hθ 0)
  have h1 : θ + (S : F) + 1 + j ≠ 0 := by
    have := hGa (S + 1); push_cast at this; intro h0; apply this; linear_combination h0
  have hKj : (K : F) - 1 - ((j : F) - 1) ≠ 0 := by
    have := natsub_ne (F := F) (a := K) (b := j) (by omega)
    intro h0; apply this; linear_combination h0
  have hFa := Dfac_mu_Pe K m S θ (j : F) hm hPz hQ0 hQoj
  have hFb := Dfac_sigma K m S θ ((j : F) - 1) (Pe_ne_zero m S hGa1) (Qo_ne_zero m S hGa1) hQ0 hKj
  have hE := congrArg (Polynomial.eval (θ + (j : F))) heq
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_lin, MainB, A3b, B3b, eval_PPf_pred] at hE
  have hQz : (PPf (S : F) m).eval (θ + (j : F)) ≠ 0 := by rw [eval_PPf_S K m S θ j]; exact hPz
  have hSum := hκ (θ + (j : F)) (by simpa [Qh2] using hQz)
  have hSum' : ∑ i ∈ Finset.range m, κ i / (θ + j + (S + 2 * (i : F) + 2)) =
      N.eval (θ + (j : F)) / (PPf (S : F) m).eval (θ + (j : F)) := by
    rw [show (PPf (S : F) m) = Qh2 m (S : F) from rfl, hSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold vY; ring_nf
  rw [hSum']
  have hu : θ + (j : F) + n ≠ 0 := by
    have := hθ ((j : ℤ) + n); push_cast at this
    intro h0; apply this; linear_combination h0
  have hum : θ + (j : F) + n - 1 ≠ 0 := by
    have := hθ ((j : ℤ) + n - 1); push_cast at this
    intro h0; apply this; linear_combination h0
  have e : θ + (j : F) - 1 + n = θ + j + n - 1 := by ring
  rw [e]
  rw [eval_PPf_S K m S θ j] at hE hQz ⊢
  refine kstep_alg _ _ _ _ _ _ _ _ hu hum hQz ?_
  linear_combination hE + (θ + (j : F) + n - 1) * hFa - (Pe m S θ j * (θ + (j : F) + n)) * hFb


/-- **(K4b).** -/
theorem K4b_field [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
    (n : ℤ) (hn : n ≤ (S : ℤ) + 1) :
    ∃ ℱ : ℕ → F, ∀ j : ℕ, j < K →
      Dfac K m S θ j * mu K m S θ j / (θ + j + n)
        - Dfac K m S θ ((j : F) - 1) * sigma K m S θ ((j : F) - 1) / (θ + j - 1 + n) =
      Dfac K m S θ (-θ - n) * mu K m S θ (-θ - n) / (θ + j + n)
        + -(Dfac K m S θ (-θ - n) * sigma K m S θ (-θ - n)) / (θ + j + n - 1)
        + ∑ i ∈ Finset.range m, ℱ i / (θ + j + (S + 2 * (i : F) + 2)) := by
  obtain ⟨ℱ, h⟩ := K4b_gen K m S hm θ hθ hKS n (fun j _ => by omega)
  refine ⟨ℱ, fun j hj => ?_⟩
  rw [h j hj, coefA_eq K m S hm θ hθ hKS n (by omega), coefB'_eq K m S hm θ hθ hKS n hn]

end CatalanCore.Star.Leonard
