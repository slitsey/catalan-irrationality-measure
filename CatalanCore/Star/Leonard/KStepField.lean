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
    (hQ0 : Qo m S θ 0 ≠ 0) (h1 : θ + S + 1 + a ≠ 0) (hQ : Qo m S θ a ≠ 0) :
    Dfac K m S θ a * mu K m S θ a * Pe m S θ a =
      -(cK K m S θ * (((K : F) - 1 - a) * (θ + S + 2 * m + 1 + a) * Qhat m S θ a)) := by
  by_cases hK : (K : F) - 1 - a = 0
  · unfold Dfac mu; rw [hK]; simp
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

section K4field

variable [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hKS : K = S + m + 1)
  (n : ℤ) (hn : n + 1 ≤ (S : ℤ))

include hm hθ hKS hn in
/-- Identification of the `A` coefficient with `(Dμ)(-θ-n)`. -/
lemma coefA_eq : coefA K m (S : F) θ (n : F) (cK K m S θ) =
    Dfac K m S θ (-θ - n) * mu K m S θ (-θ - n) := by
  set a2 : F := -θ - n with ha2
  have hc : θ + a2 = ((-n : ℤ) : F) := by rw [ha2]; push_cast; ring
  have hPe : Pe m S θ a2 ≠ 0 := Pe_ne_zero_int m S θ _ (-n) hc (fun i _ => by omega)
  have hQo : Qo m S θ a2 ≠ 0 := Qo_ne_zero_int m S θ _ (-n) hc (fun i _ => by omega)
  have hQ0 : Qo m S θ 0 ≠ 0 := by simpa using Qo_ne_zero m S (genAt_nat hθ 0)
  have h1 : θ + S + 1 + a2 ≠ 0 := by
    have : θ + (S : F) + 1 + a2 = (((S : ℤ) - n + 1 : ℤ) : F) := by rw [ha2]; push_cast; ring
    rw [this]; exact cast_ne_zero_of_pos (by omega)
  have key := Dfac_mu_Pe K m S θ a2 hm hPe hQ0 h1 hQo
  have e : (-(n : F)) = θ + a2 := by rw [ha2]; ring
  unfold coefA
  rw [e, eval_PPf_S K m S θ a2, eval_PPf_pred, eval_pK1]
  rw [div_eq_iff hPe]
  linear_combination (-1 : F) * key

include hm hθ hKS hn in
lemma coefB_eq : coefB θ (n : F) (cK K m S θ) =
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

end CatalanCore.Star.Leonard
