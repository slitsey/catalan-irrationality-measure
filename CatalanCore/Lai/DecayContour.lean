module

public import CatalanCore.Decay.ContourIdentity
public import CatalanCore.Lai.Construction
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# Lai decay, instance part A: perturbation (LD03) and the contour form of `L_n` (LD02)

* `laiL_perturb` (LD03): `L_{c, X + t}(P) = L_{c, X}(P) + 6 t ∑_{k ≤ 6n} c_k P(-k)`.
* `laiFun_deriv_zero`: `R_n P` has a triple zero at `1, …, 2n`, so its first two derivatives vanish.
* `laiL_contour` (LD02): `L_n(P)(a, b, aζ(3) + bζ(4)) = -(2πI)⁻¹ ∮_Γ R_n P K_c dz` with
  `c = (c₁, c₂) = (-3a, b)`, for any admissible polygon `Γ` crossing the real axis at a non-integer
  `v ∈ (0, 2n + 1)`.
-/

open Polynomial Finset Complex MeasureTheory

namespace CatalanCore.Lai.DecayContour

open CatalanCore.Lai CatalanCore.Decay.LineInt CatalanCore.Decay.ComplexContour

/-! ### LD03: the perturbation formula -/

theorem laiL_perturb (n : ℕ) (P : ℚ[X]) (a b x t : ℝ) :
    MvPolynomial.aeval ![a, b, x + t] (laiL n P) =
      MvPolynomial.aeval ![a, b, x] (laiL n P) +
        6 * t * ∑ k ∈ range (6 * n + 1), (laiCoef n k : ℝ) * ((P.eval (-(k : ℚ)) : ℚ) : ℝ) := by
  rw [laiL_eval, laiL_eval, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### A triple zero kills two derivatives -/

lemma deriv_vanish_triple (N D : ℝ[X]) (m : ℝ) (h0 : N.eval m = 0)
    (h1 : (derivative N).eval m = 0) (h2 : (derivative (derivative N)).eval m = 0)
    (hD : D.eval m ≠ 0) :
    deriv (fun t => N.eval t / (D.eval t) ^ 2) m = 0 ∧
      deriv (deriv (fun t => N.eval t / (D.eval t) ^ 2)) m = 0 := by
  set w : ℝ → ℝ := fun t => ((D.eval t) ^ 2)⁻¹ with hw
  set w1 : ℝ → ℝ := fun t => -2 * (derivative D).eval t / (D.eval t) ^ 3 with hw1
  have hf : (fun t => N.eval t / (D.eval t) ^ 2) = fun t => N.eval t * w t := by
    funext t; simp [hw, div_eq_mul_inv]
  have hDne : ∀ᶠ t in nhds m, D.eval t ≠ 0 :=
    ((Polynomial.continuous D).continuousAt.eventually_ne hD)
  have hwd : ∀ t, D.eval t ≠ 0 → HasDerivAt w (w1 t) t := by
    intro t ht
    have := ((D.hasDerivAt t).pow 2).inv (pow_ne_zero 2 ht)
    refine this.congr_deriv ?_
    simp only [hw1]
    norm_num
    field_simp
  have hfd : ∀ t, D.eval t ≠ 0 →
      HasDerivAt (fun t => N.eval t * w t)
        ((derivative N).eval t * w t + N.eval t * w1 t) t := fun t ht =>
    (N.hasDerivAt t).mul (hwd t ht)
  rw [hf]
  set φ : ℝ → ℝ := fun t => (derivative N).eval t * w t + N.eval t * w1 t with hφ
  have hev : deriv (fun t => N.eval t * w t) =ᶠ[nhds m] φ := by
    filter_upwards [hDne] with t ht
    exact (hfd t ht).deriv
  refine ⟨?_, ?_⟩
  · rw [(hfd m hD).deriv]
    simp [h0, h1]
  · rw [hev.deriv_eq]
    obtain ⟨W2, hw1d⟩ : ∃ W2, HasDerivAt w1 W2 m :=
      ⟨_, (((derivative D).hasDerivAt m).const_mul (-2 : ℝ)).div ((D.hasDerivAt m).pow 3)
        (pow_ne_zero 3 hD)⟩
    have hφd : HasDerivAt φ _ m :=
      (((derivative N).hasDerivAt m).mul (hwd m hD)).add ((N.hasDerivAt m).mul hw1d)
    rw [hφd.deriv]
    simp [h0, h1, h2]

/-! ### Zeros of `R_n P` -/

lemma laiFun_eq_ratio (n : ℕ) (P : ℚ[X]) :
    laiFun n P = fun t => ((laiNum n * P).map (algebraMap ℚ ℝ)).eval t /
      (((laiDen n).map (algebraMap ℚ ℝ)).eval t) ^ 2 := by
  funext t
  unfold laiFun laiRfun
  have e : ∀ Q : ℚ[X], aeval t Q = (Q.map (algebraMap ℚ ℝ)).eval t := fun Q => by
    rw [aeval_def, eval₂_eq_eval_map]
  rw [e, e, e P, Polynomial.map_mul, eval_mul]
  ring

lemma laiDen_eval_ne (n : ℕ) {m : ℝ} (hm : 0 < m) :
    ((laiDen n).map (algebraMap ℚ ℝ)).eval m ≠ 0 := by
  rw [laiDen_eq, Polynomial.map_prod, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, eval_add, eval_X, eval_C,
    eq_ratCast, Rat.cast_natCast]
  positivity

lemma laiNum_triple (n m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * n) (P : ℚ[X]) :
    (X - C (m : ℚ)) ^ 3 ∣ laiNum n * P := by
  have h1 : (X - C (m : ℚ)) ∣ laiPoch n := by
    unfold laiPoch
    have hmem := Finset.dvd_prod_of_mem (fun i : ℕ => (X - C ((2 * n : ℚ) - i)))
      (Finset.mem_range.mpr (by omega : 2 * n - m < 2 * n))
    refine (dvd_of_eq ?_).trans hmem
    have : ((2 * n : ℚ) - ((2 * n - m : ℕ) : ℚ)) = (m : ℚ) := by
      rw [Nat.cast_sub hm2]; push_cast; ring
    simp only [this]
  have h3 : (X - C (m : ℚ)) ^ 3 ∣ laiPoch n ^ 3 := pow_dvd_pow_of_dvd h1 3
  unfold laiNum
  exact (h3.trans (dvd_mul_left _ _)).mul_right P

/-- `R_n P` has a triple zero at `1, …, 2n`: its first two derivatives vanish there. -/
theorem laiFun_deriv_zero (n : ℕ) (P : ℚ[X]) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * n) :
    deriv (laiFun n P) (m : ℝ) = 0 ∧ deriv (deriv (laiFun n P)) (m : ℝ) = 0 := by
  rw [laiFun_eq_ratio]
  set Nr : ℝ[X] := (laiNum n * P).map (algebraMap ℚ ℝ) with hNr
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  by_cases hN0 : Nr = 0
  · have : (fun t : ℝ => Nr.eval t / (((laiDen n).map (algebraMap ℚ ℝ)).eval t) ^ 2) = fun _ => 0 := by
      funext t; simp [hN0]
    rw [this]; simp
  have hdvd : (X - C (m : ℝ)) ^ 3 ∣ Nr := by
    have := Polynomial.map_dvd (algebraMap ℚ ℝ) (laiNum_triple n m hm1 hm2 P)
    simpa [hNr, Polynomial.map_pow] using this
  have hmult : 3 ≤ Nr.rootMultiplicity (m : ℝ) := (le_rootMultiplicity_iff hN0).mpr hdvd
  have hr : ∀ i, i < 3 → (derivative^[i] Nr).IsRoot (m : ℝ) := fun i hi =>
    isRoot_iterate_derivative_of_lt_rootMultiplicity (lt_of_lt_of_le hi hmult)
  exact deriv_vanish_triple Nr _ (m : ℝ) (hr 0 (by norm_num)) (hr 1 (by norm_num))
    (hr 2 (by norm_num)) (laiDen_eval_ne n hmpos)

/-! ### LD02 for Lai's `R_n P`: the contour form of `L_n` -/

section Contour

open CatalanCore.Uniform.Decay.Polygon (polyI)

/-- Simple-pole coefficients `r_{k,1}` of `R_n P`, as complex numbers. -/
noncomputable def laiPFa (n : ℕ) (P : ℚ[X]) : Fin (6 * n + 1) → ℂ :=
  fun k => ((laiA1q n P (k : ℕ) : ℚ) : ℂ)

/-- Double-pole coefficients `r_{k,2}` of `R_n P`, as complex numbers. -/
noncomputable def laiPFb (n : ℕ) (P : ℚ[X]) : Fin (6 * n + 1) → ℂ :=
  fun k => ((laiA2q n P (k : ℕ) : ℚ) : ℂ)

/-- The poles `-k`, `0 ≤ k ≤ 6n`. -/
noncomputable def laiPoles (n : ℕ) : Fin (6 * n + 1) → ℝ := fun k => -((k : ℕ) : ℝ)

/-- The jet coefficients `(c₁, c₂) = (-3a, b)` (zero for every other jet). -/
noncomputable def laiCoefJ (a b : ℝ) : ℕ → ℂ :=
  fun j => if j = 1 then ((-3 * a : ℝ) : ℂ) else if j = 2 then (b : ℂ) else 0

/-- The jets `{1, 2}`. -/
def laiJets : Finset ℕ := {1, 2}

/-- The contour integrand `R_n(z) P(z) K_c(z)`, with `R_n P` in its partial-fraction form
(`laiIntegrand_eq`: equal to `R_n(z) P(z)` off the poles). -/
noncomputable def laiIntegrand (n : ℕ) (P : ℚ[X]) (a b : ℝ) (z : ℂ) : ℂ :=
  ratF (laiPFa n P) (laiPFb n P) (laiPoles n) z * Kc laiJets (laiCoefJ a b) z

/-- Off the poles, `R_n P` is the partial-fraction form `ratF`. -/
lemma ratF_eq_laiR (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) {z : ℂ}
    (hz : ∀ k ∈ range (6 * n + 1), z + (k : ℂ) ≠ 0) :
    ratF (laiPFa n P) (laiPFb n P) (laiPoles n) z =
      aeval z (laiNum n) / (aeval z (laiDen n)) ^ 2 * aeval z P := by
  rw [laiR_partial_fractions (𝕂 := ℂ) n P hP hz]
  unfold ratF laiPFa laiPFb laiPoles
  rw [← Fin.sum_univ_eq_sum_range (fun k => ((algebraMap ℚ ℂ) (laiA1q n P k) / (z + (k : ℂ)) +
    (algebraMap ℚ ℂ) (laiA2q n P k) / (z + (k : ℂ)) ^ 2)) (6 * n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [eq_ratCast]
  push_cast
  ring

lemma sum_laiPFa (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) :
    ∑ k, laiPFa n P k = 0 := by
  unfold laiPFa
  rw [Fin.sum_univ_eq_sum_range (fun k => ((laiA1q n P k : ℚ) : ℂ)) (6 * n + 1)]
  have := sum_laiA1q n P hP
  exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this

lemma ratDeriv_one (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) {B : ℝ}
    (hB : 0 < B) :
    ratDeriv 1 (laiPFa n P) (laiPFb n P) (laiPoles n) (B : ℂ) =
      ((deriv (laiFun n P) B : ℝ) : ℂ) := by
  rw [DoublePole.deriv_of_eqOn (laiFun_eq_pfFun n P hP) hB]
  unfold DoublePole.pfD1 ratDeriv laiPFa laiPFb laiPoles
  beta_reduce
  rw [Complex.ofReal_sum, ← Fin.sum_univ_eq_sum_range (fun k : ℕ => (((-(laiA1q n P k : ℝ) / (B + k) ^ 2 +
    -(2 * (laiA2q n P k : ℝ)) / (B + k) ^ 3 : ℝ)) : ℂ)) (6 * n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  have h1 : (B : ℂ) + k ≠ 0 := by
    have : (0 : ℝ) < B + k := by positivity
    exact_mod_cast this.ne'
  simp only [sub_neg_eq_add, Nat.factorial, Nat.cast_one, pow_one, mul_one, Nat.cast_ofNat,
    Nat.cast_succ, Nat.cast_zero, zero_add]
  field_simp
  ring

lemma ratDeriv_two (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) {B : ℝ}
    (hB : 0 < B) :
    ratDeriv 2 (laiPFa n P) (laiPFb n P) (laiPoles n) (B : ℂ) =
      ((deriv (deriv (laiFun n P)) B : ℝ) : ℂ) := by
  rw [DoublePole.deriv_deriv_of_eqOn (laiFun_eq_pfFun n P hP) hB]
  unfold DoublePole.pfD2 ratDeriv laiPFa laiPFb laiPoles
  beta_reduce
  rw [Complex.ofReal_sum, ← Fin.sum_univ_eq_sum_range (fun k : ℕ => ((2 * (laiA1q n P k : ℝ) / (B + k) ^ 3 +
    6 * (laiA2q n P k : ℝ) / (B + k) ^ 4 : ℝ) : ℂ)) (6 * n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  have h1 : (B : ℂ) + k ≠ 0 := by
    have : (0 : ℝ) < B + k := by positivity
    exact_mod_cast this.ne'
  simp only [sub_neg_eq_add]
  field_simp
  norm_num [Nat.factorial]
  ring

/-- The tail `∑_{B > v}` equals the full sum `∑_{m ≥ 1}` of a function vanishing on `1, …, ⌊v⌋`. -/
lemma tsum_shift_zero {G : ℕ → ℂ} {K0 : ℕ} (hG : ∀ m, m < K0 → G m = 0) :
    ∑' k : ℕ, G (K0 + k) = ∑' m : ℕ, G m := by
  have hinj : Function.Injective (fun k : ℕ => K0 + k) := fun k l h => by simpa using h
  have hsupp : Function.support G ⊆ Set.range (fun k : ℕ => K0 + k) := by
    intro m hm
    by_cases h : m < K0
    · exact absurd (hG m h) hm
    · exact ⟨m - K0, by simp only; omega⟩
  exact hinj.tsum_eq hsupp

/-- **LD02** for Lai's family: for every non-integer `v ∈ (0, 2n + 1)` and every admissible polygon
(`v → pts → tail d` into the upper half-plane, with its mirror image),
`L_n(P)(a, b, aζ(3) + bζ(4)) = -(2πI)⁻¹ ∮_Γ R_n P K_c dz`, `c = (-3a, b)`, `deg P < 6n`. -/
theorem laiL_contour (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) (a b v : ℝ)
    (hv0 : 0 < v) (hv2 : v < 2 * n + 1) (hvm : ∀ m : ℤ, v ≠ m)
    (pts : List ℂ) (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    ((MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4] (laiL n P) : ℝ) : ℂ) =
      -(2 * (Real.pi : ℂ) * I)⁻¹ *
        (polyI (laiIntegrand n P a b) (v : ℂ) pts d -
          polyI (laiIntegrand n P a b) (v : ℂ) (pts.map (starRingEnd ℂ)) (starRingEnd ℂ d)) := by
  have hpv : ∀ i, laiPoles n i < v := fun i => by
    unfold laiPoles
    have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hJ : ∀ j ∈ laiJets, 1 ≤ j := by
    intro j hj; unfold laiJets at hj; simp at hj; omega
  have hid := contour_identity_Kc (laiPFa n P) (laiPFb n P) (laiPoles n) v hvm hpv
    (sum_laiPFa n P hP) laiJets hJ (laiCoefJ a b) pts hpts hd
  change polyI (laiIntegrand n P a b) (v : ℂ) pts d -
      polyI (laiIntegrand n P a b) (v : ℂ) (pts.map (starRingEnd ℂ)) (starRingEnd ℂ d) = _ at hid
  rw [hid]
  -- the two jets
  set K0 : ℕ := ⌊v⌋.toNat with hK0
  have hfl : (⌊v⌋ : ℤ) = (K0 : ℤ) := by
    rw [hK0]; exact (Int.toNat_of_nonneg (Int.floor_nonneg.mpr hv0.le)).symm
  have hK0le : K0 ≤ 2 * n := by
    have h1 : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
    have h2 : (K0 : ℝ) = (⌊v⌋ : ℝ) := by exact_mod_cast hfl.symm
    have h3 : (K0 : ℝ) < 2 * n + 1 := by
      have : (K0 : ℝ) ≤ v := by rw [h2]; exact h1
      linarith
    have : K0 < 2 * n + 1 := by exact_mod_cast h3
    omega
  have hBk : ∀ k : ℕ, ((⌊v⌋ + 1 + (k : ℤ) : ℤ) : ℝ) = ((K0 + k : ℕ) : ℝ) + 1 := by
    intro k; rw [hfl]; push_cast; ring
  have hsum : ∀ (j : ℕ) (g : ℝ → ℝ), (j = 1 ∨ j = 2) →
      (∀ B : ℝ, 0 < B → ratDeriv j (laiPFa n P) (laiPFb n P) (laiPoles n) (B : ℂ) = (g B : ℂ)) →
      (∀ m : ℕ, 1 ≤ m → m ≤ 2 * n → g (m : ℝ) = 0) →
      ∑' k : ℕ, ratDeriv j (laiPFa n P) (laiPFb n P) (laiPoles n)
          ((((⌊v⌋ + 1 + (k : ℤ) : ℤ) : ℝ)) : ℂ) = ((∑' m : ℕ, g ((m : ℝ) + 1) : ℝ) : ℂ) := by
    intro j g _ hg hz
    rw [Complex.ofReal_tsum]
    have hk : ∀ k : ℕ, ratDeriv j (laiPFa n P) (laiPFb n P) (laiPoles n)
        ((((⌊v⌋ + 1 + (k : ℤ) : ℤ) : ℝ)) : ℂ) = ((g (((K0 + k : ℕ) : ℝ) + 1) : ℝ) : ℂ) := by
      intro k
      rw [hBk k]
      exact hg _ (by positivity)
    simp_rw [hk]
    exact tsum_shift_zero (G := fun m : ℕ => ((g ((m : ℝ) + 1) : ℝ) : ℂ)) (K0 := K0) (fun m hm => by
      have := hz (m + 1) (by omega) (by omega)
      push_cast at this
      simp [this])
  have h1 := hsum 1 (deriv (laiFun n P)) (Or.inl rfl) (fun B hB => ratDeriv_one n P hP hB)
    (fun m h1 h2 => (laiFun_deriv_zero n P h1 h2).1)
  have h2 := hsum 2 (deriv (deriv (laiFun n P))) (Or.inr rfl) (fun B hB => ratDeriv_two n P hP hB)
    (fun m h1 h2 => (laiFun_deriv_zero n P h1 h2).2)
  unfold laiJets
  rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), h1, h2, laiL_eval_moment n P hP a b]
  simp only [laiCoefJ, if_true, show (2 : ℕ) ≠ 1 from by norm_num, if_false]
  have hne : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  push_cast
  field_simp

end Contour

end CatalanCore.Lai.DecayContour
