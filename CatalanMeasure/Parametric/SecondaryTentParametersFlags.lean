module
public import CatalanMeasure.Parametric.SecondaryTentParametersInput
public import Mathlib.Algebra.Polynomial.AlgebraMap
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

def secondaryTentPolynomialWindowLinear {K : Type*} [Field K] (offset count : ℕ) :
    K[X] →ₗ[K] (Fin count → K) :=
  LinearMap.pi fun i => Polynomial.lcoeff K (offset+i.val)

theorem secondaryTent_polynomial_prefix_zero {K : Type*} [Field K]
    {n : ℕ} (P : K[X])
    (h : secondaryTentPolynomialWindowLinear 0 n P = 0) : X^n ∣ P := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  simpa [secondaryTentPolynomialWindowLinear] using congrFun h ⟨k,hk⟩

theorem secondaryTent_polynomial_prefix_eq_zero {K : Type*} [Field K]
    {n : ℕ} (P : K[X]) (hdeg : P.natDegree < n)
    (h : secondaryTentPolynomialWindowLinear 0 n P = 0) : P=0 := by
  ext k
  by_cases hk : k<n
  · simpa [secondaryTentPolynomialWindowLinear] using congrFun h ⟨k,hk⟩
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (by omega))

def secondaryTentPolynomialTranslateLinear {K : Type*} [Field K] (t : K) :
    K[X] →ₗ[K] K[X] := (Polynomial.aeval (X+C t)).toLinearMap

theorem secondaryTent_polynomial_translate_apply {K : Type*} [Field K]
    (t : K) (P : K[X]) :
    secondaryTentPolynomialTranslateLinear t P = P.comp (X+C t) := by
  simp [secondaryTentPolynomialTranslateLinear, Polynomial.aeval_def, Polynomial.comp]

theorem secondaryTent_polynomial_shift_flag {K : Type*} [Field K]
    {n : ℕ} (t : K) (P : K[X])
    (h : secondaryTentPolynomialWindowLinear 0 n
      (secondaryTentPolynomialTranslateLinear t P) = 0) :
    (X-C t)^n ∣ P := by
  apply Polynomial.X_sub_C_pow_dvd_iff.mpr
  rw [← secondaryTent_polynomial_translate_apply]
  exact secondaryTent_polynomial_prefix_zero _ h

theorem secondaryTent_polynomial_tail_flag {K : Type*} [Field K]
    {m p : ℕ} (hm : 0<m) (hmp : m≤p) (P : K[X]) (hdeg : P.natDegree < p)
    (h : secondaryTentPolynomialWindowLinear m (p-m) P = 0) : P.natDegree < m := by
  apply Nat.lt_of_le_pred hm
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp only [Nat.pred_eq_sub_one] at hk
  by_cases hkp : k<p
  · have hmk : m≤k := by omega
    have hidx : k-m < p-m := by omega
    have hc := congrFun h ⟨k-m,hidx⟩
    simpa [secondaryTentPolynomialWindowLinear, Nat.add_sub_of_le hmk] using hc
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (by omega))

theorem secondaryTent_frobenius_root_remainder {p : ℕ} [Fact p.Prime]
    (Q : (ZMod p)[X]) :
    (X-1 : (ZMod p)[X])^p ∣ Q^p-C (Q.eval 1) := by
  have hd : X-C (1 : ZMod p) ∣ Q-C (Q.eval 1) := X_sub_C_dvd_sub_C_eval
  obtain ⟨R,hR⟩ := hd
  refine ⟨R^p, ?_⟩
  have hc : (C (Q.eval 1) : (ZMod p)[X])^p=C (Q.eval 1) := by
    rw [← C_pow]
    congr 1
    exact ZMod.pow_card _
  calc
    Q^p-C (Q.eval 1) = (Q-C (Q.eval 1))^p := by rw [sub_pow_char, hc]
    _ = (X-1)^p*R^p := by rw [hR, mul_pow]; simp

/-- The small beta flag pays the full required V-branch divisor, because
all fixed seed pth powers are constant to order p at x=1. -/
theorem secondaryTent_beta_flag_pays_V {p m b : ℕ} [Fact p.Prime]
    (Q I : Fin 5 → (ZMod p)[X]) (F : (ZMod p)[X]) (β : ZMod p)
    (hmp : m≤p) (hmb : m≤b) (hF : (X-1)^b ∣ F)
    (hβ : (∑ i, C ((Q i).eval 1)*I i) = C β*F) :
    (X-1 : (ZMod p)[X])^m ∣ ∑ i, (Q i)^p*I i := by
  have hdiff : (X-1 : (ZMod p)[X])^m ∣
      (∑ i, (Q i)^p*I i) - ∑ i, C ((Q i).eval 1)*I i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro i hi
    rw [← sub_mul]
    exact dvd_mul_of_dvd_left
      ((pow_dvd_pow (X-1 : (ZMod p)[X]) hmp).trans
        (secondaryTent_frobenius_root_remainder (Q i))) _
  rw [hβ] at hdiff
  have hF' : (X-1 : (ZMod p)[X])^m ∣ C β*F :=
    dvd_mul_of_dvd_right ((pow_dvd_pow _ hmb).trans hF) _
  have hh := dvd_add hdiff hF'
  simpa using hh

end
end CatalanMeasure.Parametric
