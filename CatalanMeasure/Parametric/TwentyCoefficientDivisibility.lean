module

public import CatalanMeasure.Parametric.TwentyIntegerPolynomial
public import CatalanMeasure.Parametric.RawDigitReduction
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Coefficientwise prime divisibility for the canonical twenty polynomial

The local ring used here consists of rationals whose reduced denominator is
a unit modulo `q`.  Polynomial integrality is coefficientwise; it is never
deduced from integer-valued specializations.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Polynomial Matrix Finset OAI.InternalCatalan
open scoped BigOperators Nat

noncomputable section

def coefficientLocalRing (q : ℕ) [Fact q.Prime] : Subring ℚ where
  carrier := {a | (a.den : ZMod q) ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun ha hb => (rational_residue_add ha hb).1
  mul_mem' := fun ha hb => (rational_residue_mul ha hb).1
  neg_mem' := by intro a ha; simpa using ha

def coefficientLocalPolynomials (q : ℕ) [Fact q.Prime] : Subring ℚ[X] :=
  Polynomial.liftsRing (coefficientLocalRing q).subtype

theorem mem_coefficientLocalPolynomials_iff {q : ℕ} [Fact q.Prime] (f : ℚ[X]) :
    f ∈ coefficientLocalPolynomials q ↔ ∀ j, ((f.coeff j).den : ZMod q) ≠ 0 := by
  rw [coefficientLocalPolynomials, ← Polynomial.lifts_iff_liftsRing,
    Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h j
    obtain ⟨a, ha⟩ := h j
    rw [← ha]
    exact a.property
  · intro h j
    exact ⟨⟨f.coeff j, h j⟩, rfl⟩

theorem C_mem_coefficientLocalPolynomials {q : ℕ} [Fact q.Prime] {a : ℚ}
    (ha : (a.den : ZMod q) ≠ 0) : C a ∈ coefficientLocalPolynomials q := by
  apply (Polynomial.lifts_iff_liftsRing _ _).mp
  exact Polynomial.C_mem_lifts (coefficientLocalRing q).subtype ⟨a, ha⟩

theorem X_mem_coefficientLocalPolynomials (q : ℕ) [Fact q.Prime] :
    (X : ℚ[X]) ∈ coefficientLocalPolynomials q := by
  apply (Polynomial.lifts_iff_liftsRing _ _).mp
  exact Polynomial.X_mem_lifts (coefficientLocalRing q).subtype

theorem det_mem_coefficientLocalPolynomials {q : ℕ} [Fact q.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ[X])
    (hA : ∀ i j, A i j ∈ coefficientLocalPolynomials q) :
    A.det ∈ coefficientLocalPolynomials q := by
  rw [Matrix.det_apply']
  apply (coefficientLocalPolynomials q).sum_mem
  intro σ hσ
  apply (coefficientLocalPolynomials q).mul_mem
  · exact intCast_mem (coefficientLocalPolynomials q) _
  · exact (coefficientLocalPolynomials q).prod_mem fun i hi => hA _ _

theorem twenty_scaled_base_den {N q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hH : 27 * N < q ^ 2)
    (r k : Fin (twenty.n N)) :
    (((q : ℚ)^2 * measureBaseMatrix twenty N r k).den : ZMod q) ≠ 0 := by
  change (((q : ℚ)^2 * filteredEntryRat twenty 0 N r.val k.val).den : ZMod q) ≠ 0
  unfold filteredEntryRat
  rw [mul_sum]
  apply (rational_residue_sum _ _ ?_).1
  intro v hv
  have hraw : (((q : ℚ)^2 * rawEntryRat twenty 0 N r.val
      (twenty.b N + k.val + v)).den : ZMod q) ≠ 0 := by
    apply (raw_zero_digit_reduction twenty hq2 (by simpa only [twenty_H] using hH) ?_).1
    have hk := k.isLt
    have hv' := Finset.mem_range.mp hv
    change k.val < 20 * N at hk
    change v < 1 * N + 1 at hv'
    rw [twenty_H]
    change 3 * N + k.val + v < 27 * N
    omega
  have he : (q : ℚ)^2 * (filterCoeffRat twenty N v *
      rawEntryRat twenty 0 N r.val (twenty.b N + k.val + v)) =
      filterCoeffRat twenty N v * ((q : ℚ)^2 *
        rawEntryRat twenty 0 N r.val (twenty.b N + k.val + v)) := by ring
  rw [he]
  exact (rational_residue_mul (filterCoeff_den twenty N v) hraw).1

theorem twenty_catalan_matrix_den {N q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (r k : Fin (twenty.n N)) :
    ((measureCatalanMatrix twenty N r k).den : ZMod q) ≠ 0 := by
  change ((filteredCatalanCoeffRat twenty N r.val k.val).den : ZMod q) ≠ 0
  unfold filteredCatalanCoeffRat
  apply (rational_residue_sum _ _ ?_).1
  intro v hv
  exact (rational_residue_mul (filterCoeff_den twenty N v)
    (rawCatalanCoeff_den twenty hq2 N r.val (twenty.b N + k.val + v))).1

theorem twenty_recycling_geometry {N q : ℕ}
    (hbig : 1000000000000 ≤ N) (hNq : N < q) :
    q ≠ 2 ∧ 27*N < q^2 ∧
      2*Real.sqrt (OAI.InternalCatalan.H N) < (q : ℝ) := by
  have hNR : (1000000000000 : ℝ) ≤ N := by exact_mod_cast hbig
  have hqR : (N : ℝ) < q := by exact_mod_cast hNq
  have hs := Real.sq_sqrt (Nat.cast_nonneg (OAI.InternalCatalan.H N))
  have hs0 := Real.sqrt_nonneg (OAI.InternalCatalan.H N : ℝ)
  have hh : (OAI.InternalCatalan.H N : ℝ)=65*(N : ℝ) := by
    simp only [OAI.InternalCatalan.H, Nat.cast_mul, Nat.cast_ofNat]
  rw [hh] at hs hs0 ⊢
  refine ⟨by omega, ?_, ?_⟩
  · have h : (27 : ℝ)*N < (q : ℝ)^2 := by nlinarith
    exact_mod_cast h
  · nlinarith

theorem twentyDenomExp_recycling {N q : ℕ}
    (hbig : 1000000000000 ≤ N) (hNq : N < q) (hqN : q ≤ 2*N) :
    twentyDenomExp N q=40*N := by
  have hg := twenty_recycling_geometry hbig hNq
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hr : (q : ℝ)/N ≤ 2 := by
    apply (div_le_iff₀ hN).mpr
    exact_mod_cast hqN
  rw [twentyDenomExp, ite_eq_right hg.1, ite_eq_right (not_le.mpr hg.2.2),
    twentyCombinedOddLoss, twentyOddLoss_segment0 _ (by linarith),
    twentyPrimeGain_left (by linarith)]
  simp only [zero_mul, sub_zero]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.mul_comm] using
    (Nat.ceil_natCast (R := ℝ) (40*N))

theorem twentyDenomBound_recycling_dvd {N q : ℕ} [hq : Fact q.Prime]
    (hbig : 1000000000000 ≤ N) (hNq : N < q) (hqN : q ≤ 2*N) :
    q^(40*N) ∣ twentyDenomBound N := by
  have hmem : q ∈ measurePrimes N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hq.out.pos, ?_⟩, hq.out⟩
    unfold OAI.InternalCatalan.H
    omega
  rw [← twentyDenomExp_recycling hbig hNq hqN]
  exact Finset.dvd_prod_of_mem (fun p => p^twentyDenomExp N p) hmem

theorem int_prime_power_dvd_of_div_den {q : ℕ} [hq : Fact q.Prime]
    (a : ℤ) (k : ℕ)
    (h : ((((a : ℚ)/(q : ℚ)^k).den) : ZMod q) ≠ 0) :
    (q : ℤ)^k ∣ a := by
  let x : ℚ := (a : ℚ)/(q : ℚ)^k
  have hd : ¬q ∣ x.den := by
    intro hv
    exact h ((ZMod.natCast_eq_zero_iff x.den q).mpr hv)
  have hco : IsCoprime ((q : ℤ)^k) (x.den : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using ((hq.out.coprime_iff_not_dvd.mpr hd).pow_left k)
  apply hco.dvd_of_dvd_mul_right
  have hx : (a : ℚ)*(x.den : ℚ) = (x.num : ℚ)*(q : ℚ)^k := by
    have hn := Rat.mul_den_eq_num x
    dsimp only [x] at hn
    have hq0 : (q : ℚ)^k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.out.ne_zero)
    field_simp at hn
    nlinarith only [hn]
  have hxi : a*(x.den : ℤ)=x.num*(q : ℤ)^k := by exact_mod_cast hx
  exact ⟨x.num, by rw [hxi]; ring⟩

/-- Rescaling an affine determinant is an identity of polynomials. -/
theorem affine_det_rescale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℚ) (c : ℚ) (hc : c ≠ 0) :
    (C c) ^ Fintype.card ι *
        (det ((X : ℚ[X]) • B.map C + A.map C)).comp (C c⁻¹ * X) =
      det ((X : ℚ[X]) • B.map C + (c • A).map C) := by
  have hm := RingHom.map_det (Polynomial.compRingHom (C c⁻¹ * X))
    ((X : ℚ[X]) • B.map C + A.map C)
  change (C c)^Fintype.card ι *
    (Polynomial.compRingHom (C c⁻¹ * X))
      (det ((X : ℚ[X]) • B.map C + A.map C)) = _
  rw [hm, ← Matrix.det_smul]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply,
    smul_eq_mul, RingHom.mapMatrix_apply, Polynomial.coe_compRingHom,
    Polynomial.add_comp, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.C_comp]
  rw [mul_add]
  simp only [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc,
    Polynomial.C_1, one_mul]

/-- The canonical polynomial at `X/q²` has q-integral coefficients. -/
theorem twentyMeasureIntPoly_rescaled_local {N q : ℕ} [hq : Fact q.Prime]
    (hbig : 1000000000000 ≤ N) (hNq : N < q) (hqN : q ≤ 2*N) :
    ((twentyMeasureIntPoly N).map (Int.castRingHom ℚ)).comp
      (C (((q : ℚ)^2)⁻¹) * X) ∈ coefficientLocalPolynomials q := by
  obtain ⟨d, hd⟩ := twentyDenomBound_recycling_dvd hbig hNq hqN
  have hg := twenty_recycling_geometry hbig hNq
  let A := measureBaseMatrix twenty N
  let B := measureCatalanMatrix twenty N
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hpow : (C ((q : ℚ)^2) : ℚ[X])^(twenty.n N) = C ((q : ℚ)^(40*N)) := by
    rw [← Polynomial.C_pow]
    congr 1
    change ((q : ℚ)^2)^(20*N)=(q : ℚ)^(40*N)
    rw [← pow_mul]
    congr 1
    omega
  have hs := affine_det_rescale A B ((q : ℚ)^2) (pow_ne_zero _ hq0)
  rw [Fintype.card_fin, hpow] at hs
  have hid : ((twentyMeasureIntPoly N).map (Int.castRingHom ℚ)).comp
      (C (((q : ℚ)^2)⁻¹) * X) =
      C ((((18*N)! : ℕ) : ℚ) * (d : ℚ)) *
        det ((X : ℚ[X]) • B.map C + (((q : ℚ)^2) • A).map C) := by
    rw [(twentyMeasureIntPoly_spec hbig).1]
    rw [Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.C_comp]
    have hdQ : (twentyDenomBound N : ℚ) = (q : ℚ)^(40*N)*(d : ℚ) := by
      exact_mod_cast hd
    rw [hdQ, Polynomial.C_mul]
    change _ = C _ * _
    rw [← hs]
    dsimp only [A, B]
    unfold deltaPoly
    rw [Polynomial.C_mul]
    ring
  rw [hid]
  apply (coefficientLocalPolynomials q).mul_mem
  · have hc : ((((18*N)! : ℕ) : ℚ) * (d : ℚ)).den = 1 := by
      calc
        _ = ((((18*N)! * d : ℕ) : ℚ)).den := by
          congr 1
          exact (Nat.cast_mul _ _).symm
        _ = 1 := Rat.den_natCast _
    apply C_mem_coefficientLocalPolynomials
    rw [hc]
    simpa only [Nat.cast_one] using (one_ne_zero : (1 : ZMod q) ≠ 0)
  · apply det_mem_coefficientLocalPolynomials
    intro r k
    change X * C (B r k) + C ((q : ℚ)^2 * A r k) ∈ _
    apply (coefficientLocalPolynomials q).add_mem
    · exact (coefficientLocalPolynomials q).mul_mem (X_mem_coefficientLocalPolynomials q)
        (C_mem_coefficientLocalPolynomials (twenty_catalan_matrix_den hg.1 r k))
    · exact C_mem_coefficientLocalPolynomials (twenty_scaled_base_den hg.1 hg.2.1 r k)

/-- Coefficientwise recycling divisibility for every prime `N < q ≤ 2N`. -/
theorem twentyMeasureIntPoly_coeff_prime_pow_dvd {N q : ℕ} [Fact q.Prime]
    (hbig : 1000000000000 ≤ N) (hNq : N < q) (hqN : q ≤ 2*N) (j : ℕ) :
    (q : ℤ)^(2*j) ∣ (twentyMeasureIntPoly N).coeff j := by
  apply int_prime_power_dvd_of_div_den
  have h := (mem_coefficientLocalPolynomials_iff _).mp
    (twentyMeasureIntPoly_rescaled_local hbig hNq hqN) j
  rw [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at h
  change ((((((twentyMeasureIntPoly N).coeff j : ℤ) : ℚ) *
    (((q : ℚ)^2)⁻¹)^j).den) : ZMod q) ≠ 0 at h
  simpa only [inv_pow, ← pow_mul, div_eq_mul_inv] using h

end
end CatalanMeasure.Parametric
