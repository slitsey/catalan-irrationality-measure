module
public import CatalanMeasure.Parametric.ResidueRank
public import CatalanArchive.CatalanMeasure.Parametric.TwentyCoefficientDivisibility
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentValueContent
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Matrix Finset OAI.InternalCatalan
open scoped BigOperators Nat
noncomputable section

/-- An integral affine perturbation does not change the leading double-pole residue. -/
theorem scaledResidueMatrix_add_integral {p n : ℕ} [Fact p.Prime]
    (A B : Matrix (Fin n) (Fin n) ℚ) (z : ℚ)
    (hA : ∀ i j, (((p : ℚ)^2 * A i j).den : ZMod p) ≠ 0)
    (hB : ∀ i j, ((B i j).den : ZMod p) ≠ 0)
    (hz : (z.den : ZMod p) ≠ 0) :
    (∀ i j, (((p : ℚ)^2 * (A + z • B) i j).den : ZMod p) ≠ 0) ∧
      scaledResidueMatrix (p := p) (A + z • B) = scaledResidueMatrix A := by
  have hpp : ((((p : ℚ)^2).den) : ZMod p) ≠ 0 := by
    rw [← Nat.cast_pow]
    simp
  have hzero : palindromicRatResidue p ((p : ℚ)^2) = 0 := by
    rw [← Nat.cast_pow]
    simp [palindromicRatResidue]
  have hzb (i j) := (rational_residue_mul hz (hB i j)).1
  have hscaled (i j) := (rational_residue_mul hpp (hzb i j)).1
  constructor
  · intro i j
    change (((p : ℚ)^2 * (A i j + z * B i j)).den : ZMod p) ≠ 0
    rw [mul_add]
    exact (rational_residue_add (hA i j) (hscaled i j)).1
  · ext i j
    change palindromicRatResidue p ((p : ℚ)^2 * (A i j + z * B i j)) = _
    rw [mul_add, palindromicRatResidue_add (hA i j) (hscaled i j),
      palindromicRatResidue_mul hpp (hzb i j), hzero, zero_mul, add_zero]
    rfl

/-- A scalar rank saving survives multiplication by an integer and the full
normalizing prime power. The zero evaluation is handled separately. -/
theorem int_prime_pow_dvd_of_normalized_valuation {p d e : ℕ} [hp : Fact p.Prime]
    (a : ℤ) (c : ℕ) (r : ℚ) (he : e ≤ d)
    (ha : (a : ℚ) = (c : ℚ) * (p : ℚ)^d * r)
    (hr : -((d - e : ℕ) : ℤ) ≤ padicValRat p r) :
    (p : ℤ)^e ∣ a := by
  by_cases haz : a = 0
  · simp [haz]
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast haz
  have hprod : (c : ℚ) * (p : ℚ)^d * r ≠ 0 := by rwa [← ha]
  have hc : (c : ℚ) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).1
  have hrr : r ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hv : padicValRat p (a : ℚ) =
      padicValRat p (c : ℚ) + (d : ℤ) + padicValRat p r := by
    rw [ha, padicValRat.mul (mul_ne_zero hc (pow_ne_zero _ hpq)) hrr,
      padicValRat.mul hc (pow_ne_zero _ hpq), padicValRat.pow,
      padicValRat.self hp.out.one_lt, mul_one]
  have hcv : 0 ≤ padicValRat p (c : ℚ) :=
    rational_valuation_nonneg_of_den_ne_zero (by simp)
  have hsub : ((d - e : ℕ) : ℤ) = (d : ℤ) - (e : ℤ) := by omega
  rw [hsub] at hr
  apply (padicValInt_dvd_iff e a).mpr
  right
  rw [padicValRat.of_int] at hv
  omega

/-- The canonical normalizer contains the full double-pole payment throughout
its flat interval, including the secondary tent window. -/
theorem twentyDenomExp_secondary_flat {N p : ℕ}
    (hbig : 1000000000000 ≤ N) (hNp : N < p) (hupper : 3*p ≤ 22*N) :
    twentyDenomExp N p = 40*N := by
  have hg := twenty_recycling_geometry hbig hNp
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : (p : ℝ)/N ≤ 22/3 := by
    apply (div_le_iff₀ hN).mpr
    have hh : (3 : ℝ)*p ≤ 22*N := by exact_mod_cast hupper
    linarith
  rw [twentyDenomExp, ite_eq_right hg.1, ite_eq_right (not_le.mpr hg.2.2),
    twentyCombinedOddLoss, twentyOddLoss_segment0 _ (by linarith),
    twentyPrimeGain_left hr]
  simp only [zero_mul, sub_zero]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.mul_comm] using
    (Nat.ceil_natCast (R := ℝ) (40*N))

theorem twentyDenomBound_secondary_flat_dvd {N p : ℕ} [hp : Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (hNp : N < p) (hupper : 3*p ≤ 22*N) :
    p^(40*N) ∣ twentyDenomBound N := by
  have hmem : p ∈ measurePrimes N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hp.out.pos, ?_⟩, hp.out⟩
    unfold OAI.InternalCatalan.H
    omega
  rw [← twentyDenomExp_secondary_flat hbig hNp hupper]
  exact Finset.dvd_prod_of_mem (fun q => q^twentyDenomExp N q) hmem

theorem twentyMeasureIntPoly_secondary_rescaled_local {N q : ℕ} [hq : Fact q.Prime]
    (hbig : 1000000000000 ≤ N) (hNq : N < q) (hupper : 3*q ≤ 22*N) :
    ((twentyMeasureIntPoly N).map (Int.castRingHom ℚ)).comp
      (C (((q : ℚ)^2)⁻¹) * X) ∈ coefficientLocalPolynomials q := by
  obtain ⟨d, hd⟩ := twentyDenomBound_secondary_flat_dvd hbig hNq hupper
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


/-- The baseline double-pole coefficient weights hold in the secondary window. -/
theorem twentyMeasureIntPoly_secondary_coeff_weight {N p : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (hNp : N < p) (hupper : 3*p ≤ 22*N) (i : ℕ) :
    (p : ℤ)^(2*i) ∣ (twentyMeasureIntPoly N).coeff i := by
  apply int_prime_power_dvd_of_div_den
  have h := (mem_coefficientLocalPolynomials_iff _).mp
    (twentyMeasureIntPoly_secondary_rescaled_local hbig hNp hupper) i
  rw [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at h
  change ((((((twentyMeasureIntPoly N).coeff i : ℤ) : ℚ) *
    (((p : ℚ)^2)⁻¹)^i).den) : ZMod p) ≠ 0 at h
  simpa only [inv_pow, ← pow_mul, div_eq_mul_inv] using h

/-- An actual rank deficit of the canonical scaled base residue pays for every
integer evaluation of the canonical polynomial. -/
theorem twentyMeasureIntPoly_eval_prime_pow_dvd_of_rank {N p e : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (hNp : N < p) (hupper : 3*p ≤ 22*N)
    (he : e ≤ 20*N)
    (hrank : (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank ≤ 20*N-e)
    (z : ℤ) : (p : ℤ)^e ∣ (twentyMeasureIntPoly N).eval z := by
  have hg := twenty_recycling_geometry hbig hNp
  let A := measureBaseMatrix twenty N
  let B := measureCatalanMatrix twenty N
  have haff := scaledResidueMatrix_add_integral A B (z : ℚ)
    (twenty_scaled_base_den hg.1 hg.2.1) (twenty_catalan_matrix_den hg.1) (by simp)
  have hval := residue_rank_valuation_lower (A + (z : ℚ) • B) haff.1
    (show e ≤ twenty.n N by exact he) (by rw [haff.2]; exact hrank)
  have hdet : (A + (z : ℚ) • B).det = determinantRat twenty (z : ℚ) N := by
    congr 1
    ext r k
    change filteredEntryRat twenty 0 N r.val k.val +
      (z : ℚ)*filteredCatalanCoeffRat twenty N r.val k.val = _
    rw [filteredEntryRat_affine twenty (z : ℚ)]
  rw [hdet] at hval
  have hdimeq : 2*twenty.n N-e = 40*N-e := by change 2*(20*N)-e = _; omega
  rw [hdimeq] at hval
  obtain ⟨d, hd⟩ := twentyDenomBound_secondary_flat_dvd hbig hNp hupper
  apply int_prime_pow_dvd_of_normalized_valuation
    ((twentyMeasureIntPoly N).eval z) ((18*N)! * d)
    (determinantRat twenty (z : ℚ) N) (by omega : e ≤ 40*N) _ hval
  have hs := congrArg (fun f : ℚ[X] => f.eval (z : ℚ)) (twentyMeasureIntPoly_spec hbig).1
  rw [Polynomial.eval_intCast_map, eval_mul, eval_C, eval_mul, eval_C,
    eval_deltaPoly] at hs
  change (((twentyMeasureIntPoly N).eval z : ℤ) : ℚ) = _ at hs
  rw [hs]
  have hdQ : (twentyDenomBound N : ℚ) = (p : ℚ)^(40*N)*(d : ℚ) := by exact_mod_cast hd
  rw [hdQ, Nat.cast_mul]
  ring

/-- Canonical rank-to-coefficient-content bridge. The actual scaled base rank is
the only new arithmetic input; value divisibility is upgraded using its proved
high-coefficient weights. -/
theorem twentyMeasureIntPoly_coeff_prime_pow_dvd_of_rank {N p e : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (hNp : N < p) (hupper : 3*p ≤ 22*N)
    (he : e ≤ N)
    (hrank : (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank ≤ 20*N-e) :
    ∀ i, (p : ℤ)^e ∣ (twentyMeasureIntPoly N).coeff i := by
  apply coeff_prime_pow_dvd_of_weighted_eval (twentyMeasureIntPoly N) (by omega : e ≤ 2*p)
  · exact twentyMeasureIntPoly_secondary_coeff_weight hbig hNp hupper
  · exact twentyMeasureIntPoly_eval_prime_pow_dvd_of_rank hbig hNp hupper (by omega) hrank

/-- The rank-to-content implication specialized to the open tent window. -/
theorem twentyMeasureIntPoly_tent_coeff_prime_pow_dvd_of_rank
    {N p e : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (hlower : 52*N < 9*p) (hupper : 7*p < 44*N)
    (he : e ≤ N)
    (hrank : (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank ≤ 20*N-e) :
    ∀ i, (p : ℤ)^e ∣ (twentyMeasureIntPoly N).coeff i := by
  exact twentyMeasureIntPoly_coeff_prime_pow_dvd_of_rank hbig (by omega) (by omega) he hrank

end
end CatalanMeasure.Parametric
