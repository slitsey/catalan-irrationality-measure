module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRankContent
public import CatalanArchive.CatalanMeasure.Parametric.U3Rank
@[expose] public section

/-!
# From the U3 rank bound to coefficient content (primes in `(8N, 9N)`)

Over the primes `8N < p < 9N` the canonical normalizer has `p`-exponent
`40N - (26N - 3p)^+`, the nullity of the scaled base residue is at least
`18N - 2p - 1`, and the difference `thirdTentExponent N p` divides every
coefficient of the canonical integer polynomial.
-/

namespace CatalanMeasure.Parametric
open Polynomial Matrix Finset OAI.InternalCatalan
open scoped BigOperators Nat
noncomputable section

/-- The new content exponent at a prime in the third band. -/
def thirdTentExponent (N p : ℕ) : ℕ :=
  (min ((p : ℤ) - 8 * N - 1) (18 * (N : ℤ) - 2 * p - 1)).toNat

theorem twentyDenomExp_third {N p : ℕ} (hbig : 1000000000000 ≤ N) (h8 : 8 * N < p)
    (h9 : p < 9 * N) : twentyDenomExp N p = 40 * N - (26 * N - 3 * p) := by
  have hg := twenty_recycling_geometry hbig (show N < p by omega)
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx8 : (8 : ℝ) < (p : ℝ) / N := by
    rw [lt_div_iff₀ hN]; exact_mod_cast (by omega : 8 * N < p)
  have hx9 : (p : ℝ) / N < 9 := by
    rw [div_lt_iff₀ hN]; exact_mod_cast (by omega : p < 9 * N)
  rw [twentyDenomExp, ite_eq_right hg.1, ite_eq_right (not_le.mpr hg.2.2),
    twentyCombinedOddLoss, twentyOddLoss_segment0 _ (by linarith)]
  by_cases h3 : 3 * p ≤ 26 * N
  · have hx : (p : ℝ) / N ≤ 26 / 3 := by
      rw [div_le_iff₀ hN]
      have : (3 : ℝ) * p ≤ 26 * N := by exact_mod_cast h3
      linarith
    rw [twentyPrimeGain_fall (by linarith) hx]
    have e : (N : ℝ) * (40 - 0 * ((p : ℝ) / N) - (26 - 3 * ((p : ℝ) / N))) =
        ((14 * N + 3 * p : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    rw [e, Nat.ceil_natCast]
    omega
  · have hx : 26 / 3 ≤ (p : ℝ) / N := by
      rw [le_div_iff₀ hN]
      have : (26 : ℝ) * N < 3 * p := by exact_mod_cast (by omega : 26 * N < 3 * p)
      linarith
    rw [twentyPrimeGain_right hx]
    have e : (N : ℝ) * (40 - 0 * ((p : ℝ) / N) - 0) = ((40 * N : ℕ) : ℝ) := by
      push_cast; ring
    rw [e, Nat.ceil_natCast]
    omega

theorem twentyDenomBound_third_dvd {N p : ℕ} [hp : Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (h8 : 8 * N < p) (h9 : p < 9 * N) :
    p ^ (40 * N - (26 * N - 3 * p)) ∣ twentyDenomBound N := by
  have hmem : p ∈ measurePrimes N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hp.out.pos, ?_⟩, hp.out⟩
    unfold OAI.InternalCatalan.H
    omega
  rw [← twentyDenomExp_third hbig h8 h9]
  exact Finset.dvd_prod_of_mem (fun q => q ^ twentyDenomExp N q) hmem

theorem twentyMeasureIntPoly_third_rescaled_local {N q : ℕ} [hq : Fact q.Prime]
    (hbig : 1000000000000 ≤ N) (h8 : 8 * N < q) (h9 : q < 9 * N) :
    C ((q : ℚ) ^ (26 * N - 3 * q)) *
      ((twentyMeasureIntPoly N).map (Int.castRingHom ℚ)).comp
        (C (((q : ℚ) ^ 2)⁻¹) * X) ∈ coefficientLocalPolynomials q := by
  obtain ⟨d, hd⟩ := twentyDenomBound_third_dvd hbig h8 h9
  have hg := twenty_recycling_geometry hbig (show N < q by omega)
  let A := measureBaseMatrix twenty N
  let B := measureCatalanMatrix twenty N
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hpow : (C ((q : ℚ) ^ 2) : ℚ[X]) ^ (twenty.n N) = C ((q : ℚ) ^ (40 * N)) := by
    rw [← Polynomial.C_pow]
    congr 1
    change ((q : ℚ) ^ 2) ^ (20 * N) = (q : ℚ) ^ (40 * N)
    rw [← pow_mul]
    congr 1
    omega
  have hs := affine_det_rescale A B ((q : ℚ) ^ 2) (pow_ne_zero _ hq0)
  rw [Fintype.card_fin, hpow] at hs
  have hid : C ((q : ℚ) ^ (26 * N - 3 * q)) *
      ((twentyMeasureIntPoly N).map (Int.castRingHom ℚ)).comp (C (((q : ℚ) ^ 2)⁻¹) * X) =
      C ((((18 * N) ! : ℕ) : ℚ) * (d : ℚ)) *
        det ((X : ℚ[X]) • B.map C + (((q : ℚ) ^ 2) • A).map C) := by
    rw [(twentyMeasureIntPoly_spec hbig).1]
    rw [Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.C_comp]
    have hdQ : (twentyDenomBound N : ℚ) =
        (q : ℚ) ^ (40 * N - (26 * N - 3 * q)) * (d : ℚ) := by exact_mod_cast hd
    have hexp : (q : ℚ) ^ (26 * N - 3 * q) * (q : ℚ) ^ (40 * N - (26 * N - 3 * q)) =
        (q : ℚ) ^ (40 * N) := by
      rw [← pow_add]; congr 1; omega
    rw [hdQ, Polynomial.C_mul]
    change _ = C _ * _
    rw [← hs]
    dsimp only [A, B]
    unfold deltaPoly
    rw [Polynomial.C_mul, ← hexp]
    simp only [Polynomial.C_mul]
    ring
  rw [hid]
  apply (coefficientLocalPolynomials q).mul_mem
  · have hc : ((((18 * N) ! : ℕ) : ℚ) * (d : ℚ)).den = 1 := by
      calc
        _ = ((((18 * N) ! * d : ℕ) : ℚ)).den := by
          congr 1
          exact (Nat.cast_mul _ _).symm
        _ = 1 := Rat.den_natCast _
    apply C_mem_coefficientLocalPolynomials
    rw [hc]
    simpa only [Nat.cast_one] using (one_ne_zero : (1 : ZMod q) ≠ 0)
  · apply det_mem_coefficientLocalPolynomials
    intro r k
    change X * C (B r k) + C ((q : ℚ) ^ 2 * A r k) ∈ _
    apply (coefficientLocalPolynomials q).add_mem
    · exact (coefficientLocalPolynomials q).mul_mem (X_mem_coefficientLocalPolynomials q)
        (C_mem_coefficientLocalPolynomials (twenty_catalan_matrix_den hg.1 r k))
    · exact C_mem_coefficientLocalPolynomials (twenty_scaled_base_den hg.1 hg.2.1 r k)

theorem twentyMeasureIntPoly_third_tail {N p : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (h8 : 8 * N < p) (h9 : p < 9 * N) (i : ℕ) :
    (p : ℤ) ^ (2 * i) ∣ (p : ℤ) ^ (26 * N - 3 * p) * (twentyMeasureIntPoly N).coeff i := by
  apply int_prime_power_dvd_of_div_den
  have h := (mem_coefficientLocalPolynomials_iff _).mp
    (twentyMeasureIntPoly_third_rescaled_local hbig h8 h9) i
  rw [coeff_C_mul, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e : (((((p : ℤ) ^ (26 * N - 3 * p) * (twentyMeasureIntPoly N).coeff i : ℤ)) : ℚ) /
      (p : ℚ) ^ (2 * i)) = (p : ℚ) ^ (26 * N - 3 * p) *
        ((((twentyMeasureIntPoly N).coeff i : ℤ) : ℚ) * (((p : ℚ) ^ 2)⁻¹) ^ i) := by
    push_cast
    rw [inv_pow, ← pow_mul]
    field_simp
  rw [e]
  exact h

theorem twentyMeasureIntPoly_third_coeff_tail {N p : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (h8 : 8 * N < p) (h9 : p < 9 * N) {e i : ℕ}
    (he : e + (26 * N - 3 * p) ≤ 2 * i) :
    (p : ℤ) ^ e ∣ (twentyMeasureIntPoly N).coeff i := by
  have hp0 : (p : ℤ) ^ (26 * N - 3 * p) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have h := twentyMeasureIntPoly_third_tail hbig h8 h9 i
  have h2 : (p : ℤ) ^ (26 * N - 3 * p) * (p : ℤ) ^ e ∣
      (p : ℤ) ^ (26 * N - 3 * p) * (twentyMeasureIntPoly N).coeff i := by
    refine dvd_trans ?_ h
    rw [← pow_add, add_comm]
    exact pow_dvd_pow _ he
  exact (mul_dvd_mul_iff_left hp0).mp h2

theorem twentyMeasureIntPoly_third_eval {N p : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (h8 : 8 * N < p) (h9 : p < 9 * N)
    (hrank : (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank +
      (18 * N - 2 * p - 1) ≤ 20 * N) (z : ℤ) :
    (p : ℤ) ^ (thirdTentExponent N p) ∣ (twentyMeasureIntPoly N).eval z := by
  have hg := twenty_recycling_geometry hbig (show N < p by omega)
  let A := measureBaseMatrix twenty N
  let B := measureCatalanMatrix twenty N
  have haff := scaledResidueMatrix_add_integral A B (z : ℚ)
    (twenty_scaled_base_den hg.1 hg.2.1) (twenty_catalan_matrix_den hg.1) (by simp)
  have hval := residue_rank_valuation_lower (A + (z : ℚ) • B) haff.1
    (show 18 * N - 2 * p - 1 ≤ twenty.n N by change _ ≤ 20 * N; omega)
    (by
      rw [haff.2]
      change (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank ≤
        20 * N - (18 * N - 2 * p - 1)
      omega)
  have hdet : (A + (z : ℚ) • B).det = determinantRat twenty (z : ℚ) N := by
    congr 1
    ext r k
    change filteredEntryRat twenty 0 N r.val k.val +
      (z : ℚ) * filteredCatalanCoeffRat twenty N r.val k.val = _
    rw [filteredEntryRat_affine twenty (z : ℚ)]
  rw [hdet] at hval
  obtain ⟨d, hd⟩ := twentyDenomBound_third_dvd hbig h8 h9
  have hs := congrArg (fun f : ℚ[X] => f.eval (z : ℚ)) (twentyMeasureIntPoly_spec hbig).1
  rw [Polynomial.eval_intCast_map, eval_mul, eval_C, eval_mul, eval_C, eval_deltaPoly] at hs
  change (((twentyMeasureIntPoly N).eval z : ℤ) : ℚ) = _ at hs
  have hD : 40 * N - (26 * N - 3 * p) ≥ thirdTentExponent N p := by
    unfold thirdTentExponent; omega
  apply int_prime_pow_dvd_of_normalized_valuation
    ((twentyMeasureIntPoly N).eval z) ((18 * N)! * d)
    (determinantRat twenty (z : ℚ) N) hD
  · rw [hs]
    have hdQ : (twentyDenomBound N : ℚ) = (p : ℚ) ^ (40 * N - (26 * N - 3 * p)) * (d : ℚ) := by
      exact_mod_cast hd
    rw [hdQ, Nat.cast_mul]
    ring
  · have e : 40 * N - (26 * N - 3 * p) - thirdTentExponent N p = 2 * twenty.n N - (18 * N - 2 * p - 1) := by
      unfold thirdTentExponent; change _ = 2 * (20 * N) - _; omega
    rw [e]
    exact hval

/-- The U3 rank bound gives `p^e` dividing every coefficient. -/
theorem twentyMeasureIntPoly_third_coeff_dvd {N p : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (h8 : 8 * N < p) (h9 : p < 9 * N)
    (hrank : (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank +
      (18 * N - 2 * p - 1) ≤ 20 * N) :
    ∀ i, (p : ℤ) ^ (thirdTentExponent N p) ∣ (twentyMeasureIntPoly N).coeff i := by
  apply coeff_prime_pow_dvd_of_eval_and_tail
  · intro i hi
    apply twentyMeasureIntPoly_third_coeff_tail hbig h8 h9
    unfold thirdTentExponent; omega
  · exact twentyMeasureIntPoly_third_eval hbig h8 h9 hrank

end
end CatalanMeasure.Parametric
