module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Ring.Star
public import OAI.NumberTheory.Catalan.Determinants.TwoAdicSmoothedMinor
public import OAI.NumberTheory.Catalan.Estimates.OddPhysicalCombination

@[expose] public section

namespace OAI


noncomputable section

namespace InternalCatalan

open scoped BigOperators

def momentStartingRat (i j : ℕ) : ℚ :=
  if j ≤ i then boundaryMinus (i - j) else boundaryPlus (j - i)

theorem momentRat_reverse_diagonal (i j : ℕ) :
    momentRat i j = momentStartingRat i j -
      ∑ ell ∈ Finset.range (min i j),
        momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ) := by
  by_cases hji : j ≤ i
  · rw [momentRat_of_le hji, momentStartingRat, ite_eq_left hji, min_eq_right hji]
    congr 1
    calc
      _ = ∑ ell ∈ Finset.range j,
          momentScalar (i - j + (j - 1 - ell)) / (((j - 1 - ell) + 1 : ℕ) : ℚ) :=
        (Finset.sum_range_reflect
          (fun k => momentScalar (i - j + k) / ((k + 1 : ℕ) : ℚ)) j).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ell hell
        have he := Finset.mem_range.mp hell
        rw [momentScalarPred, ite_eq_right (by omega : i - ell ≠ 0)]
        congr 2 <;> omega
  · have hij : i < j := by omega
    rw [momentRat_of_lt hij, momentStartingRat, ite_eq_right hji, min_eq_left (Nat.le_of_lt hij)]
    congr 1
    calc
      _ = ∑ ell ∈ Finset.range i,
          momentScalar (i - 1 - ell) / ((j - i + (i - 1 - ell) + 1 : ℕ) : ℚ) :=
        (Finset.sum_range_reflect
          (fun k => momentScalar k / ((j - i + k + 1 : ℕ) : ℚ)) i).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ell hell
        have he := Finset.mem_range.mp hell
        rw [momentScalarPred, ite_eq_right (by omega : i - ell ≠ 0)]
        congr 2 <;> omega

theorem momentScalarPred_central_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz : z < 2 * p) :
    (((p : ℚ) * momentScalarPred z).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * momentScalarPred z) =
        if p ≤ z then 2 * (oddPrimeWeight p).coeff (2 * p - 1 - z) else 0 := by
  have hz2 : z < p ^ 2 := by nlinarith [hp.out.two_le]
  have h := momentScalarPred_prime_digit_reduction hp2 hz2
  refine ⟨h.1, ?_⟩
  have hres : palindromicRatResidue p ((p : ℚ) * momentScalarPred z) =
      (oddPrimeWeight p).coeff (p - 1 - z % p) *
        palindromicRatResidue p (momentScalarPred (z / p)) := h.2.2
  rw [hres]
  by_cases hpz : p ≤ z
  · have hq : z / p = 1 := by
      rw [show z = p * 1 + (z - p) by omega, Nat.mul_add_div hp.out.pos,
        Nat.div_eq_of_lt (by omega : z - p < p), add_zero]
    have hr : z % p = z - p := by
      have he := Nat.mod_add_div z p
      rw [hq, Nat.mul_one] at he
      omega
    have he : p - 1 - (z - p) = 2 * p - 1 - z := by omega
    rw [ite_eq_left hpz, hq, hr, he]
    have hs : palindromicRatResidue p (momentScalarPred 1) = 2 := by
      norm_num [momentScalarPred, momentScalar_zero, palindromicRatResidue]
    rw [hs, mul_comm]
  · rw [ite_eq_right hpz, Nat.div_eq_of_lt (by omega : z < p), momentScalarPred_zero]
    norm_num [palindromicRatResidue]

theorem momentStartingRat_central_den_ne_zero {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hj : j < p) (hi : i < p + j) :
    ((momentStartingRat i j).den : ZMod p) ≠ 0 := by
  apply rational_den_ne_zero_of_valuation_nonneg
  unfold momentStartingRat
  split_ifs with hji
  · exact boundaryMinus_odd_prime_valuation_nonneg hp.out hp2 _ (by omega)
  · exact boundaryPlus_odd_prime_valuation_nonneg hp.out hp2 _ (by omega)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem momentScalarPred_central_div_reduction {p i j ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hj : j < p) (hi : i < p + j) (hell : ell < min i j) :
    (((p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ))) =
          if p + ell ≤ i then
            (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i)) /
              ((j - ell : ℕ) : ZMod p)
          else 0 := by
  have helli : ell < i := lt_of_lt_of_le hell (Nat.min_le_left i j)
  have hellj : ell < j := lt_of_lt_of_le hell (Nat.min_le_right i j)
  have hden0 : 0 < j - ell := by omega
  have hdenlt : j - ell < p := by omega
  have hden : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hden0 hdenlt)
      ((ZMod.natCast_eq_zero_iff (j - ell) p).mp hzero)
  have hscalar := momentScalarPred_central_reduction hp2
    (show i - ell < 2 * p by omega)
  have hrecip := nat_fraction_reduced_residue (p := p) 1 (j - ell) hden
  have hrecipden : ((1 / ((j - ell : ℕ) : ℚ)).den : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_one] using hrecip.1
  have hrecipR : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
      1 / ((j - ell : ℕ) : ZMod p) := by
    simpa only [palindromicRatResidue, Nat.cast_one] using hrecip.2
  have hprod := rational_residue_mul hscalar.1 hrecipden
  have heq : (p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ)) =
      ((p : ℚ) * momentScalarPred (i - ell)) * (1 / ((j - ell : ℕ) : ℚ)) := by ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hprod.1
  · rw [heq, palindromicRatResidue_mul hscalar.1 hrecipden, hscalar.2, hrecipR]
    by_cases hle : p + ell ≤ i
    · have hscalarle : p ≤ i - ell := by omega
      have hindex : 2 * p - 1 - (i - ell) = 2 * p + ell - 1 - i := by omega
      rw [ite_eq_left hle, ite_eq_left hscalarle, hindex]
      ring
    · have hscalarnot : ¬p ≤ i - ell := by omega
      rw [ite_eq_right hle, ite_eq_right hscalarnot, zero_mul]

theorem momentRat_central_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hj : j < p) (hi : i < p + j) :
    (((p : ℚ) * momentRat i j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * momentRat i j) =
        -(∑ ell ∈ Finset.range (min i j),
          if p + ell ≤ i then
            (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i)) /
              ((j - ell : ℕ) : ZMod p)
          else 0) := by
  let f : ℕ → ℚ := fun ell =>
    (p : ℚ) * (momentScalarPred (i - ell) / ((j - ell : ℕ) : ℚ))
  have hterm (ell : ℕ) (hell : ell ∈ Finset.range (min i j)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f ell) =
          if p + ell ≤ i then
            (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i)) /
              ((j - ell : ℕ) : ZMod p)
          else 0 :=
    momentScalarPred_central_div_reduction hp2 hj hi (Finset.mem_range.mp hell)
  have hsum := rational_residue_sum (Finset.range (min i j)) f
    (fun ell hell => (hterm ell hell).1)
  have hstart := momentStartingRat_central_den_ne_zero hp2 hj hi
  have hstartmul := rational_residue_mul (a := (p : ℚ)) (by simp) hstart
  have hstartR : palindromicRatResidue p ((p : ℚ) * momentStartingRat i j) = 0 := by
    rw [palindromicRatResidue_mul (by simp) hstart]
    simp [palindromicRatResidue]
  have hstrip : (p : ℚ) * momentRat i j =
      (p : ℚ) * momentStartingRat i j - ∑ ell ∈ Finset.range (min i j), f ell := by
    simp only [momentRat_reverse_diagonal, mul_sub, Finset.mul_sum, f]
  have hdiff := rational_residue_sub hstartmul.1 hsum.1
  refine ⟨?_, ?_⟩
  · rw [hstrip]
    exact hdiff.1
  · rw [hstrip, palindromicRatResidue_sub hstartmul.1 hsum.1, hstartR, zero_sub]
    congr 1
    calc
      palindromicRatResidue p (∑ ell ∈ Finset.range (min i j), f ell) =
          ∑ ell ∈ Finset.range (min i j), palindromicRatResidue p (f ell) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun ell hell => (hterm ell hell).2)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem oddPrime_central_strip_range {R : Type*} [Semiring R] {p H i j : ℕ}
    (hp : 0 < p) (hpH : p ≤ H) (hi : i < H) (hj : H - p ≤ j) (f : ℕ → R) :
    (∑ ell ∈ Finset.range (min i j), if p + ell ≤ i then f ell else 0) =
      ∑ ell ∈ Finset.range (H - p), if p + ell ≤ i then f ell else 0 := by
  classical
  refine Finset.sum_bij_ne_zero (fun ell _ _ => ell) ?_ ?_ ?_ ?_
  · intro ell hell hf
    have hactive : p + ell ≤ i := by
      by_contra h
      exact hf (ite_eq_right h)
    exact Finset.mem_range.mpr (by omega)
  · intro ell hell hf ell' hell' hf' heq
    exact heq
  · intro ell hell hf
    have hactive : p + ell ≤ i := by
      by_contra h
      exact hf (ite_eq_right h)
    have hell' := Finset.mem_range.mp hell
    refine ⟨ell, Finset.mem_range.mpr (by omega), hf, rfl⟩
  · intro ell hell hf
    rfl

theorem rowP_momentRat_central_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) :
    (((p : ℚ) * (∑ t ∈ Finset.range (H N),
      ((rowP N r).coeff t : ℚ) * momentRat t j)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * (∑ t ∈ Finset.range (H N),
        ((rowP N r).coeff t : ℚ) * momentRat t j)) =
        -(∑ ell ∈ Finset.range (H N - p),
          (2 * oddPrimeExtractedP p N r ell 2) / ((j - ell : ℕ) : ZMod p)) := by
  let f : ℕ → ℚ := fun t => ((rowP N r).coeff t : ℚ) * ((p : ℚ) * momentRat t j)
  let c : ℕ → ℕ → ZMod p := fun t ell =>
    if p + ell ≤ t then (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t)) /
      ((j - ell : ℕ) : ZMod p) else 0
  have hterm (t : ℕ) (ht : t ∈ Finset.range (H N)) :
      ((f t).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (f t) = ((rowP N r).coeff t : ZMod p) *
        (-(∑ ell ∈ Finset.range (H N - p), c t ell)) := by
    have ht' := Finset.mem_range.mp ht
    have hm := momentRat_central_reduction hp2 hj (show t < p + j by omega)
    have hprod := rational_residue_mul (p := p) (a := ((rowP N r).coeff t : ℚ))
      (by simp) hm.1
    have htrim := oddPrime_central_strip_range hp.out.pos hpH ht' hjlo
      (fun ell => (2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t)) /
        ((j - ell : ℕ) : ZMod p))
    refine ⟨hprod.1, ?_⟩
    change palindromicRatResidue p
      (((rowP N r).coeff t : ℚ) * ((p : ℚ) * momentRat t j)) = _
    rw [palindromicRatResidue_mul (by simp) hm.1, palindromicRatResidue_intCast,
      hm.2, htrim]
  have hs := rational_residue_sum (Finset.range (H N)) f (fun t ht => (hterm t ht).1)
  have hscale : (p : ℚ) * (∑ t ∈ Finset.range (H N),
      ((rowP N r).coeff t : ℚ) * momentRat t j) = ∑ t ∈ Finset.range (H N), f t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [f]
    ring
  let P : (ZMod p)[X] := (rowP N r).map (Int.castRingHom (ZMod p))
  have hP : ∀ t, H N ≤ t → P.coeff t = 0 := by
    intro t ht
    simp only [P, coeff_map, rowP_coeff_eq_zero_of_ge hN ht, map_zero]
  have hcast (a : ℤ) : (Int.castRingHom (ZMod p)) a = (a : ZMod p) := rfl
  have hcoefficient (ell : ℕ) :
      (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) * c t ell) =
        (2 * oddPrimeExtractedP p N r ell 2) / ((j - ell : ℕ) : ZMod p) := by
    have hcoef := oddPrime_central_P_coefficient (ell := ell) hp.out.pos hH P hP
    have hcoef' :
        (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
          (if p + ell ≤ t then 2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - t) else 0)) =
          2 * oddPrimeExtractedP p N r ell 2 := by
      simpa only [P, coeff_map, hcast, oddPrimeExtractedP] using hcoef
    rw [← hcoef']
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [c]
    split_ifs <;> ring
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hs.1
  · rw [hscale]
    calc
      palindromicRatResidue p (∑ t ∈ Finset.range (H N), f t) =
          ∑ t ∈ Finset.range (H N), palindromicRatResidue p (f t) := hs.2
      _ = ∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
          (-(∑ ell ∈ Finset.range (H N - p), c t ell)) :=
        Finset.sum_congr rfl (fun t ht => (hterm t ht).2)
      _ = -(∑ ell ∈ Finset.range (H N - p), ∑ t ∈ Finset.range (H N),
          ((rowP N r).coeff t : ZMod p) * c t ell) := by
        simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro ell hell
        exact hcoefficient ell

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def oddPrimeLeadingV (p N r ell : ℕ) [Fact p.Prime] : ZMod p :=
  2 * oddPrimeExtractedP p N r ell 2 -
    (3 / 2 : ZMod p) * oddPrimeExtractedD p N r ell 1

theorem rawCatalanTerm_prime_reduction {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) (N r j : ℕ) :
    (((p : ℚ) * z * rawCatalanCoeffRat N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * z * rawCatalanCoeffRat N r j) = 0 := by
  have hpz := rational_residue_mul (p := p) (a := (p : ℚ)) (by simp) hz
  have hfull := rational_residue_mul hpz.1
    (rawCatalanCoeffRat_odd_prime_den_ne_zero hp2 N r j)
  refine ⟨hfull.1, ?_⟩
  change (((p : ℚ) * z * rawCatalanCoeffRat N r j).num : ZMod p) /
    (((p : ℚ) * z * rawCatalanCoeffRat N r j).den : ZMod p) = 0
  rw [hfull.2, hpz.2]
  simp

theorem rawEntryRat_central_layer {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * rawEntryRat z N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * rawEntryRat z N r j) =
        -(∑ ell ∈ Finset.range (H N - p),
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)) := by
  let A : ℚ := (p : ℚ) * (∑ t ∈ Finset.range (H N),
    ((rowP N r).coeff t : ℚ) * momentRat t j)
  let B : ℚ := (p : ℚ) * (∑ t ∈ Finset.range (H N),
    ((rowD N r).coeff t : ℚ) * zetaRat t j)
  let C : ℚ := (p : ℚ) * z * rawCatalanCoeffRat N r j
  have hA := rowP_momentRat_central_reduction (r := r) hp2 hN hpH hH hjlo hj
  have hB := rowD_zetaRat_central_reduction (r := r) hN hpH hH hjlo hj
  have hC := rawCatalanTerm_prime_reduction hp2 z hz N r j
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpgt : 2 < p := by have := hp.out.two_le; omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hpgt) hdiv
  have h32 := nat_fraction_reduced_residue (p := p) 3 2 htwo
  have hBprod := rational_residue_mul h32.1 hB.1
  have hdiff := rational_residue_sub hA.1 hBprod.1
  have hsum := rational_residue_add hdiff.1 hC.1
  have hsplit : (p : ℚ) * rawEntryRat z N r j = A - (3 / 2 : ℚ) * B + C := by
    dsimp only [A, B, C]
    rw [rawEntryRat_affine, rawEntryRat_zero]
    ring
  have hAR : palindromicRatResidue p A =
      -(∑ ell ∈ Finset.range (H N - p),
        (2 * oddPrimeExtractedP p N r ell 2) / ((j - ell : ℕ) : ZMod p)) := hA.2
  have hBR : palindromicRatResidue p B =
      -(∑ ell ∈ Finset.range (H N - p),
        oddPrimeExtractedD p N r ell 1 / ((j - ell : ℕ) : ZMod p)) := hB.2
  have hCR : palindromicRatResidue p C = 0 := hC.2
  have h32R : palindromicRatResidue p (3 / 2 : ℚ) = (3 / 2 : ZMod p) := h32.2
  have hsumR : palindromicRatResidue p (A - (3 / 2 : ℚ) * B + C) =
      palindromicRatResidue p (A - (3 / 2 : ℚ) * B) + palindromicRatResidue p C := hsum.2
  have hdiffR : palindromicRatResidue p (A - (3 / 2 : ℚ) * B) =
      palindromicRatResidue p A - palindromicRatResidue p ((3 / 2 : ℚ) * B) := hdiff.2
  have hprodR : palindromicRatResidue p ((3 / 2 : ℚ) * B) =
      palindromicRatResidue p (3 / 2 : ℚ) * palindromicRatResidue p B := hBprod.2
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hsum.1
  · rw [hsplit, hsumR, hdiffR, hprodR, hAR, hBR, hCR, h32R, add_zero]
    simp only [oddPrimeLeadingV, sub_div, Finset.sum_sub_distrib,
      mul_div_assoc, ← Finset.mul_sum]
    ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem rawEntryRat_low_leading {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r ell) =
        oddPrimeLeadingV p N r ell := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hH : H N < p ^ 2 := by nlinarith
  have hH2 : 2 ≤ H N := by unfold H; omega
  have hraw := rawEntryRat_general_column_layer (k := 0) (N := N) (r := r)
    hp2 hN hH hell (by simpa using (show ell < H N by omega)) z hz
  simp only [Nat.zero_mul, zero_add] at hraw
  have hM :
      (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0)) =
          2 * oddPrimeExtractedP p N r ell 2 := by
    rw [Finset.sum_eq_single 2]
    · norm_num [palindromicRatResidue, momentRatSigned, momentRat,
        boundaryMinus]
      ring
    · intro v hv hne
      by_cases hv3 : 3 ≤ v
      · rw [oddPrimeExtractedP_eq_zero_of_ge_three hp.out.pos hN hwidth hv3, zero_mul]
      · have hcases : v = 0 ∨ v = 1 := by omega
        rcases hcases with rfl | rfl <;>
          norm_num [palindromicRatResidue, momentRatSigned, momentRatNegOne,
            momentRat, boundaryPlus, boundaryMinus]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega : 2 < H N + 1))).elim
  have hD :
      (∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u 0)) = oddPrimeExtractedD p N r ell 1 := by
    rw [Finset.sum_eq_single 1]
    · norm_num [palindromicRatResidue, zetaRat, harmonicRat, Finset.sum_range_succ]
    · intro u hu hne
      by_cases hu2 : 2 ≤ u
      · rw [oddPrimeExtractedD_eq_zero_of_ge_two hN hwidth hu2, zero_mul]
      · have hu0 : u = 0 := by omega
        subst u
        norm_num [palindromicRatResidue, zetaRat, harmonicRat]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega : 1 < H N))).elim
  refine ⟨hraw.1, ?_⟩
  rw [hraw.2, hM, hD]
  rfl

theorem rawEntryRat_high_leading {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) =
        oddPrimeLeadingU p N r ell - oddPrimeLeadingV p N r ell := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hH : H N < p ^ 2 := by nlinarith
  have hlo := rawEntryRat_low_leading (r := r) hp2 hN hell hwidth hhigh z hz
  have hhi := rawEntryRat_prime_digit_reduction (N := N) (r := r) hp2 hH hhigh z hz
  have hpair := rawEntryRat_pair_leading (r := r) hp2 hN hell hwidth hhigh z hz
  have hadd := palindromicRatResidue_add hlo.1 hhi.1
  have hsum : oddPrimeLeadingV p N r ell +
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) =
        oddPrimeLeadingU p N r ell := by
    rw [← hlo.2, ← hadd, ← mul_add]
    exact hpair.2
  refine ⟨hhi.1, ?_⟩
  calc
    _ = (oddPrimeLeadingV p N r ell +
        palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell))) -
          oddPrimeLeadingV p N r ell := by ring
    _ = _ := by rw [hsum]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

def oddPrimeRepresented (p N ell : ℕ) : Prop :=
  b N ≤ ell ∨ ell < L N - p

instance oddPrimeRepresented_decidable (p N ell : ℕ) : Decidable (oddPrimeRepresented p N ell) :=
  inferInstanceAs (Decidable (b N ≤ ell ∨ ell < L N - p))

def oddPrimeRepresentativeRat (z : ℚ) (p N r ell : ℕ) : ℚ :=
  if b N ≤ ell then rawEntryRat z N r ell else -rawEntryRat z N r (p + ell)

theorem oddPrimeRepresentativeRat_scaled_reduction {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p) (hell : ell < H N - p)
    (_hrep : oddPrimeRepresented p N ell) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell) =
        oddPrimeLeadingV p N r ell := by
  have hellp : ell < p := by omega
  have hwidth : H N ≤ ell + 2 * p := by omega
  have hhigh : p + ell < H N := by omega
  by_cases hb : b N ≤ ell
  · rw [oddPrimeRepresentativeRat, ite_eq_left hb]
    exact rawEntryRat_low_leading (r := r) hp2 hN hellp hwidth hhigh z hz
  · have hellA : ell ≤ A N := by
      unfold b A at *
      omega
    have hU := oddPrimeLeadingU_eq_zero (p := p) hp.out.pos hN hr hellA
    have hraw := rawEntryRat_high_leading (r := r) hp2 hN hellp hwidth hhigh z hz
    rw [oddPrimeRepresentativeRat, ite_eq_right hb, mul_neg]
    refine ⟨?_, ?_⟩
    · simpa only [Rat.neg_den] using hraw.1
    · have hneg :
          palindromicRatResidue p (-((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell))) =
            -palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) := by
        simp only [palindromicRatResidue, Rat.neg_num, Rat.neg_den, Int.cast_neg, neg_div]
      rw [hneg, hraw.2, hU, zero_sub, neg_neg]







open scoped BigOperators

def oddPrimeShearedRat (z : ℚ) (p N r j : ℕ) : ℚ := by
  classical
  exact rawEntryRat z N r j + (p : ℚ) *
    ∑ ell ∈ Finset.range (H N - p),
      if oddPrimeRepresented p N ell then
        oddPrimeRepresentativeRat z p N r ell / ((j - ell : ℕ) : ℚ)
      else 0

theorem oddPrimeShearedRat_scaled_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * oddPrimeShearedRat z p N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) * oddPrimeShearedRat z p N r j) =
        -(∑ ell ∈ Finset.range (H N - p),
          if ¬oddPrimeRepresented p N ell then
            oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)
          else 0) := by
  classical
  let f : ℕ → ℚ := fun ell =>
    if oddPrimeRepresented p N ell then
      (p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell /
        ((j - ell : ℕ) : ℚ)
    else 0
  have hterm (ell : ℕ) (hell : ell ∈ Finset.range (H N - p)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f ell) =
          if oddPrimeRepresented p N ell then
            oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)
          else 0 := by
    by_cases hrep : oddPrimeRepresented p N ell
    · have hellJ := Finset.mem_range.mp hell
      have hrepR := oddPrimeRepresentativeRat_scaled_reduction
        hp2 hN hr hpH hH hellJ hrep z hz
      have hellj : ell < j := hellJ.trans_le hjlo
      have hdpos : 0 < j - ell := by omega
      have hdlt : j - ell < p := by omega
      have hden : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
          ((ZMod.natCast_eq_zero_iff (j - ell) p).mp hzero)
      have hinv := nat_fraction_reduced_residue (p := p) 1 (j - ell) hden
      simp only [Nat.cast_one] at hinv
      have hinvR : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
          1 / ((j - ell : ℕ) : ZMod p) := hinv.2
      have hprod := rational_residue_mul hrepR.1 hinv.1
      have heq : f ell =
          ((p : ℚ) ^ 2 * oddPrimeRepresentativeRat z p N r ell) *
            (1 / ((j - ell : ℕ) : ℚ)) := by
        dsimp only [f]
        rw [ite_eq_left hrep]
        ring
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact hprod.1
      · rw [heq, palindromicRatResidue_mul hrepR.1 hinv.1,
          hrepR.2, hinvR, ite_eq_left hrep]
        ring
    · simp [f, hrep, palindromicRatResidue]
  have hsum := rational_residue_sum (Finset.range (H N - p)) f
    (fun ell hell => (hterm ell hell).1)
  have hsumR : palindromicRatResidue p (∑ ell ∈ Finset.range (H N - p), f ell) =
      ∑ ell ∈ Finset.range (H N - p),
        if oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)
        else 0 := by
    calc
      _ = ∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f ell) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun ell hell => (hterm ell hell).2)
  have hcentral := rawEntryRat_central_layer (r := r) hp2 hN hpH hH hjlo hj z hz
  have hadd := rational_residue_add hcentral.1 hsum.1
  have hscale : (p : ℚ) * oddPrimeShearedRat z p N r j =
      (p : ℚ) * rawEntryRat z N r j + ∑ ell ∈ Finset.range (H N - p), f ell := by
    unfold oddPrimeShearedRat
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ell hell
    dsimp only [f]
    split_ifs <;> ring
  have hpartition :
      (∑ ell ∈ Finset.range (H N - p),
        oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p)) =
      (∑ ell ∈ Finset.range (H N - p),
        if oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) +
      (∑ ell ∈ Finset.range (H N - p),
        if ¬oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ell hell
    by_cases hrep : oddPrimeRepresented p N ell <;> simp [hrep]
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hadd.1
  · rw [hscale, palindromicRatResidue_add hcentral.1 hsum.1,
      hcentral.2, hsumR, hpartition]
    ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def oddPrimeLeadingLiftRat (p N r ell : ℕ) [Fact p.Prime] : ℚ :=
  ((oddPrimeLeadingV p N r ell).val : ℚ)

def oddPrimeExceptionalPartRat (_z : ℚ) (p N r j : ℕ) [Fact p.Prime] : ℚ := by
  classical
  exact ∑ ell ∈ Finset.range (H N - p),
    if ¬oddPrimeRepresented p N ell then
      -(oddPrimeLeadingLiftRat p N r ell / ((j - ell : ℕ) : ℚ)) else 0

def oddPrimeCentralRemainderRat (z : ℚ) (p N r j : ℕ) [Fact p.Prime] : ℚ :=
  oddPrimeShearedRat z p N r j - oddPrimeExceptionalPartRat z p N r j / (p : ℚ)

theorem oddPrimeLeadingLiftRat_reduction {p N r ell : ℕ} [Fact p.Prime] :
    ((oddPrimeLeadingLiftRat p N r ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (oddPrimeLeadingLiftRat p N r ell) =
        oddPrimeLeadingV p N r ell :=
  zmod_val_rat_reduction (oddPrimeLeadingV p N r ell)

theorem oddPrimeExceptionalPartRat_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hjlo : H N - p ≤ j) (hj : j < p) (z : ℚ) :
    ((oddPrimeExceptionalPartRat z p N r j).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (oddPrimeExceptionalPartRat z p N r j) =
        -(∑ ell ∈ Finset.range (H N - p),
          if ¬oddPrimeRepresented p N ell then
            oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
  classical
  let f : ℕ → ℚ := fun ell => if ¬oddPrimeRepresented p N ell then
    -(oddPrimeLeadingLiftRat p N r ell / ((j - ell : ℕ) : ℚ)) else 0
  have ht (ell : ℕ) (hell : ell ∈ Finset.range (H N - p)) :
      ((f ell).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (f ell) =
        -(if ¬oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) := by
    by_cases hex : ¬oddPrimeRepresented p N ell
    · have hell' : ell < H N - p := Finset.mem_range.mp hell
      have hd0 : 0 < j - ell := by omega
      have hdlt : j - ell < p := by omega
      have hd : ((j - ell : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        exact (Nat.not_dvd_of_pos_of_lt hd0 hdlt)
          ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
      have hf := nat_fraction_reduced_residue (p := p) 1 (j - ell) hd
      simp only [Nat.cast_one] at hf
      have hl := oddPrimeLeadingLiftRat_reduction (p := p) (N := N) (r := r) (ell := ell)
      have hm := rational_residue_mul hl.1 hf.1
      have hn := rational_residue_sub (p := p) (a := 0) (by norm_num) hm.1
      have heq : -(oddPrimeLeadingLiftRat p N r ell / ((j - ell : ℕ) : ℚ)) =
          0 - oddPrimeLeadingLiftRat p N r ell * (1 / ((j - ell : ℕ) : ℚ)) := by ring
      have hfr : palindromicRatResidue p (1 / ((j - ell : ℕ) : ℚ)) =
          1 / ((j - ell : ℕ) : ZMod p) := hf.2
      refine ⟨?_, ?_⟩
      · dsimp only [f]
        rw [ite_eq_left hex, heq]
        exact hn.1
      · dsimp only [f]
        rw [ite_eq_left hex, ite_eq_left hex, heq,
          palindromicRatResidue_sub (by norm_num) hm.1,
          palindromicRatResidue_mul hl.1 hf.1, hl.2, hfr]
        norm_num [palindromicRatResidue]
        ring
    · simp only [f, ite_eq_right hex]
      norm_num [palindromicRatResidue]
  have hs := rational_residue_sum (Finset.range (H N - p)) f (fun ell hell => (ht ell hell).1)
  refine ⟨hs.1, ?_⟩
  change palindromicRatResidue p (∑ ell ∈ Finset.range (H N - p), f ell) = _
  calc
    _ = ∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f ell) := hs.2
    _ = ∑ ell ∈ Finset.range (H N - p),
        -(if ¬oddPrimeRepresented p N ell then
          oddPrimeLeadingV p N r ell / ((j - ell : ℕ) : ZMod p) else 0) :=
      Finset.sum_congr rfl (fun ell hell => (ht ell hell).2)
    _ = _ := by rw [Finset.sum_neg_distrib]

theorem oddPrimeCentralRemainderRat_den_ne_zero {p N r j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N) (hpH : p ≤ H N)
    (hH : H N ≤ 2 * p) (hjlo : H N - p ≤ j) (hj : j < p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    ((oddPrimeCentralRemainderRat z p N r j).den : ZMod p) ≠ 0 := by
  have hc := oddPrimeShearedRat_scaled_reduction hp2 hN hr hpH hH hjlo hj z hz
  have he := oddPrimeExceptionalPartRat_reduction (r := r) hjlo hj z
  exact rational_remainder_den_ne_zero_of_scaled_residue_eq hc.1 he.1
    (hc.2.trans he.2.symm)

theorem oddPrimeShearedRat_eq_remainder_add_exceptional
    {p : ℕ} [Fact p.Prime] (z : ℚ) (N r j : ℕ) :
    oddPrimeShearedRat z p N r j = oddPrimeCentralRemainderRat z p N r j +
      (p : ℚ)⁻¹ * oddPrimeExceptionalPartRat z p N r j := by
  unfold oddPrimeCentralRemainderRat
  ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def oddPrimeUpperPairIndex (p N j : ℕ) : Prop :=
  p + b N ≤ j ∧ j < p + min (A N) (L N - p)

def oddPrimeUpperCentralIndex (p N j : ℕ) : Prop :=
  max (b N) (H N - p) ≤ j ∧ j < min p (L N)

instance oddPrimeUpperPairIndex_decidable (p N j : ℕ) :
    Decidable (oddPrimeUpperPairIndex p N j) :=
  inferInstanceAs (Decidable (p + b N ≤ j ∧ j < p + min (A N) (L N - p)))

instance oddPrimeUpperCentralIndex_decidable (p N j : ℕ) :
    Decidable (oddPrimeUpperCentralIndex p N j) :=
  inferInstanceAs (Decidable (max (b N) (H N - p) ≤ j ∧ j < min p (L N)))

def oddPrimeUpperPoolRat (z : ℚ) (p N r j : ℕ) : ℚ :=
  if oddPrimeUpperPairIndex p N j then
    rawEntryRat z N r j + rawEntryRat z N r (j - p)
  else if oddPrimeUpperCentralIndex p N j then oddPrimeShearedRat z p N r j
  else rawEntryRat z N r j

def oddPrimeUpperRepresentativePoolRat (z : ℚ) (p N r ell : ℕ) : ℚ :=
  if b N ≤ ell then oddPrimeUpperPoolRat z p N r ell
  else -oddPrimeUpperPoolRat z p N r (p + ell)

theorem oddPrimeUpperPoolRat_pair_low {p N j : ℕ} (hH : H N ≤ 2 * p)
    (hpair : oddPrimeUpperPairIndex p N j) (z : ℚ) (r : ℕ) :
    oddPrimeUpperPoolRat z p N r (j - p) = rawEntryRat z N r (j - p) := by
  have hpair' := hpair
  unfold oddPrimeUpperPairIndex at hpair'
  have hLH : L N ≤ H N := by unfold L H; omega
  have hKJ : L N - p ≤ H N - p := Nat.sub_le_sub_right hLH p
  have hellJ : j - p < H N - p := by omega
  have hellp : j - p < p := by omega
  have hnotpair : ¬oddPrimeUpperPairIndex p N (j - p) := by
    unfold oddPrimeUpperPairIndex
    omega
  have hnotcentral : ¬oddPrimeUpperCentralIndex p N (j - p) := by
    unfold oddPrimeUpperCentralIndex
    omega
  rw [oddPrimeUpperPoolRat, ite_eq_right hnotpair, ite_eq_right hnotcentral]

theorem oddPrimeUpperRepresentativePoolRat_eq {p N ell : ℕ}
    (hH : H N ≤ 2 * p) (hell : ell < H N - p) (z : ℚ) (r : ℕ) :
    oddPrimeUpperRepresentativePoolRat z p N r ell =
      oddPrimeRepresentativeRat z p N r ell := by
  have hellp : ell < p := by omega
  by_cases hb : b N ≤ ell
  · have hpnot : ¬oddPrimeUpperPairIndex p N ell := by
      unfold oddPrimeUpperPairIndex
      omega
    have hcnot : ¬oddPrimeUpperCentralIndex p N ell := by
      unfold oddPrimeUpperCentralIndex
      omega
    rw [oddPrimeUpperRepresentativePoolRat, ite_eq_left hb, oddPrimeUpperPoolRat,
      ite_eq_right hpnot, ite_eq_right hcnot, oddPrimeRepresentativeRat, ite_eq_left hb]
  · have hpnot : ¬oddPrimeUpperPairIndex p N (p + ell) := by
      unfold oddPrimeUpperPairIndex
      omega
    have hcnot : ¬oddPrimeUpperCentralIndex p N (p + ell) := by
      unfold oddPrimeUpperCentralIndex
      omega
    rw [oddPrimeUpperRepresentativePoolRat, ite_eq_right hb, oddPrimeUpperPoolRat,
      ite_eq_right hpnot, ite_eq_right hcnot, oddPrimeRepresentativeRat, ite_eq_right hb]

theorem rawEntryRat_eq_upper_pool_inverse {p N : ℕ} (hH : H N ≤ 2 * p)
    (z : ℚ) (r j : ℕ) :
    rawEntryRat z N r j = oddPrimeUpperPoolRat z p N r j -
      (if oddPrimeUpperPairIndex p N j then oddPrimeUpperPoolRat z p N r (j - p) else 0) -
      (if oddPrimeUpperCentralIndex p N j then
        (p : ℚ) * ∑ ell ∈ Finset.range (H N - p),
          if oddPrimeRepresented p N ell then
            oddPrimeUpperRepresentativePoolRat z p N r ell / ((j - ell : ℕ) : ℚ)
          else 0
        else 0) := by
  classical
  by_cases hpair : oddPrimeUpperPairIndex p N j
  · have hcentral : ¬oddPrimeUpperCentralIndex p N j := by
      unfold oddPrimeUpperPairIndex at hpair
      unfold oddPrimeUpperCentralIndex
      omega
    rw [ite_eq_left hpair, ite_eq_right hcentral, oddPrimeUpperPoolRat, ite_eq_left hpair,
      oddPrimeUpperPoolRat_pair_low hH hpair, sub_zero]
    ring
  · by_cases hcentral : oddPrimeUpperCentralIndex p N j
    · have hsum :
          (∑ ell ∈ Finset.range (H N - p), if oddPrimeRepresented p N ell then
            oddPrimeUpperRepresentativePoolRat z p N r ell / ((j - ell : ℕ) : ℚ) else 0) =
          ∑ ell ∈ Finset.range (H N - p), if oddPrimeRepresented p N ell then
            oddPrimeRepresentativeRat z p N r ell / ((j - ell : ℕ) : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [oddPrimeUpperRepresentativePoolRat_eq hH (Finset.mem_range.mp hell)]
      rw [ite_eq_right hpair, ite_eq_left hcentral, sub_zero, hsum,
        oddPrimeUpperPoolRat, ite_eq_right hpair, ite_eq_left hcentral, oddPrimeShearedRat]
      ring
    · rw [ite_eq_right hpair, ite_eq_right hcentral, sub_zero, sub_zero,
        oddPrimeUpperPoolRat, ite_eq_right hpair, ite_eq_right hcentral]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

def oddPrimeUpperRepresentativeNumber (p N ell : ℕ) : ℕ :=
  if b N ≤ ell then ell else p + ell

def oddPrimeUpperRepresentativeSign (N ell : ℕ) : ℚ :=
  if b N ≤ ell then 1 else -1

end InternalCatalan

end



namespace InternalCatalan

open Classical
open scoped BigOperators

private theorem upper_sign_den_ne_zero {p : ℕ} [Fact p.Prime] (N ell : ℕ) :
    ((oddPrimeUpperRepresentativeSign N ell).den : ZMod p) ≠ 0 := by
  unfold oddPrimeUpperRepresentativeSign
  split_ifs <;> norm_num

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem oddPrimeUpperRepresentativeNumber_mem {p N ell : ℕ}
    (hN : 0 < N) (hH : H N ≤ 2 * p) (hell : ell < H N - p)
    (hrep : oddPrimeRepresented p N ell) :
    oddPrimeUpperRepresentativeNumber p N ell ∈ Finset.Ico (b N) (L N) := by
  have hbp : b N < p := by unfold b H at *; omega
  have hJL : H N - p ≤ L N := by unfold H L at *; omega
  unfold oddPrimeUpperRepresentativeNumber
  by_cases hb : b N ≤ ell
  · rw [ite_eq_left hb]
    exact Finset.mem_Ico.mpr ⟨hb, by omega⟩
  · rw [ite_eq_right hb]
    unfold oddPrimeRepresented at hrep
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem oddPrimeUpperRepresentativePoolRat_eq_sign (z : ℚ) (p N r ell : ℕ) :
    oddPrimeUpperRepresentativePoolRat z p N r ell =
      oddPrimeUpperRepresentativeSign N ell *
        oddPrimeUpperPoolRat z p N r (oddPrimeUpperRepresentativeNumber p N ell) := by
  by_cases hb : b N ≤ ell <;>
    simp only [oddPrimeUpperRepresentativePoolRat, oddPrimeUpperRepresentativeSign,
      oddPrimeUpperRepresentativeNumber, hb, ite_true, ite_false, one_mul, neg_one_mul]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open Filter
open scoped Topology BigOperators

end InternalCatalan

end



namespace InternalCatalan
open Filter
open scoped Topology

end InternalCatalan

end OAI
