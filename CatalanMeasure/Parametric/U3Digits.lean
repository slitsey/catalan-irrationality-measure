module
public import CatalanMeasure.Parametric.U3Combination
public import CatalanMeasure.Parametric.RawDigitFunctional
@[expose] public section

/-!
# Digit response of a row combination (Lemma U3)

The raw residue response of a row combination `c` at column `j` equals
`primeDigitPair (27N) p j P_c D_c`.  In the window
`27N - 3p ≤ j % p < 24N - 2p` and on the flag subspace the response is the
single scalar `D_c[p + j%p]` times a constant depending only on `j / p`.
-/

namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

section
variable {p N : ℕ} [hp : Fact p.Prime]

/-- Raw residue response of a row combination at column `j`. -/
def u3Resp (p N j : ℕ) [Fact p.Prime] : (Fin (20 * N) → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun c := ∑ r : Fin (20 * N),
    palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat twenty 0 N r.val j) * c r
  map_add' c d := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.mul_sum, mul_left_comm]

theorem primeDigitSample_comb {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (H p ell : ℕ) (f : ℕ → R) (Q : ι → R[X]) (c : ι → R) :
    primeDigitSample H p ell f (∑ i, C (c i) * Q i) =
      ∑ i, c i * primeDigitSample H p ell f (Q i) := by
  unfold primeDigitSample
  simp only [finsetSum_coeff, coeff_C_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem primeDigitPair_comb {ι : Type*} [Fintype ι] (H j : ℕ)
    (F G : ι → (ZMod p)[X]) (c : ι → ZMod p) :
    primeDigitPair H p j (∑ i, C (c i) * F i) (∑ i, C (c i) * G i) =
      ∑ i, c i * primeDigitPair H p j (F i) (G i) := by
  unfold primeDigitPair
  have e : (X : (ZMod p)[X]) * oddPrimeWeight p * (∑ i, C (c i) * F i) =
      ∑ i, C (c i) * (X * oddPrimeWeight p * F i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e, primeDigitSample_comb, primeDigitSample_comb, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem u3Resp_eq (hN : 0 < N) (hp2 : p ≠ 2) (hH : 27 * N < p ^ 2) {j : ℕ} (hj : j < 27 * N)
    (c : Fin (20 * N) → ZMod p) :
    u3Resp p N j c = primeDigitPair (27 * N) p j ((1 - X) ^ N * u3S p N c)
      ((1 - X) ^ N * u3U p N c) := by
  have hH' : twenty.H N < p ^ 2 := by rw [twenty_H]; exact hH
  have hj' : j < twenty.H N := by rw [twenty_H]; exact hj
  have h1 : (1 - X : (ZMod p)[X]) ^ N * u3S p N c =
      ∑ r : Fin (20 * N), C (c r) * (rowP twenty N r.val).map (Int.castRingHom (ZMod p)) := by
    show (1 - X : (ZMod p)[X]) ^ N * combLin (fun r : Fin (20 * N) => u3Sv p N r.val) c = _
    rw [combLin_mul_left, combLin_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [rowP_map_eq hN r.isLt]; rfl
  have h2 : (1 - X : (ZMod p)[X]) ^ N * u3U p N c =
      ∑ r : Fin (20 * N), C (c r) * (rowD twenty N r.val).map (Int.castRingHom (ZMod p)) := by
    show (1 - X : (ZMod p)[X]) ^ N * combLin (fun r : Fin (20 * N) => u3Uv p N r.val) c = _
    rw [combLin_mul_left, combLin_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [rowD_map_eq hN r.isLt]; rfl
  rw [h1, h2, primeDigitPair_comb]
  unfold u3Resp
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hz : (((p : ℚ) * 0).den : ZMod p) ≠ 0 := by simp
  rw [rawEntry_primeDigitPair twenty_admissible hN hp2 hH' hj' 0 hz, twenty_H, mul_comm]

/-- The constant multiplying the single digit in the rank-one window. -/
def u3Kappa (p J : ℕ) [Fact p.Prime] : ZMod p :=
  palindromicRatResidue p (momentRatSigned (((1 : ℕ) : ℤ) - 1) J) -
    palindromicRatResidue p (momentRatSigned (((3 : ℕ) : ℤ) - 1) J) -
    (3 / 2 : ZMod p) * palindromicRatResidue p (zetaRat 1 J)

theorem u3Resp_window (hN : 0 < N) (hp2 : p ≠ 2) (h8 : 8 * N < p) (h9 : p < 9 * N)
    {j : ℕ} (hj : j < 24 * N) (hl1 : 27 * N - 3 * p ≤ j % p) (hl2 : j % p < 24 * N - 2 * p)
    (c : Fin (20 * N) → ZMod p) (Y : (ZMod p)[X])
    (hY : (1 - X) ^ N * u3S p N c = (1 - X ^ 2) ^ ((p + 1) / 2) * Y) :
    u3Resp p N j c = ((1 - X) ^ N * u3U p N c).coeff (p + j % p) * u3Kappa p (j / p) := by
  have hH : 27 * N < p ^ 2 := by nlinarith
  rw [u3Resp_eq hN hp2 hH (by omega) c]
  obtain ⟨hS1, hS2, hK, hQ⟩ := u3Qt_props hp2 hN h9 h8 c Y hY
  have hℓp : j % p < p := Nat.mod_lt _ hp.out.pos
  unfold primeDigitPair primeDigitSample
  rw [hQ]
  beta_reduce
  generalize j % p = ℓ at *
  generalize hq : (X * Y).coeff (p + ℓ) = q
  have hmul2 : ∀ v, 2 ≤ v → 2 * p ≤ v * p := fun v hv => Nat.mul_le_mul_right p hv
  have ha : ∀ v, 2 ≤ v → (X * Y).coeff (v * p + ℓ) = 0 := fun v hv =>
    hS2 _ (by have := hmul2 v hv; omega)
  have ha0 : (X * Y).coeff ℓ = 0 := hS1 _ (by omega)
  have hD1 : ((1 - X) ^ N * u3U p N c).coeff (p + ℓ) = q := by
    rw [hK _ (by omega), hq]
  have hb : ∀ v, ((1 - X ^ (2 * p)) * (X * Y)).coeff (v * p + ℓ) =
      if v = 1 then q else if v = 3 then -q else 0 := by
    intro v
    rw [sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
    rcases Nat.lt_or_ge v 2 with hv | hv
    · have : ¬ 2 * p ≤ v * p + ℓ := by
        have : v * p ≤ 1 * p := Nat.mul_le_mul_right p (by omega)
        omega
      rw [if_neg this]
      interval_cases v
      · simp [ha0]
      · simp [hq]
    · have h2 : 2 * p ≤ v * p + ℓ := by have := hmul2 v hv; omega
      rw [if_pos h2, ha v hv]
      have e : v * p + ℓ - 2 * p = (v - 2) * p + ℓ := by
        rw [Nat.sub_mul]; have := hmul2 v hv; omega
      rw [e]
      by_cases h3 : v = 3
      · subst h3
        have : (3 - 2) * p + ℓ = p + ℓ := by omega
        rw [this, hq]; simp
      · by_cases h2' : v = 2
        · subst h2'; simp [ha0]
        · rw [ha (v - 2) (by omega)]
          simp [h2', h3]; omega
  have hs1 : ∑ v ∈ Finset.range (27 * N + 1), ((1 - X ^ (2 * p)) * (X * Y)).coeff (v * p + ℓ) *
      palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) (j / p)) =
      q * palindromicRatResidue p (momentRatSigned (((1 : ℕ) : ℤ) - 1) (j / p)) -
      q * palindromicRatResidue p (momentRatSigned (((3 : ℕ) : ℤ) - 1) (j / p)) := by
    rw [Finset.sum_eq_add 1 3 (by norm_num)]
    · simp only [hb]; simp; ring
    · intro v _ hv
      rw [hb, if_neg hv.1, if_neg hv.2]; simp
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hs2 : ∑ v ∈ Finset.range (27 * N), ((1 - X) ^ N * u3U p N c).coeff (v * p + ℓ) *
      palindromicRatResidue p (zetaRat v (j / p)) =
      q * palindromicRatResidue p (zetaRat 1 (j / p)) := by
    rw [Finset.sum_eq_single 1]
    · simp [hD1]
    · intro v _ hv
      have : ((1 - X) ^ N * u3U p N c).coeff (v * p + ℓ) = 0 := by
        rcases Nat.lt_or_ge v 3 with h3 | h3
        · interval_cases v
          · rw [hK _ (by omega)]; simpa using ha0
          · exact absurd rfl hv
          · rw [hK _ (by have := hmul2 2 le_rfl; omega)]; exact ha 2 le_rfl
        · apply u3D_coeff_zero hp2 hN
          have := Nat.mul_le_mul_right p h3
          omega
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [hs1, hs2, hD1]
  unfold u3Kappa
  ring

end

end
end CatalanMeasure.Parametric
