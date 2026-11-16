module

public import CatalanCore.Zeta5.Frames.OuterClass

@[expose] public section

/-!
# ZC13, ZC14: the outer range `K/3 < p`

* ZC13 (`zc13_split`, `zc13_factor` in `OuterFrame`): `μ = μ₀ + p⁻¹ L`, `μ₀` integral on monomials,
  `L = U V` of inner dimension `r_p = max(0, K + 4N - 2p + 2)`.
* ZC14, weights (I15): `wO` (`OuterEntryMain`), with `v^G(Δ_K) ≥ 2 ∑ w - min(r_p, z)`
  (`outer_bound`, the complementary-minor lemma ZC11 inside `outer_frame`).
* ZC14, closed form (I17): `zc14_outer`, `v^G(Δ_K) ≥ γ_p^out` for `K/3 < p ≤ K`.
* ZC14, (I18): `zc14_big`, `v^G(Δ_K) ≥ 0` for `p > K`.
* the low-pole congruence `zc14_poleValue_congr`, `zc14_H5_congr`.
-/

open Finset Polynomial

namespace Apery

/-- The closed outer exponent `γ_p^out` (I17), with `v = K mod p`, `u = max(0, N + v - p + 1)`,
`t_p = min(N, v) + u`, `r_p = max(0, K + 4N - 2p + 2)`. -/
def gammaOut (n p : ℕ) : ℤ :=
  if 40 * n < 2 * p then
    -7 * ((40 * n : ℤ) - p) + 6 * ((min (3 * n) (40 * n % p) + (3 * n + 40 * n % p + 1 - p) : ℕ) : ℤ)
      - 1 - min ((52 * n + 2 - 2 * p : ℕ) : ℤ)
        ((p : ℤ) - 1 - 3 * n + ((3 * n + 40 * n % p + 1 - p : ℕ) : ℤ))
  else
    -7 * ((40 * n : ℤ) - p) + 3 + 12 * (3 * n : ℤ) +
      5 * ((min (3 * n) (40 * n % p) + (3 * n + 40 * n % p + 1 - p) : ℕ) : ℤ)
      - min ((52 * n + 2 - 2 * p : ℕ) : ℤ) ((p : ℤ) + ((3 * n + 40 * n % p + 1 - p : ℕ) : ℤ))

/-- `p` is odd. -/
lemma prime_odd_of_ge {p : ℕ} (hp : p.Prime) (h : 3 ≤ p) : 2 * (p / 2) + 1 = p := by
  have := hp.eq_one_or_self_of_dvd 2
  rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
  · have := this ⟨k, by omega⟩
    omega
  · omega

lemma cast_min_aux (W2 : ℚ) (A : ℤ) (r z : ℕ) (hA : W2 = (A : ℚ)) :
    W2 - min (r : ℚ) (z : ℚ) = ((A - min (r : ℤ) (z : ℤ) : ℤ) : ℚ) := by
  rw [hA, Int.cast_sub, Int.cast_min]
  push_cast
  ring

/-- **ZC14 (I15)+(I17).** For a prime `K/3 < p ≤ K` (`K = 40 n`),
`v_p^G(Δ_K) ≥ γ_p^out`. -/
theorem zc14_outer {p n : ℕ} [hp : Fact p.Prime] (hn : 1 ≤ n) (hout : 40 * n < 3 * p)
    (hpK : p ≤ 40 * n) : GV p (Δ n) (gammaOut n p : ℚ) := by
  have hp14 : 14 ≤ p := by omega
  have hm := prime_odd_of_ge hp.out (by omega)
  have hp7 : 7 ≤ p := by omega
  have hK : 2 * (40 * n) < p ^ 2 := by nlinarith
  have hpN : 3 * n < p := by omega
  have h := outer_bound (p := p) hm n hp7 hout hK hpN
  have hr : 37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) = 52 * n + 2 - 2 * p := by omega
  rw [hr] at h
  refine h.mono (le_of_eq ?_)
  symm
  have hq : 40 * n / p = 1 ∨ 40 * n / p = 2 := by
    have h1 : 1 ≤ 40 * n / p := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have h2 : 40 * n / p < 3 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    omega
  have hdm := Nat.div_add_mod (40 * n) p
  have hvl := Nat.mod_lt (40 * n) (show 0 < p by omega)
  have h3m : 3 * n ≤ 2 * (p / 2) := by omega
  rcases hq with hq | hq
  · obtain ⟨h1, h2⟩ := outer_total_q1 hm hn hout hq
    rw [hq] at hdm
    have hlt : 40 * n < 2 * p := by omega
    rw [h2, cast_min_aux _ (-7 * ((40 * n % p : ℕ) : ℤ) +
      6 * ((min (3 * n) (40 * n % p) + (3 * n + 40 * n % p + 1 - p) : ℕ) : ℤ) - 1)
      (52 * n + 2 - 2 * p) (2 * (p / 2) - 3 * n + (3 * n + 40 * n % p + 1 - p))
      (by rw [h1]; simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        Int.cast_neg, Int.cast_ofNat, Int.cast_one])]
    congr 1
    unfold gammaOut
    rw [if_pos hlt]
    omega
  · obtain ⟨h1, h2⟩ := outer_total_q2 hm hn hout hq
    rw [hq] at hdm
    have hge : ¬ 40 * n < 2 * p := by omega
    rw [h2, cast_min_aux _ (-7 * ((2 * (p / 2) + 40 * n % p : ℕ) : ℤ) + 12 * ((3 * n : ℕ) : ℤ) +
      5 * ((min (3 * n) (40 * n % p) + (3 * n + 40 * n % p + 1 - p) : ℕ) : ℤ) - 4)
      (52 * n + 2 - 2 * p) (1 + 2 * (p / 2) + (3 * n + 40 * n % p + 1 - p))
      (by rw [h1]; simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        Int.cast_neg, Int.cast_ofNat, Int.cast_one])]
    congr 1
    unfold gammaOut
    rw [if_neg hge]
    omega


/-- **ZC14 (I18).** For a prime `p > K = 40 n`, `v_p^G(Δ_K) ≥ 0`. -/
theorem zc14_big {p n : ℕ} [hp : Fact p.Prime] (hn : 1 ≤ n) (hK : 40 * n < p) :
    GV p (Δ n) 0 := by
  have hm := prime_odd_of_ge hp.out (by omega)
  have hout : 40 * n < 3 * p := by omega
  have hsq : 2 * (40 * n) < p ^ 2 := by nlinarith
  have h := outer_bound (p := p) hm n (by omega) hout hsq (by omega)
  have hr : 37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) = 0 := by omega
  rw [hr] at h
  have hq : 40 * n / p = 0 := Nat.div_eq_of_lt hK
  have hW : ∑ c : Fin (p / 2 + 1), ∑ i ∈ range (LoC hm n c), wO hm n c i = 0 := by
    rw [W_split hm hn hout, zero_sum hm hn hout (by omega), hq]
    simp only [show ¬ (0 = 1) from by omega, show ¬ (0 = 2) from by omega, if_false, zero_add]
    refine Finset.sum_eq_zero fun c hc => ?_
    unfold GO
    have : aCnt p (40 * n % p) c ≤ 2 := aCnt_le_two _ _ _
    rw [show 2 * 0 + aCnt p (40 * n % p) c - 2 = 0 by omega]
    simp
  rw [hW] at h
  simpa using h

end Apery
