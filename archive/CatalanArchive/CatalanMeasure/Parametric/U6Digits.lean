module
public import CatalanArchive.CatalanMeasure.Parametric.U6Block
@[expose] public section

/-!
# Filtered column responses (Lemma U6)

The filtered residue response at column `k` is the alternating binomial sum of
raw digit responses over the window `3N + k + v`, `0 ≤ v ≤ N`.  On a block of
columns whose window stays inside one prime digit it is a fixed linear form in
the coefficients of `(X-1)^N * Q` and `(X-1)^N * D`.
-/

namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

section
variable {p N : ℕ} [hp : Fact p.Prime]

/-- The filtered raw response at column `k`. -/
def u6Col (p N k : ℕ) [Fact p.Prime] : (Fin (20 * N) → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun c := ∑ v ∈ Finset.range (N + 1),
    ((-1 : ZMod p) ^ v * (N.choose v : ZMod p)) * u3Resp p N (3 * N + k + v) c
  map_add' c d := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.mul_sum, mul_left_comm]

theorem digit_filter_sum_aux {μ : ℕ} (hμ : N ≤ μ) (A : (ZMod p)[X]) (f : ℕ → ZMod p) (H : ℕ) :
    ∑ v ∈ Finset.range (N + 1), ((-1 : ZMod p) ^ v * (N.choose v : ZMod p)) *
        ∑ u ∈ Finset.range H, A.coeff (u * p + (μ - N + v)) * f u =
      ∑ u ∈ Finset.range H, f u * ((X - 1) ^ N * A).coeff (u * p + μ) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  have := binom_filter A (u * p + μ - N) N
  rw [show u * p + μ - N + N = u * p + μ by omega] at this
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [show u * p + μ - N + v = u * p + (μ - N + v) by omega]
  ring

theorem u6_digit_filter {μ J : ℕ} (hμ : N ≤ μ) (hμp : μ < p) (H : ℕ)
    (F G : (ZMod p)[X]) :
    ∑ v ∈ Finset.range (N + 1), ((-1 : ZMod p) ^ v * (N.choose v : ZMod p)) *
        primeDigitPair H p (J * p + (μ - N + v)) F G =
      ∑ u ∈ Finset.range (H + 1), palindromicRatResidue p (momentRatSigned ((u : ℤ) - 1) J) *
          ((X - 1) ^ N * (X * oddPrimeWeight p * F)).coeff (u * p + μ) -
        (3 / 2 : ZMod p) * ∑ u ∈ Finset.range H, palindromicRatResidue p (zetaRat u J) *
          ((X - 1) ^ N * G).coeff (u * p + μ) := by
  have key : ∀ v ∈ Finset.range (N + 1), primeDigitPair H p (J * p + (μ - N + v)) F G =
      ∑ u ∈ Finset.range (H + 1), (X * oddPrimeWeight p * F).coeff (u * p + (μ - N + v)) *
          palindromicRatResidue p (momentRatSigned ((u : ℤ) - 1) J) -
        (3 / 2 : ZMod p) * ∑ u ∈ Finset.range H, G.coeff (u * p + (μ - N + v)) *
          palindromicRatResidue p (zetaRat u J) := by
    intro v hv
    have hv' : v ≤ N := by have := Finset.mem_range.mp hv; omega
    have hlt : μ - N + v < p := by omega
    have h1 : (J * p + (μ - N + v)) % p = μ - N + v := by
      rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hlt
    have h2 : (J * p + (μ - N + v)) / p = J := by
      rw [Nat.mul_comm, Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hlt, add_zero]
    unfold primeDigitPair primeDigitSample
    rw [h1, h2]
  rw [Finset.sum_congr rfl (fun v hv => by rw [key v hv])]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · exact digit_filter_sum_aux hμ _ _ _
  · simp_rw [mul_left_comm _ (3 / 2 : ZMod p)]
    rw [← Finset.mul_sum]
    congr 1
    exact digit_filter_sum_aux hμ _ _ _


theorem u6Col_block (hN : 0 < N) (hp2 : p ≠ 2) (hH : 27 * N < p ^ 2) {J μ : ℕ}
    (hμ : N ≤ μ) (hμp : μ < p) (h4 : 4 * N ≤ J * p + μ) (hj : J * p + μ < 27 * N)
    (c : Fin (20 * N) → ZMod p) :
    u6Col p N (J * p + μ - 4 * N) c =
      ∑ u ∈ Finset.range (27 * N + 1), palindromicRatResidue p (momentRatSigned ((u : ℤ) - 1) J) *
          (u6Q p N c).coeff (u * p + μ) -
        (3 / 2 : ZMod p) * ∑ u ∈ Finset.range (27 * N), palindromicRatResidue p (zetaRat u J) *
          (u6D p N c).coeff (u * p + μ) := by
  unfold u6Col
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : ∀ v ∈ Finset.range (N + 1), u3Resp p N (3 * N + (J * p + μ - 4 * N) + v) c =
      primeDigitPair (27 * N) p (J * p + (μ - N + v)) ((1 - X) ^ N * u3S p N c)
        ((1 - X) ^ N * u3U p N c) := by
    intro v hv
    have hv' : v ≤ N := by have := Finset.mem_range.mp hv; omega
    have e : 3 * N + (J * p + μ - 4 * N) + v = J * p + (μ - N + v) := by omega
    rw [e]
    exact u3Resp_eq hN hp2 hH (by omega) c
  rw [Finset.sum_congr rfl (fun v hv => by rw [h1 v hv])]
  exact u6_digit_filter hμ hμp (27 * N) _ _


omit hp in
theorem u6_27N_lt_sq (h4 : 4 * N < p) (h9 : 2 * p < 9 * N) : 27 * N < p ^ 2 := by
  have : 3 ≤ N := by omega
  nlinarith

/-- A block column of the filtered matrix vanishes on a combination whose `Q`-digits
`2 ≤ u ≤ 6` vanish at `μ`. -/
theorem u6Col_block_zero (hN : 0 < N) (hp2 : p ≠ 2) (h4 : 4 * N < p) (h9 : 2 * p < 9 * N)
    {J μ : ℕ} (hJ1 : 1 ≤ J) (hJ5 : J ≤ 5)
    (hμ1 : p - 7 * (p - 4 * N) ≤ μ) (hμ2 : μ + 6 * (p - 4 * N) < p)
    (c : Fin (20 * N) → ZMod p)
    (hQ : ∀ u, 2 ≤ u → u ≤ 6 → (u6Q p N c).coeff (u * p + μ) = 0) :
    u6Col p N (J * p + μ - 4 * N) c = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero p hp2
  have hJp : p ≤ J * p := Nat.le_mul_of_pos_left p (by omega)
  have hJp5 : J * p ≤ 5 * p := Nat.mul_le_mul_right p hJ5
  rw [u6Col_block hN hp2 (u6_27N_lt_sq h4 h9) (by omega) (by omega) (by omega) (by omega) c]
  -- digit vanishing of `Q`
  have hQall : ∀ u, (u6Q p N c).coeff (u * p + μ) = 0 := by
    intro u
    rcases Nat.lt_or_ge u 2 with hu | hu
    · have := Nat.mul_le_mul_right p (show u ≤ 1 by omega)
      exact u6Q_coeff_zero hp2 hN c (by omega)
    rcases Nat.lt_or_ge 6 u with hu6 | hu6
    · have := Nat.mul_le_mul_right p (show 7 ≤ u by omega)
      apply coeff_eq_zero_of_natDegree_lt
      have := u6Q_natDegree hp2 hN c
      omega
    · exact hQ u hu hu6
  -- digit vanishing of `D`
  have hD : ∀ u, 2 ≤ u → u ≤ 5 → (u6D p N c).coeff (u * p + μ) = 0 := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu hu5
      have hmul := Nat.mul_le_mul_right p hu5
      have hmul2 := Nat.mul_le_mul_right p hu
      have K := u6_K6_coeff hN hp2 (by omega) c (i := u * p + μ) (by omega)
      rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h), hQall u, show u * p + μ - 2 * p = (u - 2) * p + μ by
        rw [Nat.sub_mul]; omega] at K
      have hz : (u6D p N c).coeff ((u - 2) * p + μ) = 0 := by
        by_cases hu4 : 4 ≤ u
        · exact ih (u - 2) (by omega) (by omega) (by omega)
        · have := Nat.mul_le_mul_right p (show u - 2 ≤ 1 by omega)
          exact u6D_coeff_zero hp2 c (by omega)
      rw [hz] at K
      have : (2 : ZMod p) * (u6D p N c).coeff (u * p + μ) = 0 := by linear_combination -K
      exact (mul_eq_zero.mp this).resolve_left h2
  have hDall : ∀ u, (u6D p N c).coeff (u * p + μ) = 0 := by
    intro u
    rcases Nat.lt_or_ge u 2 with hu | hu
    · have := Nat.mul_le_mul_right p (show u ≤ 1 by omega)
      exact u6D_coeff_zero hp2 c (by omega)
    rcases Nat.lt_or_ge 5 u with hu5 | hu5
    · have := Nat.mul_le_mul_right p (show 6 ≤ u by omega)
      apply coeff_eq_zero_of_natDegree_lt
      have := u6D_natDegree hp2 hN c
      omega
    · exact hD u hu hu5
  simp [hQall, hDall]

end

end
end CatalanMeasure.Parametric
