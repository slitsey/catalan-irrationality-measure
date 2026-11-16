module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import CatalanCore.Zeta5.Port.Legendre

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Legendre.lean (Moritz Firsching); changes: `vS_eq` is stated for `padicValRat p (S n)` directly (the content-side `InnerData` is not used; `InnerData.vS` is by definition `padicValRat D.p (S D.n)`); added `vS_eq_legendre` (the factorial valuations written out by Legendre's formula) and `vS_eq_firstPower` (the case `p^2 > 2K`, where only the first prime power occurs). -/

/-!
# Row ZC16: the `p`-adic valuation of `S_K`

`S_K = (K!)^(2h) 4^(h-1) / ((N!)^(12h) ∏_{i=1}^{h-1} ((2i)!)^2)` with `K = 40n`, `N = 3n`, `h = 37n`.

* `vS_eq` : `v_p(S_K) = 2h v_p(K!) - 12h v_p(N!) - 2 ∑_{i=1}^{h-1} v_p((2i)!) + (h-1) v_p(4)`;
* `vS_eq_legendre` : the same with every `v_p(m!)` replaced by Legendre's `∑_{b=1}^{log_p m} ⌊m/p^b⌋`;
* `vS_eq_firstPower` : if `p^2 > 2K` (so `p^2 > 2i` for `i < h`) only the first prime power occurs:
  `v_p(S_K) = 2h ⌊K/p⌋ - 12h ⌊N/p⌋ - 2 ∑_{i=1}^{h-1} ⌊2i/p⌋ + (h-1) v_p(4)`.
-/

open Finset

namespace Apery

/-- **Row ZC16 (5.3)**: the valuation of `S_K` in terms of factorial valuations. -/
theorem vS_eq {n : ℕ} (hn : 0 < n) {p : ℕ} (hp : p.Prime) :
    padicValRat p (S n) =
      2 * (37 * n : ℤ) * padicValNat p (40 * n).factorial -
        12 * (37 * n : ℤ) * padicValNat p (3 * n).factorial -
        2 * ∑ i ∈ Icc 1 (37 * n - 1), (padicValNat p (2 * i).factorial : ℤ) +
        ((37 * n : ℤ) - 1) * padicValNat p 4 := by
  have := Fact.mk hp
  rw [S_eq_div]
  have hA : (((40 * n).factorial ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) : ℕ) : ℚ) ≠ 0 := by
    norm_cast; positivity
  have hB : (((3 * n).factorial ^ (12 * (37 * n)) *
      ∏ i ∈ Icc 1 (37 * n - 1), (2 * i).factorial ^ 2 : ℕ) : ℚ) ≠ 0 := by
    norm_cast
    apply mul_ne_zero (by positivity)
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  rw [padicValRat.div hA hB, ← padicValRat_of_nat, ← padicValRat_of_nat,
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (Finset.prod_ne_zero_iff.mpr fun i _ => by positivity),
    padicValNat.pow, padicValNat.pow, padicValNat.pow,
    padicValNat_finset_prod p _ _ (fun i _ => by positivity)]
  simp only [padicValNat.pow]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ 37 * n)]
  push_cast
  simp only [Finset.mul_sum]
  ring

/-- Legendre's formula: `v_p(m!) = ∑_{b=1}^{log_p m} ⌊m/p^b⌋` (as an integer). -/
lemma padicValNat_factorial_int {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (padicValNat p m.factorial : ℤ) = ∑ b ∈ Ico 1 (Nat.log p m + 1), ((m / p ^ b : ℕ) : ℤ) := by
  have := Fact.mk hp
  rw [padicValNat_factorial (Nat.lt_succ_self _)]
  push_cast
  rfl

/-- **ZC16, Legendre form**: every factorial valuation of `vS_eq` written by Legendre's formula. -/
theorem vS_eq_legendre {n : ℕ} (hn : 0 < n) {p : ℕ} (hp : p.Prime) :
    padicValRat p (S n) =
      2 * (37 * n : ℤ) * (∑ b ∈ Ico 1 (Nat.log p (40 * n) + 1), (((40 * n) / p ^ b : ℕ) : ℤ)) -
        12 * (37 * n : ℤ) * (∑ b ∈ Ico 1 (Nat.log p (3 * n) + 1), (((3 * n) / p ^ b : ℕ) : ℤ)) -
        2 * ∑ i ∈ Icc 1 (37 * n - 1),
          (∑ b ∈ Ico 1 (Nat.log p (2 * i) + 1), (((2 * i) / p ^ b : ℕ) : ℤ)) +
        ((37 * n : ℤ) - 1) * padicValNat p 4 := by
  rw [vS_eq hn hp]
  simp only [padicValNat_factorial_int hp]

/-- For `m < p^2` only the first prime power occurs: `v_p(m!) = ⌊m/p⌋`. -/
lemma padicValNat_factorial_lt_sq {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m < p ^ 2) :
    (padicValNat p m.factorial : ℤ) = ((m / p : ℕ) : ℤ) := by
  have := Fact.mk hp
  have hl : Nat.log p m < 2 := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp
    · exact Nat.log_lt_of_lt_pow h.ne' hm
  rw [padicValNat_factorial (b := 2) hl]
  simp

/-- **ZC16, first prime power**: if `p^2 > 2K` (e.g. for the inner primes `p > K/M`, `K ≥ 200 M^2`),
only the first prime power occurs in Legendre's formula. -/
theorem vS_eq_firstPower {n : ℕ} (hn : 0 < n) {p : ℕ} (hp : p.Prime) (hp2 : 2 * (40 * n) < p ^ 2) :
    padicValRat p (S n) =
      2 * (37 * n : ℤ) * (((40 * n) / p : ℕ) : ℤ) - 12 * (37 * n : ℤ) * (((3 * n) / p : ℕ) : ℤ) -
        2 * ∑ i ∈ Icc 1 (37 * n - 1), (((2 * i) / p : ℕ) : ℤ) +
        ((37 * n : ℤ) - 1) * padicValNat p 4 := by
  rw [vS_eq hn hp, padicValNat_factorial_lt_sq hp (by omega : 40 * n < p ^ 2),
    padicValNat_factorial_lt_sq hp (by omega : 3 * n < p ^ 2)]
  have : ∀ i ∈ Icc 1 (37 * n - 1), (padicValNat p (2 * i).factorial : ℤ) = (((2 * i) / p : ℕ) : ℤ) :=
    fun i hi => padicValNat_factorial_lt_sq hp (by
      have := (Finset.mem_Icc.mp hi).2
      omega)
  rw [Finset.sum_congr rfl this]

end Apery
