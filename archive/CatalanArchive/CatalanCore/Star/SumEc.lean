module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Ring.Parity

/-!
# The pole exponents `e_c` and `∑ e_c = D_∞` (hybrid `κ = 0`, package P3)

Pure integer arithmetic.  With `n = K - m`, the cap exponents of `k^gen(θ; K, m, S)` (column set
`J = {1..S-1}`, `S ≥ K - m`) are, writing `Ttr j = j(j+1)/2` for `j > 0` (and `0` otherwise),

* `c ≤ S-1`           : `2 [T(n-1) - T(n-1-min(c,K)) - T(min(c,K)-m-1)]`  (Theorem L);
* `S ≤ c ≤ S+m`       : `n` if `c ≥ K`, `n² - 2 T(c-m-1)` otherwise      (Theorems H / F);
* `S+m < c ≤ S+K+m-1` : `n + 2[T(n-2) - T(d-2m-1) - T(K-2-d)]` if `d = c-S ≤ K-1`,
                         `2[T(n-1) - T(d-2m-1)]` otherwise              (Theorem T);
* otherwise `0`.

`sum_ec` proves `∑_{c=1}^{S+K+m-1} e_c = D_∞` with `D_∞ = K n + n(n-1)(K+m) - n(n²-1)/3`
(equivalently `-E` of GY, `E = -Kn - n(n-1)(K+m) + n(n-1)(n+1)/3`), with no chamber enumeration:
the truncated triangular sums telescope (`sum_Ttr_shift`, `sum_Ttr_neg`).
-/

@[expose] public section

open Finset

namespace CatalanCore.Star

/-- Truncated triangular number. -/
def Ttr (j : ℤ) : ℤ := if j ≤ 0 then 0 else j * (j + 1) / 2

/-- Truncated tetrahedral number. -/
def Tet (j : ℤ) : ℤ := if j ≤ 0 then 0 else j * (j + 1) * (j + 2) / 6

lemma Ttr_nonpos {j : ℤ} (h : j ≤ 0) : Ttr j = 0 := if_pos h
lemma Tet_nonpos {j : ℤ} (h : j ≤ 0) : Tet j = 0 := if_pos h

lemma two_Ttr {j : ℤ} (h : -1 ≤ j) : 2 * Ttr j = j * (j + 1) := by
  by_cases h0 : j ≤ 0
  · have : j = 0 ∨ j = -1 := by omega
    rcases this with rfl | rfl <;> simp [Ttr]
  · unfold Ttr
    rw [if_neg h0]
    exact Int.mul_ediv_cancel' (Int.even_mul_succ_self j).two_dvd

lemma six_Tet {j : ℤ} (h : -2 ≤ j) : 6 * Tet j = j * (j + 1) * (j + 2) := by
  by_cases h0 : j ≤ 0
  · have : j = 0 ∨ j = -1 ∨ j = -2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [Tet]
  · unfold Tet
    rw [if_neg h0]
    apply Int.mul_ediv_cancel'
    apply Int.dvd_of_emod_eq_zero
    have : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5 := by omega
    rcases this with h | h | h | h | h | h <;> simp [Int.mul_emod, Int.add_emod, h]

lemma Tet_succ (j : ℤ) : Tet (j + 1) = Tet j + Ttr (j + 1) := by
  by_cases h : -2 ≤ j
  · have h1 := six_Tet (j := j + 1) (by omega)
    have h2 := six_Tet h
    have h3 := two_Ttr (j := j + 1) (by omega)
    nlinarith
  · rw [Tet_nonpos (by omega), Tet_nonpos (by omega), Ttr_nonpos (by omega)]; rfl

lemma Icc_succ_top {lo hi : ℤ} (h : lo - 1 ≤ hi) :
    Finset.Icc lo (hi + 1) = insert (hi + 1) (Finset.Icc lo hi) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

/-- Chamber-free telescoping of shifted truncated triangular sums. -/
theorem sum_Ttr_shift (b lo hi : ℤ) (h : lo - 1 ≤ hi) :
    ∑ c ∈ Finset.Icc lo hi, Ttr (c - b) = Tet (hi - b) - Tet (lo - 1 - b) := by
  induction hi, h using Int.leInduction with
  | base => rw [Finset.Icc_eq_empty (by omega)]; simp
  | succ hi h ih =>
    rw [Icc_succ_top h, Finset.sum_insert (by simp), ih,
      show hi + 1 - b = (hi - b) + 1 by ring, Tet_succ]
    ring

/-- Reflected version. -/
theorem sum_Ttr_neg (b lo hi : ℤ) (h : lo - 1 ≤ hi) :
    ∑ c ∈ Finset.Icc lo hi, Ttr (b - c) = Tet (b - lo) - Tet (b - hi - 1) := by
  induction hi, h using Int.leInduction with
  | base => rw [Finset.Icc_eq_empty (by omega)]; simp; ring_nf
  | succ hi h ih =>
    rw [Icc_succ_top h, Finset.sum_insert (by simp), ih]
    have e := Tet_succ (b - hi - 2)
    rw [show b - hi - 2 + 1 = b - hi - 1 by ring] at e
    rw [show b - (hi + 1) - 1 = b - hi - 2 by ring, show b - (hi + 1) = b - hi - 1 by ring]
    linarith

lemma sum_Icc_split (f : ℤ → ℤ) (lo mid hi : ℤ) (h1 : lo - 1 ≤ mid) (h2 : mid ≤ hi) :
    ∑ c ∈ Finset.Icc lo hi, f c =
      ∑ c ∈ Finset.Icc lo mid, f c + ∑ c ∈ Finset.Icc (mid + 1) hi, f c := by
  rw [← Finset.sum_union]
  · congr 1; ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  · rw [Finset.disjoint_left]; intro x hx hx'
    simp only [Finset.mem_Icc] at hx hx'; omega

lemma sum_const_Icc (k lo hi : ℤ) (h : lo - 1 ≤ hi) :
    ∑ _c ∈ Finset.Icc lo hi, k = (hi + 1 - lo) * k := by
  rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
  rw [show ((hi + 1 - lo).toNat : ℤ) = hi + 1 - lo from Int.toNat_of_nonneg (by omega)]

/-- The exponent `e_c(K, m, S)` for the column set `{1..S-1}`. -/
def ec (K m S c : ℤ) : ℤ :=
  if c ≤ 0 then 0
  else if c ≤ S - 1 then
    2 * (Ttr (K - m - 1) - Ttr (K - m - 1 - min c K) - Ttr (min c K - m - 1))
  else if c ≤ S + m then
    (if K ≤ c then K - m else (K - m) ^ 2 - 2 * Ttr (c - m - 1))
  else if c ≤ S + K + m - 1 then
    (if c - S ≤ K - 1 then
      (K - m) + 2 * (Ttr (K - m - 2) - Ttr (c - S - 2 * m - 1) - Ttr (K - 2 - (c - S)))
    else 2 * (Ttr (K - m - 1) - Ttr (c - S - 2 * m - 1)))
  else 0

/-- The degree at infinity `D_∞ = K n + n(n-1)(K+m) - n(n²-1)/3`, `n = K - m`. -/
def Dinf (K m : ℤ) : ℤ :=
  K * (K - m) + (K - m) * (K - m - 1) * (K + m) - (K - m) * ((K - m) ^ 2 - 1) / 3

lemma three_Dinf (K m : ℤ) : 3 * Dinf K m =
    3 * (K * (K - m)) + 3 * ((K - m) * (K - m - 1) * (K + m)) - (K - m) * ((K - m) ^ 2 - 1) := by
  unfold Dinf
  have : (3 : ℤ) ∣ (K - m) * ((K - m) ^ 2 - 1) := by
    apply Int.dvd_of_emod_eq_zero
    have : (K - m) % 3 = 0 ∨ (K - m) % 3 = 1 ∨ (K - m) % 3 = 2 := by omega
    rcases this with h | h | h <;> simp [pow_two, Int.mul_emod, Int.sub_emod, h]
  rw [mul_sub, Int.mul_ediv_cancel' this]
  ring

variable {K m S : ℤ}

lemma ec_A {c : ℤ} (h1 : 1 ≤ c) (h2 : c ≤ S - 1) : ec K m S c =
    2 * (Ttr (K - m - 1) - Ttr (K - m - 1 - min c K) - Ttr (min c K - m - 1)) := by
  unfold ec; split_ifs <;> first | rfl | omega

lemma ec_B1 {c : ℤ} (hS : 1 ≤ S) (h1 : S ≤ c) (h2 : c ≤ S + m) (h3 : c < K) :
    ec K m S c = (K - m) ^ 2 - 2 * Ttr (c - m - 1) := by
  unfold ec; split_ifs <;> first | rfl | omega

lemma ec_B2 {c : ℤ} (hm : 0 ≤ m) (hmK : m < K) (hS : 1 ≤ S) (h1 : S ≤ c) (h2 : c ≤ S + m) (h3 : K ≤ c) :
    ec K m S c = K - m := by
  unfold ec; split_ifs <;> first | rfl | omega

lemma ec_C1 {c : ℤ} (hm : 0 ≤ m) (hS : 1 ≤ S) (h1 : S + m + 1 ≤ c) (h2 : c ≤ S + K - 1) :
    ec K m S c = (K - m) +
      2 * (Ttr (K - m - 2) - Ttr (c - S - 2 * m - 1) - Ttr (K - 2 - (c - S))) := by
  unfold ec; split_ifs <;> first | rfl | omega

lemma ec_C2 {c : ℤ} (hm : 0 ≤ m) (hmK : m < K) (hS : 1 ≤ S) (h1 : S + K ≤ c) (h2 : c ≤ S + K + m - 1) :
    ec K m S c = 2 * (Ttr (K - m - 1) - Ttr (c - S - 2 * m - 1)) := by
  unfold ec; split_ifs <;> first | rfl | omega

/-! ### Segment sums -/

lemma segA_le (hm : 0 ≤ m) (hmK : m < K) (hS : K - m ≤ S) (hSK : S ≤ K) :
    ∑ c ∈ Finset.Icc 1 (S - 1), ec K m S c =
      2 * ((S - 1) * Ttr (K - m - 1) - Tet (K - m - 2) - Tet (S - m - 2)) := by
  have h : ∀ c ∈ Finset.Icc 1 (S - 1), ec K m S c =
      2 * Ttr (K - m - 1) - 2 * Ttr ((K - m - 1) - c) - 2 * Ttr (c - (m + 1)) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [ec_A hc.1 hc.2, show min c K = c by omega,
      show c - m - 1 = c - (m + 1) by ring]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_const_Icc _ _ _ (by omega),
    sum_Ttr_neg _ _ _ (by omega), sum_Ttr_shift _ _ _ (by omega),
    Tet_nonpos (j := K - m - 1 - (S - 1) - 1) (by omega), Tet_nonpos (j := 1 - 1 - (m + 1)) (by omega)]
  rw [show K - m - 1 - 1 = K - m - 2 by ring, show S - 1 - (m + 1) = S - m - 2 by ring]
  ring

lemma segA_gt (hm : 0 ≤ m) (hmK : m < K) (hS : K - m ≤ S) (hSK : K + 1 ≤ S) :
    ∑ c ∈ Finset.Icc 1 (S - 1), ec K m S c =
      2 * (K * Ttr (K - m - 1) - Tet (K - m - 2) - Tet (K - m - 1)) := by
  rw [sum_Icc_split _ 1 K (S - 1) (by omega) (by omega)]
  have h0 : ∑ c ∈ Finset.Icc (K + 1) (S - 1), ec K m S c = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    rw [Finset.mem_Icc] at hc
    rw [ec_A (by omega) hc.2, show min c K = K by omega,
      Ttr_nonpos (j := K - m - 1 - K) (by omega)]
    ring
  rw [h0, add_zero]
  have h : ∀ c ∈ Finset.Icc 1 K, ec K m S c =
      2 * Ttr (K - m - 1) - 2 * Ttr ((K - m - 1) - c) - 2 * Ttr (c - (m + 1)) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [ec_A hc.1 (by omega), show min c K = c by omega,
      show c - m - 1 = c - (m + 1) by ring]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_const_Icc _ _ _ (by omega),
    sum_Ttr_neg _ _ _ (by omega), sum_Ttr_shift _ _ _ (by omega),
    Tet_nonpos (j := K - m - 1 - K - 1) (by omega), Tet_nonpos (j := 1 - 1 - (m + 1)) (by omega)]
  rw [show K - m - 1 - 1 = K - m - 2 by ring, show K - (m + 1) = K - m - 1 by ring]
  ring

lemma segB_le (hm : 0 ≤ m) (hmK : m < K) (hS : K - m ≤ S) (hSK : S ≤ K) :
    ∑ c ∈ Finset.Icc S (S + m), ec K m S c =
      (K - S) * (K - m) ^ 2 - 2 * (Tet (K - m - 2) - Tet (S - m - 2)) + (S + m + 1 - K) * (K - m) := by
  rw [sum_Icc_split _ S (K - 1) (S + m) (by omega) (by omega)]
  have h1 : ∀ c ∈ Finset.Icc S (K - 1), ec K m S c =
      (K - m) ^ 2 - 2 * Ttr (c - (m + 1)) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [ec_B1 (by omega) hc.1 (by omega) (by omega), show c - m - 1 = c - (m + 1) by ring]
  have h2 : ∀ c ∈ Finset.Icc (K - 1 + 1) (S + m), ec K m S c = K - m := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    exact ec_B2 hm hmK (by omega) (by omega) hc.2 (by omega)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_const_Icc _ _ _ (by omega), sum_const_Icc _ _ _ (by omega),
    sum_Ttr_shift _ _ _ (by omega)]
  rw [show K - 1 - (m + 1) = K - m - 2 by ring, show S - 1 - (m + 1) = S - m - 2 by ring]
  ring

lemma segB_gt (hm : 0 ≤ m) (hmK : m < K) (hS : K - m ≤ S) (hSK : K + 1 ≤ S) :
    ∑ c ∈ Finset.Icc S (S + m), ec K m S c = (m + 1) * (K - m) := by
  rw [Finset.sum_congr rfl (g := fun _ => K - m) fun c hc => by
    rw [Finset.mem_Icc] at hc
    exact ec_B2 hm hmK (by omega) hc.1 hc.2 (by omega), sum_const_Icc _ _ _ (by omega)]
  ring

lemma segC1 (hm : 0 ≤ m) (hmK : m < K) (hS : K - m ≤ S) :
    ∑ c ∈ Finset.Icc (S + m + 1) (S + K - 1), ec K m S c =
      (K - m - 1) * ((K - m) + 2 * Ttr (K - m - 2)) - 2 * Tet (K - 2 * m - 2) - 2 * Tet (K - m - 3) := by
  have h : ∀ c ∈ Finset.Icc (S + m + 1) (S + K - 1), ec K m S c =
      ((K - m) + 2 * Ttr (K - m - 2)) - 2 * Ttr (c - (S + 2 * m + 1)) - 2 * Ttr ((S + K - 2) - c) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [ec_C1 hm (by omega) hc.1 hc.2, show c - S - 2 * m - 1 = c - (S + 2 * m + 1) by ring,
      show K - 2 - (c - S) = (S + K - 2) - c by ring]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_const_Icc _ _ _ (by omega),
    sum_Ttr_neg _ _ _ (by omega), sum_Ttr_shift _ _ _ (by omega),
    Tet_nonpos (j := S + m + 1 - 1 - (S + 2 * m + 1)) (by omega),
    Tet_nonpos (j := S + K - 2 - (S + K - 1) - 1) (by omega)]
  rw [show S + K - 1 - (S + 2 * m + 1) = K - 2 * m - 2 by ring,
    show S + K - 2 - (S + m + 1) = K - m - 3 by ring,
    show S + K - 1 + 1 - (S + m + 1) = K - m - 1 by ring]
  ring

lemma segC2 (hm : 0 ≤ m) (hmK : m < K) (hS : K - m ≤ S) :
    ∑ c ∈ Finset.Icc (S + K) (S + K + m - 1), ec K m S c =
      2 * m * Ttr (K - m - 1) - 2 * (Tet (K - m - 2) - Tet (K - 2 * m - 2)) := by
  have h : ∀ c ∈ Finset.Icc (S + K) (S + K + m - 1), ec K m S c =
      2 * Ttr (K - m - 1) - 2 * Ttr (c - (S + 2 * m + 1)) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [ec_C2 hm hmK (by omega) hc.1 hc.2, show c - S - 2 * m - 1 = c - (S + 2 * m + 1) by ring]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_const_Icc _ _ _ (by omega), sum_Ttr_shift _ _ _ (by omega)]
  rw [show S + K + m - 1 - (S + 2 * m + 1) = K - m - 2 by ring,
    show S + K - 1 - (S + 2 * m + 1) = K - 2 * m - 2 by ring]
  ring

/-- `∑_c e_c = D_∞` (exact, for `0 ≤ m < K` and `S ≥ K - m`). -/
theorem sum_ec (hm : 0 ≤ m) (hmK : m < K) (hS : K - m ≤ S) :
    ∑ c ∈ Finset.Icc 1 (S + K + m - 1), ec K m S c = Dinf K m := by
  have hsplit : ∑ c ∈ Finset.Icc 1 (S + K + m - 1), ec K m S c =
      ∑ c ∈ Finset.Icc 1 (S - 1), ec K m S c + ∑ c ∈ Finset.Icc S (S + m), ec K m S c +
      ∑ c ∈ Finset.Icc (S + m + 1) (S + K - 1), ec K m S c +
      ∑ c ∈ Finset.Icc (S + K) (S + K + m - 1), ec K m S c := by
    rw [sum_Icc_split _ 1 (S - 1) (S + K + m - 1) (by omega) (by omega),
      sum_Icc_split _ (S - 1 + 1) (S + m) (S + K + m - 1) (by omega) (by omega),
      sum_Icc_split _ (S + m + 1) (S + K - 1) (S + K + m - 1) (by omega) (by omega),
      show S - 1 + 1 = S by ring, show S + K - 1 + 1 = S + K by ring]
    ring
  rw [hsplit]
  have hD : (Dinf K m : ℚ) = (3 * ((K : ℚ) * (K - m)) + 3 * ((K - m) * (K - m - 1) * (K + m)) -
      (K - m) * ((K - m) ^ 2 - 1)) / 3 := by
    have h3 := three_Dinf K m
    have : (3 : ℚ) * (Dinf K m : ℚ) = 3 * ((K : ℚ) * (K - m)) + 3 * ((K - m) * (K - m - 1) * (K + m)) -
      (K - m) * ((K - m) ^ 2 - 1) := by exact_mod_cast h3
    rw [eq_div_iff (by norm_num)]; linarith
  have p1 : ((Ttr (K - m - 1) : ℤ) : ℚ) = ((K : ℚ) - m - 1) * ((K : ℚ) - m) / 2 := by
    have := two_Ttr (j := K - m - 1) (by omega)
    have h : (2 : ℚ) * (Ttr (K - m - 1) : ℚ) = ((K : ℚ) - m - 1) * ((K : ℚ) - m - 1 + 1) := by
      exact_mod_cast this
    linarith
  have p2 : ((Ttr (K - m - 2) : ℤ) : ℚ) = ((K : ℚ) - m - 2) * ((K : ℚ) - m - 1) / 2 := by
    have := two_Ttr (j := K - m - 2) (by omega)
    have h : (2 : ℚ) * (Ttr (K - m - 2) : ℚ) = ((K : ℚ) - m - 2) * ((K : ℚ) - m - 2 + 1) := by
      exact_mod_cast this
    linarith
  have t1 : ((Tet (K - m - 2) : ℤ) : ℚ) =
      ((K : ℚ) - m - 2) * ((K : ℚ) - m - 1) * ((K : ℚ) - m) / 6 := by
    have := six_Tet (j := K - m - 2) (by omega)
    have h : (6 : ℚ) * (Tet (K - m - 2) : ℚ) =
        ((K : ℚ) - m - 2) * ((K : ℚ) - m - 2 + 1) * ((K : ℚ) - m - 2 + 2) := by
      exact_mod_cast this
    linarith
  have t2 : ((Tet (K - m - 3) : ℤ) : ℚ) =
      ((K : ℚ) - m - 3) * ((K : ℚ) - m - 2) * ((K : ℚ) - m - 1) / 6 := by
    have := six_Tet (j := K - m - 3) (by omega)
    have h : (6 : ℚ) * (Tet (K - m - 3) : ℚ) =
        ((K : ℚ) - m - 3) * ((K : ℚ) - m - 3 + 1) * ((K : ℚ) - m - 3 + 2) := by
      exact_mod_cast this
    linarith
  have t3 : ((Tet (K - m - 1) : ℤ) : ℚ) =
      ((K : ℚ) - m - 1) * ((K : ℚ) - m) * ((K : ℚ) - m + 1) / 6 := by
    have := six_Tet (j := K - m - 1) (by omega)
    have h : (6 : ℚ) * (Tet (K - m - 1) : ℚ) =
        ((K : ℚ) - m - 1) * ((K : ℚ) - m - 1 + 1) * ((K : ℚ) - m - 1 + 2) := by
      exact_mod_cast this
    linarith
  apply Int.cast_injective (α := ℚ)
  rcases le_or_gt S K with h | h
  · rw [segA_le hm hmK hS h, segB_le hm hmK hS h, segC1 hm hmK hS, segC2 hm hmK hS]
    push_cast
    rw [hD, p1, p2, t1, t2]
    ring
  · rw [segA_gt hm hmK hS h, segB_gt hm hmK hS h, segC1 hm hmK hS, segC2 hm hmK hS]
    push_cast
    rw [hD, p1, p2, t1, t2, t3]
    ring

end CatalanCore.Star
