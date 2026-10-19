module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Lemma N (a Pfaff-Saalschutz instance), via three Chu-Vandermonde convolutions

`∑_{a=0}^{N} C(N,a)² (x+a)_{2N} = C(2N,N) ((x+N)_N)²`, over any commutative ring.
-/

@[expose] public section

open Finset Polynomial

namespace CatalanCore.Star.Leonard

variable {R : Type*} [CommRing R]

/-- Falling factorial `y (y-1) … (y-k+1)`. -/
def ffR (y : R) (k : ℕ) : R := ∏ i ∈ Finset.range k, (y - (i : R))

lemma ffR_zero (y : R) : ffR y 0 = 1 := by simp [ffR]

lemma ffR_succ (y : R) (k : ℕ) : ffR y (k + 1) = ffR y k * (y - k) := by
  simp [ffR, Finset.prod_range_succ]

lemma smeval_desc (r : R) (k : ℕ) : (descPochhammer ℤ k).smeval r = ffR r k := by
  induction k with
  | zero => simp [ffR_zero]
  | succ k ih =>
    rw [descPochhammer_succ_right, mul_comm, Polynomial.smeval_mul, ih, ffR_succ]
    simp [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
    ring

/-- Chu-Vandermonde for falling factorials. -/
lemma ffR_add (r s : R) (k : ℕ) :
    ffR (r + s) k = ∑ p ∈ antidiagonal k, (k.choose p.1 : R) * (ffR r p.1 * ffR s p.2) := by
  have := Ring.descPochhammer_smeval_add (R := R) (r := r) (s := s) k (Commute.all r s)
  simp only [smeval_desc] at this
  rw [this]

lemma ffR_nat (a j : ℕ) : ffR (a : R) j = ((a.descFactorial j : ℕ) : R) := by
  induction j with
  | zero => simp [ffR_zero]
  | succ k ih =>
    rw [ffR_succ, ih, Nat.descFactorial_succ]
    by_cases hk : k ≤ a
    · push_cast [Nat.cast_sub hk]; ring
    · have : a.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      rw [this]; simp

lemma ffR_add_nat (y : R) (a b : ℕ) : ffR y (a + b) = ffR y a * ffR (y - a) b := by
  unfold ffR
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast; ring

lemma choose_mul_descFactorial (N a j : ℕ) (hj : j ≤ a) :
    N.choose a * a.descFactorial j = N.descFactorial j * (N - j).choose (a - j) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have := Nat.choose_mul (n := N) hj
  calc N.choose a * (j.factorial * a.choose j) = j.factorial * (N.choose a * a.choose j) := by ring
    _ = _ := by rw [this]; ring

/-- the Vandermonde sum for the moment step -/
lemma vand_moment (N j : ℕ) (hj : j ≤ N) :
    ∑ b ∈ Finset.range (N - j + 1), N.choose (j + b) * (N - j).choose b = (2 * N - j).choose N := by
  have h1 := Nat.add_choose_eq N (N - j) (N - j)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h1
  have e : N + (N - j) = 2 * N - j := by omega
  rw [e] at h1
  have h2 : (2 * N - j).choose (N - j) = (2 * N - j).choose N := by
    have := Nat.choose_symm (n := 2 * N - j) (k := N) (by omega)
    rw [← this]; congr 1; omega
  rw [← h2, h1]
  rw [← Finset.sum_range_reflect (fun b => N.choose (j + b) * (N - j).choose b) (N - j + 1)]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' := Finset.mem_range.1 hb
  simp only
  have e1 : j + (N - j + 1 - 1 - b) = N - b := by omega
  have e2 : N - j + 1 - 1 - b = N - j - b := by omega
  rw [e1, e2, Nat.choose_symm (n := N) (k := b) (by omega)]

/-- Moment step. -/
lemma moment (N j : ℕ) :
    ∑ a ∈ Finset.range (N + 1), ((N.choose a : ℕ) : R) ^ 2 * ffR (a : R) j =
      ffR (N : R) j * (((2 * N - j).choose N : ℕ) : R) := by
  rw [ffR_nat]
  by_cases hj : j ≤ N
  · -- reduce to the nat identity
    have hnat : ∑ a ∈ Finset.range (N + 1), N.choose a * (N.choose a * a.descFactorial j) =
        N.descFactorial j * (2 * N - j).choose N := by
      rw [← vand_moment N j hj, Finset.mul_sum]
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le j) (by omega : j ≤ N + 1)]
      rw [Finset.sum_eq_zero (s := Finset.Ico 0 j), zero_add, Finset.sum_Ico_eq_sum_range]
      · have : N + 1 - j = N - j + 1 := by omega
        rw [this]
        refine Finset.sum_congr rfl fun b hb => ?_
        have hb' := Finset.mem_range.1 hb
        rw [choose_mul_descFactorial N (j + b) j (by omega)]
        rw [Nat.add_sub_cancel_left]; ring
      · intro a ha
        have ha' := Finset.mem_Ico.1 ha
        rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]; simp
    have := congrArg (fun x : ℕ => (x : R)) hnat
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] at this ⊢
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [ffR_nat]; ring
  · have h0 : N.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    rw [h0]; simp only [Nat.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun a ha => ?_
    have := Finset.mem_range.1 ha
    rw [ffR_nat, Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]; simp

lemma ffR_nat_eq_zero (N i : ℕ) (hi : N < i) : ffR (N : R) i = 0 := by
  rw [ffR_nat, Nat.descFactorial_eq_zero_iff_lt.2 hi]; simp

/-- **Lemma N** in falling-factorial form. -/
theorem lemmaN_ff (N : ℕ) (y : R) :
    ∑ a ∈ Finset.range (N + 1), ((N.choose a : ℕ) : R) ^ 2 * ffR ((a : R) + y) (2 * N) =
      ((((2 * N).choose N : ℕ)) : R) * ffR y N ^ 2 := by
  -- Step A and swap
  have hA : ∀ a : ℕ, ((N.choose a : ℕ) : R) ^ 2 * ffR ((a : R) + y) (2 * N) =
      ∑ p ∈ Finset.antidiagonal (2 * N), (((2 * N).choose p.1 : ℕ) : R) * ffR y p.2 *
        (((N.choose a : ℕ) : R) ^ 2 * ffR (a : R) p.1) := by
    intro a
    rw [ffR_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  simp only [hA]
  rw [Finset.sum_comm]
  have hB : ∀ p ∈ Finset.antidiagonal (2 * N),
      ∑ a ∈ Finset.range (N + 1), (((2 * N).choose p.1 : ℕ) : R) * ffR y p.2 *
        (((N.choose a : ℕ) : R) ^ 2 * ffR (a : R) p.1) =
      (((2 * N).choose p.1 : ℕ) : R) * ffR y p.2 * (ffR (N : R) p.1 *
        (((2 * N - p.1).choose N : ℕ) : R)) := by
    intro p _
    rw [← Finset.mul_sum, moment]
  rw [Finset.sum_congr rfl hB, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- restrict to i ≤ N
  have hC : ∑ i ∈ Finset.range (2 * N).succ, (((2 * N).choose (i, 2 * N - i).1 : ℕ) : R) *
        ffR y (i, 2 * N - i).2 * (ffR (N : R) (i, 2 * N - i).1 *
          (((2 * N - (i, 2 * N - i).1).choose N : ℕ) : R)) =
      ∑ i ∈ Finset.range (N + 1), (((2 * N).choose N : ℕ) : R) * ffR y N *
        ((N.choose i : ℕ) * ffR (N : R) i * ffR (y - N) (N - i)) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : N + 1 ≤ (2 * N).succ))]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      simp only
      have e1 : ffR y (2 * N - i) = ffR y N * ffR (y - N) (N - i) := by
        rw [← ffR_add_nat]; congr 1; omega
      have e2 : ((2 * N).choose i) * (2 * N - i).choose N = (2 * N).choose N * N.choose i := by
        have := Nat.choose_mul (n := 2 * N) (k := N) (s := i) (by omega)
        have h3 : (2 * N - i).choose (N - i) = (2 * N - i).choose N := by
          have := Nat.choose_symm (n := 2 * N - i) (k := N) (by omega)
          rw [← this]; congr 1; omega
        rw [this, h3]
      have e2' : (((2 * N).choose i : ℕ) : R) * (((2 * N - i).choose N : ℕ) : R) =
          (((2 * N).choose N : ℕ) : R) * ((N.choose i : ℕ) : R) := by
        have := congrArg (Nat.cast : ℕ → R) e2
        push_cast at this
        exact_mod_cast this
      rw [e1]
      linear_combination (ffR y N * ffR (y - N) (N - i) * ffR (N : R) i) * e2'
    · intro i hi hi'
      have := Finset.mem_range.1 hi
      have : N < i := by
        by_contra h
        exact hi' (Finset.mem_range.2 (by omega))
      simp only
      rw [ffR_nat_eq_zero N i this]; simp
  rw [hC, ← Finset.mul_sum]
  have hD := ffR_add (N : R) (y - N) N
  rw [show (N : R) + (y - N) = y by ring, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hD
  rw [hD]
  simp only [pow_two]
  rw [mul_assoc]
  congr 1
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma ffR_eq_rising (z : R) (k : ℕ) (hk : 1 ≤ k) :
    ffR (z + ((k : R) - 1)) k = ∏ i ∈ Finset.range k, (z + (i : R)) := by
  unfold ffR
  rw [← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

/-- **Lemma N**: `∑_{a=0}^{N} C(N,a)² (x+a)_{2N} = C(2N,N) ((x+N)_N)²` (rising factorials). -/
theorem lemmaN (N : ℕ) (hN : 1 ≤ N) (x : R) :
    ∑ a ∈ Finset.range (N + 1), ((N.choose a : ℕ) : R) ^ 2 *
        ∏ i ∈ Finset.range (2 * N), (x + (a : R) + (i : R)) =
      (((2 * N).choose N : ℕ) : R) * (∏ i ∈ Finset.range N, (x + (N : R) + (i : R))) ^ 2 := by
  have h := lemmaN_ff N (x + (2 * (N : R) - 1))
  have e1 : ∀ a : ℕ, ffR ((a : R) + (x + (2 * (N : R) - 1))) (2 * N) =
      ∏ i ∈ Finset.range (2 * N), (x + (a : R) + (i : R)) := by
    intro a
    have := ffR_eq_rising (x + (a : R)) (2 * N) (by omega)
    rw [show (x + (a : R)) + (((2 * N : ℕ) : R) - 1) = (a : R) + (x + (2 * (N : R) - 1)) by
      push_cast; ring] at this
    exact this
  have e2 : ffR (x + (2 * (N : R) - 1)) N = ∏ i ∈ Finset.range N, (x + (N : R) + (i : R)) := by
    have := ffR_eq_rising (x + (N : R)) N hN
    rw [show (x + (N : R)) + ((N : R) - 1) = x + (2 * (N : R) - 1) by ring] at this
    exact this
  simp only [e1, e2] at h
  exact h

end CatalanCore.Star.Leonard
