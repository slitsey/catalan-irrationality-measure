module
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
@[expose] public section

/-!
# Bernstein range bound (generic degree, ordered field, affine subintervals)

For `p(t) = ∑_{i≤d} a_i t^i` the Bernstein coefficients are
`b_k = ∑_{i≤k} C(k,i)/C(d,i) · a_i` and `p(t) = ∑_k b_k C(d,k) t^k (1-t)^(d-k)`.
Hence on `[0,1]`, `min b ≤ p ≤ max b`.  Subdivision / subintervals `[u, u+w]` are handled by the
exact affine substitution `t ↦ u + w t` (`affCoeffs`).
-/

namespace CatalanCore.Uniform.Decay.Tools

open Finset

section Field

variable {K : Type*} [Field K]

/-- Polynomial evaluation of coefficient function `a` up to degree `d`. -/
def peval (a : ℕ → K) (d : ℕ) (t : K) : K := ∑ i ∈ range (d + 1), a i * t ^ i

/-- Bernstein coefficients (degree `d` basis) of `∑ a_i t^i`. -/
def bern (a : ℕ → K) (d k : ℕ) : K :=
  ∑ i ∈ range (k + 1), ((k.choose i : ℕ) : K) / ((d.choose i : ℕ) : K) * a i

/-- Bernstein basis weight. -/
def bw (d k : ℕ) (t : K) : K := ((d.choose k : ℕ) : K) * t ^ k * (1 - t) ^ (d - k)

theorem sum_bw (d : ℕ) (t : K) : ∑ k ∈ range (d + 1), bw d k t = 1 := by
  have := (add_pow t (1 - t) d).symm
  simp only [add_sub_cancel, one_pow] at this
  rw [← this]
  refine sum_congr rfl fun k _ => ?_
  unfold bw; ring

/-- Key moment identity: `∑_{k=i}^d C(k,i) C(d,k) t^k (1-t)^{d-k} = C(d,i) t^i`. -/
theorem sum_Ico_choose_bw (d i : ℕ) (hi : i ≤ d) (t : K) :
    ∑ k ∈ Ico i (d + 1), ((k.choose i : ℕ) : K) * bw d k t = ((d.choose i : ℕ) : K) * t ^ i := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hn : d + 1 - i = (d - i) + 1 := by omega
  rw [hn]
  have key : ∀ l ∈ range ((d - i) + 1),
      (((i + l).choose i : ℕ) : K) * bw d (i + l) t
        = ((d.choose i : ℕ) : K) * (t ^ i * (t ^ l * (1 - t) ^ (d - i - l) *
            (((d - i).choose l : ℕ) : K))) := by
    intro l hl
    have hl' : l ≤ d - i := by have := Finset.mem_range.mp hl; omega
    have hc : d.choose (i + l) * (i + l).choose i = d.choose i * (d - i).choose l := by
      have := Nat.choose_mul (n := d) (k := i + l) (s := i) (by omega)
      simpa using this
    have hc' : (((i + l).choose i : ℕ) : K) * ((d.choose (i + l) : ℕ) : K)
        = ((d.choose i : ℕ) : K) * (((d - i).choose l : ℕ) : K) := by
      have := congrArg (Nat.cast (R := K)) hc
      push_cast at this
      rw [mul_comm]; exact this
    unfold bw
    have e1 : d - (i + l) = d - i - l := by omega
    rw [e1, pow_add]
    calc (((i + l).choose i : ℕ) : K) * (((d.choose (i + l) : ℕ) : K) * (t ^ i * t ^ l) *
          (1 - t) ^ (d - i - l))
        = ((((i + l).choose i : ℕ) : K) * ((d.choose (i + l) : ℕ) : K)) * (t ^ i * t ^ l) *
          (1 - t) ^ (d - i - l) := by ring
      _ = _ := by rw [hc']; ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Finset.mul_sum]
  have := (add_pow t (1 - t) (d - i)).symm
  simp only [add_sub_cancel, one_pow] at this
  rw [this]
  simp

/-- The Bernstein form reproduces the polynomial. -/
theorem peval_eq_bern_sum (a : ℕ → K) (d : ℕ) [CharZero K] (t : K) :
    peval a d t = ∑ k ∈ range (d + 1), bern a d k * bw d k t := by
  unfold peval bern
  simp_rw [Finset.sum_mul]
  have hswap := Finset.sum_Ico_Ico_comm (M := K) 0 (d + 1)
    (fun i k => ((k.choose i : ℕ) : K) / ((d.choose i : ℕ) : K) * a i * bw d k t)
  simp only [Finset.range_eq_Ico] at hswap ⊢
  rw [← hswap]
  refine sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := by have := Finset.mem_Ico.mp hi; omega
  have hpos : ((d.choose i : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hid).ne'
  have h1 := sum_Ico_choose_bw d i hid t
  have : ∑ k ∈ Ico i (d + 1), ((k.choose i : ℕ) : K) / ((d.choose i : ℕ) : K) * a i * bw d k t
      = (a i / ((d.choose i : ℕ) : K)) * ∑ k ∈ Ico i (d + 1), ((k.choose i : ℕ) : K) * bw d k t := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [this, h1]
  field_simp

end Field

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem bw_nonneg (d k : ℕ) {t : K} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ bw d k t := by
  unfold bw
  have : 0 ≤ 1 - t := by linarith
  positivity

/-- **Bernstein range bound** on `[0,1]` for any degree. -/
theorem bernstein_range (a : ℕ → K) (d : ℕ) {lo hi : K}
    (hlo : ∀ k ≤ d, lo ≤ bern a d k) (hhi : ∀ k ≤ d, bern a d k ≤ hi)
    {t : K} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lo ≤ peval a d t ∧ peval a d t ≤ hi := by
  rw [peval_eq_bern_sum]
  have hs := sum_bw d t
  constructor
  · calc lo = ∑ k ∈ range (d + 1), lo * bw d k t := by rw [← Finset.mul_sum, hs, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_right (hlo k (by have := Finset.mem_range.mp hk; omega))
            (bw_nonneg d k h0 h1)
  · calc _ ≤ ∑ k ∈ range (d + 1), hi * bw d k t :=
          Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_right (hhi k (by have := Finset.mem_range.mp hk; omega))
            (bw_nonneg d k h0 h1)
      _ = hi := by rw [← Finset.mul_sum, hs, mul_one]

/-- Boolean checker: all Bernstein coefficients lie in `[lo, hi]`. -/
def bernOk (a : ℕ → K) (d : ℕ) (lo hi : K) : Bool :=
  (List.range (d + 1)).all fun k => decide (lo ≤ bern a d k) && decide (bern a d k ≤ hi)

theorem bernOk_sound {a : ℕ → K} {d : ℕ} {lo hi : K} (h : bernOk a d lo hi = true)
    {t : K} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lo ≤ peval a d t ∧ peval a d t ≤ hi := by
  unfold bernOk at h
  rw [List.all_eq_true] at h
  refine bernstein_range a d (fun k hk => ?_) (fun k hk => ?_) h0 h1
  · have := h k (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := h k (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2

/-- Coefficients of `t ↦ p(u + w t)`. -/
def affCoeffs (a : ℕ → K) (d : ℕ) (u w : K) (j : ℕ) : K :=
  w ^ j * ∑ i ∈ Ico j (d + 1), ((i.choose j : ℕ) : K) * u ^ (i - j) * a i

theorem peval_affCoeffs (a : ℕ → K) (d : ℕ) (u w t : K) :
    peval (affCoeffs a d u w) d t = peval a d (u + w * t) := by
  unfold peval affCoeffs
  have hswap := Finset.sum_Ico_Ico_comm (M := K) 0 (d + 1)
    (fun j i => a i * ((w * t) ^ j * u ^ (i - j) * ((i.choose j : ℕ) : K)))
  simp only [Finset.range_eq_Ico] at hswap ⊢
  have e1 : ∀ i ∈ Ico 0 (d + 1), a i * (u + w * t) ^ i
      = ∑ j ∈ Ico 0 (i + 1), a i * ((w * t) ^ j * u ^ (i - j) * ((i.choose j : ℕ) : K)) := by
    intro i _
    rw [add_comm u (w * t), add_pow, Finset.mul_sum]
    simp only [Finset.range_eq_Ico]
  rw [Finset.sum_congr rfl e1, ← hswap]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_comm, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- Bernstein range bound on the subinterval `[u, u + w]`, `w > 0`. -/
theorem bernstein_range_Icc (a : ℕ → K) (d : ℕ) (u w : K) (hw : 0 < w) {lo hi : K}
    (hlo : ∀ k ≤ d, lo ≤ bern (affCoeffs a d u w) d k)
    (hhi : ∀ k ≤ d, bern (affCoeffs a d u w) d k ≤ hi)
    {x : K} (hx0 : u ≤ x) (hx1 : x ≤ u + w) :
    lo ≤ peval a d x ∧ peval a d x ≤ hi := by
  have ht0 : 0 ≤ (x - u) / w := div_nonneg (by linarith) hw.le
  have ht1 : (x - u) / w ≤ 1 := by rw [div_le_one hw]; linarith
  have := bernstein_range (affCoeffs a d u w) d hlo hhi ht0 ht1
  rw [peval_affCoeffs] at this
  have e : u + w * ((x - u) / w) = x := by field_simp; ring
  rwa [e] at this

/-- Checker for a subinterval. -/
theorem bernOk_Icc_sound {a : ℕ → K} {d : ℕ} {u w lo hi : K} (hw : 0 < w)
    (h : bernOk (affCoeffs a d u w) d lo hi = true) {x : K} (hx0 : u ≤ x) (hx1 : x ≤ u + w) :
    lo ≤ peval a d x ∧ peval a d x ≤ hi := by
  have := bernOk_sound h (t := (x - u) / w) (div_nonneg (by linarith) hw.le)
    (by rw [div_le_one hw]; linarith)
  rw [peval_affCoeffs] at this
  have e : u + w * ((x - u) / w) = x := by field_simp; ring
  rwa [e] at this

end Ordered

end CatalanCore.Uniform.Decay.Tools
