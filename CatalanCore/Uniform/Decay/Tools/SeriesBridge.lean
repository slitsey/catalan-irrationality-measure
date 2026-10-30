module

public import CatalanCore.Uniform.Decay.PilotArithmetic
public import CatalanCore.Uniform.Decay.Tools.Enclosures

@[expose] public section
set_option Elab.async false

/-!
# Soundness bridge for the accepted integer series of `PilotArithmetic`

`SignedPilot.series alt a b` (64 terms, scale `10^36 + 39`) is exactly the generic
`scAtanh` / `scAtan` of `Tools.Enclosures`; hence the benchmark constants
`log2Literal` and `piLiteral` carry rigorous enclosures (they were previously only an
arithmetic benchmark with no analytic soundness theorem).
-/

namespace CatalanCore.Uniform.Decay.Tools

open CatalanCore.Uniform.Decay.SignedPilot
open Finset

theorem sign_eq (i : ℕ) : (if i % 2 == 1 then (-1 : ℤ) else 1) = (-1) ^ i := by
  rcases Nat.even_or_odd i with h | h
  · have : i % 2 = 0 := Nat.even_iff.mp h
    simp [this, h.neg_one_pow]
  · have : i % 2 = 1 := Nat.odd_iff.mp h
    simp [this, h.neg_one_pow]

theorem seriesLoop_eq (alt : Bool) (a b : ℕ) :
    ∀ (n k : ℕ) (acc : ℤ),
      seriesLoop alt (a * a) (b * b) n (a * (a * a) ^ k) (b * (b * b) ^ k) k acc
        = acc + ∑ i ∈ range n,
            (if alt && ((k + i) % 2 == 1) then (-1 : ℤ) else 1) * (scTerm scale a b (k + i) : ℤ) := by
  intro n
  induction n with
  | zero => intro k acc; simp [seriesLoop]
  | succ n ih =>
    intro k acc
    have hp : a * (a * a) ^ k * (a * a) = a * (a * a) ^ (k + 1) := by ring
    have hq : b * (b * b) ^ k * (b * b) = b * (b * b) ^ (k + 1) := by ring
    have ht : scale * (a * (a * a) ^ k) / (b * (b * b) ^ k * (2 * k + 1))
        = scTerm scale a b k := by
      unfold scTerm
      have e1 : a * (a * a) ^ k = a ^ (2 * k + 1) := by ring
      have e2 : b * (b * b) ^ k = b ^ (2 * k + 1) := by ring
      rw [e1, e2]
    simp only [seriesLoop]
    rw [hp, hq, ih, Finset.sum_range_succ' _ n, ht]
    have : ∀ i, k + 1 + i = k + (i + 1) := fun i => by omega
    simp only [this, Nat.add_zero]
    by_cases h : (alt && ((k % 2) == 1)) = true
    · simp only [h, ite_true]; ring
    · have h' : ¬ (alt && ((k % 2) == 1)) = true := h
      simp only [h', Bool.false_eq_true, ite_false]; ring

theorem series_true (a b : ℕ) : series true a b = scAtan scale a b 64 := by
  unfold series scAtan
  have := seriesLoop_eq true a b 64 0 0
  simp only [pow_zero, mul_one, zero_add] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Bool.true_and, sign_eq]

theorem series_false (a b : ℕ) : series false a b = (scAtanh scale a b 64 : ℤ) := by
  unfold series scAtanh
  have := seriesLoop_eq false a b 64 0 0
  simp only [pow_zero, mul_one, zero_add] at this
  rw [this]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem scale_pos : 0 < scale := by unfold scale; norm_num

/-- Rigorous enclosure for the 64-term alternating series (ratio `a/b < 1`). -/
theorem series_true_enclosure (a b : ℕ) (hb : 0 < b) (hab : a < b) :
    |((series true a b : ℤ) : ℝ) - (scale : ℝ) * Real.arctan ((a : ℝ) / b)|
      ≤ (2 * 32 : ℕ) + (scale : ℝ) * (((a : ℝ) / b) ^ (2 * (2 * 32) + 1) /
          (2 * ((2 * 32 : ℕ) : ℝ) + 1)) := by
  rw [series_true]
  exact scAtan_enclosure scale a b 32 hb hab

theorem series_false_enclosure (a b : ℕ) (hb : 0 < b) (hab : a < b) :
    |((series false a b : ℤ) : ℝ) -
        (scale : ℝ) * (1 / 2 * Real.log ((1 + (a : ℝ) / b) / (1 - (a : ℝ) / b)))|
      ≤ (64 : ℕ) + (scale : ℝ) * (((a : ℝ) / b) ^ (2 * 64 + 1) / (1 - ((a : ℝ) / b) ^ 2)) := by
  rw [series_false]
  exact_mod_cast scAtanh_enclosure scale a b 64 hb hab

/-- `log 2` literal: error at most 129 (units of `10^-36`). -/
theorem log2Literal_enclosure :
    |(log2Literal : ℝ) - (scale : ℝ) * Real.log 2| ≤ 129 := by
  have h := series_false_enclosure 1 3 (by norm_num) (by norm_num)
  have e : (1 + ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) / (1 - ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = 2 := by
    norm_num
  rw [e] at h
  have hc := constants_check.1
  have hl : (log2Literal : ℝ) = 2 * ((series false 1 3 : ℤ) : ℝ) := by
    rw [← hc]; push_cast; ring
  have htail : (scale : ℝ) * ((((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) ^ (2 * 64 + 1) /
      (1 - (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) ^ 2)) ≤ 1 / 2 := by
    unfold scale; norm_num
  rw [hl]
  have : |2 * ((series false 1 3 : ℤ) : ℝ) - (scale : ℝ) * Real.log 2|
      = 2 * |((series false 1 3 : ℤ) : ℝ) - (scale : ℝ) * (1 / 2 * Real.log 2)| := by
    rw [← abs_two, ← abs_mul]; congr 1; ring
  rw [this]
  push_cast at h htail ⊢
  linarith

/-- `π` literal: error at most 1300. -/
theorem piLiteral_enclosure :
    |(piLiteral : ℝ) - (scale : ℝ) * Real.pi| ≤ 1300 := by
  have h5 := series_true_enclosure 1 5 (by norm_num) (by norm_num)
  have h239 := series_true_enclosure 1 239 (by norm_num) (by norm_num)
  have hc := constants_check.2
  have hl : (piLiteral : ℝ) = 16 * ((series true 1 5 : ℤ) : ℝ) - 4 * ((series true 1 239 : ℤ) : ℝ) := by
    rw [← hc]; push_cast; ring
  have t5 : (scale : ℝ) * ((((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) ^ (2 * (2 * 32) + 1) /
      (2 * ((2 * 32 : ℕ) : ℝ) + 1)) ≤ 1 := by unfold scale; norm_num
  have t239 : (scale : ℝ) * ((((1 : ℕ) : ℝ) / ((239 : ℕ) : ℝ)) ^ (2 * (2 * 32) + 1) /
      (2 * ((2 * 32 : ℕ) : ℝ) + 1)) ≤ 1 := by unfold scale; norm_num
  have mach := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hpi : Real.pi = 16 * Real.arctan ((1 : ℝ) / 5) - 4 * Real.arctan ((1 : ℝ) / 239) := by
    have : Real.arctan (5⁻¹ : ℝ) = Real.arctan ((1 : ℝ) / 5) := by norm_num
    have h2 : Real.arctan (239⁻¹ : ℝ) = Real.arctan ((1 : ℝ) / 239) := by norm_num
    rw [this, h2] at mach
    linarith
  rw [hl, hpi]
  push_cast at h5 h239 t5 t239
  rw [abs_le] at h5 h239 ⊢
  constructor <;> nlinarith [h5.1, h5.2, h239.1, h239.2]

end CatalanCore.Uniform.Decay.Tools
