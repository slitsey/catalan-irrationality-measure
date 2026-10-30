import CatalanCore.Uniform.Bank.Fourths.Pipeline
import CatalanCore.Uniform.Bank.Fourths.Roots
import CatalanFrames.Thirds.Frame
import CatalanCore.Uniform.Content.Smith.LP1Table
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Fourths
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Smith

/-- The norm-one pipeline has the exact increment data used by the strict LP theorems. -/
theorem pipeline_twoTerm (a : ℕ) (ha : a = 1 ∨ a = 3) :
    TwoTermData (pipelineFrame a ha) 4 (4 - a) := by
  have h0 : (0 : ℚ) < (a : ℚ) / 4 := by rcases ha with rfl | rfl <;> norm_num
  have h1 : (a : ℚ) / 4 < 1 := by rcases ha with rfl | rfl <;> norm_num
  have he (t : ℕ) : (t : ℚ) - 1 + (a : ℚ) / 4 =
      (4 * (t : ℚ) - ((4 - a : ℕ) : ℚ)) / 4 := by
    rw [Nat.cast_sub (by omega : a ≤ 4)]
    push_cast
    ring
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro t ht
    change (CatalanFrames.Thirds.thirdsFrame ((a : ℚ) / 4) 1
      (if a = 1 then 5 / 8 else 3 / 8) (3 / 8) (if a = 1 then 1 else 0)
      h0 h1 (by norm_num)).Delta t = _
    rw [CatalanFrames.Thirds.Delta_eq, he, one_div_div]
    norm_num only [Nat.cast_ofNat]
  · intro t ht
    change (CatalanFrames.Thirds.thirdsFrame ((a : ℚ) / 4) 1
      (if a = 1 then 5 / 8 else 3 / 8) (3 / 8) (if a = 1 then 1 else 0)
      h0 h1 (by norm_num)).Dsq t = _
    rw [CatalanFrames.Thirds.Dsq_eq, he, div_pow, one_div_div]
    norm_num only [Nat.cast_ofNat]

theorem one_based_pole4 (a p : ℕ) (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p)
    (hodd : p % 2 = 1) :
    (root4 a p = 1 ∨ root4 a p = 3) ∧
    4 * (pole4 a p + 1) = root4 a p * p + (4 - a) ∧
    0 < pole4 a p + 1 ∧ pole4 a p + 1 < p ∧ 0 < root4 a p := by
  obtain ⟨hj, hk, hkp⟩ := root4_spec a p ha hodd
  have hroot : 4 * pole4 a p + a = root4 a p * p := by simpa [Nat.mul_comm] using hk
  have hja : root4 a p ≤ 3 := by omega
  have hjp : root4 a p * p ≤ 3 * p := Nat.mul_le_mul_right p hja
  exact ⟨hj, by omega, by omega, by omega, by omega⟩

theorem q4_simple_poles (a p N : ℕ) (ha : a = 1 ∨ a = 3)
    (hp29 : 29 ≤ p) (hN : N ≤ 2 * p) :
    ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ 4 * t - (4 - a) := by
  intro t ht htN hd
  have hn : 0 < 4 * t - (4 - a) := by omega
  have hle := Nat.le_of_dvd hn hd
  have hlt : 4 * t - (4 - a) < 8 * p := by omega
  nlinarith

theorem pipeline_lp1_hyp (a p r m : ℕ) [Fact p.Prime] (ha : a = 1 ∨ a = 3)
    (hp29 : 29 ≤ p) (hodd : p % 2 = 1) (hN : r + 2 * m ≤ 2 * p)
    (hrp : p ≤ r) (hUk : r < p + (pole4 a p + 1)) :
    LP1Hyp (pipelineFrame a ha) p 4 (4 - a) r m (pole4 a p + 1) (root4 a p) := by
  obtain ⟨hj, hk, hk0, hkp, hj0⟩ := one_based_pole4 a p ha hp29 hodd
  refine ⟨⟨pipeline_twoTerm a ha, ⟨by omega, hk, hk0, hkp, hj0, hN⟩,
    q4_simple_poles a p (r + 2 * m) ha hp29 hN, ?_, ?_⟩, hrp, hUk, by omega⟩
  · change (1 : ℚ) ∈ S p
    exact (S p).one_mem
  · change red p (1 : ℚ) ≠ 0
    rw [(Good.one (ℓ := p)).eq]
    exact one_ne_zero

theorem pipeline_lp2_hyp (a p r m : ℕ) [Fact p.Prime] (ha : a = 1 ∨ a = 3)
    (hp29 : 29 ≤ p) (hodd : p % 2 = 1)
    (hN : r + 2 * m ≤ p + (pole4 a p + 1)) (hrp : r < p) (hkr : pole4 a p + 1 ≤ r) :
    LP2Hyp (pipelineFrame a ha) p 4 (4 - a) r m (pole4 a p + 1) (root4 a p) := by
  obtain ⟨hj, hk, hk0, hkp, hj0⟩ := one_based_pole4 a p ha hp29 hodd
  have hN2 : r + 2 * m ≤ 2 * p := by omega
  refine ⟨⟨pipeline_twoTerm a ha, ⟨by omega, hk, hk0, hkp, hj0, hN⟩,
    q4_simple_poles a p (r + 2 * m) ha hp29 hN2, ?_, ?_⟩, hrp, hkr, by omega⟩
  · change (1 : ℚ) ∈ S p
    exact (S p).one_mem
  · change red p (1 : ℚ) ≠ 0
    rw [(Good.one (ℓ := p)).eq]
    exact one_ne_zero

#print axioms pipeline_twoTerm
#print axioms pipeline_lp1_hyp
#print axioms pipeline_lp2_hyp
end CatalanCore.Uniform.Bank.Fourths
