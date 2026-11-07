module

public import CatalanCore.Uniform.Bank.Fourths.Pipeline
public import CatalanFrames.Thirds.Frame
public import CatalanCore.Uniform.Content.Smith.LP1Table

@[expose] public section
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

theorem q4_simple_poles (a p N : ℕ) (ha : a = 1 ∨ a = 3)
    (hp29 : 29 ≤ p) (hN : N ≤ 2 * p) :
    ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ 4 * t - (4 - a) := by
  intro t ht htN hd
  have hn : 0 < 4 * t - (4 - a) := by omega
  have hle := Nat.le_of_dvd hn hd
  have hlt : 4 * t - (4 - a) < 8 * p := by omega
  nlinarith

#print axioms pipeline_twoTerm
end CatalanCore.Uniform.Bank.Fourths
