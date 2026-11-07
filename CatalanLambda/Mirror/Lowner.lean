module

public import CatalanLambda.Decay.Lowner
public import CatalanLambda.Mirror.NVMod

@[expose] public section

/-!
# Mirror constant: Löwner form of `-(λ' I + N₀)`

`lowFB x = ∑_{j≥0} [1/(x+j+1/4) - 1/(x+j+1)] = ψ(x+1) - ψ(x+1/4)`.  We prove
`(lowFB a - lowFB b)/(a-b)/16 = -N0n a b` for naturals `a ≠ b`, and `lowFB' a / 16 = -(λ' + N0n a a)`,
where `λ' = ∑_{k≥0} [1/(4k+1)² - 1/(16(k+1)²)] = G/2 + 5π²/96`.
-/

open Finset

namespace CatalanLambda.Mirror

open CatalanLambda.Decay (summable_inv_sq_add sum_Ioc_eq_sum_Ico sum_Icc_one_eq
  hasDerivAt_inv_add)

/-- The real series `F̄(x) = ∑_j [1/(x+j+1/4) - 1/(x+j+1)]`. -/
noncomputable def lowFB (x : ℝ) : ℝ := ∑' j : ℕ, (1 / (x + j + 1 / 4) - 1 / (x + j + 1))

/-- `λ' = ∑_{k≥0} [1/(4k+1)² - 1/(16(k+1)²)]`. -/
noncomputable def lamB : ℝ :=
  ∑' k : ℕ, (1 / (4 * (k : ℝ) + 1) ^ 2 - 1 / (16 * ((k : ℝ) + 1) ^ 2))

/-- term function on naturals -/
noncomputable def lowGnB (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1 / 4) - 1 / ((m : ℝ) + 1)

theorem lowF_natB (n : ℕ) : lowFB n = ∑' j : ℕ, lowGnB (j + n) := by
  unfold lowFB
  congr 1; ext j
  simp only [lowGnB]; push_cast; ring_nf

/-- `k`-th term of `λ'`, rewritten. -/
theorem lamTermB_eq (k : ℝ) (hk : 0 ≤ k) :
    1 / (4 * k + 1) ^ 2 - 1 / (16 * (k + 1) ^ 2)
      = (1 / 16) * (1 / (k + 1 / 4) ^ 2 - 1 / (k + 1) ^ 2) := by
  have : k + 1 / 4 ≠ 0 := by positivity
  have : k + 1 ≠ 0 := by positivity
  have h : 4 * k + 1 = 4 * (k + 1 / 4) := by ring
  rw [h]
  field_simp
  ring

theorem summable_lamTermB : Summable fun k : ℕ =>
    (1 / (4 * (k : ℝ) + 1) ^ 2 - 1 / (16 * ((k : ℝ) + 1) ^ 2)) := by
  have h1 := summable_inv_sq_add (1 / 4) (by norm_num)
  have h2 := summable_inv_sq_add 1 one_pos
  have := (h1.sub h2).mul_left (1 / 16)
  convert this using 2 with k
  exact lamTermB_eq k (Nat.cast_nonneg k)

end CatalanLambda.Mirror
