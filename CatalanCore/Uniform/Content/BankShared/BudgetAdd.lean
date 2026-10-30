module

public import CatalanCore.Uniform.Content.SmallPrimes.Budget

@[expose] public section
set_option Elab.async false

/-! # Sums of small-prime budgets (lane B, B5c)

`SmallBudget.add` is the pointwise sum of two budgets (cut: the larger cut), and `SmallBudget.unit`
is the budget `X r p = 1` on `p <= r`, whose total `sum_{p <= r} log p <= (r + 1) log r` is `o(r^2)`.
Used to absorb the rounding `2 r + 2 m <= alpha0 r + 1` of a prefix template. -/

namespace CatalanCore.Uniform.Content.BankShared
open Finset Filter CatalanCore.Uniform.Content.SmallPrimes

theorem sum_prime_log_le (n : ℕ) :
    ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p ≤ ((n : ℝ) + 1) * Real.log (n + 1) := by
  have h : ∀ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p ≤ Real.log (n + 1) := by
    intro p hp
    have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    have hpp := (Finset.mem_filter.mp hp).2
    exact Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast Nat.le_succ_of_le hpn)
  calc _ ≤ ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log (n + 1) := Finset.sum_le_sum h
    _ = (((range (n + 1)).filter Nat.Prime).card : ℝ) * Real.log (n + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n : ℝ) + 1) * Real.log (n + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))
        have h1 : ((range (n + 1)).filter Nat.Prime).card ≤ n + 1 :=
          (Finset.card_filter_le _ _).trans (by simp)
        exact_mod_cast h1

theorem unit_small (ε : ℝ) (hε : 0 < ε) : ∀ᶠ r : ℕ in atTop,
    ((r : ℝ) + 1) * (1 * Real.log r) ≤ ε * (r : ℝ) ^ 2 := by
  have hlim : Tendsto (fun r : ℕ => Real.sqrt r) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop (8 / ε)), eventually_ge_atTop 1] with r hr h1
  have hx : (1 : ℝ) ≤ r := by exact_mod_cast h1
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.2 (by linarith)
  have hss : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (by linarith)
  have hlog : Real.log r ≤ 2 * Real.sqrt r := by
    have h := Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log (Real.sqrt r) = Real.log r / 2 := Real.log_sqrt (by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hx
  have hε8 : 8 ≤ ε * Real.sqrt r := by
    have := mul_le_mul_of_nonneg_left hr hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  calc ((r : ℝ) + 1) * (1 * Real.log r) ≤ (2 * r) * (2 * Real.sqrt r) := by
        rw [one_mul]
        exact mul_le_mul (by linarith) hlog hlog0 (by positivity)
    _ = 4 * r * Real.sqrt r := by ring
    _ ≤ ε * (r : ℝ) ^ 2 := by
        have : ε * (r : ℝ) ^ 2 = (ε * Real.sqrt r) * (r * Real.sqrt r) := by
          rw [show (r : ℝ) ^ 2 = r * (Real.sqrt r * Real.sqrt r) by rw [hss]; ring]; ring
        rw [this]
        have hpos : 0 ≤ (r : ℝ) * Real.sqrt r := by positivity
        nlinarith

/-- The budget `X r p = 1` on `p <= r`. -/
noncomputable def SmallBudget.unit : SmallBudget :=
  SmallBudget.ofCutoff (fun r => r) (fun r => r) (fun _ => 1) (fun _ => zero_le_one)
    (fun _ => le_rfl) (fun ε hε => by
      filter_upwards [unit_small ε hε] with r hr
      exact hr)

/-- Pointwise sum of two budgets. -/
noncomputable def SmallBudget.add (B1 B2 : SmallBudget) : SmallBudget where
  X := fun r p => B1.X r p + B2.X r p
  cut := fun r => max (B1.cut r) (B2.cut r)
  nonneg := fun r p => add_nonneg (B1.nonneg r p) (B2.nonneg r p)
  supp := fun r p hp => by
    rw [B1.supp r p (lt_of_le_of_lt (le_max_left _ _) hp), B2.supp r p (lt_of_le_of_lt (le_max_right _ _) hp), add_zero]
  small := fun ε hε => by
    filter_upwards [B1.small (ε / 2) (by linarith), B2.small (ε / 2) (by linarith)] with r h1 h2
    have e1 : ∑ p ∈ (range (max (B1.cut r) (B2.cut r) + 1)).filter Nat.Prime, B1.X r p * Real.log p =
        ∑ p ∈ (range (B1.cut r + 1)).filter Nat.Prime, B1.X r p * Real.log p := by
      symm
      apply Finset.sum_subset
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
        have hm := le_max_left (B1.cut r) (B2.cut r)
        exact ⟨by omega, hp.2⟩
      · intro p hp hn
        rw [Finset.mem_filter, Finset.mem_range] at hp
        have hc : B1.cut r < p := by
          by_contra h
          exact hn (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp.2⟩)
        simp [B1.supp r p hc]
    have e2 : ∑ p ∈ (range (max (B1.cut r) (B2.cut r) + 1)).filter Nat.Prime, B2.X r p * Real.log p =
        ∑ p ∈ (range (B2.cut r + 1)).filter Nat.Prime, B2.X r p * Real.log p := by
      symm
      apply Finset.sum_subset
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
        have hm := le_max_right (B1.cut r) (B2.cut r)
        exact ⟨by omega, hp.2⟩
      · intro p hp hn
        rw [Finset.mem_filter, Finset.mem_range] at hp
        have hc : B2.cut r < p := by
          by_contra h
          exact hn (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp.2⟩)
        simp [B2.supp r p hc]
    simp only [add_mul, Finset.sum_add_distrib, e1, e2]
    linarith

/-- The budget `X r p = C` on `p <= r` for `r < R0`, and `0` for large `r`. -/
noncomputable def SmallBudget.early (R0 C : ℕ) : SmallBudget :=
  SmallBudget.ofCutoff (fun r => r) (fun r => r) (fun r => if r < R0 then (C : ℝ) else 0)
    (fun r => by split_ifs <;> positivity) (fun _ => le_rfl) (fun ε hε => by
      filter_upwards [eventually_ge_atTop R0] with r hr
      have h : ¬ r < R0 := not_lt.2 hr
      simp only [h, if_false, zero_mul, mul_zero]
      positivity)

end CatalanCore.Uniform.Content.BankShared
