module

public import CatalanCore.Arith.Hybrid.Extra

@[expose] public section

/-!
# Small-prime budgets (lane H14)

At a tiny prime `p` a hybrid frame has price about `r log r` (higher levels `p^k`), not
`alpha0 * r`.  Such primes are few: those with `p^2 <= L r` number at most `sqrt (L r) + 1`, so their
total contribution `sum price * log p` is `O(r^(3/2) log^2 r) = o(r^2)`.

`SmallBudget` packages an extra price `X r p >= 0`, supported on `p <= r`, with
`sum_{p <= r} X r p * log p = o(r^2)`.  The content assembler (`Cover`) then needs the class
prefix bound only in the form `price <= alpha0 * r + X r p`.  `SmallBudget.sqrtLog L C` is the
data-free instance `X r p = C r (log_2 r + 1)` for `p <= r`, `p^2 <= L r`, and `0` otherwise;
`SmallBudget.ofCutoff` is the general cutoff form.
-/

open Finset Filter Topology

namespace CatalanCore.Uniform.Content.SmallPrimes

/-- An extra small-prime price: nonnegative, supported on `p <= cut r`, with total `o(r^2)`. -/
structure SmallBudget where
  X : ℕ -> ℕ -> ℝ
  cut : ℕ -> ℕ
  nonneg : ∀ r p, 0 <= X r p
  supp : ∀ r p, cut r < p -> X r p = 0
  small : ∀ ε : ℝ, 0 < ε -> ∀ᶠ r : ℕ in atTop,
    ∑ p ∈ (range (cut r + 1)).filter Nat.Prime, X r p * Real.log p <= ε * (r : ℝ) ^ 2

/-- Cutoff estimate: a price `<= A` on `p <= s` and `0` beyond has total `<= (s+1) A log r`. -/
theorem sum_cutoff_le (n s : ℕ) (A : ℝ) (hA : 0 <= A) (X : ℕ -> ℝ)
    (hX0 : ∀ p, 0 <= X p) (hX : ∀ p, X p <= if p <= s then A else 0) :
    ∑ p ∈ (range (n + 1)).filter Nat.Prime, X p * Real.log p <=
      ((s : ℝ) + 1) * (A * Real.log n) := by
  set S := (range (n + 1)).filter Nat.Prime with hS
  have hlr : 0 <= Real.log n := Real.log_natCast_nonneg n
  have hterm : ∀ p ∈ S, X p * Real.log p <= if p <= s then A * Real.log n else 0 := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hpr : p <= n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    have hlp : 0 <= Real.log p := Real.log_natCast_nonneg p
    have hlle : Real.log p <= Real.log n :=
      Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hpr)
    by_cases h : p <= s
    · rw [if_pos h]
      have := hX p
      rw [if_pos h] at this
      exact mul_le_mul this hlle hlp hA
    · rw [if_neg h]
      have := hX p
      rw [if_neg h] at this
      have h0 : X p = 0 := le_antisymm this (hX0 p)
      rw [h0]; simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hsub : S.filter (fun p => p <= s) ⊆ Finset.range (s + 1) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    omega
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_range] at hcard
  have hcR : ((S.filter (fun p => p <= s)).card : ℝ) <= (s : ℝ) + 1 := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hcR (mul_nonneg hA hlr)

/-- **General cutoff budget.**  A price `A r` on primes `p <= s r` with
`(s r + 1) A r log r = o(r^2)`. -/
noncomputable def SmallBudget.ofCutoff (n s : ℕ -> ℕ) (A : ℕ -> ℝ) (hA : ∀ r, 0 <= A r)
    (hsn : ∀ r, s r <= n r)
    (hsmall : ∀ ε : ℝ, 0 < ε -> ∀ᶠ r : ℕ in atTop,
      ((s r : ℝ) + 1) * (A r * Real.log (n r)) <= ε * (r : ℝ) ^ 2) : SmallBudget where
  X := fun r p => if p <= s r then A r else 0
  cut := n
  nonneg := fun r p => by
    by_cases h : p <= s r <;> simp [h, hA r]
  supp := fun r p hp => by
    by_cases h : p <= s r
    · exact absurd hp (by have := hsn r; omega)
    · simp [h]
  small := fun ε hε => by
    filter_upwards [hsmall ε hε] with r hr
    refine (sum_cutoff_le (n r) (s r) (A r) (hA r) _ (fun p => ?_) (fun p => ?_)).trans hr
    · by_cases h : p <= s r <;> simp [h, hA r]
    · simp

/-- The data-free asymptotics: `(sqrt (L r) + 1) * C r (log_2 r + 1) * log (L r) = o(r^2)`. -/
theorem sqrtLog_small (L C : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      ((Nat.sqrt (L * r) : ℝ) + 1) *
          (((C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1)) * Real.log ((L * r : ℕ) : ℝ)) <=
        ε * (r : ℝ) ^ 2 := by
  set Lam : ℝ := Real.log ((L : ℝ) + 1) + 1 with hLam
  have hlL : 0 <= Real.log ((L : ℝ) + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) <= L := Nat.cast_nonneg _; linarith)
  have hLam1 : 1 <= Lam := by linarith
  have hK : (0 : ℝ) < 1200 * ((C : ℝ) + 1) * (Real.sqrt L + 1) * Lam := by positivity
  set δ : ℝ := ε / (1200 * ((C : ℝ) + 1) * (Real.sqrt L + 1) * Lam) with hδ
  have hδ0 : 0 < δ := by positivity
  have hlim := (CatalanCore.Arith.Hybrid.asymp_aux.comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds hδ0)
  filter_upwards [hlim, eventually_ge_atTop 3] with r hr h3
  simp only [Function.comp] at hr
  have hx : (3 : ℝ) <= r := by exact_mod_cast h3
  have hx0 : (0 : ℝ) < r := by linarith
  have hlr : 1 <= Real.log r := by
    have h1 : Real.exp 1 <= 3 := by
      have := Real.exp_one_lt_d9; linarith
    by_contra hh
    push_neg at hh
    have : (r : ℝ) < Real.exp 1 := by
      rw [← Real.exp_log hx0]; exact Real.exp_lt_exp.mpr hh
    linarith
  have hsr : (1 : ℝ) <= Real.sqrt r := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsL : 0 <= Real.sqrt L := Real.sqrt_nonneg _
  have hS : (Nat.sqrt (L * r) : ℝ) + 1 <= (Real.sqrt L + 1) * Real.sqrt r := by
    have h1 := Real.nat_sqrt_le_real_sqrt (a := L * r)
    have h2 : Real.sqrt ((L * r : ℕ) : ℝ) = Real.sqrt L * Real.sqrt r := by
      push_cast; exact Real.sqrt_mul (Nat.cast_nonneg _) _
    nlinarith
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hNL : (Nat.log 2 r : ℝ) <= 2 * Real.log r := by
    have h1 := Real.natLog_le_logb r 2
    have h2 : Real.logb 2 (r : ℝ) <= 2 * Real.log r := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    exact h1.trans h2
  have hNL0 : (0 : ℝ) <= (Nat.log 2 r : ℝ) := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) <= C := Nat.cast_nonneg _
  have hlin : (Nat.log 2 r : ℝ) + 1 <= 3 * Real.log r := by linarith
  have hlg : Real.log ((L * r : ℕ) : ℝ) <= Lam * Real.log r := by
    have h1 : Real.log ((L * r : ℕ) : ℝ) <= Real.log (((L : ℝ) + 1) * r) := by
      rcases Nat.eq_zero_or_pos (L * r) with h | h
      · rw [h]
        simp only [Nat.cast_zero, Real.log_zero]
        apply Real.log_nonneg
        have : (0 : ℝ) <= L := Nat.cast_nonneg _
        nlinarith
      · exact Real.log_le_log (by exact_mod_cast h) (by push_cast; nlinarith)
    have h2 : Real.log (((L : ℝ) + 1) * r) = Real.log ((L : ℝ) + 1) + Real.log r :=
      Real.log_mul (by positivity) hx0.ne'
    have h3' : Real.log ((L : ℝ) + 1) <= Real.log ((L : ℝ) + 1) * Real.log r := by
      nlinarith
    rw [hLam]
    nlinarith
  have hlast : 200 * (Real.log r) ^ 2 * Real.sqrt r / r < δ := by
    have : 0 <= 8 / (r : ℝ) := by positivity
    linarith
  have hkey : (Real.log r) ^ 2 * Real.sqrt r * r <= δ / 200 * (r : ℝ) ^ 2 := by
    have h1 : 200 * (Real.log r) ^ 2 * Real.sqrt r < δ * r := by
      rwa [div_lt_iff₀ hx0] at hlast
    nlinarith
  have hA0 : 0 <= (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by positivity
  have hlr0 : (0 : ℝ) <= Real.log r := by linarith
  have hstep : ((Nat.sqrt (L * r) : ℝ) + 1) *
      (((C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1)) * Real.log ((L * r : ℕ) : ℝ)) <=
      ((Real.sqrt L + 1) * Real.sqrt r) *
        (((C : ℝ) * r * (3 * Real.log r)) * (Lam * Real.log r)) := by
    have hA : (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) <=
        (C : ℝ) * r * (3 * Real.log r) :=
      mul_le_mul_of_nonneg_left hlin (by positivity)
    exact mul_le_mul hS (mul_le_mul hA hlg (Real.log_natCast_nonneg _) (by positivity))
      (by positivity) (by positivity)
  have hrew : ((Real.sqrt L + 1) * Real.sqrt r) *
      (((C : ℝ) * r * (3 * Real.log r)) * (Lam * Real.log r)) =
      3 * (C : ℝ) * (Real.sqrt L + 1) * Lam * ((Real.log r) ^ 2 * Real.sqrt r * r) := by ring
  have hfin : 3 * (C : ℝ) * (Real.sqrt L + 1) * Lam * ((Real.log r) ^ 2 * Real.sqrt r * r) <=
      3 * (C : ℝ) * (Real.sqrt L + 1) * Lam * (δ / 200 * (r : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have hδe : 3 * (C : ℝ) * (Real.sqrt L + 1) * Lam * (δ / 200) <= ε := by
    have h1 : 3 * (C : ℝ) * (Real.sqrt L + 1) * Lam * (δ / 200) =
        (3 * (C : ℝ) / 200) * ((Real.sqrt L + 1) * Lam * δ) := by ring
    have h2 : (3 * (C : ℝ) / 200) <= 1200 * ((C : ℝ) + 1) := by linarith
    have h3' : 0 <= (Real.sqrt L + 1) * Lam * δ := by positivity
    have h4 : 1200 * ((C : ℝ) + 1) * ((Real.sqrt L + 1) * Lam * δ) = ε := by
      rw [hδ]; field_simp
    rw [h1]
    nlinarith
  have hsq : (0 : ℝ) <= (r : ℝ) ^ 2 := sq_nonneg _
  calc _ <= _ := hstep
    _ = _ := hrew
    _ <= _ := hfin
    _ = (3 * (C : ℝ) * (Real.sqrt L + 1) * Lam * (δ / 200)) * (r : ℝ) ^ 2 := by ring
    _ <= ε * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hδe hsq

/-- **The data-free hybrid budget.**  A higher-level price `C r (log_2 r + 1)` at the primes
with `p^2 <= L r`; total `o(r^2)`. -/
noncomputable def SmallBudget.sqrtLog (L C : ℕ) : SmallBudget :=
  SmallBudget.ofCutoff (fun r => L * r) (fun r => Nat.sqrt (L * r))
    (fun r => (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1))
    (fun r => by positivity)
    (fun r => Nat.sqrt_le_self _)
    (fun ε hε => sqrtLog_small L C ε hε)

/-- The explicit value of the `sqrtLog` price on small primes. -/
theorem SmallBudget.sqrtLog_X_of (L C r p : ℕ) (hp : p * p <= L * r) :
    (SmallBudget.sqrtLog L C).X r p = (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
  have : p <= Nat.sqrt (L * r) := Nat.le_sqrt.mpr hp
  simp [SmallBudget.sqrtLog, SmallBudget.ofCutoff, this]

/-- The `sqrtLog` price vanishes beyond `sqrt (L r)` (no higher levels there). -/
theorem SmallBudget.sqrtLog_X_zero (L C r p : ℕ) (hp : L * r < p * p) :
    (SmallBudget.sqrtLog L C).X r p = 0 := by
  have : ¬ p <= Nat.sqrt (L * r) := fun h => by
    have := Nat.le_sqrt.mp h; omega
  simp [SmallBudget.sqrtLog, SmallBudget.ofCutoff, this]

end CatalanCore.Uniform.Content.SmallPrimes
