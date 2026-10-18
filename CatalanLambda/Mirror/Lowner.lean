module

public import CatalanLambda.Mirror.NVEntries
public import CatalanLambda.Decay.Reflect
public import CatalanLambda.Decay.Lowner

@[expose] public section

/-!
# Mirror constant: Löwner form of `-(λ' I + N₀)`

`lowFB x = ∑_{j≥0} [1/(x+j+1/4) - 1/(x+j+1)] = ψ(x+1) - ψ(x+1/4)`.  We prove
`(lowFB a - lowFB b)/(a-b)/16 = -N0n a b` for naturals `a ≠ b`, and `lowFB' a / 16 = -(λ' + N0n a a)`,
where `λ' = ∑_{k≥0} [1/(4k+1)² - 1/(16(k+1)²)] = G/2 + 5π²/96`.
-/

open Finset

namespace CatalanLambda.Mirror

open CatalanLambda.Decay (summable_pairC summable_inv_sq_add sum_Ioc_eq_sum_Ico sum_Icc_one_eq
  hasDerivAt_inv_add)

/-- The real series `F̄(x) = ∑_j [1/(x+j+1/4) - 1/(x+j+1)]`. -/
noncomputable def lowFB (x : ℝ) : ℝ := ∑' j : ℕ, (1 / (x + j + 1 / 4) - 1 / (x + j + 1))

/-- `λ' = ∑_{k≥0} [1/(4k+1)² - 1/(16(k+1)²)]`. -/
noncomputable def lamB : ℝ :=
  ∑' k : ℕ, (1 / (4 * (k : ℝ) + 1) ^ 2 - 1 / (16 * ((k : ℝ) + 1) ^ 2))

theorem summable_lowTermB (x : ℝ) :
    Summable fun j : ℕ => (1 / (x + j + 1 / 4) - 1 / (x + j + 1) : ℝ) := by
  have := summable_pairC (x : ℂ) (1 / 4) 1
  rw [← Complex.summable_ofReal]
  convert this using 2 with j
  push_cast; ring

/-- term function on naturals -/
noncomputable def lowGnB (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1 / 4) - 1 / ((m : ℝ) + 1)

theorem summable_lowGnB : Summable lowGnB := by
  have := summable_lowTermB 0
  convert this using 2 with j
  simp [lowGnB]

theorem lowF_natB (n : ℕ) : lowFB n = ∑' j : ℕ, lowGnB (j + n) := by
  unfold lowFB
  congr 1; ext j
  simp only [lowGnB]; push_cast; ring_nf

theorem lowF_nat_addB (n : ℕ) : (∑ i ∈ range n, lowGnB i) + lowFB n = lowFB 0 := by
  have h := summable_lowGnB.sum_add_tsum_nat_add n
  have h0 := lowF_natB 0
  simp only [Nat.cast_zero, add_zero] at h0
  rw [lowF_natB, h0]
  exact h

theorem lowF_subB (a b : ℕ) (hab : a ≤ b) :
    lowFB a - lowFB b = ∑ m ∈ Ico a b, lowGnB m := by
  have h1 := lowF_nat_addB a
  have h2 := lowF_nat_addB b
  rw [← Finset.sum_range_add_sum_Ico _ hab] at h2
  linarith

theorem lowner_ltB (a b : ℕ) (hab : a < b) :
    (lowFB a - lowFB b) / ((a : ℝ) - b) / 16 = -(N0n a b : ℝ) := by
  rw [lowF_subB a b hab.le, N0n_lt hab, sum_Ioc_eq_sum_Ico _ a b hab.le]
  push_cast
  have hba : (a : ℝ) < b := by exact_mod_cast hab
  have hsum : ∑ m ∈ Ico a b, lowGnB m
      = ∑ m ∈ Ico a b, 3 / (((m : ℝ) + 1) * (4 * ((m : ℝ) + 1) - 3)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold lowGnB
    have : (m : ℝ) + 1 / 4 ≠ 0 := by positivity
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    have : 4 * ((m : ℝ) + 1) - 3 ≠ 0 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      intro h; linarith
    field_simp
    ring
  rw [hsum]
  have : (a : ℝ) - b ≠ 0 := by linarith
  have : (b : ℝ) - a ≠ 0 := by linarith
  generalize (∑ m ∈ Ico a b, 3 / (((m : ℝ) + 1) * (4 * ((m : ℝ) + 1) - 3))) = S
  field_simp
  ring

theorem lowner_offdiagB (a b : ℕ) (hab : a ≠ b) :
    (lowFB a - lowFB b) / ((a : ℝ) - b) / 16 = -(N0n a b : ℝ) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact lowner_ltB a b h
  · rw [N0n_comm, ← lowner_ltB b a h]
    have : (a : ℝ) - b ≠ 0 := by
      have : (b : ℝ) < a := by exact_mod_cast h
      linarith
    have : (b : ℝ) - a ≠ 0 := by
      have : (b : ℝ) < a := by exact_mod_cast h
      linarith
    field_simp
    ring

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

theorem lamB_split (a : ℕ) :
    lamB + (N0n a a : ℝ) = ∑' j : ℕ, (1 / 16) * (1 / ((a : ℝ) + j + 1 / 4) ^ 2 - 1 / ((a : ℝ) + j + 1) ^ 2) := by
  have h := summable_lamTermB.sum_add_tsum_nat_add a
  have hM : (N0n a a : ℝ) = -∑ i ∈ range a,
      (1 / (4 * (i : ℝ) + 1) ^ 2 - 1 / (16 * ((i : ℝ) + 1) ^ 2)) := by
    rw [N0n_diag, sum_Icc_one_eq]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : 4 * ((i : ℝ) + 1) - 3 = 4 * i + 1 := by ring
    rw [this]; ring
  rw [hM]
  unfold lamB
  rw [← h]
  have : ∀ j : ℕ, (1 / (4 * ((j + a : ℕ) : ℝ) + 1) ^ 2 - 1 / (16 * (((j + a : ℕ) : ℝ) + 1) ^ 2))
      = (1 / 16) * (1 / ((a : ℝ) + j + 1 / 4) ^ 2 - 1 / ((a : ℝ) + j + 1) ^ 2) := by
    intro j
    rw [lamTermB_eq _ (Nat.cast_nonneg _)]
    push_cast
    ring_nf
  simp only [this]
  ring

/-- `F̄' (a) = ∑ [1/(a+j+1)² - 1/(a+j+1/4)²]`. -/
theorem hasDerivAt_lowFB (a : ℕ) :
    HasDerivAt lowFB (∑' j : ℕ, (-1 / ((a : ℝ) + j + 1 / 4) ^ 2 - -1 / ((a : ℝ) + j + 1) ^ 2)) a := by
  have hu : Summable fun j : ℕ => 2 * (1 / ((j : ℝ) + 1 / 8) ^ 2) :=
    (summable_inv_sq_add (1 / 8) (by norm_num)).mul_left 2
  have := hasDerivAt_tsum_of_isPreconnected (g := fun (j : ℕ) (y : ℝ) =>
      1 / (y + j + 1 / 4) - 1 / (y + j + 1))
    (g' := fun (j : ℕ) (y : ℝ) => -1 / (y + j + 1 / 4) ^ 2 - -1 / (y + j + 1) ^ 2)
    (u := fun j : ℕ => 2 * (1 / ((j : ℝ) + 1 / 8) ^ 2))
    (t := Set.Ioi (-1 / 8 : ℝ)) (y₀ := 0) (y := (a : ℝ)) hu isOpen_Ioi
    (isPreconnected_Ioi) ?_ ?_ (by simp [Set.mem_Ioi]; norm_num)
    (summable_lowTermB 0 |> fun h => by simpa using h) (by rw [Set.mem_Ioi]; have : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith)
  · exact this
  · intro j y hy
    rw [Set.mem_Ioi] at hy
    have h1 : y + j + 1 / 4 ≠ 0 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      intro h; linarith
    have h2 : y + j + 1 ≠ 0 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      intro h; linarith
    have e1 := hasDerivAt_inv_add ((j : ℝ) + 1 / 4) y (by rw [← add_assoc]; exact h1)
    have e2 := hasDerivAt_inv_add ((j : ℝ) + 1) y (by rw [← add_assoc]; exact h2)
    convert e1.sub e2 using 1
    · ext z; simp [add_assoc]
    · simp [add_assoc]
  · intro j y hy
    rw [Set.mem_Ioi] at hy
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have p1 : (j : ℝ) + 1 / 8 ≤ y + j + 1 / 4 := by linarith
    have p2 : (j : ℝ) + 1 / 8 ≤ y + j + 1 := by linarith
    have q : (0 : ℝ) < (j : ℝ) + 1 / 8 := by positivity
    have b1 : 1 / (y + j + 1 / 4) ^ 2 ≤ 1 / ((j : ℝ) + 1 / 8) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ q.le p1 2)
    have b2 : 1 / (y + j + 1) ^ 2 ≤ 1 / ((j : ℝ) + 1 / 8) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ q.le p2 2)
    have c1 : 0 ≤ 1 / (y + j + 1 / 4) ^ 2 := by positivity
    have c2 : 0 ≤ 1 / (y + j + 1) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_le]
    have e : -1 / (y + j + 1 / 4) ^ 2 - -1 / (y + j + 1) ^ 2
        = -(1 / (y + j + 1 / 4) ^ 2) + 1 / (y + j + 1) ^ 2 := by ring
    rw [e]
    constructor <;> linarith

/-- diagonal: `F̄'(a)/16 = -(λ' + N0n a a)`. -/
theorem lowner_diagB (a : ℕ) :
    deriv lowFB a / 16 = -(lamB + (N0n a a : ℝ)) := by
  rw [(hasDerivAt_lowFB a).deriv, lamB_split, ← tsum_neg, ← tsum_div_const]
  congr 1; ext j
  ring

end CatalanLambda.Mirror
