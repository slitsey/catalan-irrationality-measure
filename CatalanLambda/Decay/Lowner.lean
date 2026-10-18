import CatalanLambda.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Basic

/-!
# Löwner form of `λ I + M0`

`lowF z = ∑_{j≥0} [1/(z+j+3/4) - 1/(z+j+1)]`.  We prove that `lowF` is summable, that
`(lowF a - lowF b)/(a-b)/16 = M0n a b` for naturals `a ≠ b`, and `lowF' a / 16 = λ + M0n a a`.
-/

open Finset

namespace CatalanLambda.Decay

/-- The complex series `F(z) = ∑_j [1/(z+j+3/4) - 1/(z+j+1)]`. -/
noncomputable def lowFC (z : ℂ) : ℂ := ∑' j : ℕ, (1 / (z + j + 3 / 4) - 1 / (z + j + 1))

/-- The real series `F(x) = ∑_j [1/(x+j+3/4) - 1/(x+j+1)]`. -/
noncomputable def lowF (x : ℝ) : ℝ := ∑' j : ℕ, (1 / (x + j + 3 / 4) - 1 / (x + j + 1))

/-- `λ = ∑_{k≥1} [1/(16k²) - 1/(4k-1)²]`, indexed from `0`. -/
noncomputable def lamS : ℝ :=
  ∑' k : ℕ, (1 / (16 * ((k : ℝ) + 1) ^ 2) - 1 / (4 * ((k : ℝ) + 1) - 1) ^ 2)

/-- Summability of the series defining `F`, for every complex `z`. -/
theorem summable_lowTermC (z : ℂ) :
    Summable fun j : ℕ => (1 / (z + j + 3 / 4) - 1 / (z + j + 1) : ℂ) := by
  have hs : Summable fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  filter_upwards [Filter.eventually_ge_atTop (⌈2 * ‖z‖⌉₊ + 1)] with j hj
  have hj' : 2 * ‖z‖ + 1 ≤ (j : ℝ) := by
    have h1 := Nat.le_ceil (2 * ‖z‖)
    have h2 : ((⌈2 * ‖z‖⌉₊ + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
    push_cast at h2; linarith
  have key : ∀ c : ℝ, 3 / 4 ≤ c → (j : ℝ) / 2 ≤ ‖z + (j : ℂ) + (c : ℂ)‖ := by
    intro c hc
    have h3 := norm_sub_norm_le ((((j : ℝ) + c : ℝ)) : ℂ) (-z)
    have h4 : ‖((((j : ℝ) + c : ℝ)) : ℂ)‖ = (j : ℝ) + c := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h4, norm_neg] at h3
    have h5 : ((((j : ℝ) + c : ℝ)) : ℂ) - -z = z + (j : ℂ) + (c : ℂ) := by push_cast; ring
    rw [h5] at h3
    linarith
  have h1 : (j : ℝ) / 2 ≤ ‖z + (j : ℂ) + 3 / 4‖ := by simpa using key (3 / 4) (by norm_num)
  have h2 : (j : ℝ) / 2 ≤ ‖z + (j : ℂ) + 1‖ := by simpa using key 1 (by norm_num)
  have hjpos : (0 : ℝ) < j := by linarith [norm_nonneg z]
  have ha0 : z + (j : ℂ) + 3 / 4 ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) h1)
  have hb0 : z + (j : ℂ) + 1 ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) h2)
  have e : (1 / (z + j + 3 / 4) - 1 / (z + j + 1) : ℂ)
      = (1 / 4) / ((z + j + 3 / 4) * (z + j + 1)) := by
    rw [div_sub_div _ _ ha0 hb0]; congr 1; ring
  rw [e, norm_div, norm_mul]
  have hn : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
  rw [hn, div_le_div_iff₀ (by positivity) (by positivity)]
  have hA := h1
  have hB := h2
  nlinarith [mul_le_mul hA hB (by positivity) (norm_nonneg _)]

theorem summable_lowTerm (x : ℝ) :
    Summable fun j : ℕ => (1 / (x + j + 3 / 4) - 1 / (x + j + 1) : ℝ) := by
  have := summable_lowTermC (x : ℂ)
  rw [← Complex.summable_ofReal]
  convert this using 2 with j
  push_cast; ring

theorem lowFC_ofReal (x : ℝ) : lowFC (x : ℂ) = (lowF x : ℂ) := by
  unfold lowFC lowF
  rw [Complex.ofReal_tsum]
  congr 1; ext j; push_cast; ring

/-- term function on naturals -/
noncomputable def lowGn (m : ℕ) : ℝ := 1 / ((m : ℝ) + 3 / 4) - 1 / ((m : ℝ) + 1)

theorem summable_lowGn : Summable lowGn := by
  have := summable_lowTerm 0
  convert this using 2 with j
  simp [lowGn]

theorem lowF_nat (n : ℕ) : lowF n = ∑' j : ℕ, lowGn (j + n) := by
  unfold lowF
  congr 1; ext j
  simp only [lowGn]; push_cast; ring_nf

theorem lowF_nat_add (n : ℕ) : (∑ i ∈ range n, lowGn i) + lowF n = lowF 0 := by
  have h := summable_lowGn.sum_add_tsum_nat_add n
  have h0 := lowF_nat 0
  simp only [Nat.cast_zero, add_zero] at h0
  rw [lowF_nat, h0]
  exact h

theorem lowF_sub (a b : ℕ) (hab : a ≤ b) :
    lowF a - lowF b = ∑ m ∈ Ico a b, lowGn m := by
  have h1 := lowF_nat_add a
  have h2 := lowF_nat_add b
  rw [← Finset.sum_range_add_sum_Ico _ hab] at h2
  linarith

theorem sum_Ioc_eq_sum_Ico {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b : ℕ) (hab : a ≤ b) :
    ∑ k ∈ Ioc a b, f k = ∑ m ∈ Ico a b, f (m + 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn, Finset.sum_Ico_succ_top hn, ih]

theorem sum_Icc_one_eq {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a : ℕ) :
    ∑ k ∈ Icc 1 a, f k = ∑ i ∈ range a, f (i + 1) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem M0n_symm (a b : ℕ) : M0n a b = M0n b a := by
  unfold M0n
  by_cases h : a = b
  · subst h; rfl
  · have h' : b ≠ a := Ne.symm h
    rw [if_neg h, if_neg h', max_comm, min_comm]

theorem lowner_lt (a b : ℕ) (hab : a < b) :
    (lowF a - lowF b) / ((a : ℝ) - b) / 16 = (M0n a b : ℝ) := by
  rw [lowF_sub a b hab.le]
  have hne : a ≠ b := hab.ne
  have hmax : max a b = b := max_eq_right hab.le
  have hmin : min a b = a := min_eq_left hab.le
  unfold M0n
  rw [if_neg hne, hmax, hmin, sum_Ioc_eq_sum_Ico _ a b hab.le]
  push_cast
  have hba : (a : ℝ) < b := by exact_mod_cast hab
  have hsum : ∑ m ∈ Ico a b, lowGn m
      = 4 * ∑ m ∈ Ico a b, (1 / (4 * ((m : ℝ) + 1) * (4 * ((m : ℝ) + 1) - 1))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold lowGn
    have : (m : ℝ) + 3 / 4 ≠ 0 := by positivity
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    have : 4 * ((m : ℝ) + 1) - 1 ≠ 0 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      intro h; linarith
    field_simp
    ring
  rw [hsum]
  have : (a : ℝ) - b ≠ 0 := by linarith
  have : (b : ℝ) - a ≠ 0 := by linarith
  field_simp
  ring

/-- **(3a-i)** Löwner form, off-diagonal. -/
theorem lowner_offdiag (a b : ℕ) (hab : a ≠ b) :
    (lowF a - lowF b) / ((a : ℝ) - b) / 16 = (M0n a b : ℝ) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact lowner_lt a b h
  · rw [M0n_symm, ← lowner_lt b a h]
    have : (a : ℝ) - b ≠ 0 := by
      have : (b : ℝ) < a := by exact_mod_cast h
      linarith
    have : (b : ℝ) - a ≠ 0 := by
      have : (b : ℝ) < a := by exact_mod_cast h
      linarith
    field_simp
    ring

theorem summable_inv_sq_add (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + c) ^ 2 := by
  have hs : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have hs1 : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 hs
    simpa using this
  set m : ℝ := min 1 c with hm
  have hm0 : 0 < m := lt_min one_pos hc
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) (hs1.mul_left (1 / m ^ 2))
  have h1 : m * ((n : ℝ) + 1) ≤ (n : ℝ) + c := by
    have a1 : m ≤ 1 := min_le_left _ _
    have a2 : m ≤ c := min_le_right _ _
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h2 : 0 < m * ((n : ℝ) + 1) := by positivity
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have := pow_le_pow_left₀ h2.le h1 2
  nlinarith [this, mul_pow m ((n : ℝ) + 1) 2]

/-- `k`-th term of `λ`, rewritten. -/
theorem lamTerm_eq (k : ℝ) (hk : 0 ≤ k) :
    1 / (16 * (k + 1) ^ 2) - 1 / (4 * (k + 1) - 1) ^ 2
      = (1 / 16) * (1 / (k + 1) ^ 2 - 1 / (k + 3 / 4) ^ 2) := by
  have : k + 3 / 4 ≠ 0 := by positivity
  have : k + 1 ≠ 0 := by positivity
  have h : 4 * (k + 1) - 1 = 4 * (k + 3 / 4) := by ring
  rw [h]
  field_simp
  ring

theorem summable_lamTerm : Summable fun k : ℕ =>
    (1 / (16 * ((k : ℝ) + 1) ^ 2) - 1 / (4 * ((k : ℝ) + 1) - 1) ^ 2) := by
  have h1 := summable_inv_sq_add 1 one_pos
  have h2 := summable_inv_sq_add (3 / 4) (by norm_num)
  have := (h1.sub h2).mul_left (1 / 16)
  convert this using 2 with k
  exact lamTerm_eq k (Nat.cast_nonneg k)

theorem lamS_split (a : ℕ) :
    lamS + (M0n a a : ℝ) = ∑' j : ℕ, (1 / 16) * (1 / ((a : ℝ) + j + 1) ^ 2 - 1 / ((a : ℝ) + j + 3 / 4) ^ 2) := by
  have h := summable_lamTerm.sum_add_tsum_nat_add a
  have hM : (M0n a a : ℝ) = -∑ i ∈ range a,
      (1 / (16 * ((i : ℝ) + 1) ^ 2) - 1 / (4 * ((i : ℝ) + 1) - 1) ^ 2) := by
    unfold M0n
    rw [if_pos rfl, sum_Icc_one_eq]
    push_cast
    rfl
  rw [hM]
  unfold lamS
  rw [← h]
  have : ∀ j : ℕ, (1 / (16 * (((j + a : ℕ) : ℝ) + 1) ^ 2) - 1 / (4 * (((j + a : ℕ) : ℝ) + 1) - 1) ^ 2)
      = (1 / 16) * (1 / ((a : ℝ) + j + 1) ^ 2 - 1 / ((a : ℝ) + j + 3 / 4) ^ 2) := by
    intro j
    rw [lamTerm_eq _ (Nat.cast_nonneg _)]
    push_cast
    ring_nf
  simp only [this]
  ring

theorem hasDerivAt_inv_add (c y : ℝ) (h : y + c ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / (y + c)) (-1 / (y + c) ^ 2) y := by
  have := (hasDerivAt_inv h).comp y ((hasDerivAt_id y).add_const c)
  convert this using 1
  · ext z; simp [one_div]
  · ring

/-- `F' (a) = ∑ [1/(a+j+1)² - 1/(a+j+3/4)²]`. -/
theorem hasDerivAt_lowF (a : ℕ) :
    HasDerivAt lowF (∑' j : ℕ, (-1 / ((a : ℝ) + j + 3 / 4) ^ 2 - -1 / ((a : ℝ) + j + 1) ^ 2)) a := by
  have hu : Summable fun j : ℕ => 2 * (1 / ((j : ℝ) + 1 / 4) ^ 2) :=
    (summable_inv_sq_add (1 / 4) (by norm_num)).mul_left 2
  have := hasDerivAt_tsum_of_isPreconnected (g := fun (j : ℕ) (y : ℝ) =>
      1 / (y + j + 3 / 4) - 1 / (y + j + 1))
    (g' := fun (j : ℕ) (y : ℝ) => -1 / (y + j + 3 / 4) ^ 2 - -1 / (y + j + 1) ^ 2)
    (u := fun j : ℕ => 2 * (1 / ((j : ℝ) + 1 / 4) ^ 2))
    (t := Set.Ioi (-1 / 2 : ℝ)) (y₀ := 0) (y := (a : ℝ)) hu isOpen_Ioi
    (isPreconnected_Ioi) ?_ ?_ (by simp [Set.mem_Ioi]; norm_num)
    (summable_lowTerm 0 |> fun h => by simpa using h) (by rw [Set.mem_Ioi]; have : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith)
  · exact this
  · intro j y hy
    rw [Set.mem_Ioi] at hy
    have h1 : y + j + 3 / 4 ≠ 0 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      intro h; linarith
    have h2 : y + j + 1 ≠ 0 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      intro h; linarith
    have e1 := hasDerivAt_inv_add ((j : ℝ) + 3 / 4) y (by rw [← add_assoc]; exact h1)
    have e2 := hasDerivAt_inv_add ((j : ℝ) + 1) y (by rw [← add_assoc]; exact h2)
    convert e1.sub e2 using 1
    · ext z; simp [add_assoc]
    · simp [add_assoc]
  · intro j y hy
    rw [Set.mem_Ioi] at hy
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have p1 : (j : ℝ) + 1 / 4 ≤ y + j + 3 / 4 := by linarith
    have p2 : (j : ℝ) + 1 / 4 ≤ y + j + 1 := by linarith
    have q : (0 : ℝ) < (j : ℝ) + 1 / 4 := by positivity
    have b1 : 1 / (y + j + 3 / 4) ^ 2 ≤ 1 / ((j : ℝ) + 1 / 4) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ q.le p1 2)
    have b2 : 1 / (y + j + 1) ^ 2 ≤ 1 / ((j : ℝ) + 1 / 4) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ q.le p2 2)
    have c1 : 0 ≤ 1 / (y + j + 3 / 4) ^ 2 := by positivity
    have c2 : 0 ≤ 1 / (y + j + 1) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_le]
    have e : -1 / (y + j + 3 / 4) ^ 2 - -1 / (y + j + 1) ^ 2
        = -(1 / (y + j + 3 / 4) ^ 2) + 1 / (y + j + 1) ^ 2 := by ring
    rw [e]
    constructor <;> linarith

/-- **(3a-i)** diagonal: `F'(a)/16 = λ + M0n a a`. -/
theorem lowner_diag (a : ℕ) :
    deriv lowF a / 16 = lamS + (M0n a a : ℝ) := by
  rw [(hasDerivAt_lowF a).deriv, lamS_split, ← tsum_div_const]
  congr 1; ext j
  ring

end CatalanLambda.Decay
