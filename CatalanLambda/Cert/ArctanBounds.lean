import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import CatalanLambda.Cert.Tables

/-!
# Verified lower bound for `Real.arctan` on `[0, ∞)`

`thetaQ v` is a rational lower bound of `arctan v` (for rational `v ≥ 0`): table `ALO` of
`arctan (j/256)` lower bounds (even-length alternating series, checked by `decide +kernel`),
plus the tangent step `arctan v ≥ arctan a + (v - a)/(1 + b²)` for `a ≤ v ≤ b`.
-/

open Real

namespace CatalanLambda.Cert

def tabA (j : ℕ) : ℕ := (ALO >>> (64 * j)) % 2 ^ 64

def JM : ℕ := 208

def atnS {α : Type _} [Field α] (x : α) : ℕ → α
  | 0 => 0
  | n + 1 => atnS x n + (-1) ^ n * x ^ (2 * n + 1) / (2 * (n : α) + 1)

lemma atnS_cast (q : ℚ) (n : ℕ) : ((atnS q n : ℚ) : ℝ) = atnS (q : ℝ) n := by
  induction n with
  | zero => simp [atnS]
  | succ n ih => simp [atnS, ih]

lemma atnS_le_arctan {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (m : ℕ) : atnS x (2 * m) ≤ arctan x := by
  have hs := Real.hasSum_arctan (x := x) (by rwa [Real.norm_eq_abs, abs_of_nonneg h0])
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ,
      a = fun n => (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← ha] at hs
  have hsum : ∀ n, atnS x n = ∑ i ∈ Finset.range n, a i := by
    intro n
    induction n with
    | zero => simp [atnS]
    | succ n ih => rw [Finset.sum_range_succ, ← ih]; simp [atnS, ha]
  have hmono : Monotone (fun m : ℕ => ∑ i ∈ Finset.range (2 * m), a i) := by
    apply monotone_nat_of_le_succ
    intro m
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
    have e1 : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; simp
    have e2 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, e1]; ring
    have hp : x ^ (2 * (2 * m + 1) + 1) ≤ x ^ (2 * (2 * m) + 1) :=
      pow_le_pow_of_le_one h0 h1.le (by omega)
    have hd : x ^ (2 * (2 * m + 1) + 1) / ((2 * (2 * m + 1) + 1 : ℕ) : ℝ) ≤
        x ^ (2 * (2 * m) + 1) / ((2 * (2 * m) + 1 : ℕ) : ℝ) := by
      apply div_le_div₀ (by positivity) hp (by positivity)
      exact_mod_cast (by omega : 2 * (2 * m) + 1 ≤ 2 * (2 * m + 1) + 1)
    have a2m : a (2 * m) = x ^ (2 * (2 * m) + 1) / ((2 * (2 * m) + 1 : ℕ) : ℝ) := by
      rw [ha]; simp only; rw [e1]; ring
    have a2m1 : a (2 * m + 1) =
        -(x ^ (2 * (2 * m + 1) + 1) / ((2 * (2 * m + 1) + 1 : ℕ) : ℝ)) := by
      rw [ha]; simp only; rw [e2]; ring
    rw [a2m, a2m1]
    linarith
  have ht : Filter.Tendsto (fun m : ℕ => ∑ i ∈ Finset.range (2 * m), a i) Filter.atTop
      (nhds (arctan x)) :=
    hs.tendsto_sum_nat.comp
      (Filter.tendsto_atTop_mono (fun m => (by omega : m ≤ 2 * m)) Filter.tendsto_id)
  rw [hsum]
  exact hmono.ge_of_tendsto ht m

def atabCheck (j : ℕ) : Bool :=
  decide ((tabA j : ℚ) / 2 ^ 64 ≤ atnS ((j : ℚ) / 256) 100)

theorem atab_ok : ∀ j < JM + 1, atabCheck j = true := by decide +kernel

lemma tabA_le_arctan {j : ℕ} (hj : j ≤ JM) : (tabA j : ℝ) / 2 ^ 64 ≤ arctan ((j : ℝ) / 256) := by
  have h := atab_ok j (by omega)
  simp only [atabCheck, decide_eq_true_eq] at h
  have h2 := (Rat.cast_le (K := ℝ)).mpr h
  rw [atnS_cast] at h2
  push_cast at h2
  have hj' : (j : ℝ) ≤ 208 := by exact_mod_cast hj
  have := atnS_le_arctan (x := (j : ℝ) / 256) (by positivity)
    (by rw [div_lt_one (by norm_num)]; linarith) 50
  exact h2.trans this

lemma arctan_tangent {a v b : ℝ} (ha : 0 ≤ a) (hav : a ≤ v) (hvb : v ≤ b) :
    arctan a + (v - a) / (1 + b ^ 2) ≤ arctan v := by
  have key := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc a v)
    (f := arctan) (C := 1 / (1 + b ^ 2)) (Real.differentiable_arctan.continuous.continuousOn)
    (Real.differentiable_arctan.differentiableOn) (by
      intro x hx
      rw [interior_Icc] at hx
      rw [Real.deriv_arctan]
      have hx0 : 0 ≤ x := ha.trans hx.1.le
      have : x ^ 2 ≤ b ^ 2 := by nlinarith [hx.2]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)) a
    (Set.left_mem_Icc.mpr hav) v (Set.right_mem_Icc.mpr hav) hav
  have : (v - a) / (1 + b ^ 2) = 1 / (1 + b ^ 2) * (v - a) := by ring
  linarith

/-- rational lower bound for `arctan` at a point `≥ vlo`. -/
def thetaQ (vlo : ℚ) : ℚ :=
  let j := min (⌊vlo * 256⌋₊) JM
  (tabA j : ℚ) / 2 ^ 64 +
    (if j = JM then 0 else (vlo - (j : ℚ) / 256) / (1 + (((j : ℚ) + 1) / 256) ^ 2))

theorem thetaQ_le_arctan {vlo : ℚ} {v : ℝ} (h0 : 0 ≤ vlo) (hv : (vlo : ℝ) ≤ v) :
    ((thetaQ vlo : ℚ) : ℝ) ≤ arctan v := by
  unfold thetaQ
  simp only
  set j := min (⌊vlo * 256⌋₊) JM with hj
  have hv0 : (0 : ℝ) ≤ vlo := by exact_mod_cast h0
  have hfl : (⌊vlo * 256⌋₊ : ℚ) ≤ vlo * 256 := by
    have : (0 : ℚ) ≤ vlo * 256 := by positivity
    exact Nat.floor_le this
  by_cases hjm : j = JM
  · rw [if_pos hjm]
    have hle : (JM : ℚ) ≤ vlo * 256 := by
      have : JM ≤ ⌊vlo * 256⌋₊ := by omega
      exact le_trans (by exact_mod_cast this) hfl
    have hle' : ((JM : ℝ) / 256) ≤ v := by
      have : ((JM : ℚ) / 256) ≤ vlo := by linarith
      have h2 : (((JM : ℚ) / 256 : ℚ) : ℝ) ≤ (vlo : ℝ) := by exact_mod_cast this
      push_cast at h2
      linarith
    have := tabA_le_arctan (j := JM) le_rfl
    have h3 : arctan ((JM : ℝ) / 256) ≤ arctan v := Real.arctan_strictMono.monotone hle'
    rw [hjm]
    push_cast
    simp only [add_zero]
    linarith
  · rw [if_neg hjm]
    have hjlt : j < JM := lt_of_le_of_ne (min_le_right _ _) hjm
    have hjf : j = ⌊vlo * 256⌋₊ := by
      rcases min_choice (⌊vlo * 256⌋₊) JM with h | h
      · rw [hj, h]
      · exfalso; apply hjm; rw [hj, h]
    have hjle : (j : ℚ) ≤ vlo * 256 := by rw [hjf]; exact hfl
    have hjgt : vlo * 256 < (j : ℚ) + 1 := by
      have h0' : (0 : ℚ) ≤ vlo * 256 := by positivity
      have := Nat.lt_floor_add_one (vlo * 256)
      rw [hjf]; exact this
    have hta := tabA_le_arctan (j := j) hjlt.le
    have ha : (0 : ℝ) ≤ (j : ℝ) / 256 := by positivity
    have hav : (j : ℝ) / 256 ≤ vlo := by
      have : (j : ℚ) / 256 ≤ vlo := by linarith
      have h2 : (((j : ℚ) / 256 : ℚ) : ℝ) ≤ (vlo : ℝ) := by exact_mod_cast this
      push_cast at h2; exact h2
    have hvb : (vlo : ℝ) ≤ ((j : ℝ) + 1) / 256 := by
      have : vlo ≤ ((j : ℚ) + 1) / 256 := by linarith
      have h2 : ((vlo : ℚ) : ℝ) ≤ ((((j : ℚ) + 1) / 256 : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at h2; exact h2
    have tan := arctan_tangent ha hav hvb
    have mono : arctan (vlo : ℝ) ≤ arctan v := Real.arctan_strictMono.monotone hv
    push_cast
    linarith

end CatalanLambda.Cert
