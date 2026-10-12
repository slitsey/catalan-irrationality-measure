module
public import CatalanMeasure.FixedNodes
@[expose] public section
open Set Finset Real Filter Polynomial Matrix MeasureTheory
open scoped BigOperators Nat
namespace OAI.InternalCatalan

/-- Stronger fixed-node base for the first-sheet denominator. -/
theorem case_two_fixed_node_base {u : ℝ} (hu : 0 ≤ u) :
    u ^ 19 * (1 + u) ^ 4 / (1 + u ^ 2) ^ 64 ≤ 1 / (2 : ℝ) ^ 36 := by
  let q : ℝ := 1 + u ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hpoly : 3125 * q ^ 6 - 46656 * u ^ 2 =
      (5 * u ^ 2 - 1) ^ 2 * (125 * u ^ 8 + 800 * u ^ 6 + 2190 * u ^ 4 + 3344 * u ^ 2 + 3125) := by
    dsimp [q]; ring
  have hsharp : u ^ 2 ≤ (3125 / 46656 : ℝ) * q ^ 6 := by
    have hp : 0 ≤ (5 * u ^ 2 - 1) ^ 2 *
        (125 * u ^ 8 + 800 * u ^ 6 + 2190 * u ^ 4 + 3344 * u ^ 2 + 3125) := by positivity
    nlinarith only [hpoly, hp]
  have hrestpoly : q ^ 10 - 2 * u * (1 + u) ^ 4 =
      (1 - u) ^ 2 + u ^ 2 * (1 - 6 * u) ^ 2 + u ^ 4 * (1 - u) ^ 2 +
      119 * u ^ 6 + 210 * u ^ 8 + 252 * u ^ 10 + 210 * u ^ 12 +
      120 * u ^ 14 + 45 * u ^ 16 + 10 * u ^ 18 + u ^ 20 := by dsimp [q]; ring
  have hrest : u * (1 + u) ^ 4 ≤ q ^ 10 / 2 := by
    have hp : 0 ≤ (1 - u) ^ 2 + u ^ 2 * (1 - 6 * u) ^ 2 + u ^ 4 * (1 - u) ^ 2 +
        119 * u ^ 6 + 210 * u ^ 8 + 252 * u ^ 10 + 210 * u ^ 12 +
        120 * u ^ 14 + 45 * u ^ 16 + 10 * u ^ 18 + u ^ 20 := by positivity
    nlinarith only [hrestpoly, hp]
  have h18 := pow_le_pow_left₀ (sq_nonneg u) hsharp 9
  have hmul := mul_le_mul h18 hrest (by positivity : 0 ≤ u * (1 + u) ^ 4)
      (by positivity : 0 ≤ ((3125 / 46656 : ℝ) * q ^ 6) ^ 9)
  have hmul' : u ^ 19 * (1 + u) ^ 4 ≤ (3125 / 46656 : ℝ) ^ 9 / 2 * q ^ 64 := by
    convert hmul using 1 <;> ring
  have hnum : (3125 / 46656 : ℝ) ^ 9 / 2 ≤ 1 / (2 : ℝ) ^ 36 := by norm_num
  apply (div_le_iff₀ (pow_pos hq 64)).mpr
  change u ^ 19 * (1 + u) ^ 4 ≤ (1 / (2 : ℝ) ^ 36) * q ^ 64
  exact hmul'.trans (mul_le_mul_of_nonneg_right hnum (by positivity))


noncomputable def separateFixedCap (N : ℕ) : ℝ := Real.exp (-36 * Real.log 2 * N)
theorem separate_fixed_node_weight {N : ℕ} {y : ℝ} (hy : y < 0) :
    |y| ^ A N * (1 - y) ^ (2 * h N) / (1 + y ^ 2) ^ (64 * N) ≤ separateFixedCap N := by
  have hb := case_two_fixed_node_base (u := |y|) (abs_nonneg y)
  have hn := pow_le_pow_left₀ (by positivity : 0 ≤ |y| ^ 19 * (1 + |y|) ^ 4 / (1 + |y| ^ 2) ^ 64) hb N
  have he : (1 / (2 : ℝ) ^ 36) ^ N = separateFixedCap N := by
    unfold separateFixedCap
    rw [div_pow, one_pow, ← pow_mul, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (36 * N)),
      Real.log_pow, one_div, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  rw [he] at hn
  convert hn using 1
  rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, abs_of_neg hy]
  simp only [A, h]
  congr 2 <;> ring

theorem separate_rowNodeWeight_two_tight {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (hm : 1 ≤ m) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 0) :
    rowNodeWeight N y * |y| ^ g N / (|y| ^ p * |y| ^ (m - 1)) ≤
      (2 : ℝ) ^ (Cdegree N - 1) * separateFixedCap N := by
  have hy0 : y ≠ 0 := hy.2.ne
  have h1y : 0 ≤ 1 - y := by linarith [hy.2]
  have hdpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hexp : |y| ^ p * |y| ^ (m - 1) = |y| ^ (n N - 1) := by
    rw [← pow_add]; congr 1; omega
  have heq : rowNodeWeight N y * |y| ^ g N / (|y| ^ p * |y| ^ (m - 1)) =
      (2 : ℝ) ^ (Cdegree N - 1) *
        (|y| ^ A N * (1 - y) ^ (2 * h N) / (1 + y ^ 2) ^ (Cdegree N - 1 + h N)) := by
    rw [hexp, rowNodeWeight_coordinate]
    rw [← energy_abs_node_weight_two_cancel hN hy0]
    ring
  have hden : (1 + y ^ 2) ^ (64 * N) ≤ (1 + y ^ 2) ^ (Cdegree N - 1 + h N) := by
    apply pow_le_pow_right₀ (by nlinarith [sq_nonneg y])
    simp only [Cdegree, h]
    omega
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (div_le_div_of_nonneg_left (by positivity) (pow_pos hdpos (64 * N)) hden).trans
    (separate_fixed_node_weight (N := N) hy.2)


end OAI.InternalCatalan
