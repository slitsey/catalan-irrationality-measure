module
public import CatalanMeasure.PinMajorant
@[expose] public section

open Set Real
namespace OAI.InternalCatalan

noncomputable def fixedNodeCap (N : ℕ) : ℝ := Real.exp (-28 * Real.log 2 * N)

/-- A rational inequality for the complete fixed-node weight, before taking powers. -/
theorem fixed_node_base {u : ℝ} (hu : 0 ≤ u) :
    u ^ 19 * (1 + u) ^ 4 / (1 + u ^ 2) ^ 40 ≤ 1 / (2 : ℝ) ^ 28 := by
  let q : ℝ := 1 + u ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hpoly : 27 * q ^ 4 - 256 * u ^ 2 =
      (3 * u ^ 2 - 1) ^ 2 * (3 * u ^ 4 + 14 * u ^ 2 + 27) := by dsimp [q]; ring
  have hsharp : u ^ 2 ≤ (27 / 256 : ℝ) * q ^ 4 := by
    have hp : 0 ≤ (3 * u ^ 2 - 1) ^ 2 * (3 * u ^ 4 + 14 * u ^ 2 + 27) := by positivity
    nlinarith only [hpoly, hp]
  have hlin : 2 * u ≤ q := by dsimp [q]; nlinarith [sq_nonneg (u - 1)]
  have hone : 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg u]
  have hrest : u * (1 + u) ^ 4 ≤ 2 * q ^ 4 := by
    have hsum : (1 + u) ^ 2 ≤ 2 * q := by dsimp [q]; nlinarith [sq_nonneg (u - 1)]
    have h4 := pow_le_pow_left₀ (sq_nonneg (1 + u)) hsum 2
    have h2 : 2 * u ≤ q ^ 2 := le_trans hlin (by nlinarith [hq])
    nlinarith only [h4, h2, mul_nonneg hu (sq_nonneg q)]
  have h18 := pow_le_pow_left₀ (sq_nonneg u) hsharp 9
  have hmul := mul_le_mul h18 hrest (by positivity : 0 ≤ u * (1 + u) ^ 4) (by positivity)
  have hmain : u ^ 19 * (1 + u) ^ 4 ≤ 2 * (27 / 256 : ℝ) ^ 9 * q ^ 40 := by
    convert hmul using 1 <;> ring
  have hc : 2 * (27 / 256 : ℝ) ^ 9 ≤ 1 / (2 : ℝ) ^ 28 := by norm_num
  apply (div_le_iff₀ (pow_pos hq 40)).mpr
  exact hmain.trans (by gcongr)

theorem fixed_node_weight {N : ℕ} {y : ℝ} (hy : y < 0) :
    |y| ^ A N * (1 - y) ^ (2 * h N) / (1 + y ^ 2) ^ (40 * N) ≤ fixedNodeCap N := by
  have hb := fixed_node_base (u := |y|) (abs_nonneg y)
  have hn := pow_le_pow_left₀ (by positivity : 0 ≤ |y| ^ 19 * (1 + |y|) ^ 4 / (1 + |y| ^ 2) ^ 40) hb N
  have he : (1 / (2 : ℝ) ^ 28) ^ N = fixedNodeCap N := by
    unfold fixedNodeCap
    rw [div_pow, one_pow, ← pow_mul, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (28 * N)),
      Real.log_pow, one_div, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  rw [he] at hn
  convert hn using 1
  rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, abs_of_neg hy]
  simp only [A, h]
  congr 2 <;> ring

theorem rowNodeWeight_mul_sheetOneWeight_tight {N : ℕ} (hN : 0 < N) {y : ℝ}
    (hy : y ∈ Ioo (-1 : ℝ) 0) :
    rowNodeWeight N y * sheetOneWeight N y ≤ (2 : ℝ) ^ (Cdegree N - 1) * fixedNodeCap N := by
  have hy0 : y ≠ 0 := hy.2.ne
  have h1y : 0 ≤ 1 - y := by linarith [hy.2]
  have hd : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  have hdpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hC : 1 ≤ Cdegree N := Cdegree_pos hN
  have hQ : (1 + y ^ 2) ^ (((n N : ℝ) - 1) / 2) /
      (1 + y ^ 2) ^ (Cdegree N - 1 + h N) ≤ 1 / (1 + y ^ 2) ^ (40 * N) := by
    apply (div_le_div_iff₀ (pow_pos hdpos _) (pow_pos hdpos _)).mpr
    rw [one_mul, ← Real.rpow_natCast (1 + y ^ 2) (40 * N),
      ← Real.rpow_add hdpos, ← Real.rpow_natCast (1 + y ^ 2) (Cdegree N - 1 + h N)]
    apply Real.rpow_le_rpow_of_exponent_le hd
    rw [Nat.cast_add, Nat.cast_sub hC]
    simp only [n, Cdegree, h, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have heq : rowNodeWeight N y * sheetOneWeight N y = (2 : ℝ) ^ (Cdegree N - 1) *
      (|y| ^ A N * (1 - y) ^ (2 * h N) *
        ((1 + y ^ 2) ^ (((n N : ℝ) - 1) / 2) / (1 + y ^ 2) ^ (Cdegree N - 1 + h N))) := by
    rw [rowNodeWeight_coordinate]
    unfold sheetOneWeight
    rw [← energy_abs_node_weight_cancel hN hy0]
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ |y| ^ A N * (1 - y) ^ (2 * h N) * (1 / (1 + y ^ 2) ^ (40 * N)) := by
      exact mul_le_mul_of_nonneg_left hQ (by positivity)
    _ ≤ fixedNodeCap N := by
      simpa [div_eq_mul_inv] using (fixed_node_weight (N := N) hy.2)

theorem rowNodeWeight_two_tight {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (hm : 1 ≤ m) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 0) :
    rowNodeWeight N y * |y| ^ g N / (|y| ^ p * |y| ^ (m - 1)) ≤
      (2 : ℝ) ^ (Cdegree N - 1) * fixedNodeCap N := by
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
  have hden : (1 + y ^ 2) ^ (40 * N) ≤ (1 + y ^ 2) ^ (Cdegree N - 1 + h N) := by
    apply pow_le_pow_right₀ (by nlinarith [sq_nonneg y])
    simp only [Cdegree, h]
    omega
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (div_le_div_of_nonneg_left (by positivity) (pow_pos hdpos (40 * N)) hden).trans
    (fixed_node_weight (N := N) hy.2)

end OAI.InternalCatalan
