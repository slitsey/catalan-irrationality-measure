module

public import CatalanMeasure.GenD.P20.Params

@[expose] public section

/-!
# Odd-prime profile of P20 (instance file, numerals only)

`H = 27 N`, `L = 24 N`, `A = 8 N`.  Seven segments, hinge profile `f20 = twentyOddLoss`.
-/

namespace CatalanMeasure.GenD
namespace P20

open CatalanMeasure.Parametric OAI.InternalCatalan PL OddProfile

noncomputable section

/-- The segmentwise loss. -/
def lossNat (N p : ℕ) : ℕ :=
  if p ≤ 10 * N then 40 * N else
  if p ≤ 12 * N then 60 * N - 2 * p else
  if 2 * p ≤ 27 * N then 36 * N else
  if p ≤ 14 * N then 63 * N - 2 * p else
  if p ≤ 16 * N then 91 * N - 4 * p else
  if p ≤ 24 * N then 75 * N - 3 * p else 27 * N - p

theorem lower_eq {N p : ℕ} (h : 2 * p ≤ 27 * N) : lowerPrimeLoss design N p = lossNat N p := by
  rw [lowerPrimeLoss_eq]
  simp only [design_H, design_L, design_A]
  simp only [Parameters.n, Parameters.b, Parameters.q, design, twenty]
  unfold lossNat
  split_ifs <;> omega

theorem upper_eq {N p : ℕ} (h : 27 * N ≤ 2 * p) (hp : p ≤ 27 * N) :
    upperPrimeLoss design N p = lossNat N p := by
  rw [upperPrimeLoss_eq]
  simp only [upperR, upperPd, upperE, design_H, design_L, design_A]
  simp only [Parameters.n, Parameters.b, Parameters.q, design, twenty]
  unfold lossNat
  split_ifs <;> omega

/-- The hinge profile of the loss, in units of `N`. -/
def f20 : Prof :=
  ⟨40, 0, [(-2, 10), (2, 12), (-2, 27/2), (-2, 14), (1, 16), (2, 24), (1, 27)]⟩

macro "seg_ker20" : tactic =>
  `(tactic| (intro wt hwt
             simp only [f20, List.mem_cons, List.not_mem_nil, or_false] at hwt
             rcases hwt with h | h | h | h | h | h | h <;> (subst h; norm_num)))

macro "seg_facts20" : tactic =>
  `(tactic| norm_num [f20, PL.hingeSlope, PL.hingeIntercept])

theorem lossNat_cast {N p : ℕ} (hN : 0 < N) (hp : p ≤ 27 * N) :
    (lossNat N p : ℝ) = N * f20.eval ((p : ℝ) / N) := by
  unfold lossNat
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact loss_eq_segment f20 hN 40 0 (by omega) (u1 := 0) (w1 := 1) (u2 := 10) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg_ker20) (by seg_facts20) (by seg_facts20)
  · exact loss_eq_segment f20 hN 60 (-2) (by omega) (u1 := 10) (w1 := 1) (u2 := 12) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg_ker20) (by seg_facts20) (by seg_facts20)
  · exact loss_eq_segment f20 hN 36 0 (by omega) (u1 := 12) (w1 := 1) (u2 := 27) (w2 := 2)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg_ker20) (by seg_facts20) (by seg_facts20)
  · exact loss_eq_segment f20 hN 63 (-2) (by omega) (u1 := 27) (w1 := 2) (u2 := 14) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg_ker20) (by seg_facts20) (by seg_facts20)
  · exact loss_eq_segment f20 hN 91 (-4) (by omega) (u1 := 14) (w1 := 1) (u2 := 16) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg_ker20) (by seg_facts20) (by seg_facts20)
  · exact loss_eq_segment f20 hN 75 (-3) (by omega) (u1 := 16) (w1 := 1) (u2 := 24) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg_ker20) (by seg_facts20) (by seg_facts20)
  · exact loss_eq_segment f20 hN 27 (-1) (by omega) (u1 := 24) (w1 := 1) (u2 := 27) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg_ker20) (by seg_facts20) (by seg_facts20)

theorem side_of {N p : ℕ} (hN : 0 < N) (h : design.H N ≤ 2 * p) : UpperSide design N p := by
  rw [design_H] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [design_A]; omega
  · rw [design_H, design_L]; omega
  · simp only [Parameters.b, design, twenty]; omega
  · rw [design_H, design_L]; omega

end
end P20
end CatalanMeasure.GenD
