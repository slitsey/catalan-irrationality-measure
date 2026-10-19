module

public import CatalanCore.Basic.ZModGood
public import CatalanLambda.Assembly
public import CatalanFrames.Lambda.Frame

/-!
# Node-level `ℓ`-integrality of the scaled λ-Löwner entries (DO Lemma 1.1)

Bridges the legacy `CatalanLambda` entry lemmas (`entry_ll_*`, `entry_lh`, `entry_hh_*`, valid for
`ℓ + 1 = 4K`) to `CatalanCore.Good`.  With `Dq ℓ K p = 1` (low node `p < K`) or `ℓ` (high node),
the scaled entry `Dq p · Dq q · (e + M0n p q)` of the hybrid matrix is `ℓ`-integral with the
reductions listed below (`e` is `x` on a `C`-diagonal cell, else `0`).
-/

@[expose] public section

open Finset CatalanCore

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime]

/-- legacy `Good` is `CatalanCore.Good` (they unfold identically). -/
lemma toGood {x : ℚ} {y : ZMod ℓ} (h : CatalanLambda.Good ℓ x y) : Good ℓ x y := h

/-- low-low cell. -/
lemma node_ll (hlK : ℓ + 1 = 4 * K) {p q : ℕ} (hp : p < K) (hq : q < K) {e : ℚ} {eb : ZMod ℓ}
    (he : Good ℓ e eb) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K q * (e + CatalanLambda.M0n p q))
      (eb + ((if p = q then CatalanLambda.cc ℓ K else 0) + CatalanLambda.G ℓ K p q) / 16) := by
  simp only [CatalanLambda.Dq, if_pos hp, if_pos hq, one_mul]
  refine he.add ?_
  by_cases hpq : p = q
  · subst hpq; simpa using toGood (CatalanLambda.entry_ll_diag hlK hp)
  · rw [if_neg hpq, zero_add]
    rcases lt_or_gt_of_ne hpq with h | h
    · exact toGood (CatalanLambda.entry_ll_off hlK h hq)
    · rw [CatalanLambda.M0n_comm, CatalanLambda.G_comm]
      exact toGood (CatalanLambda.entry_ll_off hlK h hp)

/-- low-high cell (row low). -/
lemma node_lh (hlK : ℓ + 1 = 4 * K) {p q : ℕ} (hp : p < K) (hKq : K ≤ q) (hq : q < ℓ) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K q * (0 + CatalanLambda.M0n p q))
      (-(1 / (4 * ((q : ZMod ℓ) - p)))) := by
  simp only [CatalanLambda.Dq, if_pos hp, if_neg (show ¬ q < K by omega), one_mul, zero_add]
  exact toGood (CatalanLambda.entry_lh hlK hp hKq hq)

/-- high-low cell (row high). -/
lemma node_hl (hlK : ℓ + 1 = 4 * K) {p q : ℕ} (hKp : K ≤ p) (hp : p < ℓ) (hq : q < K) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K q * (0 + CatalanLambda.M0n p q))
      (-(1 / (4 * ((p : ZMod ℓ) - q)))) := by
  simp only [CatalanLambda.Dq, if_pos hq, if_neg (show ¬ p < K by omega), mul_one, zero_add]
  rw [CatalanLambda.M0n_comm]
  exact toGood (CatalanLambda.entry_lh hlK hq hKp hp)

/-- high-high off-diagonal cell. -/
lemma node_hh_off (hlK : ℓ + 1 = 4 * K) {p q : ℕ} (hKp : K ≤ p) (hp : p < ℓ) (hKq : K ≤ q)
    (hq : q < ℓ) (hpq : p ≠ q) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K q * (0 + CatalanLambda.M0n p q)) 0 := by
  simp only [CatalanLambda.Dq, if_neg (show ¬ p < K by omega), if_neg (show ¬ q < K by omega),
    zero_add]
  rcases lt_or_gt_of_ne hpq with h | h
  · exact toGood (CatalanLambda.entry_hh_off hlK hKp h hq)
  · rw [CatalanLambda.M0n_comm]; exact toGood (CatalanLambda.entry_hh_off hlK hKq h hp)

/-- high diagonal cell with `e = x`. -/
lemma node_hh_diag (hlK : ℓ + 1 = 4 * K) {p : ℕ} (hKp : K ≤ p) (hp : p < ℓ) {e : ℚ}
    {eb : ZMod ℓ} (he : Good ℓ e eb) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K p * (e + CatalanLambda.M0n p p)) 1 := by
  simp only [CatalanLambda.Dq, if_neg (show ¬ p < K by omega)]
  exact toGood (CatalanLambda.entry_hh_diag hlK hKp hp he)

end CatalanFrames.LambdaHybrid.NV
