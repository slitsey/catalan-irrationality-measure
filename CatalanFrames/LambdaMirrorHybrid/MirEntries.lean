module

public import CatalanCore.Basic.ZModGood
public import CatalanLambda.Mirror.NVEntries
public import CatalanFrames.LambdaMirror.Frame

/-!
# Node-level `ℓ`-integrality of the scaled mirror-Löwner entries (`ℓ + 3 = 4K`)

Mirror analogue of `LambdaHybrid/NV/Entries.lean`: wraps the legacy `CatalanLambda.Mirror.entry_*`
lemmas with `Dq ℓ K p = 1` (low) or `ℓ` (high).
-/

@[expose] public section

open Finset CatalanCore

namespace CatalanFrames.LambdaMirrorHybrid

variable {ℓ K : ℕ} [Fact ℓ.Prime]

open CatalanLambda.Mirror in
/-- low-low cell -/
lemma mnode_ll (hlK : ℓ + 3 = 4 * K) {p q : ℕ} (hp : p < K) (hq : q < K) {e : ℚ} {eb : ZMod ℓ}
    (he : Good ℓ e eb) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K q * (e + N0n p q))
      (eb + (-((if p = q then CatalanLambda.cc ℓ K else 0) + CatalanLambda.G ℓ K p q)) / 16) := by
  simp only [CatalanLambda.Dq, if_pos hp, if_pos hq, one_mul]
  refine he.add ?_
  by_cases hpq : p = q
  · subst hpq
    refine (entry_ll_diag hlK hp).congr ?_
    simp; ring
  · rw [if_neg hpq]
    rcases lt_or_gt_of_ne hpq with h | h
    · exact (entry_ll_off hlK h hq).congr (by simp)
    · rw [N0n_comm, CatalanLambda.G_comm]
      exact (entry_ll_off hlK h hp).congr (by simp)

open CatalanLambda.Mirror in
/-- low-high cell -/
lemma mnode_lh (hlK : ℓ + 3 = 4 * K) {p q : ℕ} (hp : p < K) (hKq : K ≤ q) (hq : q < ℓ) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K q * (0 + N0n p q))
      (1 / (4 * ((q : ZMod ℓ) - p))) := by
  simp only [CatalanLambda.Dq, if_pos hp, if_neg (show ¬ q < K by omega), one_mul, zero_add]
  exact entry_lh hlK hp hKq hq

open CatalanLambda.Mirror in
/-- high-low cell -/
lemma mnode_hl (hlK : ℓ + 3 = 4 * K) {p q : ℕ} (hKp : K ≤ p) (hp : p < ℓ) (hq : q < K) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K q * (0 + N0n p q))
      (1 / (4 * ((p : ZMod ℓ) - q))) := by
  simp only [CatalanLambda.Dq, if_pos hq, if_neg (show ¬ p < K by omega), mul_one, zero_add]
  rw [N0n_comm]
  exact entry_lh hlK hq hKp hp

open CatalanLambda.Mirror in
/-- high-high off-diagonal -/
lemma mnode_hh_off (hlK : ℓ + 3 = 4 * K) {p q : ℕ} (hKp : K ≤ p) (hp : p < ℓ) (hKq : K ≤ q)
    (hq : q < ℓ) (hpq : p ≠ q) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K q * (0 + N0n p q)) 0 := by
  simp only [CatalanLambda.Dq, if_neg (show ¬ p < K by omega), if_neg (show ¬ q < K by omega),
    zero_add]
  rcases lt_or_gt_of_ne hpq with h | h
  · exact entry_hh_off hlK hKp h hq
  · rw [N0n_comm]; exact entry_hh_off hlK hKq h hp

open CatalanLambda.Mirror in
/-- high diagonal -/
lemma mnode_hh_diag (hlK : ℓ + 3 = 4 * K) {p : ℕ} (hKp : K ≤ p) (hp : p < ℓ) {e : ℚ}
    {eb : ZMod ℓ} (he : Good ℓ e eb) :
    Good ℓ (CatalanLambda.Dq ℓ K p * CatalanLambda.Dq ℓ K p * (e + N0n p p)) (-1) := by
  simp only [CatalanLambda.Dq, if_neg (show ¬ p < K by omega)]
  exact entry_hh_diag hlK hKp hp he

end CatalanFrames.LambdaMirrorHybrid
