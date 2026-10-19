module

public import CatalanFrames.LambdaMirrorHybrid.MirFinal
public import CatalanFrames.HybCommon.TropLog

@[expose] public section

/-!
# Mirror: the tropical content bound (class sums)

`mir_log_Dhyb_le`: `log Dhyb mirNInst r ⌊r/8⌋ ≤ 3 · extraBound + clsSum₁ + clsSum₃` (the bad prime `3`
costs at most twice the prime-`2` term).  The class `j = 1` is `p ≡ 1 (4)` (summed to `5r`), the class
`j = 3` is `p ≡ 3 (4)` (summed to `5r/3`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
  CatalanFrames.HybCommon CatalanFrames.Lambda

namespace CatalanFrames.LambdaMirrorHybrid

lemma mirW_nonneg (r p : ℕ) : 0 ≤ WG mirNInst r p := Nat.cast_nonneg _

lemma mir_tail1 (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : p % 4 = 1) (ht : 5 * r < p) :
    XG mirNInst r p = 0 := by
  have hk := mirN_tropFacts.kq1 p hp h5 (by omega)
  have := XG_D6 mirN_tropFacts r p hp h5 (by omega) (by omega)
  omega

lemma mir_tail3 (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : p % 4 = 3) (ht : 5 * r / 3 < p) :
    XG mirNInst r p = 0 := by
  have hk := mirN_tropFacts.kq3 p hp h5 (by omega)
  have := XG_D6 mirN_tropFacts r p hp h5 (by omega) (by omega)
  omega

/-- **Level-1 plus negligible terms (mirror)**: the generic `sum_le_G` with `X = (· = 3)`. -/
theorem mir_sum_le (r : ℕ) (hr : 4 ≤ r) (T : ℕ → ℕ) (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hT : ∀ p, p.Prime → (T p : ℝ) ≤ (if p = 2 then mirEx2 r else 0) +
      (if p = 3 then mirEx3 r else 0) + ((2 * (r + r / 8) * cntM r (r / 8) p : ℕ) : ℝ) +
      (if p = 2 ∨ p = 3 then 0 else w p))
    (ht1 : ∀ p, p.Prime → 5 ≤ p → p % 4 = 1 → 5 * r < p → w p = 0)
    (ht3 : ∀ p, p.Prime → 5 ≤ p → p % 4 = 3 → 5 * r / 3 < p → w p = 0) :
    ∑ p ∈ (Finset.range (4 * (r + 2 * (r / 8)) + 6)).filter Nat.Prime, (T p : ℝ) * Real.log p ≤
      3 * extraBound r (r / 8) + clsSum 4 (1 : ZMod 4) w 0 (5 * r) +
      clsSum 4 (3 : ZMod 4) w 0 (5 * r / 3) :=
  sum_le_G r hr T w hw0 (cntM r (r / 8)) (fun p hp => cntM_le r (r / 8) p hp) (fun p hp h => cntM_zero r (r / 8) p hp h)
    (· = 3) (fun _ h => h) (fun p hp => by have h := hT p hp; simp only [mirEx2, mirEx3, ex2G, ex3G] at h ⊢; convert h) (5 * r) (5 * r / 3) (by omega) ht1 ht3

/-- **Level-1 plus negligible terms (mirror).** -/
theorem mir_log_Dhyb_le (r : ℕ) (hr : 4 ≤ r) :
    Real.log (Dhyb mirNInst r (r / 8)) ≤ 3 * extraBound r (r / 8) +
      clsSum 4 (1 : ZMod 4) (WG mirNInst r) 0 (5 * r) +
      clsSum 4 (3 : ZMod 4) (WG mirNInst r) 0 (5 * r / 3) := by
  rw [log_Dhyb, mir_Bnd]
  exact mir_sum_le r hr (tropExp mirNInst r (r / 8)) (WG mirNInst r) (mirW_nonneg r)
    (fun p hp => tropExp_mir_le r p (by omega) hp)
    (fun p hp h5 hm ht => by rw [WG, mir_tail1 r p hp h5 hm ht]; simp)
    (fun p hp h5 hm ht => by rw [WG, mir_tail3 r p hp h5 hm ht]; simp)

end CatalanFrames.LambdaMirrorHybrid
