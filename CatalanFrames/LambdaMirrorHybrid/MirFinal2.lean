module

public import CatalanFrames.LambdaMirrorHybrid.MirFinal
public import CatalanFrames.HybCommon.Numer

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

/-- **Level-1 plus negligible terms (mirror)**: an instance of `log_Dhyb_le_gen`
(`M = 4`, classes `{1, 3}`, tails `5r` and `5r/3`). -/
theorem mir_log_Dhyb_le (r : ℕ) (hr : 4 ≤ r) :
    Real.log (Dhyb mirNInst r (r / 8)) ≤ 3 * extraBound r (r / 8) +
      clsSum 4 (1 : ZMod 4) (WG mirNInst r) 0 (5 * r) +
      clsSum 4 (3 : ZMod 4) (WG mirNInst r) 0 (5 * r / 3) := by
  have hR3 : 3 ≤ (if (3 : ZMod 4) = 1 then 5 * r else 5 * r / 3) := by
    rw [if_neg (by decide)]; omega
  have h := log_Dhyb_le_gen mirBad ({1, 3} : Finset (ZMod 4))
    (fun c => if c = 1 then 5 * r else 5 * r / 3) r (r / 8) (by omega) (WG mirNInst r)
    (mirW_nonneg r) (fun p _ => le_rfl)
    (fun p hp hpb => by
      have h2 : p ≠ 2 := fun h => hpb (by simp [h, mirNInst, mirInst, HybInst.neg, HybInst.ofSing,
        ContentData.neg, mirCD])
      rcases prime_class4 hp h2 with ⟨h3', _⟩ | ⟨h1', _⟩
      · simp [h3']
      · simp [h1'])
    (fun c hc b hb hbc => by
      have hb' : b = 2 ∨ b = 3 := by
        simpa [mirNInst, mirInst, HybInst.neg, HybInst.ofSing, ContentData.neg, mirCD] using hb
      have hcc : c = 1 ∨ c = 3 := by simpa using hc
      rcases hb' with rfl | rfl <;> rcases hcc with rfl | rfl <;>
        first | (exfalso; revert hbc; decide) | exact hR3)
    (fun c hc p hp hpb hpc hlt => by
      have hcc : c = 1 ∨ c = 3 := by simpa using hc
      have h5 : 5 ≤ p := by
        have h2 : p ≠ 2 := fun h => hpb (by simp [h, mirNInst, mirInst, HybInst.neg,
          HybInst.ofSing, ContentData.neg, mirCD])
        have h3 : p ≠ 3 := fun h => hpb (by simp [h, mirNInst, mirInst, HybInst.neg,
          HybInst.ofSing, ContentData.neg, mirCD])
        have := hp.two_le
        have h4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
        omega
      rcases hcc with rfl | rfl
      · rw [if_pos rfl] at hlt
        rw [WG, mir_tail1 r p hp h5 (cls4_mod1 hpc) hlt]; simp
      · rw [if_neg (by decide)] at hlt
        rw [WG, mir_tail3 r p hp h5 (cls4_mod3 hpc) hlt]; simp)
  rw [Finset.sum_pair (by decide)] at h
  simp only [if_true, show ¬ ((3 : ZMod 4) = 1) by decide, if_false] at h
  have := mirBad.extraG_le r (r / 8)
  linarith

end CatalanFrames.LambdaMirrorHybrid
