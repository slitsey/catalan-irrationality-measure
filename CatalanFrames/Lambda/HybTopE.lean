module

public import CatalanFrames.Lambda.HybDefE3
public import CatalanFrames.Lambda.HybLemmaE2
public import CatalanCore.Arith.Hybrid.BorderE

@[expose] public section

/-!
# λ: E (classes 1 and 3) as `DefHypTop` families (MEM2C)

Bordered twins of `defHypT_E1` and `defHypT_E3`, with identical hypotheses.
-/

open Finset CatalanCore CatalanCore.Basic CatalanCore.Rect CatalanCore.Arith
  CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanFrames.Lambda

/-- Lemma E for λ at a class-1 prime, bordered. -/
theorem gleAt_E_lam_top {p r m k : ℕ} [Fact p.Prime] (S : ESetup 1 p r m 3 k) :
    GLE p (2 * ((r - p) + (r - k)) + 4 * m - m + topC lamInst r m p)
      ((afterTop r m).fullPolyG lamFrame) := by
  have := (gleAt_E_lam_wit S).border lamInst
  rw [wE_sum_lam S] at this
  exact this

theorem gle_E1_top {r p : ℕ} (hc : cleanE1 r p) [Fact p.Prime] :
    GLE p (dualE1 r (r / 8) p - r / 8 + topC lamInst r (r / 8) p)
      ((afterTop r (r / 8)).fullPolyG lamFrame) := by
  obtain ⟨hp, h4, h7, hpr⟩ := hc
  have S := eSetup_of_clean hp h4 h7 hpr
  have := gleAt_E_lam_top S
  unfold dualE1
  convert this using 2

theorem defHypTop_E1 (r : ℕ) (T : ℕ → ℕ)
    (hT : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ T p)
    (hTd : ∀ p, cleanE1 r p → dualE1 r (r / 8) p ≤ T p) :
    DefHypTop lamInst r (r / 8) T (defE1 r) := by
  classical
  refine defHypTop_of_local T (defE1 r) hT (cleanE1 r) ?_ ?_
  · intro p hp; simp [defE1, hp]
  · intro p hp hb hc
    have : Fact p.Prime := ⟨hp⟩
    have hd := hTd p hc
    have h1 : r / 8 ≤ dualE1 r (r / 8) p := by unfold dualE1; omega
    have hg := gle_E1_top hc
    have e : defE1 r p = r / 8 := by simp [defE1, hc]
    rw [e]
    intro _
    refine hg.mono ?_
    omega

theorem gle_E3_top {r p : ℕ} (hr : 16 ≤ r) (hc : cleanE3 r p) [Fact p.Prime] :
    GLE p (2 * r + r / 8 - r / 8 + topC lamInst r (r / 8) p)
      ((afterTop r (r / 8)).fullPolyG lamFrame) := by
  obtain ⟨hp, h4, h8, h5, h139⟩ := hc
  have S := eSetup3_of_clean hp h4 h8 h5 hr
  have h7 : 7 ≤ p := by omega
  have := gleAt_E3_top lamInst S lamData (not_dvd_6255 hp h7 h139)
  rw [wrc_sum S] at this
  exact this

theorem defHypTop_E3 {r : ℕ} (hr : 16 ≤ r) (T : ℕ → ℕ)
    (hT : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ T p)
    (hTd : ∀ p, cleanE3 r p → 2 * r + r / 8 ≤ T p) :
    DefHypTop lamInst r (r / 8) T (defE3 r) := by
  classical
  refine defHypTop_of_local T (defE3 r) hT (cleanE3 r) ?_ ?_
  · intro p hp; simp [defE3, hp]
  · intro p hp hb hc
    have : Fact p.Prime := ⟨hp⟩
    have hd := hTd p hc
    have hg := gle_E3_top hr hc
    have e : defE3 r p = r / 8 := by simp [defE3, hc]
    rw [e]
    intro _
    refine hg.mono ?_
    omega

end CatalanFrames.Lambda
