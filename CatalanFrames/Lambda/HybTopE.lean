module

public import CatalanFrames.Lambda.HybDefE3
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
theorem gleAt_E_lam_top {p r m k : ℕ} [Fact p.Prime] (S : ESetup p r m 3 k) :
    GLE p (2 * ((r - p) + (r - k)) + 4 * m - m + topC lamInst r m p)
      ((afterTop r m).fullPolyG lamFrame) := by
  have hp5 := S.p5
  have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have h3' : ((3 : ℕ) : ZMod p) * ((3 : ℕ) : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h3
  have he : -(4 * ((3 : ℕ) : ZMod p)⁻¹) + 1 ≠ 0 := by
    intro h
    have h4 : (-(4 * ((3 : ℕ) : ZMod p)⁻¹) + 1) * ((3 : ℕ) : ZMod p) = 0 := by rw [h]; ring
    have h5 : (-(4 * ((3 : ℕ) : ZMod p)⁻¹) + 1) * ((3 : ℕ) : ZMod p) = -1 := by
      linear_combination (-4) * h3'
    rw [h5] at h4
    exact one_ne_zero (neg_eq_zero.1 h4)
  have := gleAt_E_top lamInst lamData S (Gs p (fun x => (x⁻¹) ^ 2) (k - 1)) h3 he (lam_hUU S)
  rw [wE_sum S.hrk (by have := S.hkp; have := S.hpr; omega)] at this
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
