module

public import CatalanCore.Arith.Hybrid.DefC7Fam
public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# Theorem C7 for the bordered member `afterTop r m` (MEM2C)

No new rank computation: `defHypTop_of_wit` applied to `gleAt_C7_lam_wit`.
-/

open Finset Polynomial CatalanCore CatalanCore.Rect CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

open Classical in
/-- **Theorem C7 for the bordered member**: twin of `defHypT_C7` (same hypotheses). -/
theorem defHypTop_C7 {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr) (r m : ℕ) (T : ℕ → ℕ)
    (W : ℕ → Prop) (hSet : ∀ p : ℕ, p.Prime → W p → ∃ k, CSetup7 p r m k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → ∀ k, CSetup7 p r m k →
      ∑ a, wC7 p r k (Frame.hybRow r m a) + ∑ b, wC7 p r k (Frame.hybCol r m b) ≤ T p) :
    DefHypTop I r m T (fun p => if W p then p + (3 * p + 1) / 4 - r - m else 0) := by
  refine defHypTop_of_wit I r m T _ hT W (fun p hp => by simp [hp]) ?_
  intro p hp hWp _
  obtain ⟨k, S⟩ := hSet p hp hWp
  have hk : (3 * p + 1) / 4 = k := by have := S.hk; omega
  refine ⟨_, _, ?_, hTd p hp hWp k S⟩
  simp only [if_pos hWp, hk]
  exact gleAt_C7_lam_wit S hL

end CatalanCore.Arith.Hybrid
