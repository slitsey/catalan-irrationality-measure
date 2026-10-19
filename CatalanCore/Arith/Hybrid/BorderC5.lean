module

public import CatalanCore.Arith.Hybrid.DefC5Fam
public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# Theorem C5 for the bordered member `afterTop r m` (MEM2C/C5)
-/

open Finset Polynomial CatalanCore CatalanCore.Rect CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section GleTop

variable {p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup p r m k)

include S in
/-- Bordered twin of `gleAt_C5_lam`. -/
theorem gleAt_C5_lamTop {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr) :
    GLE p (∑ a, wC p r k (Frame.hybRow r m a) + ∑ b, wC p r k (Frame.hybCol r m b) -
      (p + k - r - m) + topC I r m p) ((afterTop r m).fullPolyG Fr) :=
  (gleAt_C5_lam_wit S hL).border I

end GleTop

open Classical in
/-- **Theorem C5 for the bordered member**: twin of `defHypT_C5`. -/
theorem defHypTop_C5 {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr) (r m : ℕ) (T : ℕ → ℕ)
    (W : ℕ → Prop) (hSet : ∀ p : ℕ, p.Prime → W p → ∃ k, CSetup p r m k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → ∀ k, CSetup p r m k →
      ∑ a, wC p r k (Frame.hybRow r m a) + ∑ b, wC p r k (Frame.hybCol r m b) ≤ T p) :
    DefHypTop I r m T (fun p => if W p then p + (p + 1) / 4 - r - m else 0) := by
  refine defHypTop_of_local T _ hT W (fun p hp => by simp [hp]) ?_
  intro p hp hb hWp
  obtain ⟨k, S⟩ := hSet p hp hWp
  haveI : Fact p.Prime := ⟨hp⟩
  have hd := hTd p hp hWp k S
  have h1 := wC_sum_ge (p := p) (r := r) (m := m) (k := k)
  have hg := gleAt_C5_lamTop S I hL
  have hk : (p + 1) / 4 = k := by have := S.hk; omega
  have hLhi := S.hLhi
  have hLlo := S.hLlo
  simp only [if_pos hWp, hk]
  exact fun [Fact p.Prime] => hg.mono (by omega)

end CatalanCore.Arith.Hybrid
