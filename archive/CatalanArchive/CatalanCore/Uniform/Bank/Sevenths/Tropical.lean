import CatalanCore.Uniform.Bank.Sevenths.PoleData
import CatalanCore.Uniform.Bank.Sevenths.Price
import CatalanCore.Uniform.Bank.Sevenths.MemberIdentity
import CatalanCore.Uniform.Bank.Sevenths.Rounding
import CatalanCore.Uniform.Content.BankShared.PoleTropical
import CatalanCore.Uniform.Content.Layers.SawCount
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.Layers

theorem sevenths_tropical_price (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] (hp64 : 64 ≤ p) (hr2 : 2 ≤ i.1)
    (hsq : 14 * i.1 < p * p) :
    ∃ lev : ℕ → ℕ → ℕ,
      seventhsPrice a depth i p ≤ tropVal (HW lev p i.1 (F7.borderSize i.1)) := by
  let r := i.1
  let m := F7.borderSize r
  have hm := (F7_border_round hr).1
  have hN : 7 * (r + 2 * m + 1) ≤ p * p := by
    have hmr : 2 * m + 1 ≤ r := by omega
    omega
  let D := sevenths_poleData a p (r + 2 * m + 1) hp64 hN
  refine ⟨poleLevels D, ?_⟩
  apply seventhsPrice_le a depth i hr p
  rw [sevenths_member_commonMinor (seventhsFrameAt a) depth r hr i.2]
  exact pole_commonMinor_gle D (by omega) r m (by omega) _

theorem sevenths_saw_price (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] (hp64 : 64 ≤ p) (hodd : p % 2 = 1)
    (hr2 : 2 ≤ i.1) (hsq : 14 * i.1 < p * p) :
    seventhsPrice a depth i p + sawM p (F7.borderSize i.1) ≤
      2 * (i.1 + F7.borderSize i.1) := by
  obtain ⟨lev, hl⟩ := sevenths_tropical_price a depth i hr p hp64 hr2 hsq
  exact (Nat.add_le_add_right hl _).trans (trop_saw_closed lev hodd)

#print axioms sevenths_tropical_price
#print axioms sevenths_saw_price
end CatalanCore.Uniform.Bank.Sevenths
