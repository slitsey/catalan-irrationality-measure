import CatalanCore.Uniform.Bank.Sevenths.TropicalLevels
import CatalanCore.Uniform.Bank.Sevenths.Price
import CatalanCore.Uniform.Bank.Sevenths.Rounding
import CatalanCore.Uniform.Bank.Sevenths.MemberIdentity
import CatalanCore.Arith.Hybrid.Values
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.BankShared

theorem seventhsPrice_tail (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] (hp : 14 * i.1 < p) : seventhsPrice a depth i p = 0 := by
  by_cases hz : i.1 = 0
  · have h := seventhsPrice_crude a depth i hr p
    simp only [Ecrude, hz, mul_zero, zero_mul] at h
    omega
  have hr2 : 2 ≤ i.1 := by omega
  let r := i.1
  let m := F7.borderSize r
  have hm := (F7_border_round hr).1
  have hmr : 2 * m + 1 ≤ r := by omega
  have hp8 : 8 ≤ p := by omega
  have hpp : p ≤ p * p := by
    have h := Nat.mul_le_mul_right p (show 1 ≤ p by omega)
    simpa only [one_mul] using h
  have hN : 7 * (r + 2 * m + 1) ≤ p * p := by omega
  let D := sevenths_poleData_of_eight a p (r + 2 * m + 1) hp8 hN
  have hlow : ∀ c, poleLevels D p c = 0 ↔ c < seventhRho a p :=
    sevenths_poleLevels_low a p _ hp8 hN
  have hb := seventhRho_bounds a p hp8
  obtain ⟨j, hj0, hj6, he⟩ := seventhRho_root a p hp8
  have hjp : p ≤ j * p := Nat.le_mul_of_pos_left p hj0
  have hk : r + 2 * m ≤ seventhRho a p := by omega
  have ht := val_D6 (lev := poleLevels D) p r m (seventhRho a p)
    (by omega) (by omega) hlow
  have ht0 : tropVal (HW (poleLevels D) p r m) = 0 := by omega
  have hg := pole_commonMinor_gle D (by nlinarith) r m (by omega)
    (retainedFin (F7_hyb hr) i.2)
  rw [ht0] at hg
  have hbound := seventhsPrice_le a depth i hr p 0 (by
    rw [sevenths_member_commonMinor (seventhsFrameAt a) depth r hr i.2]
    exact hg)
  omega

#print axioms seventhsPrice_tail
end CatalanCore.Uniform.Bank.Sevenths
