import CatalanCore.Uniform.Bank.Sevenths.LPWindows
import CatalanCore.Uniform.Bank.Sevenths.Price
import CatalanCore.Uniform.Content.BankShared.LPPrice
import CatalanCore.Uniform.Content.BankShared.Reindex
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.BankShared

/-- Exact first LP clearing price on the actual norm-49 family. -/
theorem sevenths_price_lp1 (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι)
    (hi : (F7.family (seventhsFrameAt a) depth).Adm i) (hr : i.1 % 2 = 0)
    (p j : ℕ) [Fact p.Prime] (hp64 : 64 ≤ p) (hj : 1 ≤ j)
    (hroot : 7 * seventhRho a p = j * p + seventhOffset a)
    (hN : i.1 + 2 * F7.borderSize i.1 ≤ 2 * p) (hrp : p ≤ i.1)
    (hUk : i.1 < p + seventhRho a p) :
    (seventhsPrice a depth i p : ℚ) ≤ (17 / 4 : ℚ) * i.1 -
      ((2 * (7 + j) : ℕ) : ℚ) / 7 * p + depth + 2 := by
  let kf : ℕ → ℕ → ℕ := fun _ q => seventhRho a q
  let jf : ℕ → ℕ → ℕ := fun _ _ => j
  have hk : (F7.geometry i.1).k = F7.borderSize i.1 := geometry_k_eq_borderSize F7 i.1
  have hv : lp1Valid F7 (seventhsFrameAt a) 7 (7 - seventhNumerator a) kf jf i.1 p := by
    refine ⟨F7_hyb hr, ?_⟩
    intro hp
    rw [hk]
    exact sevenths_lp1_hyp a p i.1 (F7.borderSize i.1) j hp64 hj hroot hN hrp hUk
  have hg := (lp1Layer F7 (seventhsFrameAt a) depth 7 (7 - seventhNumerator a) kf jf).gle i hi p hv
  change GLE p (lp1Base F7 kf i.1 p + 1 * delCount F7 i) _ at hg
  simp only [one_mul] at hg
  have hb := seventhRho_bounds a p (by omega)
  have hkr : seventhRho a p ≤ i.1 := by omega
  have hlo : i.1 - p ≤ seventhRho a p := by omega
  have hbase : lp1Base F7 kf i.1 p ≤
      2 * (i.1 - (seventhRho a p - (i.1 - p))) + 3 * F7.borderSize i.1 := by
    simpa only [lp1Base, hk, kf] using
      lp1_slot_bound p i.1 (F7.borderSize i.1) (seventhRho a p) hkr hlo (by omega)
  have hprice := seventhsPrice_le a depth i hr p _ hg
  have hdel := delCount_le F7 (seventhsFrameAt a) depth i hi
  have hnat : seventhsPrice a depth i p ≤
      2 * (i.1 - (seventhRho a p - (i.1 - p))) + 3 * F7.borderSize i.1 + depth := by omega
  have hQ : (seventhsPrice a depth i p : ℚ) ≤
      2 * ((i.1 - (seventhRho a p - (i.1 - p)) : ℕ) : ℚ) +
        3 * (F7.borderSize i.1 : ℚ) + depth := by exact_mod_cast hnat
  rw [Nat.cast_sub ((Nat.sub_le _ _).trans hkr), Nat.cast_sub hlo, Nat.cast_sub hrp] at hQ
  have hm : (12 : ℚ) * F7.borderSize i.1 ≤ i.1 + 6 := by exact_mod_cast (F7_border_round hr).1
  have he : (7 : ℚ) * seventhRho a p = (j : ℚ) * p + seventhOffset a := by exact_mod_cast hroot
  have ho : (0 : ℚ) ≤ seventhOffset a := Nat.cast_nonneg _
  push_cast
  nlinarith

/-- Exact second LP clearing price, retaining its full `N ≤ p+rho` hypothesis. -/
theorem sevenths_price_lp2 (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι)
    (hi : (F7.family (seventhsFrameAt a) depth).Adm i) (hr : i.1 % 2 = 0)
    (p j : ℕ) [Fact p.Prime] (hp64 : 64 ≤ p) (hj : 1 ≤ j)
    (hroot : 7 * seventhRho a p = j * p + seventhOffset a)
    (hN : i.1 + 2 * F7.borderSize i.1 ≤ p + seventhRho a p) (hrp : i.1 < p)
    (hkr : seventhRho a p ≤ i.1) (hpm : p < i.1 + F7.borderSize i.1) :
    (seventhsPrice a depth i p : ℚ) ≤ (9 / 4 : ℚ) * i.1 -
      ((2 * j : ℕ) : ℚ) / 7 * p + depth + 2 := by
  let kf : ℕ → ℕ → ℕ := fun _ q => seventhRho a q
  let jf : ℕ → ℕ → ℕ := fun _ _ => j
  have hk : (F7.geometry i.1).k = F7.borderSize i.1 := geometry_k_eq_borderSize F7 i.1
  have hv : lp2Valid F7 (seventhsFrameAt a) 7 (7 - seventhNumerator a) kf jf i.1 p := by
    refine ⟨F7_hyb hr, ?_⟩
    intro hp
    rw [hk]
    exact ⟨sevenths_lp2_hyp a p i.1 (F7.borderSize i.1) j hp64 hj hroot hN hrp hkr, hpm⟩
  have hg := (lp2Layer F7 (seventhsFrameAt a) depth 7 (7 - seventhNumerator a) kf jf).gle i hi p hv
  change GLE p (lp2Base F7 kf i.1 p + 1 * delCount F7 i) _ at hg
  simp only [one_mul] at hg
  have hbase : lp2Base F7 kf i.1 p ≤
      2 * (i.1 - seventhRho a p) + 3 * F7.borderSize i.1 := by
    simpa only [lp2Base, hk, kf] using
      lp2_slot_bound p i.1 (F7.borderSize i.1) (seventhRho a p) hrp.le
  have hprice := seventhsPrice_le a depth i hr p _ hg
  have hdel := delCount_le F7 (seventhsFrameAt a) depth i hi
  have hnat : seventhsPrice a depth i p ≤
      2 * (i.1 - seventhRho a p) + 3 * F7.borderSize i.1 + depth := by omega
  have hQ : (seventhsPrice a depth i p : ℚ) ≤
      2 * ((i.1 - seventhRho a p : ℕ) : ℚ) + 3 * (F7.borderSize i.1 : ℚ) + depth := by exact_mod_cast hnat
  rw [Nat.cast_sub hkr] at hQ
  have hm : (12 : ℚ) * F7.borderSize i.1 ≤ i.1 + 6 := by exact_mod_cast (F7_border_round hr).1
  have he : (7 : ℚ) * seventhRho a p = (j : ℚ) * p + seventhOffset a := by exact_mod_cast hroot
  have ho : (0 : ℚ) ≤ seventhOffset a := Nat.cast_nonneg _
  push_cast
  nlinarith

#print axioms sevenths_price_lp1
#print axioms sevenths_price_lp2
end CatalanCore.Uniform.Bank.Sevenths
