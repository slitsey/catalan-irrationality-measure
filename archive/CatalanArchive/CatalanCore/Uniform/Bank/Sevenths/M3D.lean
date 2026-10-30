import CatalanCore.Uniform.Bank.Sevenths.PoleData
import CatalanCore.Uniform.Bank.Sevenths.Price
import CatalanCore.Uniform.Bank.Sevenths.Rounding
import CatalanCore.Uniform.Bank.Sevenths.MemberIdentity
import CatalanCore.Uniform.Content.Wire.M3D
import CatalanCore.Uniform.Content.UFSimple.Closed
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.ChainClasses
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.UFSimple
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.Wire

/-- One exact periodic pole interval, also avoiding all core-exit cuts. -/
theorem sevenths_m3d_noCut (a : Fin 6) (r p n x y : ℕ) [Fact p.Prime]
    (hp8 : 8 ≤ p) (z : Bool) (hrx : r ≤ x) (hry : r ≤ y)
    (hxp : x < r + p) (hyp : y < r + p)
    (hxlo : n * p + (if z then seventhRho a p else 0) ≤ x)
    (hylo : n * p + (if z then seventhRho a p else 0) ≤ y)
    (hxhi : x < n * p + (if z then p else seventhRho a p))
    (hyhi : y < n * p + (if z then p else seventhRho a p)) :
    NoCut (Cut p r (ttSing p 7 (7 - seventhNumerator a))) (min (x : ℤ) y) (max (x : ℤ) y) := by
  have hb := seventhRho_bounds a p hp8
  have hB : p ∣ n * p := ⟨n, by ring⟩
  have hNo := noSing_blk (sevenths_twoTerm a) (B := n * p)
    (ℓ := if z then seventhRho a p else 0)
    (uz := (if z then p else seventhRho a p) - 1) (by omega) hB
    (by cases z <;> simp_all <;> omega) (seventhRho_dvd a p hp8) hb.1 hb.2
    (by cases z <;> simp_all <;> omega)
  have hnosing : NoCut (ttSing p 7 (7 - seventhNumerator a)) (min (x : ℤ) y) (max (x : ℤ) y) := by
    intro t ht1 ht2 hs
    have ht0 : 0 ≤ t := by omega
    lift t to ℕ using ht0 with k hk
    apply hNo k (by omega) (by omega) hs
  intro t ht1 ht2 hc
  rcases hc with hs | ⟨j, he⟩ | ⟨j, he⟩
  · exact hnosing t ht1 ht2 hs
  · exact hnosing t ht1 ht2 (Or.inl ⟨j, by rw [he]; ring⟩)
  · have hp0 : (0 : ℤ) < p := by omega
    have htlo : (r : ℤ) < t := by omega
    have hthi : t < (r : ℤ) + p := by omega
    have hj : 1 ≤ j := by
      by_contra h
      have hj0 : j ≤ 0 := by omega
      have hprod := mul_nonpos_of_nonpos_of_nonneg hj0 hp0.le
      linarith
    have hprod := mul_le_mul_of_nonneg_right hj hp0.le
    linarith

/-- The generic M3D proof clears every actual common-deletion member. -/
theorem sevenths_price_m3d_window (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι)
    (hi : (F7.family (seventhsFrameAt a) depth).Adm i) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] (hp64 : 64 ≤ p) (hr2 : 2 ≤ i.1) (hsq : 14 * i.1 < p * p)
    (A B : ℕ) (hA : i.1 ≤ A) (hAB : A ≤ B)
    (hB : B ≤ i.1 + 2 * F7.borderSize i.1) (hBp : B ≤ i.1 + p)
    (hcentral : max A (i.1 + 2 * F7.borderSize i.1 - p) ≤ B)
    (hcut : ∀ x y : ℕ, A ≤ x → x < B → A ≤ y → y < B →
      NoCut (Cut p i.1 (ttSing p 7 (7 - seventhNumerator a))) (min (x : ℤ) y) (max (x : ℤ) y)) :
    seventhsPrice a depth i p ≤ 2 * i.1 + (2 * F7.borderSize i.1 -
      (B - max A (i.1 + 2 * F7.borderSize i.1 - p))) := by
  have hm := (F7_border_round hr).1
  have hmr : 2 * F7.borderSize i.1 + 1 ≤ i.1 := by omega
  have hN : 7 * (i.1 + 2 * F7.borderSize i.1) ≤ p * p := by omega
  let D := sevenths_poleData a p (i.1 + 2 * F7.borderSize i.1) hp64 hN
  let af : ℕ → ℕ → ℕ := fun _ _ => A
  let bf : ℕ → ℕ → ℕ := fun _ _ => B
  have hk : (F7.geometry i.1).k = F7.borderSize i.1 := geometry_k_eq_borderSize F7 i.1
  have hv : m3dValid F7 (seventhsFrameAt a) af bf i.1 p := by
    refine ⟨F7_hyb hr, ?_⟩
    intro hp
    rw [hk]
    exact ⟨D, by omega, hA, hAB, hB, hBp, hcentral, hcut⟩
  have hg := (m3dLayer F7 (seventhsFrameAt a) depth af bf).gle i hi p hv
  apply seventhsPrice_le a depth i hr p _
  simpa only [m3dLayer, m3dBase, af, bf, zero_mul, add_zero, hk] using hg

#print axioms sevenths_m3d_noCut
#print axioms sevenths_price_m3d_window
end CatalanCore.Uniform.Bank.Sevenths
