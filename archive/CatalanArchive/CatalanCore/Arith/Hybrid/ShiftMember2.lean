module
public import CatalanCore.Arith.Hybrid.ShiftMember1
public import CatalanCore.Arith.Hybrid.GKTopUniform
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic CatalanCore.Rect
namespace CatalanCore.Arith.Hybrid

/-! # Member 2 (bordered by the common node), conditional on the weighted same-cell congruence

The inner `m × m` block of the scaled Schur complement of the bordered matrix `topFull` is
literally the zone block `zoneT` of member 1 (`topFull_inner`), so the weighted congruence `hwt`,
its zero pattern and the leading cross-cell blocks are the same data.  Only the border entries
need new bounds: they are `GLE (topW)` (corner `GLE (topW + topW)`), and the cost of the border is
exactly `topC = 2 topW + 1`.  No moment variant is needed. -/

namespace ChainModel
open ChainClasses LemmaE
variable {p r m o k : ℕ} [Fact p.Prime] {Fr : Frame}

theorem twoLevel_top_gle_of_wt (I : HybInst Fr) [I.DiagOK r m] (hL : LamData Fr o) (hp : 5 ≤ p)
    (hm : 2 * m < p) (hN : 4 * (r + 2 * m + 1) < p * p) (hk : (4 : ZMod p) * k = (o : ZMod p))
    (hb : p ≤ r + 2 * m)
    (CR CC : Finset (Fin m)) (w : ZMod p → RatFunc (ZMod p)) (sb : Finset (ZMod p))
    (hcell : ZoneCell p o r m CR CC) (hwt : ZoneWt Fr p r m CR CC w)
    (hzero : ZoneZero p r m CR CC w sb)
    (hσ : (CR.card + CC.card - m) + ((CR.card + CC.card - m) - sb.card) ≤ m) :
    GLE p (m - ((CR.card + CC.card - m) + ((CR.card + CC.card - m) - sb.card)) + topC I r m p
        + 2 * r) ((afterTop r m).fullPolyG Fr) := by
  classical
  have hN0 : 4 * (r + 2 * m) < p * p := by omega
  have hr0 : r ≤ r + 2 * m := by omega
  have hr : r ≤ r + 2 * m + 1 := by omega
  have hCs : ∀ (z : Fin m) i, Int1 p (C ((p : ℚ) ^ 2) * (topFull Fr p r m).toBlocks₂₁ (some z) i) := fun z i => by
    apply (int1_Cpow_iff 2 _).mpr
    rw [topFull_C_apply]
    exact GLE.C_iff.mpr (Mn_square_mem hL hp hN
      (by simp only [Option.elim_some]; have := z.isLt; omega)
      (i.isLt.trans_le hr))
  have hBs : ∀ i (y : Fin m), Int1 p (C ((p : ℚ) ^ 2) * (topFull Fr p r m).toBlocks₁₂ i (some y)) := fun i y => by
    apply (int1_Cpow_iff 2 _).mpr
    rw [topFull_B_apply]
    exact GLE.C_iff.mpr (Mn_square_mem hL hp hN (i.isLt.trans_le hr)
      (by simp only [Option.elim_some]; have := y.isLt; omega))
  have hCr : ∀ i : Fin r, GLE p (topW I r m p) ((topFull Fr p r m).toBlocks₂₁ none i) := fun i => by
    rw [topFull_C_apply]; exact gle_top_entry I r m p (by have := i.isLt; omega)
  have hBc : ∀ i : Fin r, GLE p (topW I r m p) ((topFull Fr p r m).toBlocks₁₂ i none) := fun i => by
    rw [topFull_B_apply]; exact gle_entry_top I r m p (by have := i.isLt; omega)
  have hDr : ∀ y : Fin m, GLE p (topW I r m p) ((topFull Fr p r m).toBlocks₂₂ none (some y)) := fun y => by
    simpa [Matrix.toBlocks₂₂, topFull, borderEquiv, Rect.topMat, Rect.topNode, rescaleHom,
      Frame.hybRow, Frame.hybCol] using gle_top_entry I r m p
        (show r + 2 * y.val + 1 ≤ r + 2 * m by have := y.isLt; omega)
  have hDc : ∀ z : Fin m, GLE p (topW I r m p) ((topFull Fr p r m).toBlocks₂₂ (some z) none) := fun z => by
    simpa [Matrix.toBlocks₂₂, topFull, borderEquiv, Rect.topMat, Rect.topNode, rescaleHom,
      Frame.hybRow, Frame.hybCol] using gle_entry_top I r m p
        (show r + 2 * z.val ≤ r + 2 * m by have := z.isLt; omega)
  have hD : GLE p (topW I r m p + topW I r m p) ((topFull Fr p r m).toBlocks₂₂ none none) :=
    (topFull_D_gle_two hL hp hN none none).mono (by have := topW_one_of_p_le I hb; omega)
  set F := topFull Fr p r m with hF
  set F0 := full Fr p r (zoneX r m) (zoneY r m) with hF0
  have hold : ∀ a b, F (Sum.map id some a) (Sum.map id some b) = F0 a b := topFull_inner
  have hA : F.toBlocks₁₁ = F0.toBlocks₁₁ := by
    apply Matrix.ext; intro i j; exact hold (Sum.inl i) (Sum.inl j)
  have hb' (i : Fin r) (y : Fin m) : F.toBlocks₁₂ i (some y) = F0.toBlocks₁₂ i y :=
    hold (Sum.inl i) (Sum.inr y)
  have hc' (z : Fin m) (i : Fin r) : F.toBlocks₂₁ (some z) i = F0.toBlocks₂₁ z i :=
    hold (Sum.inr z) (Sum.inl i)
  have hd' (z y : Fin m) : F.toBlocks₂₂ (some z) (some y) = F0.toBlocks₂₂ z y :=
    hold (Sum.inr z) (Sum.inr y)
  have HI := Q_int1 (xs := zoneX r m) (ys := zoneY r m) hL hp hN hr
  have HP := Q_primitive (xs := zoneX r m) (ys := zoneY r m) hL hp hN hr
  have hIF : ∀ i j, Int1 p (Atil p (fun _ : Fin r => 1) F.toBlocks₁₁ i j) := by
    rw [hA]; exact HI
  have hPF : gn p (Atil p (fun _ : Fin r => 1) F.toBlocks₁₁).det = 1 := by
    rw [hA]; exact HP
  -- the data
  set T := Tscaled (Atil p (fun _ : Fin r => 1) F.toBlocks₁₁).det F.toBlocks₁₁ F.toBlocks₁₂
    F.toBlocks₂₁ F.toBlocks₂₂ (Nmat p (fun _ : Fin r => 1) F.toBlocks₁₁) with hT
  have hTin : ∀ z y : Fin m, T (some z) (some y) = zoneT Fr p r m z y := by
    intro z y
    simp only [hT, Tscaled_apply, hA, hb', hc', hd']
    rfl
  have hint : ∀ z y : Fin m, GLE p 1 (T (some z) (some y)) := fun z y => by
    rw [hTin]; exact zoneT_gle_one hL hp hm hN0 hk z y
  have D := shiftData_of_wt (Fr := Fr) (p := p) (r := r) (N := r + 2 * m) (o := o) (k := k)
    (xs := zoneX r m) (ys := zoneY r m) hL hp hN0 hr0 hk (fun z => zoneX_lt z)
    (fun y => zoneY_lt y) CR CC w sb (fun z _ => by simp [zoneX])
    (fun y _ => by simp only [zoneY]; omega) hcell.1 hcell.2
    (fun z y => zone_dist_ne (r := r) hm z.isLt y.isLt) hwt hzero
  have e : (Matrix.of fun z y : Fin m => T (some z) (some y)) = zoneT Fr p r m := by
    exact Matrix.ext fun z y => hTin z y
  have D' : ShiftCauchyData p (Matrix.of fun z y : Fin m => T (some z) (some y))
      (fun z => ((zoneX r m z : ℕ) : ZMod p)) (fun y => ((zoneY r m y : ℕ) : ZMod p)) CR CC w sb := by
    rw [e]; exact D
  have hg : gn p (Atil p (fun _ : Fin r => 1) F.toBlocks₁₁).det = 1 := hPF
  have H := gle_full_of_shiftData_border p F (Atil p (fun _ : Fin r => 1) F.toBlocks₁₁).det hg
    (Nmat p (fun _ : Fin r => 1) F.toBlocks₁₁) (AN_eq p (fun _ : Fin r => 1) _)
    (2 * ∑ _i : Fin r, 1) (det_Atil p (fun _ : Fin r => 1) _).symm
    (fun z => ((zoneX r m z : ℕ) : ZMod p)) (fun y => ((zoneY r m y : ℕ) : ZMod p)) CR CC w sb T hT hint D'
    (topW I r m p)
    (fun z => by
      simpa only [] using Tscaled_gle_right_at (topW I r m p) F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁
        F.toBlocks₂₂ hIF hPF (some z) none (hCs z) hBc (hDc z))
    (fun y => by
      simpa only [] using Tscaled_gle_left_at (topW I r m p) F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁
        F.toBlocks₂₂ hIF hPF none (some y) hCr (fun i => hBs i y) (hDr y))
    (by simpa only [] using Tscaled_gle_product_at (topW I r m p) (topW I r m p) F.toBlocks₁₁ F.toBlocks₁₂
          F.toBlocks₂₁ F.toBlocks₂₂ hIF hPF none none hCr hBc hD)
    (by simpa [Fintype.card_fin] using hσ)
  rw [hF, topFull_det] at H
  have H2 := GLE.of_rescale H
  have hc : topC I r m p = topW I r m p + topW I r m p + 1 := rfl
  have e2 : (2 * ∑ _i : Fin r, 1) = 2 * r := by simp
  rw [e2] at H2
  simp only [Fintype.card_fin] at H2
  rw [hc]
  have := H2
  convert this using 2

end ChainModel
#print axioms ChainModel.twoLevel_top_gle_of_wt
end CatalanCore.Arith.Hybrid
