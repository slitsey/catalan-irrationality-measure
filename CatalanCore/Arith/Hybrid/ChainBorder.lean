module
public import CatalanCore.Arith.Hybrid.ChainWeighted
public import CatalanCore.Arith.Hybrid.ChainWitness
public import CatalanCore.Arith.Hybrid.LemmaE.WeightedTop
public import CatalanCore.Arith.Hybrid.LemmaE.BorderIndex
@[expose] public section
open Matrix Polynomial Finset CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r m N o k : ℕ} [Fact p.Prime] {Fr : Frame}
noncomputable def topFull (Fr : Frame) (p r m : ℕ) :
    Matrix (Fin r⊕Option (Fin m)) (Fin r⊕Option (Fin m)) ℚ[X] :=
  ((Rect.topMat Fr r m).map (rescaleHom p 2)).submatrix (borderEquiv r m) (borderEquiv r m)

lemma topFull_det : (topFull Fr p r m).det=rescaleHom p 2 ((Rect.afterTop r m).fullPolyG Fr) := by
  rw [topFull,Matrix.det_submatrix_equiv_self,det_rescale,Rect.det_topMat]
lemma topFull_inner (a b : Fin r⊕Fin m) :
    topFull Fr p r m (Sum.map id some a) (Sum.map id some b)=
      full Fr p r (fun i:Fin m=>r+2*i.val) (fun j:Fin m=>r+2*j.val+1) a b := by
  rcases a with i|i <;> rcases b with j|j
  all_goals simp [Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,topFull,Matrix.submatrix_apply,borderEquiv,Rect.topMat_inner,
    Rect.topMat,full,Rect.FullN,Rect.Blk,Rect.blkA,Rect.blkB,Rect.blkC,Rect.blkD,
    Matrix.fromBlocks,Matrix.one_apply,fullEntry,Frame.hybRow,Frame.hybCol,add_comm]

lemma topFull_B_apply (i : Fin r) (y : Option (Fin m)) :
    (topFull Fr p r m).toBlocks₁₂ i y=
      C (Fr.Mn i.val (y.elim (r+2*m) (fun j=>r+2*j.val+1))) := by
  cases y with
  | none => simp [Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,topFull,borderEquiv,Rect.topMat,Rect.topNode,rescaleHom,Frame.hybRow,Frame.hybCol]
  | some y => simp [Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,topFull,borderEquiv,Rect.topMat,Rect.topNode,rescaleHom,Frame.hybRow,Frame.hybCol]
lemma topFull_C_apply (z : Option (Fin m)) (i : Fin r) :
    (topFull Fr p r m).toBlocks₂₁ z i=
      C (Fr.Mn (z.elim (r+2*m) (fun j=>r+2*j.val)) i.val) := by
  cases z with
  | none => simp [Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,topFull,borderEquiv,Rect.topMat,Rect.topNode,rescaleHom,Frame.hybRow,Frame.hybCol]
  | some z => simp [Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,topFull,borderEquiv,Rect.topMat,Rect.topNode,rescaleHom,Frame.hybRow,Frame.hybCol]

lemma topFull_D_gle_two (hL : LamData Fr o) (hp : 5≤p)
    (hN : 4*(r+2*m+1)<p*p) (z y : Option (Fin m)) :
    GLE p 2 ((topFull Fr p r m).toBlocks₂₂ z y) := by
  have H (a b : ℕ) (ha : a≤r+2*m) (hb : b≤r+2*m) : GLE p 2 (C (Fr.Mn a b)) :=
    GLE.C_iff.mpr (Mn_square_mem hL hp hN (by omega) (by omega))
  cases z with
  | some z =>
    cases y with
    | some y =>
      simpa [Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,topFull,borderEquiv,Rect.topMat,Rect.topNode,rescaleHom,Frame.hybRow,Frame.hybCol]
        using H (r+2*z.val) (r+2*y.val+1) (by have:=z.isLt;omega) (by have:=y.isLt;omega)
    | none =>
      simpa [Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,topFull,borderEquiv,Rect.topMat,Rect.topNode,rescaleHom,Frame.hybRow,Frame.hybCol]
        using H (r+2*z.val) (r+2*m) (by have:=z.isLt;omega) (by omega)
  | none =>
    cases y with
    | some y =>
      simpa [Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,topFull,borderEquiv,Rect.topMat,Rect.topNode,rescaleHom,Frame.hybRow,Frame.hybCol]
        using H (r+2*m) (r+2*y.val+1) (by omega) (by have:=y.isLt;omega)
    | none =>
      change GLE p 2 (rescaleHom p 2 (X+C (Fr.Mn (r+2*m) (r+2*m))))
      apply gle_of_scaled_int1
      have hp0 : (p:ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have he : C ((p:ℚ)^2)*rescaleHom p 2 (X+C (Fr.Mn (r+2*m) (r+2*m))) =
          X+C ((p:ℚ)^2*Fr.Mn (r+2*m) (r+2*m)) := by
        simp only [rescaleHom,Polynomial.coe_compRingHom,add_comp,X_comp,C_comp,mul_add,←C_mul]
        have hh : C ((p:ℚ)^2)*C (((p:ℚ)^2)⁻¹)=(1:ℚ[X]) := by rw [←map_mul]; simp [hp0]
        rw [←mul_assoc,hh,one_mul]
      rw [he]
      apply Int1.add
      · exact (gle_iff_gn p 0 X).mp GLE.X
      · rw [Int1,gn_C]
        exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp
          (Mn_square_mem hL hp hN (by omega : r+2*m<r+2*m+1) (by omega : r+2*m<r+2*m+1))

/-- The same entry weights hold for the second family member, with constant cost four. -/
theorem top_det_weighted (hL : LamData Fr o) (hp : 5≤p)
    (hN : 4*(r+2*m+1)<p*p) (hk : (4:ZMod p)*k=o)
    (W : Fin m→Fin m→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 → NoCut (Cut p r (Singular p o))
      (min ((r+2*z.val:ℕ):ℤ) (r+2*y.val+1)) (max ((r+2*z.val:ℕ):ℤ) (r+2*y.val+1)))
    (hone : ∀z y,W z y=1 → (r+2*z.val)%p≠(r+2*y.val+1)%p) :
    GLE p (tropVal W+4+2*r) ((Rect.afterTop r m).fullPolyG Fr) := by
  let xs := fun i:Fin m=>r+2*i.val
  let ys := fun j:Fin m=>r+2*j.val+1
  have hr : r≤r+2*m+1 := by omega
  have hx : ∀i:Fin m,xs i<r+2*m+1 := fun i=>by dsimp[xs];have:=i.isLt;omega
  have hy : ∀i:Fin m,ys i<r+2*m+1 := fun i=>by dsimp[ys];have:=i.isLt;omega
  have HI:=Q_int1 (xs:=xs) (ys:=ys) hL hp hN hr
  have HP:=Q_primitive (xs:=xs) (ys:=ys) hL hp hN hr
  have HT:=T_entry_weighted hL hp hN hr hk hx hy
    (fun i=>by dsimp[xs];omega) (fun i=>by dsimp[ys];omega)
    (fun i j=>by dsimp[xs,ys];omega) W hW hzero hone
  have H := tcore_border_weighted (topFull Fr p r m) (full Fr p r xs ys)
    topFull_inner HI HP W HT
    (fun z i=>by
      apply (int1_Cpow_iff 2 _).mpr
      rw [topFull_C_apply]
      apply GLE.C_iff.mpr
      apply Mn_square_mem hL hp hN
      · cases z with
        | none => simp
        | some z => have:=z.isLt; simp_all <;> omega
      · exact i.isLt.trans_le hr)
    (fun i y=>by
      rw [topFull_B_apply]
      apply GLE.C_iff.mpr
      apply Mn_square_mem hL hp hN (i.isLt.trans_le hr)
      cases y with
      | none => simp
      | some y => have:=y.isLt; simp_all <;> omega)
    (topFull_D_gle_two hL hp hN)
  have he : (topFull Fr p r m).det=rescaleHom p 2 ((Rect.afterTop r m).fullPolyG Fr) := topFull_det
  rw [he] at H
  simpa only [Fintype.card_fin] using (GLE.of_rescale H)
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.top_det_weighted
