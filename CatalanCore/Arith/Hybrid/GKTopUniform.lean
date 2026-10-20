module
public import CatalanCore.Arith.Hybrid.GKUniform
public import CatalanCore.Arith.Hybrid.ChainBorder
public import CatalanCore.Arith.Hybrid.BorderDef
public import CatalanCore.Arith.Hybrid.LemmaE.WeightedBorder
@[expose] public section
open Matrix Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Rect
namespace CatalanCore.Arith.Hybrid
open ChainClasses ChainModel LemmaE
variable {o p r m k : ℕ} [Fact p.Prime] {Fr : Frame}
lemma topW_one_of_p_le (I : HybInst Fr) (hb : p≤r+2*m) : 1≤topW I r m p := by
  let a:=r+2*m-p
  have ha : a+p=r+2*m := by dsimp[a];omega
  have hp0:0<p:=(Fact.out : p.Prime).pos
  have hab : a≠r+2*m := by omega
  have hd : (p:ℤ)∣(a:ℤ)-((r+2*m:ℕ):ℤ) := by
    refine ⟨-1,?_⟩
    have he : (a:ℤ)+(p:ℤ)=((r+2*m:ℕ):ℤ) := by exact_mod_cast ha
    omega
  have hw : 1≤wt I.lev p a (r+2*m) := by
    simp only [wt,if_neg hab,if_pos hd]
    omega
  have he : 1∈Icc 1 (Elev I r m) := by
    simp only [mem_Icc]
    constructor
    · omega
    · unfold Elev;omega
  have hl : wt I.lev p a (r+2*m)≤levels I.lev p (Elev I r m) a (r+2*m) := by
    simpa only [levels,pow_one] using
      (Finset.single_le_sum (fun e (_:e∈Icc 1 (Elev I r m))=>Nat.zero_le (wt I.lev (p^e) a (r+2*m))) he)
  have ht:=topW_ge I r m p (show a≤r+2*m by omega)
  omega
lemma clean_top_gle (I : HybInst Fr) [I.DiagOK r m] (hL : LamData Fr o)
    (hp : 5≤p) (hN : 4*(r+2*m+1)<p*p) (hk : (4:ZMod p)*k=o) (hb : p≤r+2*m)
    (hcut : ∀ x y:ℕ,r≤x → x<r+2*m → r≤y → y<r+2*m →
      NoCut (Cut p r (Singular p o)) (min (x:ℤ) y) (max (x:ℤ) y)) :
    GLE p (2*r+(topW I r m p+topW I r m p)) ((afterTop r m).fullPolyG Fr) := by
  let xs:=fun i:Fin m=>r+2*i.val
  let ys:=fun j:Fin m=>r+2*j.val+1
  have hr : r≤r+2*m+1 := by omega
  have hx : ∀i:Fin m,xs i<r+2*m+1 := fun i=>by dsimp[xs];have:=i.isLt;omega
  have hy : ∀i:Fin m,ys i<r+2*m+1 := fun i=>by dsimp[ys];have:=i.isLt;omega
  have HT:=T_entry_weighted hL hp hN hr hk hx hy
    (fun i=>by dsimp[xs];omega) (fun i=>by dsimp[ys];omega)
    (fun i j=>by dsimp[xs,ys];omega) (fun _ _=>0) (fun _ _=>by omega)
    (fun i j _=>hcut _ _ (by dsimp[xs];omega) (by dsimp[xs];have:=i.isLt;omega)
      (by dsimp[ys];omega) (by dsimp[ys];have:=j.isLt;omega)) (fun _ _ he=>by omega)
  have H:=tcore_border_weighted_incidence (topFull Fr p r m) (full Fr p r xs ys)
    topFull_inner (Q_int1 hL hp hN hr) (Q_primitive hL hp hN hr) (fun _ _=>0) HT (topW I r m p)
    (fun z i=>by
      apply (int1_Cpow_iff 2 _).mpr
      rw [topFull_C_apply]
      exact GLE.C_iff.mpr (Mn_square_mem hL hp hN (by simp only [Option.elim_some];have:=z.isLt;omega) (i.isLt.trans_le hr)))
    (fun i y=>by
      apply (int1_Cpow_iff 2 _).mpr
      rw [topFull_B_apply]
      exact GLE.C_iff.mpr (Mn_square_mem hL hp hN (i.isLt.trans_le hr) (by simp only [Option.elim_some];have:=y.isLt;omega)))
    (fun i=>by rw [topFull_C_apply];exact gle_top_entry I r m p (by have:=i.isLt;omega))
    (fun i=>by rw [topFull_B_apply];exact gle_entry_top I r m p (by have:=i.isLt;omega))
    (fun y=>by
      simpa [Matrix.toBlocks₂₂,topFull,borderEquiv,Rect.topMat,Rect.topNode,rescaleHom,Frame.hybRow,Frame.hybCol]
        using gle_top_entry I r m p (show r+2*y.val+1≤r+2*m by have:=y.isLt;omega))
    (fun z=>by
      simpa [Matrix.toBlocks₂₂,topFull,borderEquiv,Rect.topMat,Rect.topNode,rescaleHom,Frame.hybRow,Frame.hybCol]
        using gle_entry_top I r m p (show r+2*z.val≤r+2*m by have:=z.isLt;omega))
    ((topFull_D_gle_two hL hp hN none none).mono (by have:=topW_one_of_p_le I hb;omega))
  rw [topFull_det] at H
  have ht : tropVal (fun _ _ : Fin m=>0)=0 := Nat.le_zero.mp (tropVal_le_of_forall (fun _=>by simp))
  simpa only [ht,zero_add,Fintype.card_fin,Nat.add_comm] using GLE.of_rescale H
lemma GKS3.uniform_top_gle (I : HybInst Fr) [I.DiagOK r m] (hL : LamData Fr o)
    (S : GKS3 o p r m k) :
    GLE p (2*r+(topW I r m p+topW I r m p)) ((afterTop r m).fullPolyG Fr) := by
  exact clean_top_gle I hL (by have:=S.p13;omega)
    (by have:=S.hN;have:=S.p13;nlinarith)
    (by have H:=congrArg (fun n:ℕ=>(n:ZMod p)) S.hk.1;simpa using H)
    (by have:=S.hr;omega) S.noCut
lemma GK1.GKS1.uniform_top_gle (I : HybInst Fr) [I.DiagOK r m] (hL : LamData Fr o)
    (S : GK1.GKS1 o p r m k) :
    GLE p (2*r+(topW I r m p+topW I r m p)) ((afterTop r m).fullPolyG Fr) := by
  exact clean_top_gle I hL (by have:=S.p13;omega)
    (by have:=S.hN;have:=S.hk;have:=S.p13;nlinarith)
    (by have H:=congrArg (fun n:ℕ=>(n:ZMod p)) S.hk.1;simpa using H)
    (by have:=S.hr;omega) S.noCut
end CatalanCore.Arith.Hybrid
#print axioms CatalanCore.Arith.Hybrid.GKS3.uniform_top_gle
#print axioms CatalanCore.Arith.Hybrid.GK1.GKS1.uniform_top_gle
