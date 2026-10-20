module
public import CatalanCore.Arith.Hybrid.ChainResidual
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}
lemma A_project_defect (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) :
    ∀ i j,gn p ((blockProject (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₁₁-
      (full Fr p r xs ys).toBlocks₁₁) i j)≤p := by
  intro i j
  by_cases hij : i.val%p=j.val%p
  · simp [blockProject,blockRect,hij,Matrix.sub_apply,gn_zero]
  · have hne : i≠j := by intro he; subst j; exact hij rfl
    simpa [blockProject,blockRect,hij,Matrix.sub_apply,gn_neg,full_A_apply_ne i j hne] using
      (gle_iff_gn p 1 _).mp (Mn_cross_gle hL hp hN hk (i.isLt.trans_le hr) (j.isLt.trans_le hr) hij)
lemma C_project_defect (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z,xs z<N) :
    ∀ z i,gn p (((full Fr p r xs ys).toBlocks₂₁-
      blockRect (fun z=>xs z%p) (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₂₁) z i)≤p := by
  intro z i
  by_cases hi : xs z%p=i.val%p
  · simp [blockRect,hi,Matrix.sub_apply,gn_zero]
  · simpa [blockRect,hi,Matrix.sub_apply,full_C_apply] using
      (gle_iff_gn p 1 _).mp (Mn_cross_gle hL hp hN hk (hx z) (i.isLt.trans_le hr) hi)
lemma B_project_defect (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hy : ∀ z,ys z<N) :
    ∀ i y,gn p (((full Fr p r xs ys).toBlocks₁₂-
      blockRect (fun i:Fin r=>i.val%p) (fun z=>ys z%p) (full Fr p r xs ys).toBlocks₁₂) i y)≤p := by
  intro i y
  by_cases hi : i.val%p=ys y%p
  · simp [blockRect,hi,Matrix.sub_apply,gn_zero]
  · simpa [blockRect,hi,Matrix.sub_apply,full_B_apply] using
      (gle_iff_gn p 1 _).mp (Mn_cross_gle hL hp hN hk (i.isLt.trans_le hr) (hy y) hi)
lemma Sr_residual_bound (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z,xs z<N) :
    ∀ z i,gn p ((h Fr p r xs ys • (full Fr p r xs ys).toBlocks₂₁-
      Sr Fr p r xs ys*(full Fr p r xs ys).toBlocks₁₁) z i)≤p :=
  row_residual_bound _ _ _ _ _ _ (le_of_eq (h_primitive hL hp hN hr))
    (Sr_int1 hL hp hN hr hx) Sr_solve p (by positivity)
    (A_project_defect hL hp hN hr hk) (C_project_defect hL hp hN hr hk hx)
lemma Sc_residual_bound (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hy : ∀ z,ys z<N) :
    ∀ i y,gn p ((h Fr p r xs ys • (full Fr p r xs ys).toBlocks₁₂-
      (full Fr p r xs ys).toBlocks₁₁*Sc Fr p r xs ys) i y)≤p :=
  col_residual_bound _ _ _ _ _ _ (le_of_eq (h_primitive hL hp hN hr))
    (Sc_int1 hL hp hN hr hy) Sc_solve p (by positivity)
    (A_project_defect hL hp hN hr hk) (B_project_defect hL hp hN hr hk hy)
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.Sr_residual_bound
