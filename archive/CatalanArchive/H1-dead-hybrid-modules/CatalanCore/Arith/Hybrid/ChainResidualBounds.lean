module
public import CatalanCore.Arith.Hybrid.PeriodicWeighted
public import CatalanCore.Arith.Hybrid.LamPoleData
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
  exact Periodic.Model.A_project_defect (Periodic.lamPoleData hL hp hN) (by omega) hr

lemma C_project_defect (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z,xs z<N) :
    ∀ z i,gn p (((full Fr p r xs ys).toBlocks₂₁-
      blockRect (fun z=>xs z%p) (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₂₁) z i)≤p := by
  exact Periodic.Model.C_project_defect (Periodic.lamPoleData hL hp hN) (by omega) hr hx

lemma B_project_defect (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hy : ∀ z,ys z<N) :
    ∀ i y,gn p (((full Fr p r xs ys).toBlocks₁₂-
      blockRect (fun i:Fin r=>i.val%p) (fun z=>ys z%p) (full Fr p r xs ys).toBlocks₁₂) i y)≤p := by
  exact Periodic.Model.B_project_defect (Periodic.lamPoleData hL hp hN) (by omega) hr hy

lemma Sr_residual_bound (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z,xs z<N) :
    ∀ z i,gn p ((h Fr p r xs ys • (full Fr p r xs ys).toBlocks₂₁-
      Sr Fr p r xs ys*(full Fr p r xs ys).toBlocks₁₁) z i)≤p := by
  exact Periodic.Model.Sr_residual_bound (Periodic.lamPoleData hL hp hN) (by omega) hr hx

lemma Sc_residual_bound (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hy : ∀ z,ys z<N) :
    ∀ i y,gn p ((h Fr p r xs ys • (full Fr p r xs ys).toBlocks₁₂-
      (full Fr p r xs ys).toBlocks₁₁*Sc Fr p r xs ys) i y)≤p := by
  exact Periodic.Model.Sc_residual_bound (Periodic.lamPoleData hL hp hN) (by omega) hr hy

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.Sr_residual_bound
