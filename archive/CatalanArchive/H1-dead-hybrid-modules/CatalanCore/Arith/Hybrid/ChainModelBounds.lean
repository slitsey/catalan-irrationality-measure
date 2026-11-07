module
public import CatalanCore.Arith.Hybrid.PeriodicModelBounds
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.ChainModel
public import CatalanCore.Arith.Hybrid.LemmaE.ProjectedBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}



lemma Q_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ i j,Int1 p (Q Fr p r xs ys i j) := by
  exact Periodic.Model.Q_int1 (Periodic.lamPoleData hL hp hN) (by omega) hr

lemma Q0_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ i j,Int1 p (Q0 Fr p r xs ys i j) := by
  exact Periodic.Model.Q0_int1 (Periodic.lamPoleData hL hp hN) (by omega) hr

lemma h_primitive (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    gn p (h Fr p r xs ys)=1 := by
  exact Periodic.Model.h_primitive (Periodic.lamPoleData hL hp hN) (by omega) hr

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.h_primitive
