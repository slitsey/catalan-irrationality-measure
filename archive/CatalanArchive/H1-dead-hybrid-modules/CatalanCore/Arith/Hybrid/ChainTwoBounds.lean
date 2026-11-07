module
public import CatalanCore.Arith.Hybrid.PeriodicWeighted
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.ChainDeltaBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]

end CatalanCore.Arith.Hybrid.LemmaE
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}
lemma A_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ i j,GLE p 2 ((full Fr p r xs ys).toBlocks₁₁ i j) := by
  exact Periodic.Model.A_gle_two (Periodic.lamPoleData hL hp hN) (by omega) hr

lemma B_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,GLE p 2 ((full Fr p r xs ys).toBlocks₁₂ i y) := by
  exact Periodic.Model.B_gle_two (Periodic.lamPoleData hL hp hN) (by omega) hr hy

lemma C_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,GLE p 2 ((full Fr p r xs ys).toBlocks₂₁ z i) := by
  exact Periodic.Model.C_gle_two (Periodic.lamPoleData hL hp hN) (by omega) hr hx

lemma D_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) : ∀ z y,GLE p 2 ((full Fr p r xs ys).toBlocks₂₂ z y) := by
  exact Periodic.Model.D_gle_two (Periodic.lamPoleData hL hp hN) (by omega) hx hy

lemma delta_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) (z y : Z) : GLE p 2 (delta Fr p r xs ys z y) := by
  exact Periodic.Model.delta_gle_two (Periodic.lamPoleData hL hp hN) (by omega) hr hx hy z y

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_gle_two
