module
public import CatalanCore.Arith.Hybrid.PeriodicModelBounds
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.ChainModelBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}


lemma B2_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,Int1 p (B2 Fr p r xs ys i y) := by
  exact Periodic.Model.B2_int1 (Periodic.lamPoleData hL hp hN) (by omega) hr hy

lemma C2_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,Int1 p (C2 Fr p r xs ys z i) := by
  exact Periodic.Model.C2_int1 (Periodic.lamPoleData hL hp hN) (by omega) hr hx

lemma Sr_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,Int1 p (Sr Fr p r xs ys z i) := by
  exact Periodic.Model.Sr_int1 (Periodic.lamPoleData hL hp hN) (by omega) hr hx

lemma Sc_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,Int1 p (Sc Fr p r xs ys i y) := by
  exact Periodic.Model.Sc_int1 (Periodic.lamPoleData hL hp hN) (by omega) hr hy

lemma Q0_det_ne (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    (Q0 Fr p r xs ys).det≠0 := by
  exact Periodic.Model.Q0_det_ne (Periodic.lamPoleData hL hp hN) (by omega) hr

lemma Sr_support (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ z i,xs z%p≠i.val%p→Sr Fr p r xs ys z i=0 := by
  exact Periodic.Model.Sr_support (Periodic.lamPoleData hL hp hN) (by omega) hr

lemma Sc_support (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ i y,i.val%p≠ys y%p→Sc Fr p r xs ys i y=0 := by
  exact Periodic.Model.Sc_support (Periodic.lamPoleData hL hp hN) (by omega) hr

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.Sr_support
