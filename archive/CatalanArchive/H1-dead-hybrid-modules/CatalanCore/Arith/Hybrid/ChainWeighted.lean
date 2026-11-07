module
public import CatalanCore.Arith.Hybrid.PeriodicWeighted
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainUnordered
public import CatalanCore.Arith.Hybrid.ChainTwoBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
lemma Q_primitive (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    gn p (Q Fr p r xs ys).det=1 := by
  exact Periodic.Model.Q_primitive (Periodic.lamPoleData hL hp hN) (by omega) hr

theorem delta_gle_weighted (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk : (4:ZMod p)*k=o) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r (Singular p o)) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    ∀ z y,GLE p (W z y) (delta Fr p r xs ys z y) := by
  exact Periodic.Model.delta_gle_weighted (Periodic.lamPoleData hL hp hN) (by omega) hr hx hy hxlo hylo hne W hW hzero hone

theorem T_entry_weighted (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk : (4:ZMod p)*k=o) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r (Singular p o)) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    ∀ z y,GLE p (W z y) (Tscaled (Q Fr p r xs ys).det
      (full Fr p r xs ys).toBlocks₁₁ (full Fr p r xs ys).toBlocks₁₂
      (full Fr p r xs ys).toBlocks₂₁ (full Fr p r xs ys).toBlocks₂₂
      (Nmat p (fun _:Fin r=>1) (full Fr p r xs ys).toBlocks₁₁) z y) := by
  exact Periodic.Model.T_entry_weighted (Periodic.lamPoleData hL hp hN) (by omega) hr hx hy hxlo hylo hne W hW hzero hone

theorem full_det_weighted (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk : (4:ZMod p)*k=o) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r (Singular p o)) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    GLE p (tropVal W+2*r) (full Fr p r xs ys).det := by
  exact Periodic.Model.full_det_weighted (Periodic.lamPoleData hL hp hN) (by omega) hr hx hy hxlo hylo hne W hW hzero hone

/-- Composition back to the original determinant does not change its denominator budget. -/
theorem original_det_weighted (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk : (4:ZMod p)*k=o) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y) (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r (Singular p o)) (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    GLE p (tropVal W+2*r) (Rect.FullN Fr (fun i:Fin r=>i.val) xs ys (X:ℚ[X])).det := by
  exact Periodic.Model.original_det_weighted (Periodic.lamPoleData hL hp hN) (by omega) hr hx hy hxlo hylo hne W hW hzero hone

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.original_det_weighted
