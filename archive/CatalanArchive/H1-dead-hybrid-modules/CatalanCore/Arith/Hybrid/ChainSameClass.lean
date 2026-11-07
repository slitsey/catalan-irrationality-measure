module
public import CatalanCore.Arith.Hybrid.PeriodicCancellation
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainCancellation
public import CatalanCore.Arith.Hybrid.ChainDeltaBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
theorem delta_int1_ordered (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk4 : (4:ZMod p)*k=o) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r (Singular p o)) (xs z) (ys y))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0) :
    Int1 p (delta Fr p r xs ys z y) := by
  exact Periodic.Model.delta_int1_ordered (Periodic.lamPoleData hL hp5 hN) (by omega) hr hxN hyN z y hz hy hzy hc hd

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_int1_ordered
