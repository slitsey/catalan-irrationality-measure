module
public import CatalanCore.Arith.Hybrid.PeriodicWeighted
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.ChainSameClass
public import CatalanCore.Arith.Hybrid.ChainSymmetry
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainClasses


end CatalanCore.Arith.Hybrid.ChainClasses
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
/-- The same-class cleared difference is integral in either node order. -/
theorem delta_int1_noCut (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk4 : (4:ZMod p)*k=o) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y)
    (hc : NoCut (Cut p r (Singular p o))
      (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0) :
    Int1 p (delta Fr p r xs ys z y) := by
  exact Periodic.Model.delta_int1_noCut (Periodic.lamPoleData hL hp5 hN) (by omega) hr hxN hyN z y hz hy hc hd

theorem delta_int1_distinct (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk4 : (4:ZMod p)*k=o) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y)
    (hc : NoCut (Cut p r (Singular p o))
      (min (xs z:ℤ) (ys y)) (max (xs z:ℤ) (ys y)))
    (hne : xs z≠ys y) : Int1 p (delta Fr p r xs ys z y) := by
  exact Periodic.Model.delta_int1_distinct (Periodic.lamPoleData hL hp5 hN) (by omega) hr hxN hyN z y hz hy hc hne

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_int1_noCut
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_int1_distinct
