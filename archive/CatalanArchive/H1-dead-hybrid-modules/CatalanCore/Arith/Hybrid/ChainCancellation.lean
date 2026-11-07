module
public import CatalanCore.Arith.Hybrid.PeriodicCancellation
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainPartners
public import CatalanCore.Arith.Hybrid.ChainLoewner
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}

/-- Actual-frame first-order cancellation along an arbitrary cut-free pair of chains. -/
theorem restricted_delta_int1 (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk4 : (4:ZMod p)*k=o) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r (Singular p o)) (xs z) (ys y))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0) :
    let e := chainTransport hzy hc
    let sr := fun i : ChainIndex p r (xs z) => Sr Fr p r xs ys z (chainNode i)
    let sc := fun i : ChainIndex p r (xs z) => Sc Fr p r xs ys (chainNode (e i)) y
    Int1 p ((h Fr p r xs ys)^2*C (Fr.Mn (xs z) (ys y))-
      h Fr p r xs ys*(∑i,sr i*C (Fr.Mn (chainNode i).val (ys y)))-
      h Fr p r xs ys*(∑i,C (Fr.Mn (xs z) (chainNode (e i)).val)*sc i)+
      ∑i,∑j,sr i*C (Fr.Mn (chainNode i).val (chainNode (e j)).val)*sc j) := by
  exact Periodic.Model.restricted_delta_int1 (Periodic.lamPoleData hL hp5 hN) (by omega) hr hxN hyN z y hz hy hzy hc hd

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.restricted_delta_int1
