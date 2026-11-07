module
public import CatalanCore.Arith.Hybrid.PeriodicPartners
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.ChainBlocks
public import CatalanCore.Arith.Hybrid.ChainPartnerBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}

lemma Sr_chain_solve (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (z : Z) (hz : r≤xs z) (i : ChainIndex p r (xs z)) :
    ((fun j : ChainIndex p r (xs z) => Sr Fr p r xs ys z (chainNode j)) ᵥ*
      chainMatrix (p:=p) Fr r (xs z)) i =
      h Fr p r xs ys * C2 Fr p r xs ys z (chainNode i) := by
  exact Periodic.Model.Sr_chain_solve (Periodic.lamPoleData hL hp5 hN) (by omega) hr z hz i

lemma Sc_chain_solve (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (y : Z) (hy : r≤ys y) (i : ChainIndex p r (ys y)) :
    (chainMatrix (p:=p) Fr r (ys y) *ᵥ
      (fun j : ChainIndex p r (ys y) => Sc Fr p r xs ys (chainNode j) y)) i =
      h Fr p r xs ys * B2 Fr p r xs ys (chainNode i) y := by
  exact Periodic.Model.Sc_chain_solve (Periodic.lamPoleData hL hp5 hN) (by omega) hr y hy i

/-- Cleared model partners agree along corresponding chains on any cut-free interval. -/
theorem partners_chain_cng (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r (Singular p o)) (xs z) (ys y))
    (i : ChainIndex p r (xs z)) :
    Cng p (Sr Fr p r xs ys z (chainNode i))
      (Sc Fr p r xs ys (chainNode (chainTransport hzy hc i)) y) := by
  exact Periodic.Model.partners_chain_cng (Periodic.lamPoleData hL hp5 hN) (by omega) hr hxN hyN z y hz hy hzy hc i

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.partners_chain_cng
