module
public import CatalanCore.Arith.Hybrid.PeriodicWeighted
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.ChainResidualBounds
public import CatalanCore.Arith.Hybrid.LemmaE.ModelWeighted
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}


lemma delta_gle_one_at (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p))
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) (z y : Z) (hxy : xs z%p≠ys y%p) :
    GLE p 1 (delta Fr p r xs ys z y) := by
  exact Periodic.Model.delta_gle_one_at (Periodic.lamPoleData hL hp hN) (by omega) hr hx hy z y hxy

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_gle_one_at
