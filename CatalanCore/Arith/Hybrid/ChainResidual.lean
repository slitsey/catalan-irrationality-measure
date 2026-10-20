module
public import CatalanCore.Arith.Hybrid.PeriodicModelBounds
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.ChainPartnerBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}






lemma Mn_cross_gle (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    {k A B : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hA : A<N) (hB : B<N)
    (hd : A%p≠B%p) : GLE p 1 (C (Fr.Mn A B)) := by
  exact Periodic.Model.Mn_cross_gle (Periodic.lamPoleData hL hp hN) hA hB hd

end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.Sr_solve
