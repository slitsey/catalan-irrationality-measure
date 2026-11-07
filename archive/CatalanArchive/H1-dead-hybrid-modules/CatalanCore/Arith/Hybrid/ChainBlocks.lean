module
public import CatalanCore.Arith.Hybrid.PeriodicPartners
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.ChainEntries
public import CatalanCore.Arith.Hybrid.ChainModelBounds
public import CatalanCore.Arith.Hybrid.LemmaE.ChainSolve
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainClasses
open LemmaE
variable {p : ℕ} [Fact p.Prime]




lemma chainMatrix_primitive {Fr : Frame} {o N r z : ℕ}
    (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    gn p (chainMatrix (p:=p) Fr r z).det=1 := by
  exact Periodic.Model.chainMatrix_primitive (Periodic.lamPoleData hL hp5 hN) (by omega) hr

lemma chainMatrix_cng {Fr : Frame} {o N r z w : ℕ}
    (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hzw : z≤w) (h : NoCut (Cut p r (Singular p o)) z w)
    (i j : ChainIndex p r z) :
    Cng p (chainMatrix (p:=p) Fr r z i j)
      (chainMatrix (p:=p) Fr r w (chainTransport hzw h i) (chainTransport hzw h j)) := by
  exact Periodic.Model.chainMatrix_cng (Periodic.lamPoleData hL hp5 hN) (by omega) hr hzw h i j

end CatalanCore.Arith.Hybrid.ChainClasses
#print axioms CatalanCore.Arith.Hybrid.ChainClasses.chainMatrix_cng
