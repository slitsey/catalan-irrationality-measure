module
public import CatalanCore.Arith.Hybrid.ChainWitness
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open ChainClasses
lemma fullPoly_eq_fullN (Fr : Frame) (r m : ℕ) : Fr.fullPoly r m =
    (Rect.FullN Fr (fun i:Fin r=>i.val) (fun i:Fin m=>r+2*i.val)
      (fun j:Fin m=>r+2*j.val+1) (X:ℚ[X])).det := by
  unfold Frame.fullPoly
  congr 1
  ext a b
  rcases a with a|a <;> rcases b with b|b <;>
    simp [Rect.FullN,Rect.Blk,Rect.blkA,Rect.blkB,Rect.blkC,Rect.blkD,
      Matrix.fromBlocks,Matrix.one_apply,Frame.hybRow,Frame.hybCol,Matrix.of_apply,add_comm]
variable {p r m o k a b : ℕ} [Fact p.Prime] {Fr : Frame}
theorem witness_fullPoly_gle (hL : LamData Fr o) (hp : 5≤p)
    (hN : 4*(r+2*m)<p*p) (hk : (4:ZMod p)*k=o)
    (hcut : ∀ x y:ℕ,a≤x→x<b→a≤y→y<b→
      NoCut (Cut p r (Singular p o)) (min (x:ℤ) y) (max (x:ℤ) y)) :
    GLE p (tropVal (witnessTable p r m a b)+2*r) (Fr.fullPoly r m) := by
  rw [fullPoly_eq_fullN]
  exact witness_original_gle hL hp hN hk hcut
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.witness_fullPoly_gle
