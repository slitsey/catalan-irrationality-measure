module
public import CatalanCore.Arith.Hybrid.PoleModel
public import CatalanCore.Arith.Hybrid.ChainAlgebra
@[expose] public section
open Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid
open ChainClasses LemmaE
variable {p o N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- **Reduction of the scaled core to its pole model.**  For two core nodes in one residue class,
`p² Mn a b` and the exact singular model `poleScaledEntry` agree modulo `p`
(in fact modulo `p²`, `poleScaledEntry_second_order`).  First step of N1, N2, N3. -/
theorem square_entry_pole_cng (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) {a b : ℕ}
    (ha : a<N) (hb : b<N) (hc : a%p=b%p) :
    Cng p (C ((p:ℚ)^2*Fr.Mn a b)) (C (poleScaledEntry Fr p o a b)) := by
  have hNp : N<p*p := by omega
  have H := poleScaledEntry_second_order hL hp (ha.trans hNp) (hb.trans hNp) hc
  have hG : Good p ((p:ℚ)^2*Fr.Mn a b) (red p ((p:ℚ)^2*Fr.Mn a b)) :=
    good_red (Mn_square_mem hL hp hN ha hb)
  have hpx := (Good.natCast (ℓ:=p) p).mul H
  have e : (p:ℚ)*(((p:ℚ)^2*Fr.Mn a b-poleScaledEntry Fr p o a b)/p) =
      (p:ℚ)^2*Fr.Mn a b-poleScaledEntry Fr p o a b := by
    have hp0 : (p:ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    field_simp
  have hP : Good p (poleScaledEntry Fr p o a b) (red p ((p:ℚ)^2*Fr.Mn a b)) := by
    have h1 := hG.sub (hpx.congr' e)
    refine (h1.congr' (by ring)).congr ?_
    simp
  exact good_constants_cng hG hP

/-- The actual residue-chain matrix is congruent modulo `p` to `U * 1 + (pole model)`. -/
theorem chainMatrix_cng_pole (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) {r z : ℕ}
    (hr : r≤N) (i j : ChainIndex p r z) :
    Cng p (chainMatrix (p:=p) Fr r z i j)
      (C (poleScaledEntry Fr p o (chainNode i).val (chainNode j).val) +
        X*(if i=j then 1 else 0)) := by
  simp only [chainMatrix, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  refine Cng.add (square_entry_pole_cng hL hp hN ((chainNode i).isLt.trans_le hr)
    ((chainNode j).isLt.trans_le hr) (by rw [chainNode_mod, chainNode_mod])) (Cng.refl _)

#print axioms square_entry_pole_cng
#print axioms chainMatrix_cng_pole
end CatalanCore.Arith.Hybrid
