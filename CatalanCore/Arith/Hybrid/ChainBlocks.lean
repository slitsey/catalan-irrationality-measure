module
public import CatalanCore.Arith.Hybrid.ChainEntries
public import CatalanCore.Arith.Hybrid.ChainModelBounds
public import CatalanCore.Arith.Hybrid.LemmaE.ChainSolve
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainClasses
open LemmaE
variable {p : ℕ} [Fact p.Prime]

lemma chainNode_mod {r z : ℕ} (i : ChainIndex p r z) :
    (chainNode i).val % p = z % p :=
  Nat.modEq_iff_dvd.mpr (chainNode_dvd i)

lemma chain_image_of_mod {r z : ℕ} (hz : r≤z) (a : Fin r)
    (ha : a.val%p=z%p) : a∈Set.range (@chainNode p r z) := by
  obtain ⟨i,hi⟩ := exists_chainNode (Fact.out : p.Prime).pos hz a (Nat.modEq_iff_dvd.mp ha)
  exact ⟨i,hi⟩

noncomputable def chainMatrix (Fr : Frame) (r z : ℕ) :
    Matrix (ChainIndex p r z) (ChainIndex p r z) ℚ[X] :=
  (Matrix.of (fun i j : ChainIndex p r z => (p:ℚ)^2*Fr.Mn (chainNode i).val (chainNode j).val)).map (C : ℚ →+* ℚ[X]) + (X : ℚ[X]) • 1

lemma chainMatrix_primitive {Fr : Frame} {o N r z : ℕ}
    (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    gn p (chainMatrix (p:=p) Fr r z).det=1 := by
  apply prim_det_shift
  intro i j
  exact Mn_square_mem hL hp5 hN ((chainNode i).isLt.trans_le hr) ((chainNode j).isLt.trans_le hr)

lemma Q0_chain {Fr : Frame} {r z : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (xs ys : Z→ℕ) :
    (ChainModel.Q0 Fr p r xs ys).submatrix (@chainNode p r z) chainNode =
      chainMatrix (p:=p) Fr r z := by
  ext i j
  rw [Matrix.submatrix_apply, ChainModel.Q0_apply_same _ _ (by rw [chainNode_mod,chainNode_mod]), ChainModel.Q_apply]
  simp only [chainMatrix, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  simp only [(chainNode_injective (Fact.out : p.Prime).pos).eq_iff]

lemma chainMatrix_cng {Fr : Frame} {o N r z w : ℕ}
    (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hzw : z≤w) (h : NoCut (Cut p r (Singular p o)) z w)
    (i j : ChainIndex p r z) :
    Cng p (chainMatrix (p:=p) Fr r z i j)
      (chainMatrix (p:=p) Fr r w (chainTransport hzw h i) (chainTransport hzw h j)) := by
  have H := square_chain_cng hL hp5 hN hr hzw h i j
  simpa only [chainMatrix, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Equiv.apply_eq_iff_eq] using
    H.add (Cng.refl (X*(if i=j then 1 else 0)))

end CatalanCore.Arith.Hybrid.ChainClasses
#print axioms CatalanCore.Arith.Hybrid.ChainClasses.chainMatrix_cng
