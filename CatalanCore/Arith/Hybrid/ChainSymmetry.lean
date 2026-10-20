module
public import CatalanCore.Arith.Hybrid.ChainDeltaBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
lemma Q0_swap : Q0 Fr p r ys xs=Q0 Fr p r xs ys := rfl
lemma h_swap : h Fr p r ys xs=h Fr p r xs ys := rfl
lemma Q0_transpose : (Q0 Fr p r xs ys).transpose=Q0 Fr p r ys xs := by
  apply Matrix.ext
  intro i j
  change Q0 Fr p r xs ys j i = Q0 Fr p r ys xs i j
  by_cases hij : i.val%p=j.val%p
  · rw [Q0_apply_same j i hij.symm,Q0_apply_same i j hij,Q_apply,Q_apply]
    simp only [Mn_symm (Fr:=Fr) j.val i.val,eq_comm (a:=i) (b:=j)]
  · simp [Q0,blockProject,blockRect,hij,Ne.symm hij]
lemma Sr_swap : Sr Fr p r ys xs=(Sc Fr p r xs ys).transpose := by
  unfold Sr Sc modelRow modelCol
  rw [Matrix.transpose_mul, Matrix.adjugate_transpose,Q0_transpose]
  congr 1
  apply Matrix.ext
  intro z i
  simp only [blockRect,Matrix.transpose_apply,B2_apply,C2_apply]
  simp only [Mn_symm (Fr:=Fr) (ys z) i.val,eq_comm (a:=ys z%p) (b:=i.val%p)]
lemma Sc_swap : Sc Fr p r ys xs=(Sr Fr p r xs ys).transpose := by
  rw [Sr_swap (xs:=ys) (ys:=xs),Matrix.transpose_transpose]
lemma full_A_swap : (full Fr p r ys xs).toBlocks₁₁=(full Fr p r xs ys).toBlocks₁₁.transpose := by
  apply Matrix.ext
  intro i j
  change rescaleHom p 2 (C (Fr.Mn i.val j.val)+X*(if i=j then 1 else 0)) =
    rescaleHom p 2 (C (Fr.Mn j.val i.val)+X*(if j=i then 1 else 0))
  simp only [Mn_symm (Fr:=Fr) i.val j.val,eq_comm (a:=i) (b:=j)]
lemma full_B_swap : (full Fr p r ys xs).toBlocks₁₂=(full Fr p r xs ys).toBlocks₂₁.transpose := by
  apply Matrix.ext
  intro i z
  simp only [Matrix.transpose_apply,full_B_apply,full_C_apply,Mn_symm (Fr:=Fr) i.val (xs z)]
lemma full_C_swap : (full Fr p r ys xs).toBlocks₂₁=(full Fr p r xs ys).toBlocks₁₂.transpose := by
  rw [full_B_swap (xs:=ys) (ys:=xs),Matrix.transpose_transpose]
lemma full_D_swap : (full Fr p r ys xs).toBlocks₂₂=(full Fr p r xs ys).toBlocks₂₂.transpose := by
  apply Matrix.ext
  intro z y
  simp only [Matrix.transpose_apply,full_D_apply,Mn_symm (Fr:=Fr) (ys z) (xs y)]
lemma delta_swap : delta Fr p r ys xs=(delta Fr p r xs ys).transpose := by
  unfold delta
  conv_lhs =>
    rw [h_swap (xs:=xs) (ys:=ys),Sr_swap (xs:=xs) (ys:=ys),
      Sc_swap (xs:=xs) (ys:=ys),full_A_swap (xs:=xs) (ys:=ys),
      full_B_swap (xs:=xs) (ys:=ys),full_C_swap (xs:=xs) (ys:=ys),
      full_D_swap (xs:=xs) (ys:=ys)]
  simp only [Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_smul,
    Matrix.transpose_mul,Matrix.mul_assoc]
  abel
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_swap
