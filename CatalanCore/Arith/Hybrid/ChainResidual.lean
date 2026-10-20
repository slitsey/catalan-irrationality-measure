module
public import CatalanCore.Arith.Hybrid.ChainPartnerBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}
lemma full_B_apply (i : Fin r) (y : Z) :
    (full Fr p r xs ys).toBlocks₁₂ i y=C (Fr.Mn i.val (ys y)) := by
  change rescaleHom p 2 (C (Fr.Mn i.val (ys y))) = _
  simp [rescaleHom]
lemma full_C_apply (z : Z) (i : Fin r) :
    (full Fr p r xs ys).toBlocks₂₁ z i=C (Fr.Mn (xs z) i.val) := by
  change rescaleHom p 2 (C (Fr.Mn (xs z) i.val)) = _
  simp [rescaleHom]
lemma full_A_apply_ne (i j : Fin r) (hij : i≠j) :
    (full Fr p r xs ys).toBlocks₁₁ i j=C (Fr.Mn i.val j.val) := by
  change rescaleHom p 2 (C (Fr.Mn i.val j.val)+X*(if i=j then 1 else 0)) = _
  simp [hij,rescaleHom]
lemma Q_eq_smul : Q Fr p r xs ys=C ((p:ℚ)^2) • (full Fr p r xs ys).toBlocks₁₁ := by
  ext i j
  simp only [Q, Atil_apply, pow_one, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm _ (C (p:ℚ)), ← mul_assoc, ← map_mul]
  simp [pow_two]
lemma Sr_solve : Sr Fr p r xs ys * blockProject (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₁₁ =
    h Fr p r xs ys • blockRect (fun z=>xs z%p) (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₂₁ := by
  have hp0 : C ((p:ℚ)^2)≠(0:ℚ[X]) := by simp [(Fact.out : p.Prime).ne_zero]
  simpa only [Sr, h, Q0, Q_eq_smul, C2] using projected_row_solve
    (fun i:Fin r=>i.val%p) (fun z=>xs z%p) (C ((p:ℚ)^2)) hp0
    (full Fr p r xs ys).toBlocks₁₁ (full Fr p r xs ys).toBlocks₂₁
lemma Sc_solve : blockProject (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₁₁ * Sc Fr p r xs ys =
    h Fr p r xs ys • blockRect (fun i:Fin r=>i.val%p) (fun z=>ys z%p) (full Fr p r xs ys).toBlocks₁₂ := by
  have hp0 : C ((p:ℚ)^2)≠(0:ℚ[X]) := by simp [(Fact.out : p.Prime).ne_zero]
  simpa only [Sc, h, Q0, Q_eq_smul, B2] using projected_col_solve
    (fun i:Fin r=>i.val%p) (fun z=>ys z%p) (C ((p:ℚ)^2)) hp0
    (full Fr p r xs ys).toBlocks₁₁ (full Fr p r xs ys).toBlocks₁₂
lemma Mn_cross_gle (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    {k A B : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p)) (hA : A<N) (hB : B<N)
    (hd : A%p≠B%p) : GLE p 1 (C (Fr.Mn A B)) := by
  apply GLE.C_iff.mpr
  simpa only [pow_one] using (show (p:ℚ)*Fr.Mn A B ∈ Basic.LocRing p from (good_Mn_cross_uniform hL hp hN hk hA hB (by
    intro H
    apply hd
    exact (ZMod.natCast_eq_natCast_iff' A B p).mp (sub_eq_zero.mp H).symm)).mem)
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.Sr_solve
