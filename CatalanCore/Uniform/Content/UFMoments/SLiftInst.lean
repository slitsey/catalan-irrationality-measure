module

public import CatalanCore.Uniform.Content.UFMoments.JType

@[expose] public section

/-!
# UF moments: the scaled lift satisfies the node hypotheses

For `A = sLift c xs ys hint` (from `PoleData`):

* `sLift_core_rel`, `sLift_row_rel`, `sLift_col_rel`: the Loewner commutator relations of the core
  block, a border row and a border column (all in the node form of `NodeExp`);
* `sLift_core_symm`: the core block is symmetric;
* `sLift_rowA`, `sLift_rowB`, `sLift_colA`, `sLift_colB`: the four moments in `GaussLoc p` in the
  inverse form required by `node_bridge` / `jtype_node`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem frame_Mn_symm (Fr : Frame) (a b : ℕ) : Fr.Mn a b = Fr.Mn b a := by
  by_cases h : a = b
  · rw [h]
  · unfold Frame.Mn
    rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

section
variable (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
  (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)

theorem sLift_core_rel : ∀ a b, a ≠ b →
    nL p Fr * (nd p (c b) - nd p (c a)) *
        (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ a b =
      PF p Fr (c b) - PF p Fr (c a) := by
  intro a b hab
  have e : (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ a b =
      Polynomial.C (sConst c xs ys (hint_of_poleData D hN hc hx hy) (Sum.inl a) (Sum.inl b)) := by
    simp [sLift, Matrix.toBlocks₁₁, Matrix.one_apply_ne hab]
  rw [e]
  exact const_commutator D (hc a) (hc b) _

theorem sLift_row_rel (z : κ) : ∀ a,
    nL p Fr * (nd p (c a) - nd p (xs z)) *
        (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₂₁ z a =
      PF p Fr (c a) - PF p Fr (xs z) := by
  intro a
  have e : (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₂₁ z a =
      Polynomial.C (sConst c xs ys (hint_of_poleData D hN hc hx hy) (Sum.inr z) (Sum.inl a)) := by
    simp [sLift, Matrix.toBlocks₂₁]
  rw [e]
  exact const_commutator D (hx z) (hc a) _

theorem sLift_col_rel (y : κ) : ∀ a,
    nL p Fr * (nd p (c a) - nd p (ys y)) *
        (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₂ a y =
      PF p Fr (c a) - PF p Fr (ys y) := by
  intro a
  have e : (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₂ a y =
      Polynomial.C (sConst c xs ys (hint_of_poleData D hN hc hx hy) (Sum.inl a) (Sum.inr y)) := by
    simp [sLift, Matrix.toBlocks₁₂]
  rw [e]
  have h : nL p Fr * (nd p (ys y) - nd p (c a)) *
      Polynomial.C (sConst c xs ys (hint_of_poleData D hN hc hx hy) (Sum.inl a) (Sum.inr y)) =
      PF p Fr (ys y) - PF p Fr (c a) := const_commutator D (hc a) (hy y) _
  linear_combination (-1 : (LocRing p)[X]) * h

theorem sLift_core_symm :
    (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ᵀ =
      (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ := by
  ext a b
  by_cases hab : a = b
  · rw [hab]; rfl
  · simp only [Matrix.transpose_apply, sLift, Matrix.toBlocks₁₁, Matrix.of_apply,
      Matrix.add_apply, Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply,
      Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab), smul_zero, add_zero, sConst]
    simp only [rowNode, colNode, Sum.elim_inl, frame_Mn_symm Fr (c b) (c a)]

end

end CatalanCore.Uniform.Content.UFMoments
