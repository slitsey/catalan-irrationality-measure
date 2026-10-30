module
public import CatalanCore.Arith.Hybrid.ShiftChainReduce
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

open ChainClasses

/-! # Cell constancy of the source moments

Two zone nodes of one pole interval (no singular cut and no core-exit cut between them) have
the same source moments `(A, B)`: the chains correspond by translation, and the exact pole data
(entries, cumulatives) are translation invariant on a cut-free interval. -/

section Reindex
variable {p o : ℕ} [Fact p.Prime] {Fr : Frame} {ι ι' : Type} [Fintype ι] [DecidableEq ι]
  [Fintype ι'] [DecidableEq ι']

/-- The source moments only depend on the transported pole data. -/
theorem sourceAB_reindex (e : ι ≃ ι') (a : ι → ℕ) (a' : ι' → ℕ) (z z' : ℕ)
    (hQ : ∀ i j, poleScaledEntry Fr p o (a' (e i)) (a' (e j)) = poleScaledEntry Fr p o (a i) (a j))
    (hb : ∀ i, poleScaledEntry Fr p o (a' (e i)) z' = poleScaledEntry Fr p o (a i) z)
    (hL : ∀ i, poleL Fr p o (a' (e i)) = poleL Fr p o (a i))
    (hz : poleL Fr p o z' = poleL Fr p o z) :
    sourceA Fr p o a' z' = sourceA Fr p o a z ∧ sourceB Fr p o a' z' = sourceB Fr p o a z := by
  have hM : poleRed Fr p o a' = (poleRed Fr p o a).submatrix e.symm e.symm := by
    ext i j
    simp only [poleRed, Matrix.of_apply, Matrix.submatrix_apply]
    have := hQ (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at this
    rw [this]
    congr 2
    simp [e.symm.injective.eq_iff]
  have hg : ∀ i, ((poleRed Fr p o a')⁻¹ *ᵥ
      (fun i => rfC p (red p (poleScaledEntry Fr p o (a' i) z')))) (e i) =
      ((poleRed Fr p o a)⁻¹ *ᵥ
      (fun i => rfC p (red p (poleScaledEntry Fr p o (a i) z)))) i := by
    intro i
    have hv : (fun i' => rfC p (red p (poleScaledEntry Fr p o (a' i') z'))) ∘ e.symm.symm =
        fun i => rfC p (red p (poleScaledEntry Fr p o (a i) z)) :=
      funext fun i => by simp [Function.comp, hb]
    rw [hM, Matrix.inv_submatrix_equiv, Matrix.submatrix_mulVec_equiv, hv]
    simp
  constructor
  · unfold sourceA
    rw [hz]
    congr 1
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl; intro i _
    rw [hg, hL]
  · unfold sourceB
    congr 1
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl; intro i _
    rw [hg]

end Reindex

section Transport
variable {p o : ℕ} [Fact p.Prime] {Fr : Frame}

/-- **Cell constancy.**  Two zone nodes `x ≤ x'` in one cut-free interval (no singular node and
no core-exit cut in `(x, x']`) have the same source moments. -/
theorem sourceAB_chainTransport (hL : LamData Fr o) {r x x' : ℕ} (hxx : x ≤ x')
    (hnc : NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (x:ℤ) (x':ℤ)) :
    sourceA Fr p o (fun j : ChainIndex p r x' => (chainNode j).val) x' =
        sourceA Fr p o (fun j : ChainIndex p r x => (chainNode j).val) x ∧
      sourceB Fr p o (fun j : ChainIndex p r x' => (chainNode j).val) x' =
        sourceB Fr p o (fun j : ChainIndex p r x => (chainNode j).val) x := by
  set e : ChainIndex p r x ≃ ChainIndex p r x' := chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc
    with he
  have hshift : ∀ i : ChainIndex p r x, ((chainNode (e i)).val : ℤ) =
      ((chainNode i).val : ℤ) + ((x':ℤ) - x) := fun i =>
    chainNode_transport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc i
  have hperiod : ∀ t j : ℤ, Singular (p:ℤ) (o:ℤ) (t + j * p) ↔ Singular (p:ℤ) (o:ℤ) t :=
    singular_periodic _ _
  -- cut-free translates of every chain node
  have hnc_i : ∀ i : ChainIndex p r x, NoCut (Singular (p:ℤ) (o:ℤ))
      ((chainNode i).val : ℤ) ((chainNode (e i)).val : ℤ) := by
    intro i
    have H := noCut_translate (i := i.val) hperiod hnc
    have h1 : ((chainNode i).val : ℤ) = (x:ℤ) - i.val * p := chainNode_cast i
    have h2 : ((chainNode (e i)).val : ℤ) = (x':ℤ) - i.val * p := chainNode_cast (e i)
    rw [h1, h2]; exact H
  have hle : ∀ i : ChainIndex p r x, (chainNode i).val ≤ (chainNode (e i)).val := fun i => by
    have := hshift i
    have hxx' : (x:ℤ) ≤ x' := by exact_mod_cast hxx
    omega
  have hP : ∀ i : ChainIndex p r x,
      polePrefix Fr p o (chainNode i).val = polePrefix Fr p o (chainNode (e i)).val := fun i =>
    polePrefix_nocut hL (hle i) (hnc_i i)
  have hW : ∀ i : ChainIndex p r x,
      poleSquarePrefix Fr p o (chainNode i).val = poleSquarePrefix Fr p o (chainNode (e i)).val :=
    fun i => poleSquarePrefix_nocut hL (hle i) (hnc_i i)
  have h0 : NoCut (Singular (p:ℤ) (o:ℤ)) (x:ℤ) (x':ℤ) := fun t h1 h2 hs => hnc t h1 h2 (Or.inl hs)
  have hP0 : polePrefix Fr p o x = polePrefix Fr p o x' := polePrefix_nocut hL hxx h0
  have hW0 : poleSquarePrefix Fr p o x = poleSquarePrefix Fr p o x' := poleSquarePrefix_nocut hL hxx h0
  refine sourceAB_reindex e _ _ x x' ?_ ?_ ?_ ?_
  · intro i j
    symm
    apply poleScaledEntry_transport
    · have := hshift i; have := hshift j; omega
    · exact hP i
    · exact hP j
    · exact hW i
  · intro i
    symm
    apply poleScaledEntry_transport
    · have := hshift i; omega
    · exact hP i
    · exact hP0
    · exact hW i
  · intro i
    unfold poleL; rw [hP i]
  · unfold poleL; rw [hP0]

end Transport


section Const
variable {p o : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type}

/-- Constancy of the source moments over a set of nodes lying in one cut-free interval. -/
theorem sourceAB_const (hL : LamData Fr o) {r : ℕ} (S : Finset Z) (node : Z → ℕ) (hS : S.Nonempty)
    (hcell : ∀ z ∈ S, ∀ z' ∈ S, node z ≤ node z' →
      NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (node z : ℤ) (node z' : ℤ)) :
    ∃ SA SB : RatFunc (ZMod p), ∀ z ∈ S,
      sourceA Fr p o (fun j : ChainIndex p r (node z) => (chainNode j).val) (node z) = SA ∧
      sourceB Fr p o (fun j : ChainIndex p r (node z) => (chainNode j).val) (node z) = SB := by
  obtain ⟨z0, hz0⟩ := hS
  refine ⟨sourceA Fr p o (fun j : ChainIndex p r (node z0) => (chainNode j).val) (node z0),
    sourceB Fr p o (fun j : ChainIndex p r (node z0) => (chainNode j).val) (node z0), fun z hz => ?_⟩
  rcases le_total (node z0) (node z) with h | h
  · exact sourceAB_chainTransport hL h (hcell z0 hz0 z hz h)
  · have := sourceAB_chainTransport hL h (hcell z hz z0 hz0 h)
    exact ⟨this.1.symm, this.2.symm⟩
end Const

#print axioms sourceAB_const
end CatalanCore.Arith.Hybrid
