module

public import CatalanCore.Arith.Hybrid.LemmaE.LabelE2
public import CatalanCore.Arith.Hybrid.LemmaE.PairRank
public import CatalanCore.Arith.Hybrid.DefBSchur

@[expose] public section

/-!
# Lemma E, class `p ≡ 1 (4)`, at a prime `p < r`: the `GLE` bound from the rank principle

`gleAt_E` (dual form): for a λ-like frame, `p` with the setting `ESetup` and the scalar Schur
complement hypothesis `hUU` on the unpaired block `U = [r-p, k)`,

  `GLE p (∑u + ∑v - m) (fullPoly)`,   `∑u + ∑v = 2 (2r - p - k) + 4m` (`wE_sum`).

Proof: the reduction `BE` of `p^{u+v} Full` is `fromBlocks T Up Wp Mp` over `(U ⊕ X) ⊕ P`
and has rank `≤ |P| + |U| = r` (`rank_E_abs`); `gle_full_of_rank` converts the corank `m`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section Equiv

variable {r : ℕ} (m : ℕ)

/-- Reindexing `Fin r ⊕ Fin m ≃ (A ⊕ Fin m) ⊕ B` for a predicate `q`. -/
def eE (r m : ℕ) (q : Fin r → Prop) [DecidablePred q] :
    Fin r ⊕ Fin m ≃ ({c : Fin r // q c} ⊕ Fin m) ⊕ {c : Fin r // ¬ q c} :=
  (((Equiv.sumCompl q).symm).sumCongr (Equiv.refl (Fin m))).trans
    ((Equiv.sumAssoc _ _ _).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans (Equiv.sumAssoc _ _ _).symm))

variable (q : Fin r → Prop) [DecidablePred q]

lemma eE_inl_pos {c : Fin r} (h : q c) :
    eE r m q (Sum.inl c) = Sum.inl (Sum.inl ⟨c, h⟩) := by
  have h1 : (Equiv.sumCompl q).symm c = Sum.inl ⟨c, h⟩ :=
    @Equiv.sumCompl_symm_apply_of_pos _ q _ c h
  simp [eE, h1]

lemma eE_inl_neg {c : Fin r} (h : ¬ q c) :
    eE r m q (Sum.inl c) = Sum.inr ⟨c, h⟩ := by
  have h1 : (Equiv.sumCompl q).symm c = Sum.inr ⟨c, h⟩ :=
    @Equiv.sumCompl_symm_apply_of_neg _ q _ c h
  simp [eE, h1]

lemma eE_inr (i : Fin m) : eE r m q (Sum.inr i) = Sum.inl (Sum.inr i) := by
  simp [eE]

lemma eE_symm_ll (u : {c : Fin r // q c}) :
    (eE r m q).symm (Sum.inl (Sum.inl u)) = Sum.inl u.1 := by
  rw [Equiv.symm_apply_eq, eE_inl_pos m q u.2]

lemma eE_symm_lr (x : Fin m) : (eE r m q).symm (Sum.inl (Sum.inr x)) = Sum.inr x := by
  rw [Equiv.symm_apply_eq, eE_inr]

lemma eE_symm_r (c : {c : Fin r // ¬ q c}) :
    (eE r m q).symm (Sum.inr c) = Sum.inl c.1 := by
  rw [Equiv.symm_apply_eq, eE_inl_neg m q c.2]

end Equiv

section Main

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m j k : ℕ}

lemma BE_ll (c c' : Fin r) : BE p j r m k (Sum.inl c) (Sum.inl c') =
    rfC p (TE p j r k c c') + (if c = c' ∧ wE p r k (c : ℕ) = 0 then rfX p else 0) := by
  simp [BE, Frame.hybRow, Frame.hybCol]

lemma BE_lz (c : Fin r) (y : Fin m) : BE p j r m k (Sum.inl c) (Sum.inr y) =
    rfC p (TE p j r k c (r + 2 * (y : ℕ) + 1)) := by
  simp [BE, Frame.hybRow, Frame.hybCol]

lemma BE_zl (x : Fin m) (c : Fin r) : BE p j r m k (Sum.inr x) (Sum.inl c) =
    rfC p (TE p j r k (r + 2 * (x : ℕ)) c) := by
  simp [BE, Frame.hybRow, Frame.hybCol]

lemma BE_zz (x y : Fin m) : BE p j r m k (Sum.inr x) (Sum.inr y) =
    rfC p (TE p j r k (r + 2 * (x : ℕ)) (r + 2 * (y : ℕ) + 1)) := by
  simp [BE, Frame.hybRow, Frame.hybCol]

lemma card_UP (p r k : ℕ) : Fintype.card (UE p r k) + Fintype.card (PE p r k) = r := by
  have := Fintype.card_congr (Equiv.sumCompl (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k))
  rw [Fintype.card_sum, Fintype.card_fin] at this
  exact this

lemma hs0_ne (c : ZMod p) : rfX p + rfC p c ≠ 0 := by
  unfold rfX rfC
  rw [← map_add]
  exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))).2
    (Polynomial.X_add_C_ne_zero _)

end Main

end CatalanCore.Arith.Hybrid
