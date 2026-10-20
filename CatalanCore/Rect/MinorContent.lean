module

public import CatalanCore.Rect.CommonMinor
public import CatalanCore.Rect.PairBridge
public import CatalanCore.Arith.Hybrid.PrincipalMinor

@[expose] public section

/-! # Content of bounded common-node deletions

No cancellation of the original determinant is used: its entrywise tropical
denominator bound also clears every principal common-node restriction.
-/

open Finset Polynomial Matrix Filter
open CatalanCore.Arith.Hybrid

namespace CatalanCore.Rect

def commonMinorEmbedding (r m : ℕ) (s : Finset (Fin r)) :
    (s ⊕ Fin m) ↪ (Fin r ⊕ Fin m) where
  toFun := Sum.map Subtype.val id
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [Sum.map, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, id_eq] at h
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    · cases h
    · cases h
    · exact congrArg Sum.inr (Sum.inr.inj h)

theorem commonMinorPoly_gle {Fr : Frame} (I : HybInst Fr) (p : ℕ) [Fact p.Prime]
    (r m : ℕ) [I.DiagOK r m] (s : Finset (Fin r)) :
    GLE p (tropExp I r m p) (commonMinorPoly Fr r m s) := by
  let e := commonMinorEmbedding r m s
  have h : GLE p (tropVal (fun a b : s ⊕ Fin m => hybW I r m p (e a) (e b)))
      (commonMinorPoly Fr r m s) := by
    unfold commonMinorPoly
    apply det_gle
    intro a b
    have he := fullEntry_gle I p r m (e a) (e b)
    rcases a with a | a <;> rcases b with b | b <;>
      simpa [e, commonMinorEmbedding, FullN, Blk, blkA, blkB, blkC, blkD,
        Matrix.fromBlocks, Matrix.one_apply, Frame.hybRow, Frame.hybCol, add_comm] using he
  exact h.mono (tropVal_embedding_le (hybW I r m p) e)

theorem commonMinorPoly_integral {Fr : Frame} (I : HybInst Fr) (r m : ℕ)
    [I.DiagOK r m] (s : Finset (Fin r)) (j : ℕ) :
    ∃ z : ℤ, (Dhyb I r m : ℚ) * (commonMinorPoly Fr r m s).coeff j = z :=
  Dhyb_integral_of_gle I r m _ (fun p => commonMinorPoly_gle I p r m s) j

theorem hasContent_commonMinorFam {Fr : Frame} (I : ℕ → ℕ → HybInst Fr)
    [∀ r m, (I r m).DiagOK r m] (A : ℕ → ℕ → Prop) (d : ℕ) (Λ : ℝ)
    (hlog : ∀ ε > 0, ∀ᶠ r in atTop, ∀ m, A r m →
      Real.log (Dhyb (I r m) r m) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    HasContent (commonMinorFam Fr A d) Λ := by
  refine ⟨fun i => Dhyb (I i.1 i.2.1) i.1 i.2.1,
    fun i => Dhyb_pos _ _ _, ?_, ?_⟩
  · intro i _ p q hq
    exact int_clear _ i.1 (natDegree_commonMinorPoly_le Fr i.1 i.2.1 i.2.2) _
      (commonMinorPoly_integral (I i.1 i.2.1) i.1 i.2.1 i.2.2) p q hq
  · intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlog ε hε)
    exact ⟨N, fun i hi hr => hN i.1 hr i.2.1 hi.1⟩

end CatalanCore.Rect
