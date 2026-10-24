module

public import CatalanFrames.Thirds.ContentHyb
public import CatalanCore.Rect.MinorContent

@[expose] public section

/-!
# `HasContent` of the common-minor family of the thirds frames (M7)

Generic in the frame (`ThirdsData`), in the deletion budget `d` and in any admissible predicate
contained in the window `r ≤ 8m ≤ r + 9`.  The content constant is `32313/10000`
(`Clow + Chigh = 3.2312582… ≤ 3.2313`).
-/

open Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen

namespace CatalanFrames.Thirds

/-- The admissible window of the thirds family: `r ≤ 8m ≤ r + 9`. -/
def ThirdsAdm (r m : ℕ) : Prop := r ≤ 8 * m ∧ 8 * m ≤ r + 9

theorem thirds_hasContent {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e)
    (hbands : (Band (thirdsInst T) 6 1 3 1 1 2 ∧ Band (thirdsInst T) 6 5 3 2 1 2) ∨
      (Band (thirdsInst T) 6 1 3 2 1 2 ∧ Band (thirdsInst T) 6 5 3 1 1 2))
    (A : ℕ → ℕ → Prop) (hA : ∀ r m, A r m → ThirdsAdm r m) (d : ℕ) :
    HasContent (commonMinorFam Fr A d) (32313 / 10000) := by
  haveI : ∀ r m, ((fun _ _ => thirdsInst T : ℕ → ℕ → HybInst Fr) r m).DiagOK r m :=
    fun r m => thirdsInst_diagOK T r m
  refine hasContent_commonMinorFam (fun _ _ => thirdsInst T) A d (32313 / 10000) ?_
  intro ε hε
  filter_upwards [thirds_log_content_of T hbands hε] with r h m hm
  exact h m (hA r m hm).1 (hA r m hm).2

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.thirds_hasContent
