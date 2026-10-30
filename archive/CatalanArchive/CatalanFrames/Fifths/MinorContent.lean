module
public import CatalanFrames.Fifths.ContentHyb
public import CatalanFrames.Fifths.Admissible
public import CatalanCore.Rect.MinorContent
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.Fifths
/-- The exact fifths content price for any common-minor family inside the admissible window. -/
theorem fifths_hasContent {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u)
    (A : ℕ → ℕ → Prop) (hA : ∀ r m,A r m → FifthsAdm r m) (d : ℕ) :
    HasContent (commonMinorFam Fr A d) (fifthsPrice : ℝ) := by
  haveI : ∀ r m,((fun _ _ => fifthsInst T : ℕ → ℕ → HybInst Fr) r m).DiagOK r m :=
    fun r m => fifthsInst_diagOK T r m
  refine hasContent_commonMinorFam (fun _ _ => fifthsInst T) A d (fifthsPrice : ℝ) ?_
  intro ε hε
  filter_upwards [fifths_log_content T hε] with r h m hm
  exact h m (hA r m hm).1 (hA r m hm).2
theorem fifths1_hasContent :
    HasContent (commonMinorFam fifths1 FifthsAdm 1) (fifthsPrice : ℝ) :=
  fifths_hasContent fifths1_data FifthsAdm (fun _ _ h => h) 1
theorem fifths2_hasContent :
    HasContent (commonMinorFam fifths2 FifthsAdm 1) (fifthsPrice : ℝ) :=
  fifths_hasContent fifths2_data FifthsAdm (fun _ _ h => h) 1
theorem fifths3_hasContent :
    HasContent (commonMinorFam fifths3 FifthsAdm 1) (fifthsPrice : ℝ) :=
  fifths_hasContent fifths3_data FifthsAdm (fun _ _ h => h) 1
theorem fifths4_hasContent :
    HasContent (commonMinorFam fifths4 FifthsAdm 1) (fifthsPrice : ℝ) :=
  fifths_hasContent fifths4_data FifthsAdm (fun _ _ h => h) 1
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths1_hasContent
#print axioms CatalanFrames.Fifths.fifths2_hasContent
#print axioms CatalanFrames.Fifths.fifths3_hasContent
#print axioms CatalanFrames.Fifths.fifths4_hasContent
