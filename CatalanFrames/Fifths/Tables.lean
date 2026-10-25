module
public import CatalanFrames.HybCommon.Pieces
@[expose] public section
open CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
namespace CatalanFrames.Fifths
/-! Exact table data. Uniform Covers obligations remain separate and are not assumed proved. -/
noncomputable def tail1 : List Piece :=
  [mkPiece 1 4 15 16 17 (0) 48 8,
   mkPiece 15 16 1 1 65 (-24) 120 20,
   mkPiece 1 1 5 4 35 (-14) 60 10,
   mkPiece 5 4 5 1 45 (-8) 120 20,
   mkPiece 5 1 25 4 25 (-4) 120 20,
   mkPiece 25 4 7 1 0 (0) 6 1]
lemma tail1_chain : Chain (1/4) tail1 := by simp only [tail1,Chain,mkPiece];norm_num
lemma tail1_end : lastEnd (1/4) tail1 = 7 := by simp [tail1,lastEnd,mkPiece]
noncomputable def table1 : List Piece := ld1++tail1
lemma table1_chain : Chain (1/68) table1 := by unfold table1;rw [chain_append,ld1_end];exact ⟨ld1_chain,tail1_chain⟩
lemma table1_end : lastEnd (1/68) table1 = 7 := by unfold table1;rw [lastEnd_append,ld1_end,tail1_end]
noncomputable def tail2 : List Piece :=
  [mkPiece 1 4 45 56 17 (0) 48 8,
   mkPiece 45 56 25 28 65 (-28) 120 20,
   mkPiece 25 28 1 1 45 (-28) 60 10,
   mkPiece 1 1 5 4 35 (-18) 60 10,
   mkPiece 5 4 5 2 45 (-16) 120 20,
   mkPiece 5 2 25 8 25 (-8) 120 20,
   mkPiece 25 8 7 1 0 (0) 6 1]
lemma tail2_chain : Chain (1/4) tail2 := by simp only [tail2,Chain,mkPiece];norm_num
lemma tail2_end : lastEnd (1/4) tail2 = 7 := by simp [tail2,lastEnd,mkPiece]
noncomputable def table2 : List Piece := ld1++tail2
lemma table2_chain : Chain (1/68) table2 := by unfold table2;rw [chain_append,ld1_end];exact ⟨ld1_chain,tail2_chain⟩
lemma table2_end : lastEnd (1/68) table2 = 7 := by unfold table2;rw [lastEnd_append,ld1_end,tail2_end]
noncomputable def tail3 : List Piece :=
  [mkPiece 1 4 45 64 17 (0) 48 8,
   mkPiece 45 64 25 32 65 (-32) 120 20,
   mkPiece 25 32 1 1 45 (-32) 60 10,
   mkPiece 1 1 5 4 35 (-22) 60 10,
   mkPiece 5 4 5 3 45 (-24) 120 20,
   mkPiece 5 3 25 12 25 (-12) 120 20,
   mkPiece 25 12 7 1 0 (0) 6 1]
lemma tail3_chain : Chain (1/4) tail3 := by simp only [tail3,Chain,mkPiece];norm_num
lemma tail3_end : lastEnd (1/4) tail3 = 7 := by simp [tail3,lastEnd,mkPiece]
noncomputable def table3 : List Piece := ld1++tail3
lemma table3_chain : Chain (1/68) table3 := by unfold table3;rw [chain_append,ld1_end];exact ⟨ld1_chain,tail3_chain⟩
lemma table3_end : lastEnd (1/68) table3 = 7 := by unfold table3;rw [lastEnd_append,ld1_end,tail3_end]
noncomputable def tail4 : List Piece :=
  [mkPiece 1 4 5 8 17 (0) 48 8,
   mkPiece 5 8 25 36 65 (-36) 120 20,
   mkPiece 25 36 1 1 45 (-36) 60 10,
   mkPiece 1 1 5 4 35 (-26) 60 10,
   mkPiece 5 4 25 16 25 (-16) 120 20,
   mkPiece 25 16 7 1 0 (0) 6 1]
lemma tail4_chain : Chain (1/4) tail4 := by simp only [tail4,Chain,mkPiece];norm_num
lemma tail4_end : lastEnd (1/4) tail4 = 7 := by simp [tail4,lastEnd,mkPiece]
noncomputable def table4 : List Piece := ld1++tail4
lemma table4_chain : Chain (1/68) table4 := by unfold table4;rw [chain_append,ld1_end];exact ⟨ld1_chain,tail4_chain⟩
lemma table4_end : lastEnd (1/68) table4 = 7 := by unfold table4;rw [lastEnd_append,ld1_end,tail4_end]
def fifthsPrice : ℚ := 195975263767/53321748480
theorem finite_price_eq : ((9/4*(1/68)+listInt table1)+(9/4*(1/68)+listInt table2)+(9/4*(1/68)+listInt table3)+(9/4*(1/68)+listInt table4))/4 = (fifthsPrice : ℝ) := by
  simp only [fifthsPrice,table1,table2,table3,table4,listInt_append,ld1,tail1,tail2,tail3,tail4,listInt,Piece.int,mkPiece]
  norm_num
theorem fifths_exponent_check : (18386549/2500000 : ℚ)/(390557/100000-fifthsPrice) ≤ 639/20 := by norm_num [fifthsPrice]
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.finite_price_eq
#print axioms CatalanFrames.Fifths.fifths_exponent_check
