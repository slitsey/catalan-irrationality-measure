module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic
@[expose] public section
open Finset Matrix
namespace CatalanCore.Linalg
variable {K I J C U V : Type*} [Field K]
  [Fintype I] [Fintype J] [Fintype C] [Fintype U] [Fintype V]
  [DecidableEq C]

def weightedColumns (A : Matrix U C K) (w : C→K) (s : Finset C) : Matrix U s K :=
  fun u c=>A u c.val*w c.val
def restrictedRows (B : Matrix C V K) (s : Finset C) : Matrix s V K :=
  fun c v=>B c.val v

/-- Projecting a weighted Cauchy/Gram sum leaves only its free support.
Weights at occupied residues may be arbitrary. -/
theorem weighted_projection_support
    (F : Matrix I C K) (G : Matrix C J K) (L : Matrix U I K)
    (R : Matrix J V K) (w : C→K) (s : Finset C)
    (hzero : ∀c,c∉s→w c=0 ∨ (∀u,(L*F) u c=0) ∨ (∀v,(G*R) c v=0)) :
    L*(F*Matrix.diagonal w*G)*R=
      weightedColumns (L*F) w s * restrictedRows (G*R) s := by
  have hassoc : L*(F*Matrix.diagonal w*G)*R=((L*F)*Matrix.diagonal w)*(G*R) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc]
  apply Matrix.ext
  intro u v
  change (∑c,((L*F)*Matrix.diagonal w) u c*(G*R) c v)=
    ∑c:s,(L*F) u c.val*w c.val*(G*R) c.val v
  simp_rw [Matrix.mul_diagonal]
  symm
  apply Fintype.sum_of_injective (Subtype.val : s→C) Subtype.val_injective
  · intro c hc
    have hn : c∉s := by intro h;exact hc ⟨⟨c,h⟩,rfl⟩
    rcases hzero c hn with hw|hl|hr
    · simp [hw]
    · simp [hl u]
    · simp [hr v]
  · intro c;rfl

theorem weighted_projection_rank
    (F : Matrix I C K) (G : Matrix C J K) (L : Matrix U I K)
    (R : Matrix J V K) (w : C→K) (s : Finset C)
    (hzero : ∀c,c∉s→w c=0 ∨ (∀u,(L*F) u c=0) ∨ (∀v,(G*R) c v=0)) :
    (L*(F*Matrix.diagonal w*G)*R).rank≤s.card := by
  rw [weighted_projection_support F G L R w s hzero]
  apply (Matrix.rank_mul_le_left _ _).trans
  simpa using (Matrix.rank_le_card_width (weightedColumns (L*F) w s))
end CatalanCore.Linalg
