module
public import CatalanCore.Arith.Hybrid.D1Exact
public import CatalanCore.Arith.Hybrid.PieceTools
@[expose] public section
open Finset
namespace CatalanCore.Arith.Hybrid

/-- Four affine D1 ranges below a quarter border; independent of frame and level. -/
noncomputable def quarterD1Pieces : List Piece :=
  [mkPiece 1 12 1 10 11 (-12) 100 4,
   mkPiece 1 10 1 8 9 8 100 4,
   mkPiece 1 8 1 6 11 (-8) 100 4,
   mkPiece 1 6 1 4 9 4 100 4]

lemma quarterD1_chain : Chain (1/12) quarterD1Pieces := by
  simp only [quarterD1Pieces, Chain, mkPiece]
  norm_num
lemma quarterD1_end : lastEnd (1/12) quarterD1Pieces = (1/4 : ℝ) := by
  simp [quarterD1Pieces, lastEnd, mkPiece]
lemma quarterD1_integral :
    (5/2 : ℝ)*(1/12)+listInt quarterD1Pieces=(5/2 : ℝ)*(1/4)-1/160 := by
  simp only [quarterD1Pieces, listInt, Piece.int, mkPiece]
  norm_num

/-- Exact nearest-multiple arithmetic supplies every new cover with bounded rounding slack. -/
theorem quarterD1_covers {M : ℕ} {c : ZMod M} {r m : ℕ} {w : ℕ → ℕ}
    (hm1 : r ≤ 4*m) (hm2 : 4*m ≤ r+3)
    (hw : ∀ p : ℕ, p.Prime → (p : ZMod M)=c →
      w p ≤ 2*r+2*m-min (m%p) (p-m%p)) :
    ∀ P ∈ quarterD1Pieces, Covers c (fun p => (w p : ℝ)) r P := by
  intro P hP
  simp only [quarterD1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · intro p hlo hhi hp hc
    rw [floor_mk_s] at hlo
    rw [floor_mk_t] at hhi
    have hb := hw p hp hc
    have hd := dist_ge p m 2 hp.pos (by omega)
    generalize m%p=s0 at hb hd
    exact real_of_int_bound 4 11 (-12) 100 (by norm_num) (by omega)
  · intro p hlo hhi hp hc
    rw [floor_mk_s] at hlo
    rw [floor_mk_t] at hhi
    have hb := hw p hp hc
    have hd := dist_ge p m 2 hp.pos (by omega)
    generalize m%p=s0 at hb hd
    exact real_of_int_bound 4 9 8 100 (by norm_num) (by omega)
  · intro p hlo hhi hp hc
    rw [floor_mk_s] at hlo
    rw [floor_mk_t] at hhi
    have hb := hw p hp hc
    have hd := dist_ge p m 1 hp.pos (by omega)
    generalize m%p=s0 at hb hd
    exact real_of_int_bound 4 11 (-8) 100 (by norm_num) (by omega)
  · intro p hlo hhi hp hc
    rw [floor_mk_s] at hlo
    rw [floor_mk_t] at hhi
    have hb := hw p hp hc
    have hd := dist_ge p m 1 hp.pos (by omega)
    generalize m%p=s0 at hb hd
    exact real_of_int_bound 4 9 4 100 (by norm_num) (by omega)
end CatalanCore.Arith.Hybrid
