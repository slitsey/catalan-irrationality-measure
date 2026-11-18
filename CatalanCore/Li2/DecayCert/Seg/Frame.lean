module
public import CatalanCore.Li2.DecayCert.BentSpec
/-! Bent frames from rational vertices: the polygon through `coord 0 = 0, coord 1, …, coord n`
with cut `0`, its dual frame, and the `BentFrame` package, from one Boolean vertex check. -/
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.DecayCert Set

/-- The vertex check: `n > 0`, the first vertex at the origin, every later vertex in the right
half plane, imaginary parts strictly increasing. -/
def frameCoordCheck (coord : ℕ → CQ) (n : ℕ) : Bool :=
  decide (0 < n ∧ coord 0=(0,0)) &&
  (List.range n).all (fun j => decide (0 < (coord (j+1)).1 ∧ (coord j).2 < (coord (j+1)).2))

theorem frameCoordCheck_spec (coord : ℕ → CQ) (n : ℕ) (h : frameCoordCheck coord n=true) :
    0 < n ∧ coord 0=(0,0) ∧ (∀ j, 1 ≤ j → j ≤ n → 0 < (coord j).1) ∧
      (∀ j, j < n → (coord j).2 < (coord (j+1)).2) := by
  simp only [frameCoordCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] at h
  obtain ⟨⟨hn,h0⟩,hs⟩ := h
  refine ⟨hn,h0,fun j h1 h2 => ?_,fun j hj => (hs j hj).2⟩
  obtain ⟨k,rfl⟩ : ∃ k, j=k+1 := ⟨j-1,by omega⟩
  exact (hs k (by omega)).1

theorem frameCoord_im_strict (coord : ℕ → CQ) (n : ℕ)
    (hs : ∀ j, j < n → (coord j).2 < (coord (j+1)).2) :
    ∀ i j, i < j → j ≤ n → (coord i).2 < (coord j).2 := by
  intro i j hij hjn
  induction j with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact (ih h (by omega)).trans (hs k (by omega))
    · subst h; exact hs i (by omega)

noncomputable def polygonOf (coord : ℕ → CQ) (n : ℕ) (h : frameCoordCheck coord n=true) :
    CatalanCore.Li2.Uniform.PolygonFrame where
  cut := 0
  nonneg := le_rfl
  edges := n
  edges_pos := (frameCoordCheck_spec coord n h).1
  vertex j := cqReal (coord j)
  initial := by
    rw [(frameCoordCheck_spec coord n h).2.1]
    simp [cqReal]
  real_pos j h1 h2 := by
    rw [cqReal_re]
    exact_mod_cast (frameCoordCheck_spec coord n h).2.2.1 j h1 h2
  imag_strict i j hij hj := by
    rw [cqReal_im,cqReal_im]
    exact_mod_cast frameCoord_im_strict coord n (frameCoordCheck_spec coord n h).2.2.2 i j hij hj

noncomputable def dualFrameOf (P : CatalanCore.Li2.Uniform.PolygonFrame) :
    CatalanCore.Li2.Uniform.DualFrame where
  lattice := Icc 0 P.cut
  free s := CatalanCore.Li2.Uniform.polygonFree P s
  lattice_mem _ hx := hx.1
  lattice_kind := Or.inr ⟨P.cut,P.nonneg,rfl⟩
  pure := false
  pure_lattice h := by simp at h
  pure_free h := by simp at h

/-- The bent frame with vertices `coord 0, …, coord n`. -/
noncomputable def bentFrameOf (coord : ℕ → CQ) (n : ℕ) (h : frameCoordCheck coord n=true) : BentFrame where
  frame := dualFrameOf (polygonOf coord n h)
  polygon := polygonOf coord n h
  hpure := rfl
  hlattice := rfl
  hfree _ := rfl
  cut_zero := rfl
  coord := coord
  coord_eq _ _ := rfl

end CatalanCore.Li2.DecayCert.Seg
