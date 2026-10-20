module
public import CatalanFrames.P6Hybrid.IntervalContent
@[expose] public section
open Finset Polynomial Matrix CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid

/-- Finite arithmetic data for the gain windows. -/
structure IntervalRow where
  c : ℕ
  loN : ℕ
  loD : ℕ
  hiN : ℕ
  hiD : ℕ
  A : ℤ
  B : ℤ
  den : ℕ
  j : ℕ
  k : ℕ
  deriving DecidableEq

def intervalProfile : List IntervalRow := [
  ⟨1, 9, 32, 2, 7, (-9), 32, 8, 21, 24⟩,
  ⟨1, 2, 7, 5, 16, (-1), 4, 8, 21, 24⟩,
  ⟨1, 5, 16, 9, 28, 9, (-28), 8, 21, 24⟩,
  ⟨1, 3, 8, 2, 5, (-9), 24, 8, 15, 18⟩,
  ⟨1, 2, 5, 5, 12, (-1), 4, 8, 15, 18⟩,
  ⟨1, 5, 12, 9, 20, 9, (-20), 8, 15, 18⟩,
  ⟨1, 27, 56, 1, 2, (-27), 56, 24, 12, 14⟩,
  ⟨1, 1, 2, 15, 28, (-3), 8, 24, 12, 14⟩,
  ⟨1, 15, 28, 9, 16, 9, (-16), 8, 12, 14⟩,
  ⟨1, 9, 16, 5, 8, (-9), 16, 8, 9, 12⟩,
  ⟨1, 5, 8, 2, 3, 1, 0, 8, 9, 12⟩,
  ⟨1, 2, 3, 3, 4, 9, (-12), 8, 9, 12⟩,
  ⟨1, 3, 4, 5, 6, (-3), 4, 24, 8, 9⟩,
  ⟨1, 5, 6, 27, 32, 27, (-32), 24, 8, 9⟩,
  ⟨5, 1, 4, 5, 18, (-1), 4, 8, 24, 27⟩,
  ⟨5, 5, 18, 9, 32, 9, (-32), 8, 24, 27⟩,
  ⟨5, 9, 28, 1, 3, (-9), 28, 8, 18, 21⟩,
  ⟨5, 1, 3, 5, 14, (-1), 4, 8, 18, 21⟩,
  ⟨5, 5, 14, 3, 8, 9, (-24), 8, 18, 21⟩,
  ⟨5, 3, 8, 5, 12, (-3), 8, 24, 16, 18⟩,
  ⟨5, 5, 12, 27, 64, 27, (-64), 24, 16, 18⟩,
  ⟨5, 9, 20, 1, 2, (-9), 20, 8, 12, 15⟩,
  ⟨5, 1, 2, 9, 16, 9, (-16), 8, 12, 15⟩,
  ⟨5, 9, 16, 3, 5, (-9), 16, 8, 10, 12⟩,
  ⟨5, 3, 5, 5, 8, (-3), 8, 24, 10, 12⟩,
  ⟨5, 5, 8, 27, 40, 27, (-40), 24, 10, 12⟩]

def IntervalRow.active (P : IntervalRow) (r p : ℕ) : Prop :=
  p%6=P.c ∧ P.loN*r<P.loD*p ∧ P.hiD*p≤P.hiN*r

def IntervalRow.area (P : IntervalRow) : ℚ :=
  let lo : ℚ:=P.loN/P.loD
  let hi : ℚ:=P.hiN/P.hiD
  ((P.A:ℚ)*(hi-lo)+(P.B:ℚ)*(hi^2-lo^2)/2)/P.den/2

theorem intervalProfile_gain : (intervalProfile.map IntervalRow.area).sum=11983/645120 := by
  norm_num [intervalProfile,IntervalRow.area]

theorem intervalProfile_arithmetic (P : IntervalRow) (hP : P∈intervalProfile)
    {r m p : ℕ} (hm1 : r≤8*m) (hm2 : 8*m≤r+9) (ha : P.active r p) :
    (P.den:ℤ)*((p6WitnessRight r m p P.k-p6WitnessLeft r p P.j-m:ℕ):ℤ)≥
      P.A*r+P.B*p-100*P.den := by
  simp only [intervalProfile,List.mem_cons,List.mem_nil_iff,or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp [IntervalRow.active] at ha
    dsimp [p6WitnessRight,p6WitnessLeft]
    push_cast
    omega

theorem intervalProfile_poles (P : IntervalRow) (hP : P∈intervalProfile) :
    (P.c=1 ∨ P.c=5) ∧ ∀a:ℤ,(P.j:ℤ)<a→a<P.k→¬p6PoleMask P.c a := by
  simp only [intervalProfile,List.mem_cons,List.mem_nil_iff,or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · decide
    · intro a hja hak
      norm_num [p6PoleMask] at *
      omega

theorem intervalProfile_geometry (P : IntervalRow) (hP : P∈intervalProfile) :
    (∀ r p, P.active r p → r < 4*p) ∧
      (∀ r m p, 2*(p6WitnessRight r m p P.k-p6WitnessLeft r p P.j) ≤ p) := by
  simp only [intervalProfile,List.mem_cons,List.mem_nil_iff,or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · intro r p ha;dsimp [IntervalRow.active] at ha;omega
    · intro r m p;dsimp [p6WitnessRight,p6WitnessLeft];omega

theorem intervalProfile_data (P : IntervalRow) (hP : P∈intervalProfile) :
    0<P.den ∧ 0<P.loD ∧ 0<P.hiD ∧ 0<P.loN ∧
      (P.loN:ℚ)/P.loD≤(P.hiN:ℚ)/P.hiD ∧ (P.hiN:ℚ)/P.hiD≤1 ∧ P.c<6 := by
  simp only [intervalProfile,List.mem_cons,List.mem_nil_iff,or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

theorem intervalProfile_nodup : intervalProfile.Nodup := by decide

theorem intervalProfile_disjoint : intervalProfile.Pairwise (fun P Q=>
    P.c≠Q.c ∨ (P.hiN:ℚ)/P.hiD≤(Q.loN:ℚ)/Q.loD ∨
      (Q.hiN:ℚ)/Q.hiD≤(P.loN:ℚ)/P.loD) := by
  norm_num [intervalProfile,List.pairwise_cons]
end CatalanFrames.P6Hybrid
