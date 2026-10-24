module
public import CatalanArchive.CatalanFrames.P6Hybrid.ProfileBaseSum
public import CatalanArchive.CatalanFrames.P6Hybrid.ProfileGlobalSum
public import CatalanFrames.P6Hybrid.Admissible
@[expose] public section
open Finset Filter Polynomial CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid
open CatalanFrames.P6

theorem intervalDenominator_log_uniform (mf : ℕ→ℕ)
    (hadm : ∀r,r≤8*mf r ∧ 8*mf r≤r+9) :
    ∀ε>0,∀ᶠr:ℕ in atTop,
      Real.log (intervalDenominator r (mf r))≤(2159207/645120+ε)*(r:ℝ)^2 := by
  intro ε hε
  filter_upwards [intervalBase_sum_uniform mf hadm (ε/2) (by positivity),
    intervalProfile_sum_lower mf hadm (ε:=ε/2) (by positivity)] with r hb hd
  rw [log_intervalDenominator]
  have he : (10339/3072:ℝ)-11983/645120=2159207/645120 := by norm_num
  nlinarith

theorem intervalDenominator_log_all :
    ∀ε>0,∀ᶠr:ℕ in atTop,∀m,P6Adm9 r m→
      Real.log (intervalDenominator r m)≤(2159207/645120+ε)*(r:ℝ)^2 := by
  have h1:=intervalDenominator_log_uniform (fun r=>(r+7)/8) (fun r=>⟨by omega,by omega⟩)
  have h2:=intervalDenominator_log_uniform (fun r=>r/8+1) (fun r=>⟨by omega,by omega⟩)
  have h3:=intervalDenominator_log_uniform p6mfC (fun r=>by unfold p6mfC;split_ifs <;> omega)
  intro ε hε
  filter_upwards [h1 ε hε,h2 ε hε,h3 ε hε] with r a b c m hm
  rcases hm.cases with rfl|rfl|rfl
  · exact a
  · exact b
  · exact c

noncomputable def intervalMinorDenominator (r m : ℕ) : ℕ :=
  if 1000≤r then intervalDenominator r m else Dhyb (p6Inst r m) r m

/-- Full periodic content, using the existing minor family and degree budget. -/
theorem p6_interval_minor_content (d : ℕ) :
    HasContent (commonMinorFam p6Frame P6Adm9 d) (2159207/645120) := by
  classical
  refine ⟨fun i=>intervalMinorDenominator i.1 i.2.1,?_,?_,?_⟩
  · intro i
    dsimp only [intervalMinorDenominator]
    split_ifs
    · exact intervalDenominator_pos _ _
    · exact Dhyb_pos _ _ _
  · intro i hi p q hq
    apply int_clear _ i.1 (natDegree_commonMinorPoly_le p6Frame i.1 i.2.1 i.2.2) _ _ p q hq
    intro j
    dsimp only [intervalMinorDenominator]
    split_ifs with hr
    · exact intervalDenominator_integral hr hi.1.1 hi.1.2 i.2.2 j
    · exact commonMinorPoly_integral (p6Inst i.1 i.2.1) i.1 i.2.1 i.2.2 j
  · intro ε hε
    have h:=intervalDenominator_log_all ε hε
    obtain ⟨N,hN⟩:=eventually_atTop.mp h
    refine ⟨max N 1000,?_⟩
    intro i hi hr
    change max N 1000 ≤ i.1 at hr
    change Real.log (intervalMinorDenominator i.1 i.2.1)≤_
    rw [intervalMinorDenominator,if_pos (by omega : 1000 ≤ i.1)]
    exact hN i.1 (by omega) i.2.1 hi.1
end CatalanFrames.P6Hybrid
