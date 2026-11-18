module
public import CatalanCore.Li2.DecayCert.Source
@[expose] public section
set_option Elab.async false
open Set MeasureTheory
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.Decay

/-- Logical fusion only: the builder is a parameter, never a bent evaluator here. -/
theorem fused_result_sound {Spec Result : Type*} (build : Spec → Option Result)
    (check : Spec → Result → Bool) (Good : Spec → Prop)
    (hsound : ∀p m,build p=some m → check p m=true → Good p)
    (p : Spec) (hc : (build p).any (check p)=true) : Good p := by
  cases he : build p with
  | none => simp [he] at hc
  | some m => exact hsound p m he (by simpa [he] using hc)

/-- Row 9: checked bounds of the computed range, with sign checked in the same Boolean. -/
theorem computed_range_checked {Spec : Type*} (build : Spec → Option QBox)
    (f : Spec → ℝ → ℝ) (domain : Spec → Set ℝ)
    (hsound : ∀p B,build p=some B → ∀u∈domain p,f p u∈Icc (B.1:ℝ) (B.2:ℝ))
    (p : Spec) (lo hi : ℚ) (positive : Bool)
    (hc : (build p).any (fun B=>decide (lo≤B.1 ∧ B.2≤hi) &&
      if positive then decide (0≤lo) else decide (hi≤0))=true) :
    ∀u∈domain p,f p u∈Icc (lo:ℝ) (hi:ℝ) ∧
      (if positive then 0≤f p u else f p u≤0) := by
  cases he : build p with
  | none => simp [he] at hc
  | some B =>
    have hb : (lo≤B.1 ∧ B.2≤hi) ∧
        (if positive then decide (0≤lo) else decide (hi≤0))=true := by
      simpa only [he,Option.any_some,Bool.and_eq_true,decide_eq_true_eq] using hc
    intro u hu
    have hf:=hsound p B he u hu
    have hl : (lo:ℝ)≤(B.1:ℝ) := by exact_mod_cast hb.1.1
    have hh : (B.2:ℝ)≤(hi:ℝ) := by exact_mod_cast hb.1.2
    refine ⟨⟨hl.trans hf.1,hf.2.trans hh⟩,?_⟩
    cases hp : positive
    · have hn : hi≤0 := by simpa only [hp,Bool.false_eq_true,ite_false,decide_eq_true_eq] using hb.2
      have hnR : (hi:ℝ)≤0 := by exact_mod_cast hn
      exact (hf.2.trans hh).trans hnR
    · have hn : 0≤lo := by simpa only [hp,ite_true,decide_eq_true_eq] using hb.2
      have hnR : (0:ℝ)≤(lo:ℝ) := by exact_mod_cast hn
      exact hnR.trans (hl.trans hf.1)

/-- Rows 8/16: actual W from one checked evaluator result. No model is certificate data. -/
theorem cellC1_of_eval {Spec : Type*} (build : Spec → Option QBox)
    (z : ℝ) (σ : Measure ℂ) (point : Spec → ℝ → ℂ) (domain : Spec → Set ℝ)
    (hsound : ∀p B,build p=some B → ∀u∈domain p,
      W z σ (point p u)∈Icc (B.1:ℝ) (B.2:ℝ))
    (p : Spec) (ell : ℚ)
    (hc : (build p).any (fun B=>decide (B.2≤ell))=true) :
    ∀u∈domain p,W z σ (point p u)≤(ell:ℝ) := by
  cases he : build p with
  | none => simp [he] at hc
  | some B =>
    have hb : B.2≤ell := by simpa [he] using hc
    have hbR : (B.2:ℝ)≤(ell:ℝ) := by exact_mod_cast hb
    exact fun u hu => (hsound p B he u hu).2.trans hbR

/-- Row 13: a computed line and its checked residual give the actual pointwise line bound. -/
theorem lineCell_of_eval {Spec : Type*} (build : Spec → Option (ℚ×ℚ×ℚ))
    (f : Spec → ℝ → ℝ) (domain : Spec → Set ℝ)
    (hsound : ∀p out,build p=some out → ∀u∈domain p,
      f p u-((out.1:ℝ)+(out.2.1:ℝ)*u)≤(out.2.2:ℝ))
    (p : Spec) (hc : (build p).any (fun out=>decide (out.2.2≤0))=true) :
    ∃out,build p=some out ∧ ∀u∈domain p,f p u≤(out.1:ℝ)+(out.2.1:ℝ)*u := by
  cases he : build p with
  | none => simp [he] at hc
  | some out =>
    have hb : out.2.2≤0 := by simpa [he] using hc
    have hbR : (out.2.2:ℝ)≤0 := by exact_mod_cast hb
    refine ⟨out,rfl,?_⟩
    intro u hu
    have hh:=hsound p out he u hu
    linarith

#print axioms fused_result_sound
#print axioms computed_range_checked
#print axioms cellC1_of_eval
#print axioms lineCell_of_eval
end CatalanCore.Li2.DecayCert.Seg

