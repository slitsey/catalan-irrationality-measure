module
public import CatalanCore.Li2.DecayCert.Assembly.Base
@[expose] public section
set_option Elab.async false
open Set MeasureTheory
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.Decay
noncomputable section

/-- Row 17: theorem-only terminal bridge for a future fused evaluator.
    The builder correctness theorem is global; it is not a certificate field. -/
theorem bent_certificate_of_eval {Spec : Type*}
    (build : Spec → Option (ℚ×ℚ×LinePartition 1 4))
    (z : ℝ) (hz : ValidZ z) (hneg : z<0)
    (F : CatalanCore.Li2.Decay.Frame) (geom : CatalanCore.Li2.Uniform.FrameGeometry F)
    (hcut : CatalanCore.Li2.Uniform.frameCut geom=some 0) (d : CatalanCore.Li2.Decay.DualDatum)
    (hsound : ∀p out,build p=some out →
      FreeBound z F d (out.1:ℝ) ∧ I d.σ≤(out.2.1:ℝ) ∧
      ∀c∈out.2.2.cells,∀u∈Icc 0 (c.len:ℝ),
        omega z ((c.start:ℝ)+(c.dir:ℝ)*u)-
          2*U d.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ))≤(c.a:ℝ)+(c.b:ℝ)*u)
    (p : Spec) (ρ lam D K : ℚ) (hρ : (0:ℝ)<(ρ:ℝ))
    (hK : 12*Real.log 2+4≤(K:ℝ))
    (hc : (build p).any (fun out=>decide (out.1≤lam ∧
      D≤ -K-out.2.1-2*lam-out.2.2.posSumQ ρ lam))=true) :
    WindowDecay (normalizedQ z) (li2 z) (D:ℝ) (ρ:ℝ) := by
  cases he : build p with
  | none => simp [he] at hc
  | some out =>
    have hp : out.1≤lam ∧ D≤ -K-out.2.1-2*lam-out.2.2.posSumQ ρ lam := by
      simpa [he] using hc
    obtain ⟨hfree,hI,hline⟩:=hsound p out he
    have hlam : (out.1:ℝ)≤(lam:ℝ) := by exact_mod_cast hp.1
    apply bent_certificate_decay z hz hneg F geom hcut d (out.1:ℝ) lam ρ out.2.1 D
      hρ hlam hfree hI out.2.2 hline
    have hscalar : (D:ℝ)≤ -(K:ℝ)-(out.2.1:ℝ)-2*(lam:ℝ)-
        (out.2.2.posSumQ ρ lam:ℝ) := by exact_mod_cast hp.2
    rw [posSum_cast] at hscalar
    linarith

/-- Row 17's dual-value form, obtained from a checked computed result. -/
theorem bent_bounds_of_eval {Spec : Type*}
    (build : Spec → Option (ℚ×ℚ×LinePartition 1 4))
    (z : ℝ) (F : CatalanCore.Li2.Decay.Frame)
    (geom : CatalanCore.Li2.Uniform.FrameGeometry F)
    (hcut : CatalanCore.Li2.Uniform.frameCut geom=some 0)
    (d : CatalanCore.Li2.Decay.DualDatum)
    (hsound : ∀p out,build p=some out →
      FreeBound z F d (out.1:ℝ) ∧ I d.σ≤(out.2.1:ℝ) ∧
      ∀c∈out.2.2.cells,∀u∈Icc 0 (c.len:ℝ),
        omega z ((c.start:ℝ)+(c.dir:ℝ)*u)-
          2*U d.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ))≤(c.a:ℝ)+(c.b:ℝ)*u)
    (p : Spec) (ρ lam D K : ℚ) (hK : 12*Real.log 2+4≤(K:ℝ))
    (hc : (build p).any (fun out=>decide (out.1≤lam ∧
      D≤ -K-out.2.1-2*lam-out.2.2.posSumQ ρ lam))=true) :
    (D:ℝ)≤dualValue z (ρ:ℝ) F d.σ (lam:ℝ) ∧ FreeBound z F d (lam:ℝ) := by
  cases he : build p with
  | none => simp [he] at hc
  | some out =>
    have hp : out.1≤lam ∧ D≤ -K-out.2.1-2*lam-out.2.2.posSumQ ρ lam := by
      simpa [he] using hc
    obtain ⟨hfree,hI,hline⟩:=hsound p out he
    have hlam : (out.1:ℝ)≤(lam:ℝ) := by exact_mod_cast hp.1
    have hf : Continuous (fun x : ℝ=>omega z x-2*U d.σ (-(x:ℂ))) := by
      convert continuous_A_real z 0 d using 1
      funext x
      simp only [A,sub_zero]
    have hA:=Dsum_spec _ out.2.2 hf.continuousOn hline ρ lam
    have hA' : atomPenalty z (ρ:ℝ) d.σ (lam:ℝ)≤(out.2.2.posSumQ ρ lam:ℝ) := by
      unfold atomPenalty
      convert hA using 1
      congr 1
      funext x
      congr 1
      unfold A
      ring
    have hscalar : (D:ℝ)≤ -(K:ℝ)-(out.2.1:ℝ)-2*(lam:ℝ)-
        (out.2.2.posSumQ ρ lam:ℝ) := by exact_mod_cast hp.2
    refine ⟨?_,fun s hs=>(hfree s hs).trans hlam⟩
    unfold dualValue
    rw [frameCut_zero_latPenalty F geom hcut]
    linarith

#print axioms bent_bounds_of_eval

#print axioms bent_certificate_of_eval
end
end CatalanCore.Li2.DecayCert.Seg

