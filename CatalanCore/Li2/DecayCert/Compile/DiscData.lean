module
public import CatalanCore.Li2.DecayCert.Compile.Majorant
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski
noncomputable section

def segDiscMajorantExpr (d : QSegment) (w : SegDiscWitness) : SE :=
  seAdd (seScale |d.c 0|
    (seAdd (.log w.terms w.phiHi)
      (seAdd (.log w.terms 2) (seAdd .pi (.log w.terms (1/(1-w.fraction)))))))
    (seRat ((List.range (d.coeff.length-1)).map (fun k : ℕ => |d.c (k+1)|/(k+1:ℚ))).sum)

theorem segDiscMajorantExpr_value (d : QSegment) (w : SegDiscWitness) :
    (segDiscMajorantExpr d w).value =
      |(d.c 0:ℝ)| *(Real.log (w.phiHi:ℝ)+Real.log 2+Real.pi-Real.log (1-(w.fraction:ℝ)))+
        ∑ k ∈ Finset.range (d.coeff.length-1), |(d.c (k+1):ℝ)|/(k+1:ℕ) := by
  unfold segDiscMajorantExpr
  rw [seAdd_value,seScale_value,seAdd_value,seAdd_value,seAdd_value,seRat_value,list_sum_map_range]
  simp only [ScalarExpr.value]
  push_cast
  rw [one_div,Real.log_inv]
  ring

theorem norm_cqReal_le_of_cqSq_le {q : CQ} {a : ℚ} (ha : 0 ≤ a) (hq : cqSq q ≤ a^2) :
    ‖cqReal q‖ ≤ (a:ℝ) := by
  have he : ‖cqReal q‖^2 ≤ (a:ℝ)^2 := by rw [← cqSq_eq_norm_sq]; exact_mod_cast hq
  have hnon : 0 ≤ (a:ℝ) := by exact_mod_cast ha
  nlinarith [norm_nonneg (cqReal q)]

theorem cqReal_ne_of_cqSq_ne (q : CQ) (hq : cqSq q ≠ 0) : cqReal q ≠ 0 := by
  intro hz
  have he : (cqSq q:ℝ)=0 := by rw [cqSq_eq_norm_sq,hz,norm_zero]; norm_num
  exact hq (by exact_mod_cast he)

theorem segDiscOK_hasPrimitive (d : QSegment) (p e : CQ) (rt : ℚ) (w : SegDiscWitness)
    (hg : segDiscOK d p e rt w=true) :
    let ζ := cqScale (1/2) (cqAdd w.phi (cqInv w.phi))
    let γ := cqDiv e d.half
    ∃ hh : cqReal d.half ≠ 0, ∃ G : ℂ → ℂ, ∃ b : ℕ → ℂ,
      IsDiscSegmentPrimitive (d.toSegment hh) (cqReal ζ) (cqReal γ) w.radius G ∧
      AnalyticOnNhd ℂ G (Metric.ball 0 (w.radius:ℝ)) ∧ HasTaylorSeriesAt G b 0 ∧
      (∀ u ∈ Metric.ball (0:ℂ) (w.radius:ℝ), ‖G u‖ ≤ (segDiscMajorantExpr d w).value) := by
  let ζ := cqScale (1/2) (cqAdd w.phi (cqInv w.phi))
  let γ := cqDiv e d.half
  have hb := of_decide_eq_true hg
  rcases hb with ⟨hhalf,he,hphi,hd,hdsq,hg0,hgsq,hz0,hzsq,hR,hf0,hf1,hgR,hrt,hdr,hH1,hZH,hHsq⟩
  have hh := cqReal_ne_of_cqSq_ne d.half hhalf
  have hRr : 0 < (w.radius:ℝ) := by exact_mod_cast hR
  have hoff : ∀ u ∈ Metric.ball (0:ℂ) (w.radius:ℝ),1 < jc (cqReal ζ+cqReal γ*u) :=
    checked_affine_off_slit ζ γ w.distanceLo w.radius w.fraction w.gammaHi hd hR.le hf1 hg0 hdsq hgsq hgR
  have hs : 1 < jc (cqReal ζ) := by simpa using hoff 0 (Metric.mem_ball_self hRr)
  rcases segment_disc_primitive_exists (d.toSegment hh) (cqReal ζ) (cqReal γ) (w.radius:ℝ) hRr hoff with
    ⟨G,hG,hGa,b,hb⟩
  have hdist := slit_distance_lower ζ w.distanceLo hd.le hdsq
  let dist := Metric.infDist (cqReal ζ) sourceSlit
  have hdpos : 0 < dist := (show 0 < (w.distanceLo:ℝ) by exact_mod_cast hd).trans_le hdist
  have hgnorm : ‖cqReal γ‖ ≤ (w.gammaHi:ℝ) := norm_cqReal_le_of_cqSq_le hg0 hgsq
  have hznorm : ‖cqReal ζ‖ ≤ (w.zetaHi:ℝ) := norm_cqReal_le_of_cqSq_le hz0 hzsq
  have hfracR : 0 < (w.fraction:ℝ) := by exact_mod_cast hf0
  have hbound : ‖cqReal γ‖*(w.radius:ℝ) ≤ (w.fraction:ℝ)*dist := by
    calc
      _ ≤ (w.gammaHi:ℝ)*(w.radius:ℝ) := mul_le_mul_of_nonneg_right hgnorm hRr.le
      _ ≤ (w.fraction:ℝ)*(w.distanceLo:ℝ) := by exact_mod_cast hgR
      _ ≤ _ := mul_le_mul_of_nonneg_left hdist hfracR.le
  have hZ : ‖cqReal ζ‖ ≤ (w.zetaHi:ℝ)+(w.gammaHi:ℝ)*(w.radius:ℝ) := by
    have hgR0 : 0 ≤ (w.gammaHi:ℝ)*(w.radius:ℝ) := mul_nonneg (by exact_mod_cast hg0) hRr.le
    linarith
  have hφH : ‖jphi (cqReal ζ)‖ ≤ (w.phiHi:ℝ) :=
    jphi_le_of_quadratic_bound (cqReal ζ) hs _ _ hZ (by exact_mod_cast hZH) (by exact_mod_cast hHsq)
  refine ⟨hh,G,b,hG,hGa,hb,?_⟩
  intro u hu
  rw [segDiscMajorantExpr_value]
  exact discPrimitive_norm_bound_checked (d.toSegment hh) (cqReal ζ) (cqReal γ) hs dist
    w.radius w.fraction w.phiHi rfl hdpos (by exact_mod_cast hf1) hbound hφH G hG u hu

#print axioms segDiscMajorantExpr_value
#print axioms norm_cqReal_le_of_cqSq_le
#print axioms cqReal_ne_of_cqSq_ne
#print axioms segDiscOK_hasPrimitive
end
end CatalanCore.Li2.DecayCert
