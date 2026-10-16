module
public import CatalanMeasure.Parametric.GapCircleGeometry
public import CatalanMeasure.Cert.FieldEval
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Polynomial.Chebyshev CatalanMeasure.Cert OAI.InternalCatalan
noncomputable section

private theorem filter_pos_cast {q : ℚ} (h : 0<(1001/1000:ℚ)^2+1+2*q) :
    (0:ℝ)<(1001/1000:ℝ)^2+1+2*(q:ℝ) := by
  have hh : ((0:ℚ):ℝ)<(((1001/1000:ℚ)^2+1+2*q:ℚ):ℝ) := by exact_mod_cast h
  push_cast at hh
  norm_num at hh ⊢
  exact hh

structure GapCirclePiece where
  lo : ℚ
  hi : ℚ
  b1 : ℚ
  b2 : ℚ
  H : ℚ
  base : ℚ

def GapCirclePiece.terms (p : GapCirclePiece) : List LogTerm :=
  [⟨9,0,p.base,0⟩,⟨1,0,(1001/1000)^2+1+2*p.hi,0⟩]

def GapCirclePiece.OK (p : GapCirclePiece) : Bool :=
  let a := interpolationGap
  let r : ℚ := 1001/1000
  decide (0≤p.lo ∧ p.lo≤p.hi ∧ 0≤p.b1 ∧ 0≤p.b2 ∧ 0≤p.H ∧ p.H≤p.base ∧
    (r^2+1)^2-4*p.lo^2≤p.b1^2 ∧
    (r^2+a^2)^2-4*a^2*p.lo^2≤p.b2^2 ∧
    (p.b1+p.b2)/(1-a^2)≤p.H ∧ p.H^2-1≤(p.base-p.H)^2 ∧
    0<p.base ∧ 0<r^2+1+2*p.hi) &&
  match sumLogs p.terms with
  | some ve => decide (ve.1+ve.2≤17913/1000)
  | none => false

theorem GapCirclePiece.log_bound (p : GapCirclePiece) (hp : p.OK=true) :
    9*Real.log (p.base:ℝ)+Real.log ((1001/1000:ℝ)^2+1+2*(p.hi:ℝ))≤gapWeightCost := by
  unfold GapCirclePiece.OK at hp
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hp
  obtain ⟨hnum,hlog⟩ := hp
  obtain ⟨hlo,hlh,hb1,hb2,hH,hHB,hc1,hc2,hHC,hBC,hbp,hfp⟩ := hnum
  split at hlog
  · rename_i ve he
    have hs := sumLogs_spec he
    have hv : (p.terms.map LogTerm.val).sum=
        9*Real.log (p.base:ℝ)+Real.log ((1001/1000:ℝ)^2+1+2*(p.hi:ℝ)) := by
      simp only [GapCirclePiece.terms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [realLogTerm 9 p.base (by exact_mod_cast hbp.ne' ),
        realLogTerm 1 ((1001/1000)^2+1+2*p.hi) (by exact_mod_cast hfp.ne' )]
      push_cast
      have hb : (0:ℝ)<p.base := by exact_mod_cast hbp
      have hf := filter_pos_cast hfp
      norm_num at hf ⊢ <;> rw [abs_of_pos hb,abs_of_pos hf]
    rw [hv] at hs
    have hh : ve.1+ve.2≤(17913/1000:ℚ) := of_decide_eq_true hlog
    have hr : ((ve.1+ve.2:ℚ):ℝ)≤((17913/1000:ℚ):ℝ) := by exact_mod_cast hh
    push_cast at hr
    norm_num at hr
    unfold gapWeightCost
    linarith only [(abs_le.mp hs).2,hr]
  · simp at hlog

theorem GapCirclePiece.K_bound (p : GapCirclePiece) (hp : p.OK=true) :
    (p.base:ℝ)^9*((1001/1000:ℝ)^2+1+2*(p.hi:ℝ))≤Real.exp gapWeightCost := by
  have hn : 0<p.base ∧ 0<(1001/1000:ℚ)^2+1+2*p.hi := by
    have hh := hp
    unfold GapCirclePiece.OK at hh
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
    obtain ⟨hlo,hlh,hb1,hb2,hH,hHB,hc1,hc2,hHC,hBC,hbp,hfp⟩ := hh.1
    exact ⟨hbp,hfp⟩
  have hb : (0:ℝ)<p.base := by exact_mod_cast hn.1
  have hf := filter_pos_cast hn.2
  rw [← Real.exp_log (mul_pos (pow_pos hb 9) hf)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (pow_pos hb 9).ne' hf.ne',Real.log_pow]
  exact p.log_bound hp

theorem GapCirclePiece.circle_bound (p : GapCirclePiece) (hp : p.OK=true)
    (N : ℕ) (z : ℂ) (hz : ‖z‖=(1001/1000:ℝ))
    (hs : |z.re| ∈ Set.Icc (p.lo:ℝ) p.hi) :
    ‖((gapPolynomial (interpolationGap:ℝ) N).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1:ℂ)-z‖^(2*N) ≤ Real.exp (gapWeightCost*N) := by
  have hh := hp
  unfold GapCirclePiece.OK at hh
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  obtain ⟨hlo,hlh,hb1,hb2,hH,hHB,hc1,hc2,hHC,hBC,hbp,hfp⟩ := hh.1
  have ha0 : (0:ℝ) < interpolationGap := by norm_num [interpolationGap]
  have ha1 : (interpolationGap:ℝ)<1 := by norm_num [interpolationGap]
  have hd : (0:ℝ)<1-(interpolationGap:ℝ)^2 := by norm_num [interpolationGap]
  have hc1R : ((1001/1000:ℝ)^2+1)^2-4*(p.lo:ℝ)^2≤(p.b1:ℝ)^2 := by
    have hh : ((((1001/1000:ℚ)^2+1)^2-4*p.lo^2:ℚ):ℝ)≤((p.b1^2:ℚ):ℝ) := by
      exact_mod_cast hc1
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  have hc2R : ((1001/1000:ℝ)^2+(interpolationGap:ℝ)^2)^2-
      4*(interpolationGap:ℝ)^2*(p.lo:ℝ)^2≤(p.b2:ℝ)^2 := by
    have hh : ((((1001/1000:ℚ)^2+interpolationGap^2)^2-
        4*interpolationGap^2*p.lo^2:ℚ):ℝ)≤((p.b2^2:ℚ):ℝ) := by exact_mod_cast hc2
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  have hc := gap_circle_radical_caps (a := (interpolationGap:ℝ))
    (radius := (1001/1000:ℝ)) (lo := (p.lo:ℝ)) (b1 := (p.b1:ℝ)) (b2 := (p.b2:ℝ))
    (by exact_mod_cast hlo) ha0.le (by exact_mod_cast hb1) (by exact_mod_cast hb2)
    hc1R hc2R z hz hs.1
  let w : ℂ := ((gapArgument (interpolationGap:ℝ)).map (algebraMap ℝ ℂ)).eval z
  let H : ℝ := (‖w-1‖+‖w+1‖)/2
  have hH0 : 0≤H := by dsimp [H]; positivity
  have hHi : H≤(p.H:ℝ) := by
    have hdist := gap_argument_complex_distances ha0 ha1 z
    dsimp [H,w]
    rw [hdist.1,hdist.2]
    calc
      _ = (‖z^2-1‖+‖z^2-((interpolationGap:ℝ):ℂ)^2‖)/(1-(interpolationGap:ℝ)^2) := by ring
      _ ≤ ((p.b1:ℝ)+p.b2)/(1-(interpolationGap:ℝ)^2) :=
        div_le_div_of_nonneg_right (add_le_add hc.1 hc.2) hd.le
      _ ≤ _ := by exact_mod_cast hHC
  have hbr : (0:ℝ)≤p.base-p.H := by exact_mod_cast sub_nonneg.mpr hHB
  have hroot : Real.sqrt (H^2-1)≤(p.base:ℝ)-(p.H:ℝ) := by
    rw [Real.sqrt_le_left hbr]
    have hnum : (p.H:ℝ)^2-1≤((p.base:ℝ)-(p.H:ℝ))^2 := by exact_mod_cast hBC
    have hHsq := pow_le_pow_left₀ hH0 hHi 2
    linarith only [hHsq,hnum]
  have hT : ‖(T ℂ ((9*N:ℕ):ℤ)).eval w‖≤(p.base:ℝ)^(9*N) := by
    apply (CatalanMeasure.norm_T_eval_le (9*N) w).trans
    apply pow_le_pow_left₀ (by positivity)
    change H+Real.sqrt (H^2-1)≤(p.base:ℝ)
    linarith only [hHi,hroot]
  have hf := gap_circle_filter_sq z hz hs.2
  have hfilter : ‖(1:ℂ)-z‖^(2*N)≤((1001/1000:ℝ)^2+1+2*(p.hi:ℝ))^N := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hf N
  have he : ‖((gapPolynomial (interpolationGap:ℝ) N).map (algebraMap ℝ ℂ)).eval z‖=
      ‖(T ℂ ((9*N:ℕ):ℤ)).eval w‖ := by
    rw [gapPolynomial,Polynomial.map_comp,Chebyshev.map_T,eval_comp]
  rw [he]
  calc
    _ ≤ (p.base:ℝ)^(9*N)*((1001/1000:ℝ)^2+1+2*(p.hi:ℝ))^N :=
      mul_le_mul hT hfilter (by positivity) (by positivity)
    _ = ((p.base:ℝ)^9*((1001/1000:ℝ)^2+1+2*(p.hi:ℝ)))^N := by rw [mul_pow,pow_mul]
    _ ≤ (Real.exp gapWeightCost)^N :=
      pow_le_pow_left₀ (by
        have hb : (0:ℝ)<p.base := by exact_mod_cast hbp
        have hff := filter_pos_cast hfp
        positivity) (p.K_bound hp) N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end
end CatalanMeasure.Parametric
