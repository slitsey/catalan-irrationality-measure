module
public import CatalanCore.Decay.CurveFamily
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace CatalanCore.Tools.ExponentialSampling
theorem radial_piece (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a)
    (p : CatalanCore.Decay.CurveFamily.Piece) :
    Integrable (fun s : ℂ => M*Real.exp (-a*‖s‖)) (ENNReal.ofReal ‖p.D‖ • p.nu.map p.zeta) := by
  have hf : Measurable (fun s : ℂ => M*Real.exp (-a*‖s‖)) := by fun_prop
  have hzeta : Measurable p.zeta := by unfold CatalanCore.Decay.CurveFamily.Piece.zeta; fun_prop
  by_cases hD : p.D=0
  · simp [hD]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply (integrable_map_measure hf.aestronglyMeasurable hzeta.aemeasurable).2
  change Integrable (fun t : ℝ => M*Real.exp (-a*‖p.zeta t‖)) p.nu
  unfold CatalanCore.Decay.CurveFamily.Piece.nu
  split_ifs with hray
  · apply CatalanCore.Decay.CurveFamily.integrable_Ioi_of_le (M := M*Real.exp (a*‖p.a‖))
      (μ := a*‖p.D‖) (by positivity) (by fun_prop)
    intro t ht
    have ht0 : 0 < t := ht
    have hnorm : t*‖p.D‖ ≤ ‖p.zeta t‖+‖p.a‖ := by
      have hh := norm_sub_le (p.zeta t) p.a
      have he : p.zeta t-p.a=(t:ℂ)*p.D := by dsimp [CatalanCore.Decay.CurveFamily.Piece.zeta]; ring
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0] at hh
      exact hh
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
      _ ≤ M*Real.exp (a*‖p.a‖+(-(a*‖p.D‖)*t)) := by
        gcongr
        nlinarith
      _ = _ := by rw [Real.exp_add]; ring
  · apply CatalanCore.Decay.CurveFamily.integrable_Ioc_of_le (M := M) (by fun_prop)
    intro t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right hM (Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg (p.zeta t)]))

theorem geometric_sample (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a) (n : ℕ) (hn : 0 < n) :
    Summable (fun x : ℕ => M*Real.exp (-a*(((x+1:ℕ):ℝ)/n))) ∧
      (∑' x : ℕ, M*Real.exp (-a*(((x+1:ℕ):ℝ)/n))) ≤ (M/a)*(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let b := a/(n:ℝ)
  let q := Real.exp (-b)
  have hb : 0 < b := by dsimp [b]; positivity
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he (x : ℕ) : M*Real.exp (-a*(((x+1:ℕ):ℝ)/n))=(M*q)*q^x := by
    dsimp [q,b]
    rw [← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
    congr 1
    push_cast
    field_simp
    <;> ring
  have hs : Summable (fun x : ℕ => M*Real.exp (-a*(((x+1:ℕ):ℝ)/n))) := by
    simp_rw [he]
    exact (summable_geometric_of_lt_one hq.le hq1).mul_left (M*q)
  refine ⟨hs,?_⟩
  have hden : b*q ≤ 1-q := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp b) hq.le
    have hexp : Real.exp b*q=1 := by dsimp [q]; rw [← Real.exp_add]; simp
    rw [hexp] at hh
    nlinarith
  have hquot : q/(1-q) ≤ 1/b := by
    apply (div_le_div_iff₀ (by linarith : 0 < 1-q) hb).mpr
    nlinarith
  simp_rw [he]
  rw [tsum_mul_left,tsum_geometric_of_lt_one hq.le hq1]
  calc
    (M*q)*(1-q)⁻¹ = M*(q/(1-q)) := by ring
    _ ≤ M*(1/b) := mul_le_mul_of_nonneg_left hquot hM
    _ = _ := by dsimp [b]; field_simp <;> ring

end CatalanCore.Tools.ExponentialSampling
#print axioms CatalanCore.Tools.ExponentialSampling.radial_piece
#print axioms CatalanCore.Tools.ExponentialSampling.geometric_sample
