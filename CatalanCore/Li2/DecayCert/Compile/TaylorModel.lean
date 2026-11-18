module
public import CatalanCore.Li2.DecayCert.Compile.DiscData
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

theorem evalModel_add_constant (b : ℕ → ℂ) (C : ℝ) (J : ℕ) (t : ℝ) :
    evalModel ((List.range (J+1)).map (fun j => if j=0 then C+(b j).re else (b j).re)) t =
      C+(∑ j ∈ Finset.range (J+1),b j*(t:ℂ)^j).re := by
  have he (j : ℕ) : (if j=0 then C+(b j).re else (b j).re)*t^j =
      (b j*(t:ℂ)^j).re+(if j=0 then C else 0) := by
    by_cases hj : j=0
    · subst j; simp; ring
    · simp only [if_neg hj,add_zero]
      rw [← Complex.ofReal_pow]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [evalModel_map_range,Complex.re_sum]
  simp only [he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_range]
  simp [add_comm]

theorem disc_taylor_models (G : ℂ → ℂ) (b : ℕ → ℂ) (C : ℝ)
    (shift : ℂ) (R rt δ M : ℝ) (hR : 0 < R) (hrt : 0 ≤ rt) (hδ : 0 ≤ δ)
    (hrR : rt+δ < R) (hs : ‖shift‖ ≤ δ)
    (hG : AnalyticOnNhd ℂ G (Metric.ball 0 R)) (hb : HasTaylorSeriesAt G b 0)
    (hM : ∀ z ∈ Metric.ball (0:ℂ) R,‖G z‖ ≤ M) (J : ℕ) :
    Models (fun t => C+(G ((t:ℂ)+shift)).re)
      ((List.range (J+1)).map (fun j => if j=0 then C+(b j).re else (b j).re)) rt
      (M*((rt+δ)/R)^(J+1)/(1-(rt+δ)/R)+
        δ*(∑ k ∈ Finset.range J,(k+1:ℕ)*‖b (k+1)‖*(rt+δ)^k)) := by
  have hr0 : 0 ≤ rt+δ := add_nonneg hrt hδ
  have hρ0 : 0 ≤ (rt+δ)/R := div_nonneg hr0 hR.le
  have hρ1 : (rt+δ)/R < 1 := (div_lt_one hR).mpr hrR
  have hM0 : 0 ≤ M := (norm_nonneg (G 0)).trans (hM 0 (Metric.mem_ball_self hR))
  refine ⟨hrt,add_nonneg ?_ ?_,?_⟩
  · exact div_nonneg (mul_nonneg hM0 (pow_nonneg hρ0 _)) (by linarith)
  · apply mul_nonneg hδ
    apply Finset.sum_nonneg
    intro k hk
    positivity
  · intro t ht
    let z : ℂ := (t:ℂ)+shift
    have hz : ‖z‖ ≤ rt+δ := by
      exact (norm_add_le _ _).trans (add_le_add (by simpa using ht) hs)
    have ht' : ‖(t:ℂ)‖ ≤ rt+δ := by
      have hh : ‖(t:ℂ)‖ ≤ rt := by simpa using ht
      linarith
    have hshift : ‖z-(t:ℂ)‖ ≤ δ := by
      have he : z-(t:ℂ)=shift := by dsimp [z]; ring
      rwa [he]
    have htail := taylor_remainder_bound hb R (rt+δ) M hR ⟨hr0,hrR⟩ hG.differentiableOn hM z hz (J+1)
    have hdisp := norm_taylor_displacement b J z (t:ℂ) (rt+δ) δ hr0 hz ht' hshift
    rw [evalModel_add_constant]
    have he : (C+(G z).re)-(C+(∑ j ∈ Finset.range (J+1),b j*(t:ℂ)^j).re) =
        (G z-(∑ j ∈ Finset.range (J+1),b j*(t:ℂ)^j)).re := by rw [Complex.sub_re]; ring
    change |(C+(G z).re)-(C+(∑ j ∈ Finset.range (J+1),b j*(t:ℂ)^j).re)| ≤ _
    rw [he]
    apply (Complex.abs_re_le_norm _).trans
    have htri : ‖G z-(∑ j ∈ Finset.range (J+1),b j*(t:ℂ)^j)‖ ≤
        ‖G z-(∑ j ∈ Finset.range (J+1),b j*z^j)‖+
          ‖(∑ j ∈ Finset.range (J+1),b j*z^j)-(∑ j ∈ Finset.range (J+1),b j*(t:ℂ)^j)‖ := by
      have he : G z-(∑ j ∈ Finset.range (J+1),b j*(t:ℂ)^j) =
          (G z-(∑ j ∈ Finset.range (J+1),b j*z^j))+
            ((∑ j ∈ Finset.range (J+1),b j*z^j)-(∑ j ∈ Finset.range (J+1),b j*(t:ℂ)^j)) := by ring
      rw [he]
      exact norm_add_le _ _
    exact htri.trans (add_le_add htail hdisp)

#print axioms evalModel_add_constant
#print axioms disc_taylor_models
end
end CatalanCore.Li2.DecayCert
