module
public import CatalanMeasure.Parametric.GapCirclePieces
@[expose] public section
namespace CatalanMeasure.Parametric
open Set
noncomputable section

def gapCircleCoverFrom (a : ℚ) : List GapCirclePiece → ℚ → Bool
  | [],_ => false
  | [p],b => decide (p.lo=a ∧ p.hi=b ∧ a≤b)
  | p::q::ps,b => decide (p.lo=a ∧ p.lo≤p.hi) && gapCircleCoverFrom p.hi (q::ps) b

theorem gap_circle_cover_exists {ps : List GapCirclePiece} {a b : ℚ}
    (hc : gapCircleCoverFrom a ps b=true) {s : ℝ} (hs : s ∈ Icc (a:ℝ) b) :
    ∃ p ∈ ps, s ∈ Icc (p.lo:ℝ) p.hi := by
  induction ps generalizing a with
  | nil => simp [gapCircleCoverFrom] at hc
  | cons p ps ih =>
    cases ps with
    | nil =>
      have hh : p.lo=a ∧ p.hi=b ∧ a≤b := of_decide_eq_true hc
      refine ⟨p,by simp,?_⟩
      simpa only [hh.1,hh.2.1] using hs
    | cons q qs =>
      simp only [gapCircleCoverFrom,Bool.and_eq_true,decide_eq_true_eq] at hc
      by_cases h : s≤(p.hi:ℝ)
      · refine ⟨p,by simp,?_⟩
        exact ⟨by simpa only [hc.1.1] using hs.1,h⟩
      · obtain ⟨v,hv,hsv⟩ := ih hc.2 ⟨(lt_of_not_ge h).le,hs.2⟩
        exact ⟨v,List.mem_cons_of_mem _ hv,hsv⟩

theorem gap_circle_bound_of_cover {ps : List GapCirclePiece}
    (hc : gapCircleCoverFrom 0 ps (1001/1000)=true)
    (hp : ps.all GapCirclePiece.OK=true) (N : ℕ) (z : ℂ)
    (hz : ‖z‖=(1001/1000:ℝ)) :
    ‖((gapPolynomial (interpolationGap:ℝ) N).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1:ℂ)-z‖^(2*N)≤Real.exp (gapWeightCost*N) := by
  have hs : |z.re|≤(1001/1000:ℝ) := by
    simpa only [hz] using Complex.abs_re_le_norm z
  obtain ⟨p,hmem,hsp⟩ := gap_circle_cover_exists hc
    (show |z.re| ∈ Icc ((0:ℚ):ℝ) ((1001/1000:ℚ):ℝ) by
      norm_num only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat]; exact ⟨abs_nonneg _,hs⟩)
  exact p.circle_bound (List.all_eq_true.mp hp p hmem) N z hz hsp

end
end CatalanMeasure.Parametric
