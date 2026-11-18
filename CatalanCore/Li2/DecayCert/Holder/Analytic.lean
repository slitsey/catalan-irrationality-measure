module
public import CatalanCore.Li2.DecayCert.Holder.Norm
public import CatalanCore.Li2.DecayCert.Holder.Comparison
public import CatalanCore.Li2.DecayCert.Holder.Own
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section
theorem holder_off_cell (d : SegmentData) (hpos : d.densityNonneg)
    (b e : ℂ) (D : ℝ) (hD : 0 ≤ D) (hgeom : EndCellGeometry d b e D .off) :
    ∀ τ ∈ Icc 0 D,|P d.ν (b+e*(τ:ℂ))-P d.ν b| ≤ endMajorant d b e D .off := by
  let ζ := (b-d.M)/d.h
  let γ := e/d.h
  let l := ‖γ‖*D
  let F := ∑ k ∈ Finset.range (d.N+1),|d.c k| *(endPhi d b e D)^k
  let A := ∑ k ∈ Finset.range d.N,(k+1:ℕ)*|d.c (k+1)| *(endPhi d b e D)^k
  let den := Real.sqrt ((‖ζ-1‖-l)*(‖ζ+1‖-l))
  have hl : 0 ≤ l := mul_nonneg (norm_nonneg _) hD
  rcases hgeom with ⟨hsep,hoff⟩
  have hs1 : l < ‖ζ-1‖ := hsep.trans_le (min_le_left _ _)
  have hs2 : l < ‖ζ+1‖ := hsep.trans_le (min_le_right _ _)
  have hden : 0 < den := Real.sqrt_pos.2 (mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hs2))
  have hΦ : 0 ≤ endPhi d b e D := zero_le_one.trans (endPhi_one_le d b e D hD)
  have hF : 0 ≤ F := by dsimp only [F]; apply Finset.sum_nonneg; intro k hk; positivity
  have hA : 0 ≤ A := by dsimp only [A]; apply Finset.sum_nonneg; intro k hk; positivity
  have hB : 0 ≤ ‖γ‖*(F/den+A) := by positivity
  have hf : ContinuousOn (fun t : ℝ => P d.ν (b+e*(t:ℂ))) (Icc 0 D) :=
    (d.continuous_P hpos).comp_continuousOn (by fun_prop)
  have hderiv (t : ℝ) (ht : t ∈ Ioo 0 D) :
      HasDerivAt (fun v : ℝ => P d.ν (b+e*(v:ℂ))) (segmentPathDerivative d b e t) t :=
    d.potential_path_hasDerivAt hpos b e t (hoff t ⟨ht.1.le,ht.2.le⟩)
  have hbnd (t : ℝ) (ht : t ∈ Ioo 0 D) : |segmentPathDerivative d b e t| ≤ ‖γ‖*(F/den+A) := by
    have hz : (b+e*(t:ℂ)-d.M)/d.h=ζ+γ*(t:ℂ) := by dsimp only [ζ,γ]; ring
    have hdisp : ‖(b+e*(t:ℂ)-d.M)/d.h-ζ‖ ≤ l := by
      rw [hz,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
      exact mul_le_mul_of_nonneg_left ht.2.le (norm_nonneg _)
    have hn := norm_jq_off_lower ζ ((b+e*(t:ℂ)-d.M)/d.h) l hl hdisp hs1 hs2 (hoff t ⟨ht.1.le,ht.2.le⟩)
    have hv := segmentPathDerivative_bound d b e D t hD ⟨ht.1.le,ht.2.le⟩
    exact hv.trans (mul_le_mul_of_nonneg_left
      (add_le_add (div_le_div_of_nonneg_left hF hden hn) (le_refl A)) (norm_nonneg γ))
  have he := holder_linear_derivative_bound _ (segmentPathDerivative d b e) D _ hD hB hf hderiv hbnd
  intro τ hτ
  have ht := he τ hτ
  have hzero : b+e*((0:ℝ):ℂ)=b := by simp
  rw [hzero] at ht
  have hc : ‖γ‖*(F/den+A)*D=endMajorant d b e D .off := by
    dsimp only [endMajorant,ζ,γ,l,F,A,den]
    ring
  rwa [hc] at ht

theorem holder_branch_cell (d : SegmentData) (hpos : d.densityNonneg)
    (b e : ℂ) (D : ℝ) (hD : 0 ≤ D) (hsmall : ‖e/d.h‖*D < 1)
    (hgeom : EndCellGeometry d b e D .branch) :
    ∀ τ ∈ Icc 0 D,|P d.ν (b+e*(τ:ℂ))-P d.ν b| ≤ endMajorant d b e D .branch := by
  let ζ := (b-d.M)/d.h
  let γ := e/d.h
  let g := ‖γ‖
  let l := g*D
  let F := ∑ k ∈ Finset.range (d.N+1),|d.c k| *(endPhi d b e D)^k
  let A := ∑ k ∈ Finset.range d.N,(k+1:ℕ)*|d.c (k+1)| *(endPhi d b e D)^k
  let den := Real.sqrt (2-l)
  rcases hgeom with ⟨hε,he,hoff⟩
  have hg : 0 < g := norm_pos_iff.mpr (div_ne_zero he d.h_ne)
  have hl : 0 ≤ l := mul_nonneg hg.le hD
  have hden : 0 < den := Real.sqrt_pos.2 (by dsimp only [l,g,γ]; linarith)
  have hΦ : 0 ≤ endPhi d b e D := zero_le_one.trans (endPhi_one_le d b e D hD)
  have hF : 0 ≤ F := by dsimp only [F]; apply Finset.sum_nonneg; intro k hk; positivity
  have hA : 0 ≤ A := by dsimp only [A]; apply Finset.sum_nonneg; intro k hk; positivity
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hquot : g/Real.sqrt g=Real.sqrt g := by
    apply (div_eq_iff hsg.ne').2
    simpa only [pow_two] using (Real.sq_sqrt hg.le).symm
  have hf : ContinuousOn (fun t : ℝ => P d.ν (b+e*(t:ℂ))) (Icc 0 D) :=
    (d.continuous_P hpos).comp_continuousOn (by fun_prop)
  have hderiv (t : ℝ) (ht : t ∈ Ioo 0 D) :
      HasDerivAt (fun v : ℝ => P d.ν (b+e*(v:ℂ))) (segmentPathDerivative d b e t) t :=
    d.potential_path_hasDerivAt hpos b e t (hoff t ⟨ht.1,ht.2.le⟩)
  have hbnd (t : ℝ) (ht : t ∈ Ioo 0 D) :
      |segmentPathDerivative d b e t| ≤ (F*Real.sqrt g/den)/Real.sqrt t+A*g := by
    have hz : (b+e*(t:ℂ)-d.M)/d.h=ζ+γ*(t:ℂ) := by dsimp only [ζ,γ]; ring
    have hn := norm_jq_branch_lower ζ γ t D hε ⟨ht.1.le,ht.2.le⟩ hsmall
      (by rw [← hz]; exact hoff t ⟨ht.1,ht.2.le⟩)
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
    have hprod : 0 < Real.sqrt g*Real.sqrt t*den := by positivity
    have hn' : Real.sqrt g*Real.sqrt t*den ≤ ‖jq ((b+e*(t:ℂ)-d.M)/d.h)‖ := by
      simpa only [hz,g,den,l] using hn
    have hv := segmentPathDerivative_bound d b e D t hD ⟨ht.1.le,ht.2.le⟩
    have hh : g*(F/(Real.sqrt g*Real.sqrt t*den)+A)=
        (F*Real.sqrt g/den)/Real.sqrt t+A*g := by
      calc
        _ = (g/Real.sqrt g)*F/den/Real.sqrt t+A*g := by
          field_simp [hsg.ne',hst.ne',hden.ne'] <;> ring
        _ = _ := by rw [hquot]; ring
    rw [← hh]
    exact hv.trans (mul_le_mul_of_nonneg_left
      (add_le_add (div_le_div_of_nonneg_left hF hprod hn') (le_refl A)) hg.le)
  have he := holder_sqrt_derivative_bound _ (segmentPathDerivative d b e) D (F*Real.sqrt g/den) (A*g)
    hD (by positivity) (by positivity) hf hderiv hbnd
  intro τ hτ
  have ht := he τ hτ
  have hzero : b+e*((0:ℝ):ℂ)=b := by simp
  rw [hzero] at ht
  have hc : 2*(F*Real.sqrt g/den)*Real.sqrt D+(A*g)*D=endMajorant d b e D .branch := by
    change 2*(F*Real.sqrt g/den)*Real.sqrt D+(A*g)*D=F*(2*Real.sqrt (g*D)/den)+A*(g*D)
    rw [Real.sqrt_mul hg.le]
    ring
  rwa [hc] at ht

theorem holder_end_cell (d : SegmentData) (hpos : d.densityNonneg)
    (b e : ℂ) (D : ℝ) (hD : 0 ≤ D) (hsmall : ‖e/d.h‖*D < 1)
    (kind : EndCellKind) (hgeom : EndCellGeometry d b e D kind) :
    ∀ τ ∈ Icc 0 D,|P d.ν (b+e*(τ:ℂ))-P d.ν b| ≤ endMajorant d b e D kind := by
  cases kind with
  | own => exact holder_own_cell d hpos b e D hD hgeom
  | off => exact holder_off_cell d hpos b e D hD hgeom
  | branch => exact holder_branch_cell d hpos b e D hD hsmall hgeom
#print axioms holder_off_cell
#print axioms holder_branch_cell
#print axioms holder_end_cell
end
end CatalanCore.Li2.DecayCert
