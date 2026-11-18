module
public import CatalanCore.Li2.DecayCert.Lattice.Stieltjes.ArcMoments
public import CatalanCore.Li2.DecayCert.Density.Source
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open MeasureTheory Set Polynomial
open scoped BigOperators
open CatalanCore.Zeta5.Potential CatalanCore.Tools.Joukowski
namespace CatalanCore.Li2.DecayCert

private theorem density_real_eval_all (d : QSegment) (x : ℝ) :
    (d.density.map (Rat.castHom ℝ)).eval x=
      chebF (fun k : ℕ => (d.c k:ℝ)) (d.coeff.length-1) x := by
  by_cases hl : 0<d.coeff.length
  · exact density_real_eval d hl x
  · have he : d.coeff=[] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_not_pos hl)
    simp [QSegment.density,he,chebF,QSegment.c]

/-- Exact source identity, including k=0 and the zero density. -/
theorem inverseMoment_stieltjesQ (d : QSegment) (φ : ℚ) (hφ : 1<φ)
    (hhalf : 0<d.half.1)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,
      0≤chebF (fun k : ℕ => (d.c k:ℝ)) (d.coeff.length-1) x) (k : ℕ) :
    inverseMoment d.measure
      (((d.mid.1-d.half.1*((φ+φ⁻¹)/2):ℚ):ℝ)) k=(stieltjesQ d φ k:ℝ) := by
  let ξ : ℚ := (φ+φ⁻¹)/2
  let B : ℚ[X] := d.density.comp (Polynomial.X-Polynomial.C ξ)
  have hg : Measurable (fun s : ℂ =>
      (s.re-((d.mid.1-d.half.1*ξ:ℚ):ℝ))^(-(k:ℤ))) := by fun_prop
  have hsource : inverseMoment d.measure (((d.mid.1-d.half.1*ξ:ℚ):ℝ)) k=
      ∫ θ, (d.density.map (Rat.castHom ℝ)).eval (Real.cos θ)*
        ((d.half.1:ℝ)*((ξ:ℝ)+Real.cos θ))^(-(k:ℤ)) ∂arc := by
    unfold inverseMoment
    change (∫ s, (s.re-((d.mid.1-d.half.1*ξ:ℚ):ℝ))^(-(k:ℤ))
      ∂(segMeasure (cqReal d.mid) (cqReal d.half)
        (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1)))=_
    rw [integral_segMeasure hpos hg]
    apply integral_congr_ae (ae_of_all _ ?_)
    intro θ
    rw [← density_real_eval_all]
    congr 2
    simp [cqReal]
    rw [← Complex.ofReal_cos]
    simp only [Complex.ofReal_re]
    ring
  have hB (θ : ℝ) :
      (B.map (Rat.castHom ℝ)).eval ((ξ:ℝ)-Real.cos θ)=
        (d.density.map (Rat.castHom ℝ)).eval (-Real.cos θ) := by
    simp only [B,Polynomial.eval_map,Polynomial.eval₂_comp,
      Polynomial.eval₂_sub,Polynomial.eval₂_X,Polynomial.eval₂_C]
    congr 1
    change (ξ:ℝ)-Real.cos θ-(ξ:ℝ)=-Real.cos θ
    ring
  have hreflect :
      (∫ θ, (d.density.map (Rat.castHom ℝ)).eval (Real.cos θ)*
        ((d.half.1:ℝ)*((ξ:ℝ)+Real.cos θ))^(-(k:ℤ)) ∂arc)=
      (d.half.1:ℝ)^(-(k:ℤ))*(∫ θ,
        (B.map (Rat.castHom ℝ)).eval ((ξ:ℝ)-Real.cos θ)*
          ((ξ:ℝ)-Real.cos θ)^(-(k:ℤ)) ∂arc) := by
    rw [← arc_reflection (fun θ => (d.density.map (Rat.castHom ℝ)).eval (Real.cos θ)*
      ((d.half.1:ℝ)*((ξ:ℝ)+Real.cos θ))^(-(k:ℤ)))]
    rw [← integral_const_mul]
    apply integral_congr_ae (ae_of_all _ ?_)
    intro θ
    rw [Real.cos_pi_sub,← sub_eq_add_neg,mul_zpow,hB]
    ring
  change inverseMoment d.measure (((d.mid.1-d.half.1*ξ:ℚ):ℝ)) k=_
  rw [hsource,hreflect,arc_shift_polynomial B φ hφ k]
  unfold stieltjesQ
  push_cast
  rfl

#print axioms inverseMoment_stieltjesQ
end CatalanCore.Li2.DecayCert
