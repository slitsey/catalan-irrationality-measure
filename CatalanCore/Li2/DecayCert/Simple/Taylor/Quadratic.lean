module
public import CatalanCore.Li2.DecayCert.Simple.Taylor.Defs
public import CatalanCore.Li2.DecayCert.Lattice.Simple.Fixed
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanMeasure.GenD.Signed.TaylorCell
noncomputable section
 theorem qmaxF_sound (a1 a2 R : ℤ) (u : ℝ) (hu : |u|≤dec S R) :
    dec S a1*u+dec S a2*u^2≤dec S (qmaxF a1 a2 R) := by
  have hq:=quad_le_quadSupR (a1:ℝ) (a2:ℝ) (dec S R) u hu
  have hS:=S_real_pos
  have hSS : (0:ℤ)<S*S := mul_pos S_pos S_pos
  have heplus:=ceilDiv_ge (a1*R*S+a2*R*R) (S*S) hSS.ne'
  have heminus:=ceilDiv_ge (-a1*R*S+a2*R*R) (S*S) hSS.ne'
  have hpEq : ((a1*R*S+a2*R*R:ℤ):ℝ)/((S*S:ℤ):ℝ)=
      (a1:ℝ)*dec S R+(a2:ℝ)*(dec S R)^2 := by
    unfold dec; push_cast; field_simp
  have hmEq : ((-a1*R*S+a2*R*R:ℤ):ℝ)/((S*S:ℤ):ℝ)=
      -(a1:ℝ)*dec S R+(a2:ℝ)*(dec S R)^2 := by
    unfold dec; push_cast; field_simp
  rw [hpEq] at heplus
  rw [hmEq] at heminus
  have hguard : (a2<0 ∧ |a1| *S≤-2*a2*R) ↔
      ((a2:ℝ)<0 ∧ |(a1:ℝ)|≤-2*(a2:ℝ)*dec S R) := by
    constructor
    · rintro ⟨h1,h2⟩
      refine ⟨by exact_mod_cast h1,?_⟩
      have h2R : |(a1:ℝ)| *(S:ℝ)≤-2*(a2:ℝ)*(R:ℝ) := by exact_mod_cast h2
      unfold dec
      rw [←mul_div_assoc]
      exact (le_div_iff₀ hS).2 h2R
    · rintro ⟨h1,h2⟩
      refine ⟨by exact_mod_cast h1,?_⟩
      have h2R : |(a1:ℝ)| *(S:ℝ)≤-2*(a2:ℝ)*(R:ℝ) := by
        apply (le_div_iff₀ hS).mp
        simpa only [dec,mul_div_assoc] using h2
      exact_mod_cast h2R
  have habs (a : ℤ) : absI a=|a| := by simp [absI,abs_eq_max_neg]
  have hfinal : (a1:ℝ)*u+(a2:ℝ)*u^2≤(qmaxF a1 a2 R:ℝ) := by
    unfold qmaxF
    simp only [habs]
    split_ifs with h
    · rw [quadSupR,ite_eq_left (hguard.mp h)] at hq
      have hv:=ceilDiv_ge (a1*a1) (-4*a2) (by omega)
      have hvEq : ((a1*a1:ℤ):ℝ)/((-4*a2:ℤ):ℝ)=(a1:ℝ)^2/(-4*(a2:ℝ)) := by push_cast; ring
      rw [hvEq] at hv
      exact (hq.trans hv).trans (by exact_mod_cast (le_max_right
        (max (ceilDiv (a1*R*S+a2*R*R) (S*S)) (ceilDiv (-a1*R*S+a2*R*R) (S*S)))
        (ceilDiv (a1*a1) (-4*a2))))
    · rw [quadSupR,ite_eq_right (fun hg=>h (hguard.mpr hg))] at hq
      simp only [Int.cast_max]
      rcases le_total 0 (a1:ℝ) with ha|ha
      · rw [abs_of_nonneg ha] at hq
        exact (hq.trans heplus).trans (le_max_left _ _)
      · rw [abs_of_nonpos ha] at hq
        exact (hq.trans heminus).trans (le_max_right _ _)
  unfold dec
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div,←add_div]
  exact div_le_div_of_nonneg_right hfinal hS.le
#print axioms qmaxF_sound
end
end CatalanCore.Li2.DecayCert.Simple
