module

public import CatalanCore.Uniform.Bank.Plane3.Point
public import CatalanCore.Uniform.Bank.Plane2.Measure
public import CatalanCore.Uniform.Bank.Plane2.Zeta3

@[expose] public section
set_option Elab.async false

/-! Public all-fraction third-plane bound. The b=0 endpoint reuses Z03;
the b!=0 family retains its exact exponent until the final epsilon removal. -/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Measure CatalanCore.Uniform

theorem plane3_final (a b : ℚ) (hab : a≠0 ∨ b≠0) :
    ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
      (q:ℝ)^(-(72.84:ℝ))< |((a:ℝ)*(riemannZeta 3).re+(b:ℝ)*Real.pi^4)-(p:ℝ)/q| := by
  have hex : ∃ E : ℝ,0≤E ∧ E<72.84 ∧
      MeasureLBAt ((a:ℝ)*(riemannZeta 3).re+(b:ℝ)*Real.pi^4) E ∧
      Irrational ((a:ℝ)*(riemannZeta 3).re+(b:ℝ)*Real.pi^4) := by
    by_cases hb : b=0
    · subst b
      have ha : a≠0 := by simpa using hab
      have hz : Irrational (riemannZeta 3).re := by
        simpa using (Plane2.plane2_measure 1 0 (Or.inl one_ne_zero)).2
      have hm := Plane2.zeta3_measure.affine (by norm_num : (0:ℝ)≤((60382/10000:ℚ):ℝ)) a 0 ha
      have hi := irrational_affine hz a 0 ha
      refine ⟨((60382/10000:ℚ):ℝ),by norm_num,by norm_num,?_,?_⟩
      · simpa using hm
      · simpa using hi
    · have key := plane3_point_nonzero_b a b hb
      have hη : (p3Lam:ℝ)<p3Cert.Dr := by exact_mod_cast p3_eta
      have hcc : 0<p3Cert.cr := by exact_mod_cast p3_cc
      refine ⟨p3Cert.cr/(p3Cert.Dr-(p3Lam:ℝ)),(div_pos hcc (sub_pos.mpr hη)).le,?_,key.1,key.2⟩
      change ((Cover.Dchi.ccert:ℚ):ℝ)/(((Cover.Dchi.Dt:ℚ):ℝ)-(p3Lam:ℝ))<72.84
      have hrat : Cover.Dchi.ccert/(Cover.Dchi.Dt-p3Lam)<(1821/25:ℚ) := by
        convert p3_ratio using 1 <;> norm_num
      have hreal := (Rat.cast_lt (K:=ℝ)).2 hrat
      push_cast at hreal
      convert hreal using 1 <;> norm_num
  obtain ⟨E,hE,hlt,hm,hi⟩ := hex
  obtain ⟨q0,hq⟩ := MeasureLBAt.all_of_irrational hE hi hm (72.84-E) (sub_pos.mpr hlt)
  filter_upwards [Filter.eventually_ge_atTop q0] with q hqq p
  have h := hq p q hqq
  simpa only [show E+(72.84-E)=72.84 by ring] using h

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_final
