module

public import CatalanCore.Uniform.Bank.Plane3.Frame
public import CatalanCore.Uniform.Bank.Plane3.Numerics
public import CatalanCore.Uniform.Bank.Plane3.Decay

@[expose] public section
set_option Elab.async false

/-! Dedicated pure endpoint wiring. The exact content mass is a parameter;
the full accepted order-three decay and support theorem are consumed unchanged. -/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Measure CatalanCore.Uniform CatalanCore.Uniform.Support
open CatalanCore.Uniform.Content.Shape

noncomputable def pi4Datum := datum (0 : ℚ) 15 (by norm_num)
noncomputable def pi4Family := P3G.seqFamily pi4Datum.f pi4Datum.e pi4Datum.xi 1

theorem pi4Datum_xi : pi4Datum.xi = Real.pi^4 := by
  rw [pi4Datum,datum_xi]
  push_cast
  ring

theorem pi4_point_of_content (Λ : ℚ)
    (hcontent : HasScaledContent
      (pi4Family.restrictAdm (fun n => SeqFamily.scale P3G.geometry n%2=0))
      (SeqFamily.scale P3G.geometry) (Λ:ℝ))
    (hη : (Λ:ℝ)<p3Cert.Dr) :
    MeasureLBAt (Real.pi^4) (p3Cert.cr/(p3Cert.Dr-(Λ:ℝ))) ∧
      Irrational (Real.pi^4) := by
  have hdecay : HasScaledDecay pi4Family (SeqFamily.scale P3G.geometry) p3Cert.Dr p3Cert.cr :=
    plane3_decay 0 15 (by norm_num) (1/10) p3c_pos (by norm_num)
      p3Cert p3_negative p3_spline_mass p3_dim p3_node_energy p3_eps 1
  have hdeg : ∀ n,pi4Family.Adm n →
      (pi4Family.deg n:ℝ)≤1*SeqFamily.scale P3G.geometry n+(P3G.common.n:ℝ) := by
    intro n _
    have h := P3G.seq_degree_bound pi4Datum.f pi4Datum.e pi4Datum.xi 1 n
    rw [p3_common_mass,Rat.cast_one,one_mul] at h
    simpa only [pi4Family,one_mul] using h
  have hconst : pi4Family.const=(1:ℚ)*(Real.pi^4)+(0:ℚ) := by
    change pi4Datum.xi=_
    rw [pi4Datum_xi]
    norm_num
  have hcc : 0<p3Cert.cr := by exact_mod_cast p3_cc
  have hnv := datum_nv 0 15 (by norm_num) (1/10) p3c_pos 1 (by decide)
  have key := support_measureLB pi4Family (SeqFamily.scale P3G.geometry) hcontent hdecay hη hcc
    one_pos (Nat.cast_nonneg _) hdeg hnv (a:=1) (b:=0) (by norm_num) hconst
  simpa only [one_mul] using key

theorem pi4_final_of_content (Λ M : ℚ)
    (hcontent : HasScaledContent
      (pi4Family.restrictAdm (fun n => SeqFamily.scale P3G.geometry n%2=0))
      (SeqFamily.scale P3G.geometry) (Λ:ℝ))
    (hη : Λ<Cover.Dchi.Dt)
    (hratio : Cover.Dchi.ccert/(Cover.Dchi.Dt-Λ)<M) :
    ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
      (q:ℝ)^(-(M:ℝ))< |Real.pi^4-(p:ℝ)/q| := by
  have hηr : (Λ:ℝ)<p3Cert.Dr := by exact_mod_cast hη
  have hcc : 0<p3Cert.cr := by exact_mod_cast p3_cc
  have key := pi4_point_of_content Λ hcontent hηr
  let E := p3Cert.cr/(p3Cert.Dr-(Λ:ℝ))
  have hE : 0≤E := (div_pos hcc (sub_pos.mpr hηr)).le
  have hlt : E<(M:ℝ) := by
    change ((Cover.Dchi.ccert:ℚ):ℝ)/(((Cover.Dchi.Dt:ℚ):ℝ)-(Λ:ℝ))<(M:ℝ)
    exact_mod_cast hratio
  obtain ⟨q0,hq⟩ := MeasureLBAt.all_of_irrational hE key.2 key.1 ((M:ℝ)-E) (sub_pos.mpr hlt)
  filter_upwards [Filter.eventually_ge_atTop q0] with q hqq p
  have h := hq p q hqq
  simpa only [show E+((M:ℝ)-E)=(M:ℝ) by ring] using h

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_point_of_content
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_final_of_content
