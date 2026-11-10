module

public import CatalanCore.Uniform.Bank.Plane3.Numerics
public import CatalanCore.Uniform.Bank.Plane3.Decay
public import CatalanCore.Uniform.Bank.Plane3.Content

@[expose] public section
set_option Elab.async false

/-! The third-plane point instance uses full refined content, full jet
decay and general NV. Every rational coefficient pair with b nonzero is covered. -/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Measure CatalanCore.Uniform CatalanCore.Uniform.Support
open CatalanCore.Uniform.Content.Shape

theorem plane3_point_nonzero_b (a b : ℚ) (hb : b≠0) :
    MeasureLBAt ((a:ℝ)*(riemannZeta 3).re+(b:ℝ)*Real.pi^4) (p3Cert.cr/(p3Cert.Dr-(p3Lam:ℝ))) ∧
      Irrational ((a:ℝ)*(riemannZeta 3).re+(b:ℝ)*Real.pi^4) := by
  have hu : (15:ℚ)*b≠0 := mul_ne_zero (by norm_num) hb
  let F := P3G.seqFamily (datum (-a/2) (15*b) hu).f
    (datum (-a/2) (15*b) hu).e (datum (-a/2) (15*b) hu).xi 1
  have hcontent : HasScaledContent
      (F.restrictAdm (fun n => SeqFamily.scale P3G.geometry n%2=0))
      (SeqFamily.scale P3G.geometry) (p3Lam:ℝ) := plane3_content (-a/2) (15*b) hu 1
  have hdecay : HasScaledDecay F (SeqFamily.scale P3G.geometry) p3Cert.Dr p3Cert.cr :=
    plane3_decay (-a/2) (15*b) hu (13/100) p3c_pos (by norm_num)
      p3Cert p3_negative p3_spline_mass p3_dim p3_node_energy p3_eps 1
  have hdeg : ∀ n,F.Adm n → (F.deg n:ℝ)≤1*SeqFamily.scale P3G.geometry n+(P3G.common.n:ℝ) := by
    intro n _
    have h := P3G.seq_degree_bound (datum (-a/2) (15*b) hu).f
      (datum (-a/2) (15*b) hu).e (datum (-a/2) (15*b) hu).xi 1 n
    rw [p3_common_mass,Rat.cast_one,one_mul] at h
    simpa only [one_mul] using h
  have hconst : F.const=(1:ℚ)*((a:ℝ)*(riemannZeta 3).re+(b:ℝ)*Real.pi^4)+(0:ℚ) := by
    change (datum (-a/2) (15*b) hu).xi=_
    rw [datum_xi]
    push_cast
    ring
  have hη : (p3Lam:ℝ)<p3Cert.Dr := by exact_mod_cast p3_eta
  have hcc : 0<p3Cert.cr := by exact_mod_cast p3_cc
  have hnv := datum_nv (-a/2) (15*b) hu (13/100) p3c_pos 1 (by decide)
  have key := support_measureLB F (SeqFamily.scale P3G.geometry) hcontent hdecay hη hcc
    one_pos (Nat.cast_nonneg _) hdeg hnv (a:=1) (b:=0) (by norm_num) hconst
  simpa only [one_mul] using key

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_point_nonzero_b
