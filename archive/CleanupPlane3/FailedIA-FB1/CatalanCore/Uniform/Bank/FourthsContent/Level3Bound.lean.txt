module
public import CatalanCore.Uniform.Bank.Fourths.Cover.Check
public import CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
public import CatalanCore.Uniform.Decay.AltFold
public import CatalanCore.Uniform.Bank.Plane1.Rows
public import CatalanCore.Uniform.Frame.NVAdapter
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.FourthsContent.Level3Bound
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.Fourths CatalanCore.Uniform.Bank.Fourths.Cover
  CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

def publicMu : ℚ := 311973/10000
theorem eta : bankData.Λ<Dchi.Dt := by decide +kernel
theorem cc_pos : (0:ℚ)<Dchi.ccert := by decide +kernel
theorem mu_strict : Dchi.ccert/(Dchi.Dt-bankData.Λ)<publicMu := by decide +kernel
theorem ratio_pos : 0<(Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ)) := by
  have hgap : (0:ℝ)<(Dchi.Dt:ℝ)-(bankData.Λ:ℝ) := by exact_mod_cast (sub_pos.mpr eta)
  have hcc : (0:ℝ)<(Dchi.ccert:ℝ) := by exact_mod_cast cc_pos
  exact div_pos hcc hgap

theorem tab_RP : TabC.RP=altPieces (1/5) := by decide +kernel
theorem tab_CP : TabC.CP=altPieces (1/5) := by decide +kernel
theorem tab_Mq : TabC.Mq=1+(1/5:ℚ)/2 := by decide +kernel
theorem energy_ok : energyCheck 30 (altPieces (1/5)) (altPieces (1/5)) Dchi.Inu=true := by decide +kernel
theorem dim_eq : Dchi.dim=2 := by decide +kernel
theorem eps_pos : 0<Dchi.ε := by decide +kernel

/-- Actual current refit rate and constant; no old Level3Measure rate is imported. -/
theorem decay_of_frame {Fr:Frame} (hC:Frame.contourCheck Fr=true)
    (hAR:∀ i:Fin Fr.d,((⌊Fr.xs-Fr.μ i⌋:ℤ):ℚ)+Fr.μ i≤Fr.n0off)
    (hnorm1:(1:ℚ)≤Fr.norm) (hd:Fr.d=2) (hm0:∀ i,(1/4:ℚ)≤Fr.μ i) (depth:ℕ) :
    HasScaledDecay ((altGeom (1/5) one_fifth_pos).family Fr depth) (altGeom (1/5) one_fifth_pos).scale
      (Dchi.Dt:ℝ) (Dchi.ccert:ℝ) :=
  altGeom_hasScaledDecay_F (1/5) one_fifth_pos (by norm_num) hC hAR hnorm1 TabC tab_RP tab_CP tab_Mq
    Dchi Pply check_true (by rw [dim_eq,hd]) 30 energy_ok (m0:=1/4) (by norm_num)
    (fun i => by exact_mod_cast hm0 i) eps_pos depth

noncomputable def depth0 (Fr:Frame) : ℕ := (altGeom (1/5) one_fifth_pos).selectionDepth Fr 2
theorem depth0_le {Fr:Frame} (hd:Fr.d=2) : depth0 Fr≤64 := by
  unfold depth0 BlockGeom.selectionDepth
  rw [hd]
  decide +kernel

theorem nv0_even (Fr:Frame) (hd:1≤Fr.d) (hw:∀ i,Fr.w i≠0) :
    ∃ R0:ℕ,∀ s:ℕ,R0≤s → ∀ x:ℚ,∃ n,
      (((altGeom (1/5) one_fifth_pos).family Fr (depth0 Fr)).restrictAdm (fun i=>i.1%2=0)).Adm n ∧
      (altGeom (1/5) one_fifth_pos).scale n=2*s ∧
      (((altGeom (1/5) one_fifth_pos).family Fr (depth0 Fr)).restrictAdm (fun i=>i.1%2=0)).evalQ n x≠0 := by
  have hnv := (altGeom (1/5) one_fifth_pos).hasNV0 Fr 2 (depth0 Fr) (by norm_num) hd hw
    (fun i=>by simp [altGeom,single,commonB])
    (fun i=>by simp [altGeom,single,rowB])
    (fun i=>by simp [altGeom,single,colB]) le_rfl
  obtain ⟨R0,hR⟩:=hnv
  refine ⟨R0,fun s hs x=>?_⟩
  obtain ⟨n,hn,hsc,hne⟩:=hR (2*s) (by omega) x
  exact ⟨n,⟨hn,by have hscale:(altGeom (1/5) one_fifth_pos).scale n=n.1:=rfl;omega⟩,hsc,hne⟩

theorem point_of_frame (Fr:Frame) (hd:1≤Fr.d) (hw:∀ i,Fr.w i≠0)
    {ξ:ℝ} {u v:ℚ} (hu:u≠0) (hconst:Fr.const=(u:ℝ)*ξ+v)
    (hS:HasScaledContent (AltEven (1/5) one_fifth_pos Fr (depth0 Fr)) (altGeom (1/5) one_fifth_pos).scale (bankData.Λ:ℝ))
    (hD:HasScaledDecay ((altGeom (1/5) one_fifth_pos).family Fr (depth0 Fr)) (altGeom (1/5) one_fifth_pos).scale (Dchi.Dt:ℝ) (Dchi.ccert:ℝ)) :
    Measure.MeasureLBAt ξ ((Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))) ∧ Irrational ξ :=
  CatalanCore.Uniform.Bank.Plane1.alt_point (1/5) one_fifth_pos Fr (depth0 Fr) hS hD
    (by exact_mod_cast eta) (by exact_mod_cast cc_pos) (nv0_even Fr hd hw) hu hconst

theorem mu_le_real : (Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))≤(publicMu:ℝ) := by
  exact_mod_cast (le_of_lt mu_strict)

theorem lambda_decay (sgn:Bool) : HasScaledDecay ((altGeom (1/5) one_fifth_pos).family (lambdaFrame sgn) (depth0 (lambdaFrame sgn)))
    (altGeom (1/5) one_fifth_pos).scale (Dchi.Dt:ℝ) (Dchi.ccert:ℝ) := by
  cases sgn <;> exact decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) _
theorem lambda_content (sgn:Bool) : HasScaledContent (AltEven (1/5) one_fifth_pos (lambdaFrame sgn) (depth0 (lambdaFrame sgn)))
    (altGeom (1/5) one_fifth_pos).scale (bankData.Λ:ℝ) := by
  cases sgn
  · exact lamMinus_content_auto _ (depth0_le (lambdaFrame_d false))
  · exact lamPlus_content_auto _ (depth0_le (lambdaFrame_d true))
theorem lambda_point_exact (sgn:Bool) : Measure.MeasureLBAt (lambdaTarget sgn)
    ((Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))) ∧ Irrational (lambdaTarget sgn) :=
  point_of_frame (lambdaFrame sgn) (by rw [lambdaFrame_d];norm_num) (lambdaFrame_w_ne sgn)
    (u:=1/2) (v:=0) (by norm_num) (by simpa only [add_zero] using lambdaFrame_const sgn)
    (lambda_content sgn) (lambda_decay sgn)
theorem lambda_point (sgn:Bool) : Measure.MeasureLBAt (lambdaTarget sgn) (publicMu:ℝ) ∧ Irrational (lambdaTarget sgn) :=
  ⟨Measure.MeasureLBAt.mono mu_le_real (lambda_point_exact sgn).1,(lambda_point_exact sgn).2⟩
theorem lambda_measure (sgn:Bool) : Measure.MeasureLBAt (lambdaTarget sgn) (publicMu:ℝ) := (lambda_point sgn).1

end CatalanCore.Uniform.Bank.FourthsContent.Level3Bound
#print axioms CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.eta
#print axioms CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.cc_pos
#print axioms CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.mu_strict
#print axioms CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.nv0_even
#print axioms CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.point_of_frame
