module
public import CatalanCore.Uniform.Bank.Fifths.Cover.Check
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
public import CatalanCore.Uniform.Decay.AltFold
public import CatalanCore.Uniform.Bank.Plane1.Rows
public import CatalanCore.Uniform.Frame.NVAdapter
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Bound
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Bank.Fifths.Cover
  CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

def publicMu : ℚ := 59439/2500
theorem eta : bankData.Λ<Dchi.Dt := by decide +kernel
theorem cc_pos : (0:ℚ)<Dchi.ccert := by decide +kernel
theorem mu_strict : Dchi.ccert/(Dchi.Dt-bankData.Λ)<publicMu := by decide +kernel
theorem ratio_pos : 0<(Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ)) := by
  have hgap : (0:ℝ)<(Dchi.Dt:ℝ)-(bankData.Λ:ℝ) := by exact_mod_cast (sub_pos.mpr eta)
  have hcc : (0:ℝ)<(Dchi.ccert:ℝ) := by exact_mod_cast cc_pos
  exact div_pos hcc hgap

theorem tab_RP : TabC.RP=altPieces (2/9) := by decide +kernel
theorem tab_CP : TabC.CP=altPieces (2/9) := by decide +kernel
theorem tab_Mq : TabC.Mq=1+(2/9:ℚ)/2 := by decide +kernel
theorem energy_ok : energyCheck 30 (altPieces (2/9)) (altPieces (2/9)) Dchi.Inu=true := by decide +kernel
theorem dim_eq : Dchi.dim=2 := by decide +kernel
theorem eps_pos : 0<Dchi.ε := by decide +kernel

/-- Actual current refit rate and constant; no old Level3Measure rate is imported. -/
theorem decay_of_frame {Fr:Frame} (hC:Frame.contourCheck Fr=true)
    (hAR:∀ i:Fin Fr.d,((⌊Fr.xs-Fr.μ i⌋:ℤ):ℚ)+Fr.μ i≤Fr.n0off)
    (hnorm1:(1:ℚ)≤Fr.norm) (hd:Fr.d=2) (hm0:∀ i,(1/5:ℚ)≤Fr.μ i) (depth:ℕ) :
    HasScaledDecay ((altGeom (2/9) two_ninths_pos).family Fr depth) (altGeom (2/9) two_ninths_pos).scale
      (Dchi.Dt:ℝ) (Dchi.ccert:ℝ) :=
  altGeom_hasScaledDecay_F (2/9) two_ninths_pos (by norm_num) hC hAR hnorm1 TabC tab_RP tab_CP tab_Mq
    Dchi Pply check_true (by rw [dim_eq,hd]) 30 energy_ok (m0:=1/5) (by norm_num)
    (fun i => by
      have h : (((1/5:ℚ):ℝ)) ≤ (Fr.μ i:ℝ) := Rat.cast_le.mpr (hm0 i)
      norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
      exact h) eps_pos depth

noncomputable def depth0 (Fr:Frame) : ℕ := (altGeom (2/9) two_ninths_pos).selectionDepth Fr 2
theorem depth0_le {Fr:Frame} (hd:Fr.d=2) : depth0 Fr≤64 := by
  unfold depth0 BlockGeom.selectionDepth
  rw [hd]
  decide +kernel

theorem nv0_even (Fr:Frame) (hd:1≤Fr.d) (hw:∀ i,Fr.w i≠0) :
    ∃ R0:ℕ,∀ s:ℕ,R0≤s → ∀ x:ℚ,∃ n,
      (((altGeom (2/9) two_ninths_pos).family Fr (depth0 Fr)).restrictAdm (fun i=>i.1%2=0)).Adm n ∧
      (altGeom (2/9) two_ninths_pos).scale n=2*s ∧
      (((altGeom (2/9) two_ninths_pos).family Fr (depth0 Fr)).restrictAdm (fun i=>i.1%2=0)).evalQ n x≠0 := by
  have hnv := (altGeom (2/9) two_ninths_pos).hasNV0 Fr 2 (depth0 Fr) (by norm_num) hd hw
    (fun i=>by simp [altGeom,single,commonB])
    (fun i=>by simp [altGeom,single,rowB])
    (fun i=>by simp [altGeom,single,colB]) le_rfl
  obtain ⟨R0,hR⟩:=hnv
  refine ⟨R0,fun s hs x=>?_⟩
  obtain ⟨n,hn,hsc,hne⟩:=hR (2*s) (by omega) x
  exact ⟨n,⟨hn,by have hscale:(altGeom (2/9) two_ninths_pos).scale n=n.1:=rfl;omega⟩,hsc,hne⟩

theorem point_of_frame (Fr:Frame) (hd:1≤Fr.d) (hw:∀ i,Fr.w i≠0)
    {ξ:ℝ} {u v:ℚ} (hu:u≠0) (hconst:Fr.const=(u:ℝ)*ξ+v)
    (hS:HasScaledContent (CatalanCore.Uniform.Content.BankShared.Check.AltEven (2/9) two_ninths_pos Fr (depth0 Fr)) (altGeom (2/9) two_ninths_pos).scale (bankData.Λ:ℝ))
    (hD:HasScaledDecay ((altGeom (2/9) two_ninths_pos).family Fr (depth0 Fr)) (altGeom (2/9) two_ninths_pos).scale (Dchi.Dt:ℝ) (Dchi.ccert:ℝ)) :
    Measure.MeasureLBAt ξ ((Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))) ∧ Irrational ξ :=
  CatalanCore.Uniform.Bank.Plane1.alt_point (2/9) two_ninths_pos Fr (depth0 Fr) hS hD
    (by exact_mod_cast eta) (by exact_mod_cast cc_pos) (nv0_even Fr hd hw) hu hconst

theorem mu_le_real : (Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))≤(publicMu:ℝ) := by
  exact_mod_cast (le_of_lt mu_strict)

theorem fifths1_decay : HasScaledDecay ((altGeom (2/9) two_ninths_pos).family fifths1 (depth0 fifths1))
    (altGeom (2/9) two_ninths_pos).scale (Dchi.Dt:ℝ) (Dchi.ccert:ℝ) :=
  decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) _
theorem fifths1_point_exact : Measure.MeasureLBAt (fifthsTarget 1)
    ((Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))) ∧ Irrational (fifthsTarget 1) :=
  point_of_frame fifths1 (by decide +kernel) (by decide +kernel) (u:=-1/25) (v:=0) (by norm_num)
    (by simpa only [Rat.cast_zero,add_zero] using fifths1_const) (fifths1_content_auto _ (depth0_le (Fr:=fifths1) rfl)) fifths1_decay
theorem fifths1_point : Measure.MeasureLBAt (fifthsTarget 1) (publicMu:ℝ) ∧ Irrational (fifthsTarget 1) :=
  ⟨Measure.MeasureLBAt.mono mu_le_real fifths1_point_exact.1,fifths1_point_exact.2⟩
theorem fifths1_measure : Measure.MeasureLBAt (fifthsTarget 1) (publicMu:ℝ) := fifths1_point.1

theorem fifths2_decay : HasScaledDecay ((altGeom (2/9) two_ninths_pos).family fifths2 (depth0 fifths2))
    (altGeom (2/9) two_ninths_pos).scale (Dchi.Dt:ℝ) (Dchi.ccert:ℝ) :=
  decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) _
theorem fifths2_point_exact : Measure.MeasureLBAt (fifthsTarget 2)
    ((Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))) ∧ Irrational (fifthsTarget 2) :=
  point_of_frame fifths2 (by decide +kernel) (by decide +kernel) (u:=-1/25) (v:=0) (by norm_num)
    (by simpa only [Rat.cast_zero,add_zero] using fifths2_const) (fifths2_content_auto _ (depth0_le (Fr:=fifths2) rfl)) fifths2_decay
theorem fifths2_point : Measure.MeasureLBAt (fifthsTarget 2) (publicMu:ℝ) ∧ Irrational (fifthsTarget 2) :=
  ⟨Measure.MeasureLBAt.mono mu_le_real fifths2_point_exact.1,fifths2_point_exact.2⟩
theorem fifths2_measure : Measure.MeasureLBAt (fifthsTarget 2) (publicMu:ℝ) := fifths2_point.1

theorem fifths3_decay : HasScaledDecay ((altGeom (2/9) two_ninths_pos).family fifths3 (depth0 fifths3))
    (altGeom (2/9) two_ninths_pos).scale (Dchi.Dt:ℝ) (Dchi.ccert:ℝ) :=
  decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) _
theorem fifths3_point_exact : Measure.MeasureLBAt (fifthsTarget 3)
    ((Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))) ∧ Irrational (fifthsTarget 3) :=
  point_of_frame fifths3 (by decide +kernel) (by decide +kernel) (u:=-1/25) (v:=0) (by norm_num)
    (by simpa only [Rat.cast_zero,add_zero] using fifths3_const) (fifths3_content_auto _ (depth0_le (Fr:=fifths3) rfl)) fifths3_decay
theorem fifths3_point : Measure.MeasureLBAt (fifthsTarget 3) (publicMu:ℝ) ∧ Irrational (fifthsTarget 3) :=
  ⟨Measure.MeasureLBAt.mono mu_le_real fifths3_point_exact.1,fifths3_point_exact.2⟩
theorem fifths3_measure : Measure.MeasureLBAt (fifthsTarget 3) (publicMu:ℝ) := fifths3_point.1

theorem fifths4_decay : HasScaledDecay ((altGeom (2/9) two_ninths_pos).family fifths4 (depth0 fifths4))
    (altGeom (2/9) two_ninths_pos).scale (Dchi.Dt:ℝ) (Dchi.ccert:ℝ) :=
  decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) _
theorem fifths4_point_exact : Measure.MeasureLBAt (fifthsTarget 4)
    ((Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))) ∧ Irrational (fifthsTarget 4) :=
  point_of_frame fifths4 (by decide +kernel) (by decide +kernel) (u:=-1/25) (v:=0) (by norm_num)
    (by simpa only [Rat.cast_zero,add_zero] using fifths4_const) (fifths4_content_auto _ (depth0_le (Fr:=fifths4) rfl)) fifths4_decay
theorem fifths4_point : Measure.MeasureLBAt (fifthsTarget 4) (publicMu:ℝ) ∧ Irrational (fifthsTarget 4) :=
  ⟨Measure.MeasureLBAt.mono mu_le_real fifths4_point_exact.1,fifths4_point_exact.2⟩
theorem fifths4_measure : Measure.MeasureLBAt (fifthsTarget 4) (publicMu:ℝ) := fifths4_point.1

end CatalanCore.Uniform.Bank.FifthsContent.Level3Bound
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.eta
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.cc_pos
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.mu_strict
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.nv0_even
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.point_of_frame
