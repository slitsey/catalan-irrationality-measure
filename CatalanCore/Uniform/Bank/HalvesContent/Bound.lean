module
public import CatalanCore.Uniform.Bank.Halves.Cover.Check
public import CatalanCore.Uniform.Decay.AltFold
public import CatalanCore.Uniform.Bank.HalvesContent.Auto
public import CatalanCore.Uniform.Bank.Halves.NV
public import CatalanCore.Uniform.Bank.Plane1.Rows
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.HalvesContent.Bound
open CatalanCore CatalanCore.Uniform CatalanCore.Measure CatalanCore.Uniform.Bank.Halves
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.HalvesContent.Auto
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Bank.Halves.Cover
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; exact two-piece geometry bindings, no physical cell rechecks.
theorem tab_RP : TabC.RP = altPieces (3/10) := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; exact two-piece geometry binding.
theorem tab_CP : TabC.CP = altPieces (3/10) := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one rational equality.
theorem tab_Mq : TabC.Mq = 1+(3/10:ℚ)/2 := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; four node-pair contributions,30 log terms each; independent node energy retained.
theorem energy_ok : energyCheck 30 (altPieces (3/10)) (altPieces (3/10)) Dchi.Inu=true := by
  -- kcost: 1.0 s C forecast, N30 two-piece node energy class measured0.26s in Plane2.Bound.
  decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one natural equality.
theorem dim_eq : Dchi.dim=2 := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one scalar comparison.
theorem eps_pos : 0<Dchi.ε := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one scalar comparison.
theorem cc_pos : 0<Dchi.ccert := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one scalar comparison, accepted full content mass reused.
theorem lam_lt : bankData.Λ<Dchi.Dt := by rw [bankData_Λ];decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; exact scalar division, no content/cell rechecks.
theorem mu_strict : Dchi.ccert/(Dchi.Dt-bankData.Λ)<(65253/10000:ℚ) := by
  rw [bankData_Λ];decide +kernel
theorem m0_le : ∀ i,(1/2:ℝ)≤halves.μ i := by
  intro i;fin_cases i
  · show (1/2:ℝ)≤((1/2:ℚ):ℝ);norm_num
  · show (1/2:ℝ)≤((1:ℚ):ℝ);norm_num
theorem decay (depth : ℕ) :
    HasScaledDecay (FH.family halves depth) FH.scale (Dchi.Dt:ℝ) (Dchi.ccert:ℝ) :=
  altGeom_hasScaledDecay_F (3/10) three_tenths_pos (by norm_num)
    (Fr:=halves) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    TabC tab_RP tab_CP tab_Mq Dchi Pply check_true (by rw [dim_eq];rfl)
    30 energy_ok (m0:=1/2) (by norm_num) m0_le eps_pos depth
theorem pi2_point_exact :
    MeasureLBAt (Real.pi^2) ((Dchi.ccert:ℝ)/((Dchi.Dt:ℝ)-(bankData.Λ:ℝ))) ∧
      Irrational (Real.pi^2) := by
  have hd : FH.selectionDepth halves 2 ≤ 64 := by
    unfold BlockGeom.selectionDepth
    change _ ≤ 64
    decide +kernel
  apply CatalanCore.Uniform.Bank.Plane1.alt_point (3/10) three_tenths_pos halves
    (FH.selectionDepth halves 2) (halves_content_auto _ hd) (decay _)
    (by exact_mod_cast lam_lt) (by exact_mod_cast cc_pos) ?_
    (u:= -1/12) (v:=0) (by norm_num) (by simpa using halves_const)
  obtain ⟨R0,hR⟩ := FH_nv0 halves (by change 1≤2;norm_num) halves_w_ne _ le_rfl
  refine ⟨R0,fun s hs x=>?_⟩
  obtain ⟨n,hn,hsc,hne⟩ := hR (2*s) (by omega) x
  exact ⟨n,⟨hn,by have : FH.scale n=n.1 := rfl;omega⟩,hsc,hne⟩
theorem pi2_measure : MeasureLBAt (Real.pi^2) ((65253/10000:ℚ):ℝ) :=
  pi2_point_exact.1.mono (by exact_mod_cast (le_of_lt mu_strict))
end CatalanCore.Uniform.Bank.HalvesContent.Bound
#print axioms CatalanCore.Uniform.Bank.HalvesContent.Bound.pi2_point_exact
#print axioms CatalanCore.Uniform.Bank.HalvesContent.Bound.pi2_measure
