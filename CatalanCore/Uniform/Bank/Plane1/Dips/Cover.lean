module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Cover.Check
public import CatalanCore.Uniform.Bank.Plane1.Decay
public import CatalanCore.Uniform.Decay.AltFold
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Plane1.Dips
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Bank.Plane1 CatalanCore.Uniform.Decay.Nodes
open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyWire3
open CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.AltDecay
abbrev DipD := Cover.Dchi
abbrev DipTab := Cover.TabC
theorem dipC_pos : (0:ℚ)<1/4 := by norm_num
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; two-piece exact geometry bindings, no physicalcell checks.
theorem dip_RP : DipTab.RP=altPieces (1/4) := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; two-piece exact geometry binding.
theorem dip_CP : DipTab.CP=altPieces (1/4) := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one rational equality.
theorem dip_Mq : DipTab.Mq=1+(1/4:ℚ)/2 := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one natural equality.
theorem dip_dim : DipD.dim=3 := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one positive scalar comparison.
theorem dip_eps : 0<DipD.ε := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; fournodepair contributions x30logterms, same accepted node-energy class.
theorem dip_energy : energyCheck 30 (altPieces (1/4)) (altPieces (1/4)) DipD.Inu=true := by
  -- kcost: 1.0 s C forecast, N30 two-piece node energy class measured0.26s in Plane2.Bound.
  decide +kernel
theorem quarter_decay (σ : Support) (a b c : ℤ) (h0 : a+b+c=0) (depth : ℕ) :
    HasScaledDecay ((altGeom (1/4) dipC_pos).family (planeFrame σ a b c h0) depth)
      (altGeom (1/4) dipC_pos).scale (DipD.Dt:ℝ) (DipD.ccert:ℝ) :=
  altGeom_hasScaledDecay_F (1/4) dipC_pos (by norm_num) (planeFrame_contourCheck σ a b c h0)
    (planeFrame_hAR σ a b c h0) (le_refl _) DipTab dip_RP dip_CP dip_Mq
    DipD Cover.Pply Cover.check_true (by rw [dip_dim];rfl) 30 dip_energy
    (m0:=1/3) (by norm_num) (planeFrame_mu_real σ a b c h0) dip_eps depth
end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.quarter_decay
