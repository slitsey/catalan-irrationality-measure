module
public import CatalanCore.Cert.SigmaHybS.Final
public import CatalanCore.Decay.Rect.HybridHook
@[expose] public section
namespace CatalanCore.Cert.SigmaHybS.Data
open CatalanCore
theorem D_le : (390557 / 100000 : ℚ) ≤ certS.Dof 2 (1 / 8) (17024457 / 10 ^ 7) := by
  unfold CatalanCore.Cert.CertCoreGs.Dof certS
  simp only [SBASE, IBOUNDS, MPRAY, SVAL]
  norm_num


/-- All numerical data of certS; the decay mechanisms are frame-independent. -/
theorem certified : HybridDecayData certS (1/8) 2 (17024457/10^7) (390557/100000) 2 where
  hα := by norm_num
  hg := hg_hybS
  hw0 := wtH_nonneg
  hRc := by norm_num
  hc := cH_norm
  hInu := CatalanCore.Cert.SigmaHyb.Inu_le
  hD := D_le
  hcc := by norm_num [certS]
#print axioms certified
end CatalanCore.Cert.SigmaHybS.Data
