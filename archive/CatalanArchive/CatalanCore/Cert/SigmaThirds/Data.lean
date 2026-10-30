module

public import CatalanCore.Cert.SigmaThirds.Final
public import CatalanCore.Decay.Rect.HybridHook

@[expose] public section

namespace CatalanCore.Cert.SigmaThirds.Data

open CatalanCore

/-- Verified numerical data of the thirds-specific certificate. -/
theorem certified : HybridDecayData certS (1 / 8) 2 (17024457 / 10 ^ 7)
    (77423 / 20000) 2 where
  hα := by norm_num
  hg := hg_hybS
  hw0 := wtH_nonneg
  hRc := by norm_num
  hc := cH_norm
  hInu := CatalanCore.Cert.SigmaHyb.Inu_le
  hD := CatalanCore.Cert.SigmaThirds.D_le
  hcc := by
    change (0 : ℝ) ≤ (((169697 / 25000 : ℚ)) : ℝ)
    norm_num

#print axioms certified

end CatalanCore.Cert.SigmaThirds.Data
