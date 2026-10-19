module

public import CatalanCore.Cert.SigmaP6.Final
public import CatalanCore.Cert.Sigma300.Glue

@[expose] public section

/-!
# P6's own sigma (FK row D): the decay input `HasDecay (ofFrame p6Frame) D c`

`SigmaP6.certCore` is a frame-free `CertCore` for the K = 699 measure `sigD` (`rho = 1/2048`,
`eps = 1/1000`), with the contour radius **`r0 = 1/10`** (NOT lambda's `7/50`): the audit
FP-audit-P6decay requires every P6 write-up using this row to say "fix `r0 = 1/10`".
`CertCore.r0` is a field, so `decay_of_cert` needs no change.
-/

open CatalanCore CatalanCore.Cert

namespace CatalanCore.Cert.SigmaP6

theorem ccert_eq : certCore.ccert = 66510 / 10000 := rfl

/-- **P6 row D.**  Density 3, P6's own sigma: `D = 3.0408`, `c = 6.6510`. -/
theorem p6_decay_rowD :
    HasDecay (PolyFamily.ofFrame CatalanFrames.P6.p6Frame) (((30408 / 10000 : ℚ)) : ℝ)
      (((66510 / 10000 : ℚ)) : ℝ) := by
  have := decay_of_cert Sigma300.p6_decayOK certCore Dof_three
  rwa [ccert_eq] at this

end CatalanCore.Cert.SigmaP6
