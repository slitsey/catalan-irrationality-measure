module

public import CatalanFrames.P6Hybrid.Admissible
public import CatalanCore.Decay.Rect.DecayMinor
public import CatalanCore.Cert.SigmaP6H.Final

@[expose] public section

open CatalanCore CatalanCore.Rect CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

/-- Every fixed deletion budget preserves the existing P6 decay certificate. -/
theorem p6_minor_decay (d : ℕ) :
    HasDecay (commonMinorFam p6Frame P6Adm9 d) (37251 / 10000) (66510 / 10000) := by
  have hA : ∀ r m, P6Adm9 r m → ((1 / 8 : ℚ) : ℝ) * r ≤ m ∧
      (m : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) * r + (9 / 8 : ℝ) := by
    intro r m h
    have h1 : (r : ℝ) ≤ 8 * m := by exact_mod_cast h.1
    have h2 : (8 : ℝ) * m ≤ r + 9 := by exact_mod_cast h.2
    push_cast
    constructor <;> linarith
  have h := hasDecay_commonMinorFam (Fr := p6Frame)
    CatalanCore.Cert.Sigma300.p6_decayOK CatalanCore.Cert.SigmaP6H.certP6H
    (α := 1 / 8) (by norm_num) (a := 9 / 8) (by norm_num)
    CatalanCore.Cert.SigmaP6H.hg_P6 CatalanCore.Cert.SigmaP6H.wtH_nonneg
    (Rc := 4) (by norm_num) CatalanCore.Cert.SigmaP6H.cH_norm
    CatalanCore.Cert.SigmaHyb.Inu_le CatalanCore.Cert.SigmaP6H.D_le
    (by rw [CatalanCore.Cert.SigmaP6H.certP6H_ccert]; norm_num) d hA
  rw [CatalanCore.Cert.SigmaP6H.certP6H_ccert] at h
  convert h using 1 <;> norm_num

end CatalanFrames.P6Hybrid
