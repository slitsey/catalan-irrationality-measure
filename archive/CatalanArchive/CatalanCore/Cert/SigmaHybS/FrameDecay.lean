module

public import CatalanCore.Cert.SigmaHybS.Final
public import CatalanCore.Decay.Rect.DecayTop

@[expose] public section
open _root_.CatalanCore.Cert.SigmaHybS

/-!
# Frame-generic decay from the slope-`5/2` hybrid certificate `certS`

`hybS_decay` / `hybS_mem2_decay`: for ANY frame with `Fr.DecayOKs' (5/2)` and `Fr.d = 2`, the
certificate `certS` gives `HasDecay (hybridFamUp Fr (1/8)) D c` and `Mem2Decay Fr D c`,
`D = 3.90557 ≤ Dof = 3.9055710…`, `c = 18386549/2500000`.  `decayOKs_of_legacy` upgrades the legacy
frame hypotheses (`Frame.DecayOK'`) to slope `5/2` whenever `δ0 ≥ 1/10`.  The λ and mirror
instances are one-liners (`LambdaHybrid/FinalS`, `LambdaMirrorHybrid/FinalS`).
-/

namespace CatalanArchive.CatalanCore.Cert.SigmaHybS.FrameDecay

open _root_.CatalanCore

/-- Legacy frame hypotheses give the slope-`5/2` ones when `δ0 ≥ 1/10` (`1 ≤ 4 · (5/2) · δ0`). -/
theorem decayOKs_of_legacy {Fr : Frame} (h : Fr.DecayOK') (hδ : (1 : ℚ) / 10 ≤ Fr.δ0) :
    Fr.DecayOKs' (5 / 2 : ℝ) where
  contour := h.contour
  slope := ⟨by norm_num, by norm_num, by
    have := (Rat.cast_le (K := ℝ)).2 hδ
    push_cast at this
    linarith⟩
  atomRange := h.atomRange
  norm_ge := h.norm_ge

/-- The slightly smaller exponent `D = 3.90557` of the certificate (`Dof = 3.9055710002…`). -/
theorem D_le' : (390557 / 100000 : ℚ) ≤ certS.Dof 2 (1 / 8) (17024457 / 10 ^ 7) := by
  unfold CatalanCore.Cert.CertCoreGs.Dof certS
  simp only [SBASE, IBOUNDS, MPRAY, SVAL]
  norm_num

/-- **Frame-generic hybrid decay, member 1.** -/
theorem hybS_decay {Fr : Frame} (hFr : Fr.DecayOKs' (5 / 2 : ℝ)) (hd : Fr.d = 2) :
    HasDecay (hybridFamUp Fr (1 / 8 : ℚ)) (((390557 / 100000 : ℚ)) : ℝ)
      (((18386549 / 2500000 : ℚ)) : ℝ) :=
  decay_of_certG_rect_slope (sl := (5 / 2 : ℝ)) (Fr := Fr) hFr certS (α := 1 / 8)
    (by norm_num) hg_hybS (fun k => wtH_nonneg k) (Rc := 2) (by norm_num) cH_norm
    CatalanCore.Cert.SigmaHyb.Inu_le (by rw [hd]; exact D_le')

/-- **Frame-generic hybrid decay, member 2.** -/
theorem hybS_mem2_decay {Fr : Frame} (hFr : Fr.DecayOKs' (5 / 2 : ℝ)) (hd : Fr.d = 2) :
    Rect.Mem2Decay Fr (((390557 / 100000 : ℚ)) : ℝ) (((18386549 / 2500000 : ℚ)) : ℝ) :=
  mem2Decay_of_certG_rect_slope (sl := (5 / 2 : ℝ)) (Fr := Fr) hFr certS hg_hybS
    (fun k => wtH_nonneg k) (Rc := 2) (by norm_num) cH_norm
    CatalanCore.Cert.SigmaHyb.Inu_le (by rw [hd]; exact D_le') (by norm_num [certS])

#print axioms hybS_decay
#print axioms hybS_mem2_decay

end CatalanArchive.CatalanCore.Cert.SigmaHybS.FrameDecay
