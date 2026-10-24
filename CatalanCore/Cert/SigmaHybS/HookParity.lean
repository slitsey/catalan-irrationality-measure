module

public import CatalanCore.Decay.Rect.HybridHook
public import CatalanCore.Cert.SigmaHybS.FrameDecay

@[expose] public section

/-! # Compatibility audit of the shared hybrid decay hook

The existing certificate and public API types are unchanged. Both production
and compatibility endpoints use the same certified data bundle.
-/

namespace CatalanCore.Cert.SigmaHybS.HookParity

open CatalanCore

/-- All numerical specialization is confined to the certS instance. -/
theorem data : HybridDecayData certS (1 / 8) 2 (17024457 / 10^7)
    (390557 / 100000) 2 :=
  Data.certified

theorem hybS_decay_prepared {Fr : Frame} (hFr : Fr.DecayOKs' (5 / 2 : ℝ))
    (hd : Fr.d = 2) :
    HasDecay (hybridFamUp Fr (1 / 8 : ℚ)) (((390557 / 100000 : ℚ)) : ℝ)
      (((18386549 / 2500000 : ℚ)) : ℝ) :=
  data.hybridDecay hFr hd

/-- This compatibility target deliberately retains the fixed-ratio legacy type.
The fully generic second-member API is HybridDecayData.membersDecay. -/
theorem hybS_mem2_decay_prepared {Fr : Frame} (hFr : Fr.DecayOKs' (5 / 2 : ℝ))
    (hd : Fr.d = 2) :
    Rect.Mem2Decay Fr (((390557 / 100000 : ℚ)) : ℝ)
      (((18386549 / 2500000 : ℚ)) : ℝ) :=
  mem2Decay_of_certG_rect_slope hFr certS data.hg data.hw0 data.hRc data.hc
    data.hInu (by rw [hd]; exact data.hD) data.hcc

/-- Preserve the old public names and statements, rather than introducing
another published numerical theorem during this preparation. -/
example {Fr : Frame} (hFr : Fr.DecayOKs' (5 / 2 : ℝ)) (hd : Fr.d = 2) :
    hybS_decay_prepared hFr hd = hybS_decay hFr hd := Subsingleton.elim _ _

example {Fr : Frame} (hFr : Fr.DecayOKs' (5 / 2 : ℝ)) (hd : Fr.d = 2) :
    hybS_mem2_decay_prepared hFr hd = hybS_mem2_decay hFr hd := Subsingleton.elim _ _

#print axioms data
#print axioms hybS_decay_prepared
#print axioms hybS_mem2_decay_prepared

end CatalanCore.Cert.SigmaHybS.HookParity
