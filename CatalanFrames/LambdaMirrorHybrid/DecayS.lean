module

public import CatalanFrames.LambdaMirrorHybrid.MirContent
public import CatalanCore.Cert.Sigma300.Glue
public import CatalanCore.Cert.SigmaHybS.FrameDecay

@[expose] public section

/-!
# λ′ (mirror): slope-`5/2` decay (both members) and the generic final assembly

The decay is the frame-generic `hybS_decay` / `hybS_mem2_decay` (same transfer as
`mir_hybrid_decay`, slope `5/2`).  `mir_hyb_measure_final2_of`: any `DefBothG` content family at
`3 ≤ Λ ≤ 3.678854` gives `μ(G + 5π²/48) ≤ 32.44`.
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.LambdaMirror CatalanFrames.HybCommon

namespace CatalanFrames.LambdaMirrorHybrid

theorem mir_decayOKs : mirFrame.DecayOKs' (5 / 2 : ℝ) :=
  CatalanCore.Cert.SigmaHybS.decayOKs_of_legacy CatalanCore.Cert.Sigma300.mirror_decayOK
    (by norm_num [mirFrame])

/-- **Mirror hybrid decay, member 1, slope `5/2`.** -/
theorem mir_hybrid_decayS :
    HasDecay (hybridFamUp mirFrame (1 / 8 : ℚ)) (((390557 / 100000 : ℚ)) : ℝ)
      (((18386549 / 2500000 : ℚ)) : ℝ) :=
  CatalanCore.Cert.SigmaHybS.hybS_decay mir_decayOKs rfl

/-- **Mirror hybrid decay, member 2, slope `5/2`.** -/
theorem mir_mem2_decayS :
    Mem2Decay mirFrame (((390557 / 100000 : ℚ)) : ℝ) (((18386549 / 2500000 : ℚ)) : ℝ) :=
  CatalanCore.Cert.SigmaHybS.hybS_mem2_decay mir_decayOKs rfl

/-- **λ′ headline from any content family at `3 ≤ Λ ≤ 3.678854`**: `μ(G + 5π²/48) ≤ 32.44`. -/
theorem mir_hyb_measure_final2_of {Λ : ℚ}
    (hboth : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBothG mirNInst r T δ ∧
      Real.log (DhybT mirNInst r (r / 8) T δ) ≤ ((Λ : ℝ) + ε) * (r : ℝ) ^ 2)
    (hΛ0 : 3 ≤ Λ) (hΛ : Λ ≤ 3678854 / 1000000) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      + 5 * Real.pi ^ 2 / 48) (((811 / 25 : ℚ)) : ℝ) :=
  mir_hyb_measure_G (D := 390557 / 100000) (C := 18386549 / 2500000) (E := 811 / 25)
    (mir_hasContent_of_both (by exact_mod_cast (by linarith : (0 : ℚ) ≤ Λ)) hboth) mir_hybrid_decayS mir_mem2_decayS
    (by linarith) (by norm_num) (by linarith)
    (by rw [div_le_iff₀ (by linarith)]; nlinarith) (by norm_num)

#print axioms mir_hyb_measure_final2_of

end CatalanFrames.LambdaMirrorHybrid
