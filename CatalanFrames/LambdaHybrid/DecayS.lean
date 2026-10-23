module

public import CatalanFrames.LambdaHybrid.AssemblyFinal
public import CatalanCore.Cert.SigmaHybS.FrameDecay

@[expose] public section

/-!
# λ: slope-`5/2` decay (both members) and the generic final assembly

`lam_hyb_measure_final2_of`: from any `DefBoth` content family at a constant `3 ≤ Λ ≤ 3.678854`,
`μ(G - 5π²/48) ≤ 32.44` (`D = 3.90557`, `c = 7.3546196`).  The merged-content instance
(`FinalS`) supplies `Λ = HybCommon.mergedLambda`.
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

theorem lam_decayS :
    HasDecay (hybridFamUp lamFrame (1 / 8 : ℚ)) (((390557 / 100000 : ℚ)) : ℝ)
      (((18386549 / 2500000 : ℚ)) : ℝ) :=
  CatalanCore.Cert.SigmaHybS.hybS_decay CatalanCore.Cert.SigmaHybS.lam_decayOKs rfl

theorem lam_mem2_decayS :
    Mem2Decay lamFrame (((390557 / 100000 : ℚ)) : ℝ) (((18386549 / 2500000 : ℚ)) : ℝ) :=
  CatalanCore.Cert.SigmaHybS.hybS_mem2_decay CatalanCore.Cert.SigmaHybS.lam_decayOKs rfl

/-- `lam_hyb_measure_of_both` with the decay data as hypotheses (generic in `D`, `C`). -/
theorem lam_hyb_measure_of_both_dec {Λ D C E : ℚ}
    (hboth : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ ((Λ : ℝ) + ε) * (r : ℝ) ^ 2)
    (hΛ0 : 0 ≤ Λ)
    (hD : HasDecay (hybridFamUp lamFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2d : Mem2Decay lamFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E)
    (hE0 : 0 ≤ E) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (E : ℝ) :=
  lam_pairMeasure_G hE0
    (lam_hyb_measure_of_content_eps
      (fun ε hε => (hboth ε hε).mono fun _ ⟨T, δ, hδ, hlog⟩ => ⟨T, δ, hδ.1, hlog⟩) hΛ0
      hD (lam_mem2Content_of_both le_rfl hboth) M2d hη hC hη2 hE)

/-- **λ headline from any content family at `3 ≤ Λ ≤ 3.678854`**: `μ(G - 5π²/48) ≤ 32.44`. -/
theorem lam_hyb_measure_final2_of {Λ : ℚ}
    (hboth : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ ((Λ : ℝ) + ε) * (r : ℝ) ^ 2)
    (hΛ0 : 3 ≤ Λ) (hΛ : Λ ≤ 3678854 / 1000000) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (((811 / 25 : ℚ)) : ℝ) :=
  lam_hyb_measure_of_both_dec (D := 390557 / 100000) (C := 18386549 / 2500000)
    (E := 811 / 25) hboth (by linarith) lam_decayS lam_mem2_decayS
    (by linarith) (by norm_num) (by linarith)
    (by rw [div_le_iff₀ (by linarith)]; nlinarith) (by norm_num)

#print axioms lam_hyb_measure_final2_of

end CatalanFrames.LambdaHybrid
