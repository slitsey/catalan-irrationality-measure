module

public import CatalanFrames.LambdaMirrorHybrid.MirT
public import CatalanFrames.HybCommon.TopSum
public import CatalanFrames.HybCommon.NegRect
public import CatalanFrames.LambdaMirrorHybrid.Assembly
public import CatalanCore.Cert.SigmaHyb.FinalH
public import CatalanCore.Cert.Sigma300.Glue
public import CatalanCore.Decay.Rect.DecayTop

@[expose] public section

/-!
# The mirror hybrid measure theorem `mir_hyb_measure_final` (`G + 5π²/48`)

Content: `mir_logDhybT_le` (tropical + extended weights) with the five generic deficit sums
(`HybCommon.Sums*`) gives `both_eps_G`; bordering (`mem2Content_of_both_G`) gives `Mem2Content`.
Decay: the same hybrid certificate `certHyb` as λ, applied with `mirror_decayOK` (frame-generic
`decay_of_certG_rect` / `decay_top_of_certG_rect`).
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.LambdaMirror CatalanFrames.HybCommon

namespace CatalanFrames.LambdaMirrorHybrid

/-- **Mirror hybrid decay, member 1** (`D = 3.9028`, `c = 7.6444`): the λ certificate at `mirFrame`. -/
theorem mir_hybrid_decay :
    HasDecay (hybridFamUp mirFrame (1 / 8 : ℚ)) (((39028 / 10000 : ℚ)) : ℝ)
      (((76444 / 10000 : ℚ)) : ℝ) :=
  CatalanCore.decay_of_certG_rect (Fr := mirFrame) CatalanCore.Cert.Sigma300.mirror_decayOK
    CatalanCore.Cert.SigmaHyb.certHyb (α := 1 / 8) (by norm_num)
    CatalanCore.Cert.SigmaHyb.hg_hyb (fun k => CatalanCore.Cert.SigmaHyb.wtH_nonneg k) (Rc := 1)
    (by norm_num) CatalanCore.Cert.SigmaHyb.cH_norm CatalanCore.Cert.SigmaHyb.Inu_le
    CatalanCore.Cert.SigmaHyb.D_le

/-- **Mirror hybrid decay, member 2.** -/
theorem mir_mem2_decay :
    Mem2Decay mirFrame (((39028 / 10000 : ℚ)) : ℝ) (((76444 / 10000 : ℚ)) : ℝ) :=
  CatalanCore.mem2Decay_of_certG_rect (Fr := mirFrame)
    CatalanCore.Cert.Sigma300.mirror_decayOK CatalanCore.Cert.SigmaHyb.certHyb
    CatalanCore.Cert.SigmaHyb.hg_hyb (fun k => CatalanCore.Cert.SigmaHyb.wtH_nonneg k)
    (Rc := 1) (by norm_num) CatalanCore.Cert.SigmaHyb.cH_norm CatalanCore.Cert.SigmaHyb.Inu_le
    CatalanCore.Cert.SigmaHyb.D_le (by simp [CatalanCore.Cert.SigmaHyb.certHyb]; norm_num)

#print axioms mir_hybrid_decay
#print axioms mir_mem2_decay

/-- The border cost is negligible for the mirror instance. -/
theorem mir_topC_sum {ε : ℝ} (hε : 0 < ε) : ∀ᶠ r : ℕ in atTop,
    ∑ p ∈ (Finset.range (Bnd mirNInst r (r / 8))).filter Nat.Prime,
      (topC mirNInst r (r / 8) p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2 :=
  topC_sum_G mirNInst mirBad (fun r => r / 8) (fun r => Nat.div_le_self r 8) hε

/-- The `ε`-form of the content bound with all seven bordered deficits, mirror. -/
theorem mir_both_eps {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBothG mirNInst r T δ ∧
      Real.log (DhybT mirNInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 :=
  both_eps_G7 mirNInst mirNData (Or.inr rfl) (fun ε hε => mir_logDhybT_le hε) hΛ

/-- **`Mem2Content` for the mirror** at `Λ₁ = 24729491161/6665218560 - 1/448 - 1/576 - 1/352`. -/
theorem mir_mem2Content {Λ : ℝ}
    (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    Mem2Content mirFrame Λ :=
  Mem2Content.of_neg (Fr₁ := mirNFrame) (Fr₂ := mirFrame) (fun a b => mir_Mn_neg a b)
    (mem2Content_of_both_G mirNInst le_rfl (fun ε hε => mir_topC_sum hε) (mir_both_eps hΛ))

/-- **Mirror content of the pair family** (both members). -/
theorem mir_hasContent {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    HasContent (hybPairFam mirFrame 8) Λ := by
  obtain ⟨T, δ, hdef, hlog⟩ := contentFam_of_eps mirInst Λ (by
    intro ε hε
    filter_upwards [mir_both_eps hΛ ε hε] with r ⟨T, δ, hd, hl⟩
    exact ⟨T, δ, DefHypT.of_neg (I₁ := mirNInst) (I₂ := mirInst) (fun a b => mir_Mn_neg a b)
      (mir_Bnd_eq r (r / 8)) hd.1, hl⟩)
  exact hasContent_hybPair mirInst hΛ0 T δ hdef hlog (mir_mem2Content hΛ)

/-- **The mirror hybrid measure theorem**: `μ(G + 5π²/48) ≤ 38.35`. -/
theorem mir_hyb_measure_final :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      + 5 * Real.pi ^ 2 / 48) (((3835 / 100 : ℚ)) : ℝ) :=
  mir_hyb_measure_G (Λ := 370343 / 100000) (D := 39028 / 10000) (C := 76444 / 10000)
    (E := 3835 / 100)
    (mir_hasContent (by norm_num) (by push_cast; norm_num)) mir_hybrid_decay mir_mem2_decay
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- final theorem
#print axioms mir_hyb_measure_final

end CatalanFrames.LambdaMirrorHybrid
