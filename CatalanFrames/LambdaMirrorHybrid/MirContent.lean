module
public import CatalanFrames.LambdaMirrorHybrid.MirT
public import CatalanFrames.HybCommon.TopSum
public import CatalanFrames.HybCommon.NegRect
public import CatalanFrames.LambdaMirrorHybrid.Assembly
public import CatalanCore.Decay.Rect.DecayTop
@[expose] public section
/-! Mirror content (`G + 5π²/48`): the bordered content family and `HasContent`, without the
decay certificate. -/
open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.LambdaMirror CatalanFrames.HybCommon
namespace CatalanFrames.LambdaMirrorHybrid

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
theorem mir_mem2Content_of_both {Λ : ℝ}
    (hboth : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBothG mirNInst r T δ ∧
      Real.log (DhybT mirNInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    Mem2Content mirFrame Λ :=
  Mem2Content.of_neg (Fr₁ := mirNFrame) (Fr₂ := mirFrame) (fun a b => mir_Mn_neg a b)
    (mem2Content_of_both_G mirNInst le_rfl (fun ε hε => mir_topC_sum hε) hboth)

theorem mir_mem2Content {Λ : ℝ}
    (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    Mem2Content mirFrame Λ :=
  mir_mem2Content_of_both (mir_both_eps hΛ)

/-- **Mirror content of the pair family** (both members). -/
theorem mir_hasContent_of_both {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hboth : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBothG mirNInst r T δ ∧
      Real.log (DhybT mirNInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    HasContent (hybPairFam mirFrame 8) Λ := by
  obtain ⟨T, δ, hdef, hlog⟩ := contentFam_of_eps mirInst Λ (by
    intro ε hε
    filter_upwards [hboth ε hε] with r ⟨T, δ, hd, hl⟩
    exact ⟨T, δ, DefHypT.of_neg (I₁ := mirNInst) (I₂ := mirInst) (fun a b => mir_Mn_neg a b)
      (mir_Bnd_eq r (r / 8)) hd.1, hl⟩)
  exact hasContent_hybPair mirInst hΛ0 T δ hdef hlog (mir_mem2Content_of_both hboth)

theorem mir_hasContent {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    HasContent (hybPairFam mirFrame 8) Λ :=
  mir_hasContent_of_both hΛ0 (mir_both_eps hΛ)

end CatalanFrames.LambdaMirrorHybrid
