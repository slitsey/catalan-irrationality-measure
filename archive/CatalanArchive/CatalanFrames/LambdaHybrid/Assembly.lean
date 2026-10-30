module

public import CatalanFrames.Lambda.HybInst
public import CatalanFrames.Lambda.Const
public import CatalanCore.NV.Hybrid.FinalNV
public import CatalanFrames.LambdaHybrid.NV.LamData
public import CatalanCore.Rect.PairNV
public import CatalanCore.Rect.PairBridge
public import CatalanCore.Measure.Scaling

@[expose] public section

/-!
# λ: the hybrid measure theorem from content, decay and nonvanishing (LAMASM)

Assembly of `μ(λ) ≤ C/(D - Λ)` (the `κ = 0` exponent; pinned degree) for
`λ = G/2 - 5π²/96`, in the form `G - 5π²/48` via the generic scaling lemma.

* content: `lam_content_eps` repackages `lam_content_deficit2` as "for each `ε`, eventually a
  deficit family with `log DhybT ≤ (Λ + ε) r²`", `Λ ≥ 24729491161/6665218560 = 3.710229595…`.
  The assembly takes the constant `Λ` as a PARAMETER: a better content theorem (C7, GK deficits)
  only needs to supply the same `∀ ε, ∀ᶠ r, ∃ T δ, DefHypT ∧ log DhybT ≤ (Λ+ε) r²` shape
  (`lam_hyb_measure_of_content_eps`);
* decay: `HasDecay (hybridFamUp lamFrame (1/8)) D C` (hypothesis; `decay_of_certG_rect`);
* nonvanishing: `lam_hybPairNV` from `nv_hyb_nonvanishing`, prime choice by `hasNVPin_hybPair`;
* second member: content and decay of `afterTop r m` are proved in `Mem2Content` and
  `Mem2Decay`; this generic assembly accepts those results through its second-member hypotheses.
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

/-! ### Nonvanishing -/

theorem lam_hybPairNV : HybPairNV lamFrame (fun l => l % 4 = 3) (fun l => (l + 1) / 4) := by
  intro ℓ hℓ hcls m s' r hm hmK hrK hr hS x hx h1 h2
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hc : ℓ % 4 = 3 := hcls
  have hlK : ℓ + 1 = 4 * ((ℓ + 1) / 4) := by omega
  exact NV.nv_hyb_nonvanishing (NV.lamData hlK) m s' r hm hmK hrK hr hS (CatalanCore.mem_S.2 hx)
    h1 h2

theorem lam_hK : ∀ l : ℕ, l.Prime → l % 4 = 3 → l ≤ 4 * ((l + 1) / 4) ∧
    4 * ((l + 1) / 4) ≤ l + 3 := by
  intro l _ h
  omega

/-! ### The theorem -/

/-- **λ hybrid measure from decay** (content constant `Λ` a parameter, exponent `C / (D - Λ)`).
Hypotheses: member-1 decay (from `decay_of_certG_rect`), the second-member inputs, and the
numerical side conditions. -/
theorem lam_hyb_measure_of_content_eps {Λ D C E : ℚ}
    (hcont : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefHypT lamInst r (r / 8) T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ ((Λ : ℝ) + ε) * (r : ℝ) ^ 2)
    (hΛ0 : 0 ≤ Λ)
    (hD : HasDecay (hybridFamUp lamFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2c : Mem2Content lamFrame (Λ : ℝ)) (M2d : Mem2Decay lamFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E) :
    (hybPairFam lamFrame 8).MeasureLB (E : ℝ) := by
  obtain ⟨T, δ, hdef, hlog⟩ := contentFam_of_eps lamInst (Λ : ℝ) hcont
  have hc := hasContent_hybPair lamInst (by exact_mod_cast hΛ0) T δ hdef hlog M2c
  have hdec := hasDecay_hybPair (by exact_mod_cast hC.le) hD M2d
  exact measure_hybPair lamFrame (c := 3) (by norm_num) (by simpa using isUnit_mod4_three)
    lam_hK lam_hybPairNV hc hdec hη hC hη2 hE

end CatalanFrames.LambdaHybrid
