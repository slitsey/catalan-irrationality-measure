module

public import CatalanFrames.Lambda.HybContent2C
public import CatalanFrames.Lambda.Const
public import CatalanFrames.LambdaHybrid.NV.FinalNV
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
* OPEN (analytic, DZ-audit item 4): content and decay of DO's second member `afterTop r m`
  (`Mem2Content`, `Mem2Decay`).
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

/-! ### Content: from `lam_content_deficit2` to the `ε`-form -/

theorem eventually_log_le {e : ℝ} (he : 0 < e) :
    ∀ᶠ r : ℕ in atTop, Real.log r ≤ e * r := by
  have h := Real.isLittleO_log_id_atTop.bound he
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with r hr
  simp only [id, Real.norm_eq_abs] at hr
  exact (le_abs_self _).trans (hr.trans (by rw [abs_of_nonneg (Nat.cast_nonneg r)]))

/-- The arithmetic of the clean-up of the `m`-dependent and `log r` terms. -/
theorem lam_num {Λ ε r L m lg : ℝ} (hΛ : 24729491161 / 6665218560 ≤ Λ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 100) (hr : 3 ≤ ε * r) (hL0 : 0 ≤ L) (hL : L ≤ ε / 10 * r)
    (hm : r / 8 - 1 ≤ m)
    (hmain : lg ≤ (24994314577 / 6665218560 + ε / 10) * r ^ 2
      - m * ((1 / 7 - ε / 10) * r - 4 * L) - m * ((7 / 80 - ε / 10) * r - 6 * L)
      - (1 / 128 - ε / 10) * r ^ 2 - (1 / 320 - ε / 10) * r ^ 2) :
    lg ≤ (Λ + ε) * r ^ 2 := by
  have hr0 : 0 ≤ r := by
    by_contra h
    push Not at h
    nlinarith
  have hX1 : 0 ≤ (1 / 7 - ε / 10) * r - 4 * L := by nlinarith
  have hX2 : 0 ≤ (7 / 80 - ε / 10) * r - 6 * L := by nlinarith
  have h1 : (r / 8 - 1) * ((1 / 7 - ε / 10) * r - 4 * L) ≤ m * ((1 / 7 - ε / 10) * r - 4 * L) :=
    mul_le_mul_of_nonneg_right hm hX1
  have h2 : (r / 8 - 1) * ((7 / 80 - ε / 10) * r - 6 * L) ≤
      m * ((7 / 80 - ε / 10) * r - 6 * L) :=
    mul_le_mul_of_nonneg_right hm hX2
  have hrL : r * L ≤ ε / 10 * r ^ 2 := by nlinarith
  have hrr : 0 ≤ r ^ 2 := sq_nonneg r
  have hlin : 129 / 560 * r ≤ ε / 10 * r ^ 2 := by nlinarith
  nlinarith

theorem lam_content_eps {Λ : ℝ} (hΛ : 24729491161 / 6665218560 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefHypT lamInst r (r / 8) T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  set ε₁ : ℝ := min ε (1 / 100) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε (by norm_num)
  have hε₁1 : ε₁ ≤ 1 / 100 := min_le_right _ _
  have hε₁2 : ε₁ ≤ ε := min_le_left _ _
  have hd := lam_content_deficit2 (ε := ε₁ / 10) (by positivity)
  have hl := eventually_log_le (e := ε₁ / 10) (by positivity)
  have hbig : ∀ᶠ r : ℕ in atTop, 3 ≤ ε₁ * r := by
    have : Tendsto (fun r : ℕ => ε₁ * (r : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hε₁0
    exact this.eventually_ge_atTop 3
  filter_upwards [hd, hl, hbig, eventually_ge_atTop 16] with r ⟨δ, hδ, _, _, _, _, hlog⟩ hL hb hr16
  refine ⟨Tfun2 r, δ, hδ, ?_⟩
  have hm : (r : ℝ) / 8 - 1 ≤ ((r / 8 : ℕ) : ℝ) := by
    have : (r : ℝ) < 8 * ((r / 8 : ℕ) : ℝ) + 8 := by
      have := Nat.lt_div_mul_add (a := r) (b := 8) (by norm_num)
      exact_mod_cast (by omega : r < 8 * (r / 8) + 8)
    linarith
  have hL0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have key := lam_num (Λ := Λ + (ε - ε₁)) (ε := ε₁) (r := (r : ℝ)) (L := Real.log r)
    (m := ((r / 8 : ℕ) : ℝ)) (lg := Real.log (DhybT lamInst r (r / 8) (Tfun2 r) δ))
    (by linarith) hε₁0 hε₁1 hb hL0 hL hm hlog
  have : (Λ + (ε - ε₁) + ε₁) = Λ + ε := by ring
  rw [this] at key
  exact key

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

/-- **`lam_hyb_measure_of_decay`**: `μ(λ) ≤ C/(D - Λ)` with the content theorem
`lam_content_deficit2` (`Λ ≥ 24729491161/6665218560`). -/
theorem lam_hyb_measure_of_decay {Λ D C E : ℚ} (hΛ : (24729491161 / 6665218560 : ℚ) ≤ Λ)
    (hD : HasDecay (hybridFamUp lamFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2c : Mem2Content lamFrame (Λ : ℝ)) (M2d : Mem2Decay lamFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E) :
    (hybPairFam lamFrame 8).MeasureLB (E : ℝ) :=
  lam_hyb_measure_of_content_eps
    (lam_content_eps (by have h := (Rat.cast_le (K := ℝ)).2 hΛ; push_cast at h; exact h))
    (le_trans (by norm_num) hΛ) hD M2c M2d hη hC hη2 hE

/-- The headline statement in the project's form `G - 5π²/48` (generic scaling lemma). -/
theorem lam_hyb_measure_G {Λ D C E : ℚ} (hΛ : (24729491161 / 6665218560 : ℚ) ≤ Λ)
    (hD : HasDecay (hybridFamUp lamFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2c : Mem2Content lamFrame (Λ : ℝ)) (M2d : Mem2Decay lamFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E)
    (hE0 : 0 ≤ E) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (E : ℝ) := by
  have h := lam_hyb_measure_of_decay hΛ hD M2c M2d hη hC hη2 hE
  have h' : Measure.MeasureLBAt lamFrame.const (E : ℝ) := h
  rw [const_eq] at h'
  have := h'.affine (by exact_mod_cast hE0) 2 0 (by norm_num)
  convert this using 1
  push_cast
  ring

/-! ### The k180s numbers -/

/-- Decay for the `k180s` certificate: `D = 3.9027944`, `c = 7.6477917` (to be instantiated by
`decay_of_certG_rect` once `CatalanCore/Cert/SigmaHyb` provides the certificate). -/
def LamHybDecayK180s : Prop :=
  HasDecay (hybridFamUp lamFrame (1 / 8)) (((39027944 / 10000000 : ℚ)) : ℝ)
    (((76477917 / 10000000 : ℚ)) : ℝ)

/-- With `D = 3.9027944`, `c = 7.6477917`, `Λ = 3.7102296`: exponent `≤ 39.72`
(`c/(D-Λ) = 39.71541…`). -/
theorem lam_hyb_measure_k180s (hD : LamHybDecayK180s)
    (M2c : Mem2Content lamFrame (((37102296 / 10000000 : ℚ)) : ℝ))
    (M2d : Mem2Decay lamFrame (((39027944 / 10000000 : ℚ)) : ℝ)
      (((76477917 / 10000000 : ℚ)) : ℝ)) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (((3972 / 100 : ℚ)) : ℝ) :=
  lam_hyb_measure_G (Λ := 37102296 / 10000000) (D := 39027944 / 10000000)
    (C := 76477917 / 10000000) (E := 3972 / 100) (by norm_num) hD M2c M2d (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms lam_hyb_measure_of_decay
#print axioms lam_hyb_measure_G
#print axioms lam_hyb_measure_k180s

end CatalanFrames.LambdaHybrid
