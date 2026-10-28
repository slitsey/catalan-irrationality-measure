module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import CatalanCore.Decay.Rect.DecayRect
public import CatalanCore.Decay.Rect.DecayTop
public import CatalanCore.Decay.Rect.DecayMinor
public import CatalanCore.Uniform.Decay.Spline.ChainCore

@[expose] public section

/-!
# Signed window and member decay (lane D, package D2)

Mechanical signed copies (`hw0 -> hwV`, `decay_coreW -> SignedChain.decay_coreW`) of
`decay_rect_win`, `decay_of_certG_rect_slope`, `decay_top_of_certG_rect_slack`,
`mem1DecayA_of_certG_rect_slack_slope`, `mem2DecayA_of_certG_rect_slack_slope`,
`decay_common_win`, `hasDecay_commonMinorFam`.
-/

open Filter Topology Finset
open CatalanLambda.Decay (Usig Utau Irho cexpr)

namespace CatalanCore.SignedChain

variable {sl : ℝ}

open CatalanCore CatalanCore.Decay CatalanCore.Rect

/-- **The window-`a` decay of the first member**: `decay_coreW` (window `w = a + 1`) plus the window
lemma `window_rect` for the single pattern `(r, m)`, for every `α r ≤ m ≤ α r + a` (`0 ≤ a`). -/
theorem decay_rect_win {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α) {a : ℝ} (ha : 0 ≤ a)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m : ℕ, N₀ ≤ r → (α : ℝ) * r ≤ m → (m : ℝ) ≤ α * r + a → ∀ t : ℝ,
      |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) →
      |Polynomial.aeval (Fr.const + t) (Fr.fullPoly r m)|
        ≤ Real.exp (-((D : ℝ) - δ) * (r : ℝ) ^ 2) := by
  classical
  obtain ⟨e, m0, κ, B0, he0, he1, hm0, hm0xs, hm0μ, -, hB0, hcore⟩ :=
    decay_coreW (w := a + 1) hFr F hα (by linarith) hg hwV hRc hc hInu hD
  intro δ hδ
  obtain ⟨N, hN⟩ := hcore δ hδ
  refine ⟨N, ?_⟩
  intro r m hr hαr hαr' t ht
  obtain ⟨hrpos, hR, ⟨T0, hEn, hb⟩, -⟩ := hN r m hr hαr (by linarith)
  have ht' : |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) := ht
  have hwin := window_rect hFr he0 he1 hm0xs hm0μ hR hEn ht'
  rw [← hB0] at hwin
  refine hwin.trans ?_
  have h2r : (2 : ℝ) ^ r = Real.exp (r * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [h2r, ← Real.exp_add]
  apply Real.exp_le_exp.2
  linarith [hb]

/-- `decay_of_certG_rect_slope`: the window-`1` case of `decay_rect_win`, as decay of `hybridFamUp`. -/
theorem decay_of_certG_rect_slope {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu) :
    HasDecay (hybridFamUp Fr α) (D : ℝ) (F.ccert : ℝ) := by
  classical
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_rect_win hFr F hα (a := 1) zero_le_one hg hwV hRc hc hInu hD δ hδ
  refine ⟨N, ?_⟩
  rintro ⟨r, m⟩ ⟨hadm1, hadm2⟩ hr t ht
  have hαr : (α : ℝ) * r ≤ m := by exact_mod_cast hadm1
  have hαr' : (m : ℝ) ≤ α * r + 1 := by exact_mod_cast hadm2
  have hev : (hybridFamUp Fr α).evalR (r, m) ((hybridFamUp Fr α).const + t)
      = Polynomial.aeval (Fr.const + t) (Fr.fullPoly r m) := by
    simp [PolyFamily.evalR, hybridFamUp, Rect.hybridFam, PolyFamily.hybrid]
  show |(hybridFamUp Fr α).evalR (r, m) ((hybridFamUp Fr α).const + t)| ≤ _
  rw [hev]
  exact hN r m hr hαr hαr' t ht

theorem decay_top_of_certG_rect_slack {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) {a : ℝ} (ha : 0 ≤ a) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m : ℕ, N₀ ≤ r → (α : ℝ) * r ≤ m → (m : ℝ) ≤ α * r + a → ∀ t : ℝ,
      |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) →
      |Polynomial.aeval (Fr.const + t) ((Rect.afterTop r m).fullPolyG Fr)|
        ≤ Real.exp (-((D : ℝ) - δ) * (r : ℝ) ^ 2) := by
  classical
  obtain ⟨e, m0, κ, B0, he0, he1, hm0, hm0xs, hm0μ, hκdef, hB0, hcore⟩ :=
    decay_coreW (w := a + 1) hFr F hα (by linarith) hg hwV hRc hc hInu hD
  intro δ hδ
  obtain ⟨N, hN⟩ := hcore (δ / 2) (half_pos hδ)
  refine ⟨max N ⌈2 / δ⌉₊, ?_⟩
  rintro r m hr hmα hmα' t ht
  have hrN : N ≤ r := le_trans (le_max_left _ _) hr
  have hr3 : ⌈2 / δ⌉₊ ≤ r := le_trans (le_max_right _ _) hr
  have hαr : (α : ℝ) * r ≤ m := hmα
  have hαr' : (m : ℝ) ≤ α * r + (a + 1) := by linarith
  obtain ⟨hrpos, hR, ⟨T0, hEn, hb0⟩, h1⟩ := hN r m hrN hαr hαr'
  obtain ⟨T1, hEn1, hb1⟩ := h1 (by linarith)
  have ht' : |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) := ht
  have hwin := window_rect_top hFr he0 he1 hm0 hm0xs hm0μ hR hcc hEn hEn1 ht'
  rw [← hB0, ← hκdef] at hwin
  refine hwin.trans ?_
  have h2r : (2 : ℝ) ^ (r + 1) = Real.exp ((r + 1 : ℕ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [h2r, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hδr : 2 / δ ≤ r := (Nat.le_ceil _).trans (by exact_mod_cast hr3)
  rw [div_le_iff₀ hδ] at hδr
  have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
  have hslack : Real.log 2 ≤ δ / 2 * (r : ℝ) ^ 2 := by nlinarith
  push_cast
  rcases le_total (T0 + ((r : ℝ) + m) * Real.log (Fr.Wabs * ((F.r0 : ℝ) * r) + B0))
      (T1 + ((r : ℝ) + m + 1) * (Real.log (Fr.Wabs * ((F.r0 : ℝ) * r) + B0) + κ)) with hm | hm
  · rw [max_eq_right hm]
    nlinarith [hb1, hslack]
  · rw [max_eq_left hm]
    nlinarith [hb0, hslack]

/-- **Member decay on a relation `A` inside the window `α r ≤ m ≤ α r + a`** (P6GAP):
`Mem1DecayA` from `decay_rect_win`. -/
theorem mem1DecayA_of_certG_rect_slack_slope {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    Rect.Mem1DecayA Fr A (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_rect_win hFr F hα ha hg hwV hRc hc hInu hD δ hδ
  exact ⟨N, fun r m hAr hr t ht => hN r m hr (hA r m hAr).1 (hA r m hAr).2 t ht⟩

/-- **The second-member decay on a relation `A` inside `α r ≤ m ≤ α r + a`** (P6GAP). -/
theorem mem2DecayA_of_certG_rect_slack_slope {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    Rect.Mem2DecayA Fr A (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_top_of_certG_rect_slack hFr F hα hg hwV hRc hc hInu hD hcc ha δ hδ
  exact ⟨N, fun r m hAr hr t ht => hN r m hr (hA r m hAr).1 (hA r m hAr).2 t ht⟩

/-- Bounded common deletions retain the exact same certified leading constants. -/
theorem decay_common_win {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α) {a : ℝ} (ha : 0 ≤ a)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : 0 ≤ (F.ccert : ℝ)) (d : ℕ) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m : ℕ, N₀ ≤ r → (α : ℝ) * r ≤ m → (m : ℝ) ≤ α * r + a →
      ∀ s : Finset (Fin r), r - s.card ≤ d → ∀ t : ℝ,
      |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) →
      |Polynomial.aeval (Fr.const + t) (commonMinorPoly Fr r m s)|
        ≤ Real.exp (-((D : ℝ) - δ) * (r : ℝ) ^ 2) := by
  classical
  obtain ⟨e, m0, κ, B0, he0, he1, hm0, hm0xs, hm0μ, -, hB0, hcore⟩ :=
    decay_coreW (w := a + 1) hFr F hα (by linarith) hg hwV hRc hc hInu hD
  intro δ hδ
  obtain ⟨N, hN⟩ := hcore (δ / 2) (by positivity)
  obtain ⟨N1, hN1⟩ := exists_nat_ge (2 * (F.ccert : ℝ) * d / δ)
  refine ⟨max N N1, ?_⟩
  intro r m hr hαr hαr' s hs t ht
  obtain ⟨hrpos, hR, ⟨T0, hEn, hb⟩, -⟩ := hN r m ((le_max_left _ _).trans hr) hαr (by linarith)
  have hwin := window_rect_common hFr he0 he1 hm0xs hm0μ hR
    (fun a : s => a.1) Subtype.val_injective hEn ht
  rw [← hB0, ← aeval_commonMinorPoly] at hwin
  have hSr : s.card ≤ r := by simpa using Finset.card_le_univ s
  have hmissing : (r : ℝ) - s.card ≤ d := by exact_mod_cast (show r - s.card ≤ d from hs)
  have hr1 : (N1 : ℝ) ≤ r := by exact_mod_cast ((le_max_right _ _).trans hr)
  have hlinear : 2 * (F.ccert : ℝ) * d ≤ δ * r := by
    have h := (div_le_iff₀ hδ).1 (hN1.trans hr1)
    nlinarith
  have hcost : (F.ccert : ℝ) * r * ((r : ℝ) - s.card) ≤ δ / 2 * (r : ℝ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hmissing (mul_nonneg hcc (Nat.cast_nonneg r))
    have h2 := mul_le_mul_of_nonneg_right hlinear (Nat.cast_nonneg r)
    nlinarith
  have h2r : (2 : ℝ) ^ r = Real.exp (r * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  refine hwin.trans ?_
  rw [h2r, ← Real.exp_add]
  apply Real.exp_le_exp.2
  simp only [Fintype.card_coe] at *
  linarith

theorem hasDecay_commonMinorFam {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α) {a : ℝ} (ha : 0 ≤ a)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : 0 ≤ (F.ccert : ℝ)) (d : ℕ) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    HasDecay (commonMinorFam Fr A d) (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_common_win hFr F hα ha hg hwV hRc hc hInu hD hcc d δ hδ
  refine ⟨N, ?_⟩
  intro i hi hr t ht
  exact hN i.1 i.2.1 hr (hA _ _ hi.1).1 (hA _ _ hi.1).2 i.2.2 hi.2 t ht

end CatalanCore.SignedChain
