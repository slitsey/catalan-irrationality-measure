module

public import CatalanCore.Decay.Rect.DecayCore
public import CatalanCore.Decay.Rect.WindowTop
public import CatalanCore.Rect.PairBridge

@[expose] public section

/-!
# Decay of DO's second member `afterTop r m` (MEM2D)

Same certificate and same constants as `decay_of_certG_rect`, and the same shared core
`decay_core`.  For `m = α r` the member `afterTop r m` is controlled by the energy bounds of the
two patterns `(r, m)` and `(r, m+1)` (`window_rect_top`), the latter perturbed by `O(r)`
(`rectEnergy_perturb`), which is absorbed into the slack `δ r²`.
`mem2Decay_of_certG_rect_slope` packages the `m = r/8` cast glue shared by every `α = 1/8` frame.
-/

open Filter Topology
open CatalanLambda.Decay (Usig Utau Irho cexpr)

namespace CatalanCore

variable {sl : ℝ}

open Decay

theorem decay_top_of_certG_rect_slack {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) {a : ℝ} (ha : 0 ≤ a) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m : ℕ, N₀ ≤ r → (α : ℝ) * r ≤ m → (m : ℝ) ≤ α * r + a → ∀ t : ℝ,
      |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) →
      |Polynomial.aeval (Fr.const + t) ((Rect.afterTop r m).fullPolyG Fr)|
        ≤ Real.exp (-((D : ℝ) - δ) * (r : ℝ) ^ 2) := by
  classical
  obtain ⟨e, m0, κ, B0, he0, he1, hm0, hm0xs, hm0μ, hκdef, hB0, hcore⟩ :=
    decay_coreW (w := a + 1) hFr F hα (by linarith) hg hw0 hRc hc hInu hD
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

/-- The window-`1` case (`α r ≤ m ≤ α r + 1`). -/
theorem decay_top_of_certG_rect_win {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m : ℕ, N₀ ≤ r → (α : ℝ) * r ≤ m → (m : ℝ) ≤ α * r + 1 → ∀ t : ℝ,
      |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) →
      |Polynomial.aeval (Fr.const + t) ((Rect.afterTop r m).fullPolyG Fr)|
        ≤ Real.exp (-((D : ℝ) - δ) * (r : ℝ) ^ 2) :=
  decay_top_of_certG_rect_slack hFr F hα hg hw0 hRc hc hInu hD hcc zero_le_one

/-- `decay_top_of_certG_rect_win` for `m = α r` exactly. -/
theorem decay_top_of_certG_rect {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m : ℕ, N₀ ≤ r → (m : ℝ) = α * r → ∀ t : ℝ,
      |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) →
      |Polynomial.aeval (Fr.const + t) ((Rect.afterTop r m).fullPolyG Fr)|
        ≤ Real.exp (-((D : ℝ) - δ) * (r : ℝ) ^ 2) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_top_of_certG_rect_win hFr F hα hg hw0 hRc hc hInu hD hcc δ hδ
  exact ⟨N, fun r m hr hm t ht => hN r m hr hm.ge (by rw [hm]; linarith) t ht⟩

/-- **Member decay on a relation `A` inside the window `α r ≤ m ≤ α r + a`** (P6GAP):
`Mem1DecayA` from `decay_rect_win`. -/
theorem mem1DecayA_of_certG_rect_slack_slope {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    Rect.Mem1DecayA Fr A (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_rect_win hFr F hα ha hg hw0 hRc hc hInu hD δ hδ
  exact ⟨N, fun r m hAr hr t ht => hN r m hr (hA r m hAr).1 (hA r m hAr).2 t ht⟩

/-- **The second-member decay on a relation `A` inside `α r ≤ m ≤ α r + a`** (P6GAP). -/
theorem mem2DecayA_of_certG_rect_slack_slope {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    Rect.Mem2DecayA Fr A (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_top_of_certG_rect_slack hFr F hα hg hw0 hRc hc hInu hD hcc ha δ hδ
  exact ⟨N, fun r m hAr hr t ht => hN r m hr (hA r m hAr).1 (hA r m hAr).2 t ht⟩

/-- **The second-member decay on an admissible relation `A`, window `α r ≤ m ≤ α r + 1`**
(P6): `decay_top_of_certG_rect_win` stated as `Mem2DecayA`. -/
theorem mem2DecayA_of_certG_rect_win {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + 1) :
    Rect.Mem2DecayA Fr A (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_top_of_certG_rect_win hFr F hα hg hw0 hRc hc hInu hD hcc δ hδ
  exact ⟨N, fun r m hAr hr t ht => hN r m hr (hA r m hAr).1 (hA r m hAr).2 t ht⟩

/-- **The second-member decay on an admissible relation `A`** (G3): `decay_top_of_certG_rect`
for every `(r, m)` with `A r m` and `m = α r` exactly, stated as `Mem2DecayA`. -/
theorem mem2DecayA_of_certG_rect {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) {A : ℕ → ℕ → Prop} (hA : ∀ r m, A r m → (m : ℝ) = α * r) :
    Rect.Mem2DecayA Fr A (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_top_of_certG_rect hFr F hα hg hw0 hRc hc hInu hD hcc δ hδ
  exact ⟨N, fun r m hAr hr t ht => hN r m hr (hA r m hAr) t ht⟩

/-- **The second-member decay of every `α = 1/8` frame**: `decay_top_of_certG_rect` at `α = 1/8`
and `m = r/8` (the cast glue, once), stated as `Mem2Decay`. -/
theorem mem2Decay_of_certG_rect_slope {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (F : Cert.CertCoreGs sl K ρ ε c wt)
    (hg : ∀ s : ℂ, F.g s = (1 + (((1 / 8 : ℚ)) : ℝ)) * Usig ρ c wt s
        - Unu (((1 / 8 : ℚ)) : ℝ) s + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (((1 / 8 : ℚ)) : ℝ)) {D : ℚ}
    (hD : D ≤ F.Dof Fr.d (1 / 8) Inu) (hcc : (0 : ℝ) ≤ F.ccert) :
    Rect.Mem2Decay Fr (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := mem2DecayA_of_certG_rect hFr F (α := 1 / 8) (by norm_num) hg hw0 hRc hc
    hInu hD hcc (A := Rect.admDiv 8) (fun r m ⟨h8, hm⟩ => by
      subst hm
      obtain ⟨k, rfl⟩ := h8
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
      push_cast; ring) δ hδ
  exact ⟨N, fun r h8 hr t ht => hN r (r / 8) ⟨h8, rfl⟩ hr t ht⟩

/-- **`mem1DecayA_of_certG_rect_slack`** (slope `3`, the existing statement). -/
theorem mem1DecayA_of_certG_rect_slack {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOK') (F : Cert.CertCoreG K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    Rect.Mem1DecayA Fr A (D : ℝ) (F.ccert : ℝ) :=
  mem1DecayA_of_certG_rect_slack_slope hFr.toDecayOKs' F hα hg hw0 hRc hc hInu hD ha hA

/-- **`mem2DecayA_of_certG_rect_slack`** (slope `3`, the existing statement). -/
theorem mem2DecayA_of_certG_rect_slack {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOK') (F : Cert.CertCoreG K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    Rect.Mem2DecayA Fr A (D : ℝ) (F.ccert : ℝ) :=
  mem2DecayA_of_certG_rect_slack_slope hFr.toDecayOKs' F hα hg hw0 hRc hc hInu hD hcc ha hA

/-- **`mem2Decay_of_certG_rect`** (slope `3`, the existing statement). -/
theorem mem2Decay_of_certG_rect {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOK') (F : Cert.CertCoreG K ρ ε c wt)
    (hg : ∀ s : ℂ, F.g s = (1 + (((1 / 8 : ℚ)) : ℝ)) * Usig ρ c wt s
        - Unu (((1 / 8 : ℚ)) : ℝ) s + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (((1 / 8 : ℚ)) : ℝ)) {D : ℚ}
    (hD : D ≤ F.Dof Fr.d (1 / 8) Inu) (hcc : (0 : ℝ) ≤ F.ccert) :
    Rect.Mem2Decay Fr (D : ℝ) (F.ccert : ℝ) :=
  mem2Decay_of_certG_rect_slope hFr.toDecayOKs' F hg hw0 hRc hc hInu hD hcc

end CatalanCore
