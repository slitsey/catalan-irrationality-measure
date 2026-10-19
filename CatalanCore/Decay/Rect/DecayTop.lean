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
`mem2Decay_of_certG_rect` packages the `m = r/8` cast glue shared by every `α = 1/8` frame.
-/

open Filter Topology
open CatalanLambda.Decay (Usig Utau Irho cexpr)

namespace CatalanCore

open Decay

theorem decay_top_of_certG_rect {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOK') (F : Cert.CertCoreG K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : (0 : ℝ) ≤ F.ccert) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m : ℕ, N₀ ≤ r → (m : ℝ) = α * r → ∀ t : ℝ,
      |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) →
      |Polynomial.aeval (Fr.const + t) ((Rect.afterTop r m).fullPolyG Fr)|
        ≤ Real.exp (-((D : ℝ) - δ) * (r : ℝ) ^ 2) := by
  classical
  obtain ⟨e, m0, κ, B0, he0, he1, hm0, hm0xs, hm0μ, hκdef, hB0, hcore⟩ :=
    decay_core hFr F hα hg hw0 hRc hc hInu hD
  intro δ hδ
  obtain ⟨N, hN⟩ := hcore (δ / 2) (half_pos hδ)
  refine ⟨max N ⌈2 / δ⌉₊, ?_⟩
  rintro r m hr hmα t ht
  have hrN : N ≤ r := le_trans (le_max_left _ _) hr
  have hr3 : ⌈2 / δ⌉₊ ≤ r := le_trans (le_max_right _ _) hr
  have hαr : (α : ℝ) * r ≤ m := hmα.ge
  have hαr' : (m : ℝ) ≤ α * r + 1 := by
    have : (0 : ℝ) ≤ 1 := by norm_num
    linarith [hmα.le]
  obtain ⟨hrpos, hR, ⟨T0, hEn, hb0⟩, h1⟩ := hN r m hrN hαr hαr'
  obtain ⟨T1, hEn1, hb1⟩ := h1 (by linarith [hmα.le])
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

/-- **The second-member decay of every `α = 1/8` frame**: `decay_top_of_certG_rect` at `α = 1/8`
and `m = r/8` (the cast glue, once), stated as `Mem2Decay`. -/
theorem mem2Decay_of_certG_rect {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOK') (F : Cert.CertCoreG K ρ ε c wt)
    (hg : ∀ s : ℂ, F.g s = (1 + (((1 / 8 : ℚ)) : ℝ)) * Usig ρ c wt s
        - Unu (((1 / 8 : ℚ)) : ℝ) s + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (((1 / 8 : ℚ)) : ℝ)) {D : ℚ}
    (hD : D ≤ F.Dof Fr.d (1 / 8) Inu) (hcc : (0 : ℝ) ≤ F.ccert) :
    Rect.Mem2Decay Fr (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_top_of_certG_rect hFr F (α := 1 / 8) (by norm_num) hg hw0 hRc hc
    hInu hD hcc δ hδ
  refine ⟨N, fun r h8 hr t ht => ?_⟩
  have hm : ((r / 8 : ℕ) : ℝ) = (((1 / 8 : ℚ)) : ℝ) * r := by
    obtain ⟨k, rfl⟩ := h8
    rw [Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast; ring
  exact hN r (r / 8) hr hm t ht

end CatalanCore
