module

public import CatalanCore.Decay.Rect.DecayCore
public import CatalanCore.Decay.Rect.WindowMinor

@[expose] public section

open Filter Topology Finset
open CatalanLambda.Decay (Usig Utau Irho cexpr)

namespace CatalanCore

open Decay Rect

/-- Bounded common deletions retain the exact same certified leading constants. -/
theorem decay_common_win {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOK') (F : Cert.CertCoreG K ρ ε c wt) {α : ℚ} (hα : 0 < α) {a : ℝ} (ha : 0 ≤ a)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : 0 ≤ (F.ccert : ℝ)) (d : ℕ) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m : ℕ, N₀ ≤ r → (α : ℝ) * r ≤ m → (m : ℝ) ≤ α * r + a →
      ∀ s : Finset (Fin r), r - s.card ≤ d → ∀ t : ℝ,
      |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) →
      |Polynomial.aeval (Fr.const + t) (commonMinorPoly Fr r m s)|
        ≤ Real.exp (-((D : ℝ) - δ) * (r : ℝ) ^ 2) := by
  classical
  obtain ⟨e, m0, κ, B0, he0, he1, hm0, hm0xs, hm0μ, -, hB0, hcore⟩ :=
    decay_coreW (w := a + 1) hFr F hα (by linarith) hg hw0 hRc hc hInu hD
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
    (hFr : Fr.DecayOK') (F : Cert.CertCoreG K ρ ε c wt) {α : ℚ} (hα : 0 < α) {a : ℝ} (ha : 0 ≤ a)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu)
    (hcc : 0 ≤ (F.ccert : ℝ)) (d : ℕ) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    HasDecay (commonMinorFam Fr A d) (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := decay_common_win hFr F hα ha hg hw0 hRc hc hInu hD hcc d δ hδ
  refine ⟨N, ?_⟩
  intro i hi hr t ht
  exact hN i.1 i.2.1 hr (hA _ _ hi.1).1 (hA _ _ hi.1).2 i.2.2 hi.2 t ht

end CatalanCore
