module

public import CatalanCore.Decay.Rect.DecayCore
public import CatalanCore.Decay.Rect.WindowR
public import CatalanCore.Rect.Family

@[expose] public section

/-!
# `decay_of_certG_rect`: the route-independent rectangular decay (WP-H2-core)

For any frame `Fr` (`DecayOK'`) and any `CertCoreG` whose function `g` satisfies the hybrid
soundness identity `g = (1+α) U^σ - (U^τ + U^ex_{2α}) + (1-ε) π|Im|`:

`HasDecay (hybridFamUp Fr α) D F.ccert` for `D ≤ F.Dof Fr.d α Inu` and `Inu ≤ Jfun α`
(`Jfun α = I(ν_α)`, the energy of `Leb[0,1] + ½ Leb[1, 1+2α]`),

where `hybridFamUp` is `hybridFam` with admissibility restricted to `α r ≤ m ≤ α r + 1`.
-/

open Filter Topology
open CatalanLambda.Decay (Usig Utau Irho cexpr)

namespace CatalanCore

open Decay

/-- The hybrid family with the admissibility `α r ≤ m ≤ α r + 1` (coordinator decision). -/
noncomputable def hybridFamUp (Fr : Frame) (α : ℚ) : PolyFamily :=
  { Rect.hybridFam Fr α with
    Adm := fun rm => α * (rm.1 : ℚ) ≤ rm.2 ∧ (rm.2 : ℚ) ≤ α * rm.1 + 1 }

/-- `decay_of_certG_rect`: `decay_core` (constants, energy hypotheses, asymptotics) plus the
window lemma `window_rect` for the single pattern `(r, m)`. -/
theorem decay_of_certG_rect {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOK') (F : Cert.CertCoreG K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu) :
    HasDecay (hybridFamUp Fr α) (D : ℝ) (F.ccert : ℝ) := by
  classical
  obtain ⟨e, m0, κ, B0, he0, he1, hm0, hm0xs, hm0μ, -, hB0, hcore⟩ :=
    decay_core hFr F hα hg hw0 hRc hc hInu hD
  intro δ hδ
  obtain ⟨N, hN⟩ := hcore δ hδ
  refine ⟨N, ?_⟩
  rintro ⟨r, m⟩ ⟨hadm1, hadm2⟩ hr t ht
  have hαr : (α : ℝ) * r ≤ m := by exact_mod_cast hadm1
  have hαr' : (m : ℝ) ≤ α * r + 1 := by exact_mod_cast hadm2
  obtain ⟨hrpos, hR, ⟨T0, hEn, hb⟩, -⟩ := hN r m hr hαr hαr'
  have ht' : |t| ≤ Real.exp (-(F.ccert : ℝ) * (r : ℝ)) := ht
  have hwin := window_rect hFr he0 he1 hm0xs hm0μ hR hEn ht'
  rw [← hB0] at hwin
  have hev : (hybridFamUp Fr α).evalR (r, m) ((hybridFamUp Fr α).const + t)
      = Polynomial.aeval (Fr.const + t) (Fr.fullPoly r m) := by
    simp [PolyFamily.evalR, hybridFamUp, Rect.hybridFam, PolyFamily.hybrid]
  show |(hybridFamUp Fr α).evalR (r, m) ((hybridFamUp Fr α).const + t)| ≤ _
  rw [hev]
  refine hwin.trans ?_
  have h2r : (2 : ℝ) ^ r = Real.exp (r * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hdeg : (((hybridFamUp Fr α).deg (r, m) : ℕ) : ℝ) = r := rfl
  rw [hdeg, h2r, ← Real.exp_add]
  apply Real.exp_le_exp.2
  linarith [hb]

end CatalanCore
