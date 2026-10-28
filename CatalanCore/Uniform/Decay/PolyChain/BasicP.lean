module

public import CatalanCore.Uniform.Decay.Cert.Basic

@[expose] public section

/-!
# Elementary checks without the straight-ray cover (lane D, package D7)

`SplineData.basicOkP` is D5's `basicOk` without the conjunct `coverOk 0 umax rayBoxes`, and
`BasicFactsP` is `BasicFacts` without the field `hray`; `basicOkP_sound` is the copied proof.
The polygon checker `checkP` uses these, so polygon bank data need no ray boxes (`sl`, `umax`,
`rayBoxes` of `SplineData` are ignored by the polygon chain).
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Tools

namespace SplineData

variable (D : SplineData)

/-- All elementary checks except the straight-ray cover. -/
def basicOkP : Bool :=
  decide (0 < D.Mq) && decide (0 < D.ε) && decide (D.ε < 1) && decide (0 < D.r0) && decide (0 < D.W) &&
  decide (0 < D.rho) && decide (0 < D.theta) && decide (0 < D.etaS) && decide (0 ≤ D.Rc) &&
  decide (0 ≤ D.ccert) && decide (2 * (D.mprime - D.gmin) ≤ D.ccert) &&
  (List.finRange D.n).all D.segOk && (List.finRange D.n).all D.conjOk &&
  decide (∑ i : Fin D.n, massOf (D.l i) = 1) &&
  decide (0 ≤ D.lossS) && decide ((315 / 100 : ℚ) * D.rho * D.BsQ ≤ D.lossS) &&
  coverOk 0 1 D.lineCells && D.dofOk

end SplineData

namespace SplineData

variable {D : SplineData}

/-- Everything `basicOkP` establishes (`BasicFacts` without the ray cover). -/
structure BasicFactsP (D : SplineData) : Prop where
  hM : 0 < D.Mq
  hε0 : 0 < (D.ε : ℝ)
  hε1 : (D.ε : ℝ) < 1
  r0_pos : 0 < D.r0
  W_pos : 0 < D.W
  hρ : 0 < (D.rho : ℝ)
  hθ : 0 < D.theta
  hηS : 0 < D.etaS
  hRc : 0 ≤ (D.Rc : ℝ)
  hcc : 0 ≤ (D.ccert : ℝ)
  hccert : 2 * ((D.mprime : ℝ) - D.gmin) ≤ D.ccert
  hAB : ∀ i, D.A i ≠ D.B i
  hne : ∀ i, D.l i ≠ []
  hbern : ∀ i, bernOkK (D.l i) 0 (D.M i) = true
  hmass : ∑ i : Fin D.n, ∑ j ∈ range ((D.l i).length - 1 + 1), coeffs (D.l i) j / ((j : ℚ) + 1) = 1
  hAR : ∀ i, ‖D.A i‖ ≤ (D.Rc : ℝ)
  hBR : ∀ i, ‖D.B i‖ ≤ (D.Rc : ℝ)
  hτ : Function.Involutive D.tauF
  hAτ : ∀ i, D.A (D.tauF i) = (starRingEnd ℂ) (D.A i)
  hBτ : ∀ i, D.B (D.tauF i) = (starRingEnd ℂ) (D.B i)
  hlτ : ∀ i, D.l (D.tauF i) = D.l i
  hloss : Real.pi * (D.rho : ℝ) * Bs D.A D.B (fun i => (D.M i : ℝ)) ≤ D.lossS
  hline : ∀ x : ℝ, (0 : ℝ) ≤ x → x ≤ 1 → ∃ p ∈ D.lineCells, (p.1 : ℝ) ≤ x ∧ x ≤ p.2
  hD : D.Dt ≤ 2 * (D.Mq * D.mprime + D.dim * D.Scap) - D.Mq ^ 2 * D.Ibound + D.Inu
    - (2 * D.Mq ^ 2 * (D.lossS + D.theta) + 2 * D.dim * D.etaS
      + D.Mq ^ 2 * (D.V * D.lossS + 2 * D.V * D.theta))

theorem basicOkP_sound (h : D.basicOkP = true) : BasicFactsP D := by
  simp only [basicOkP, dofOk, Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hM, hε0, hε1, hr0, hW, hρ, hθ, hη, hRc, hcc, hcert, hseg, hconj, hmass, hl0, hloss,
    hline, hD⟩ := h
  have hsegF : ∀ i, D.segOk i = true := fun i => all_finRange hseg i
  have F := fun i => segOk_facts hRc (hsegF i)
  have hconjF := fun i => conjOk_facts (all_finRange hconj i)
  have htauLt : ∀ i, (D.seg i).tau < D.n := fun i => (F i).2.2.2.2.2.2.2.2
  have hBs : Bs D.A D.B (fun i => (D.M i : ℝ)) ≤ (D.BsQ : ℝ) := by
    unfold Bs BsQ
    push_cast
    exact Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (by exact_mod_cast (F i).2.2.2.2.1)
      (by exact_mod_cast (F i).2.2.2.1) (F i).2.2.2.2.2.1
  have hBs0 : 0 ≤ Bs D.A D.B (fun i => (D.M i : ℝ)) :=
    Finset.sum_nonneg fun i _ => div_nonneg (Rat.cast_nonneg.mpr (F i).2.2.2.2.1) (norm_nonneg _)
  have hlossR : (315 / 100 : ℝ) * D.rho * D.BsQ ≤ D.lossS := by
    have := (Rat.cast_le (K := ℝ)).2 hloss
    push_cast at this
    exact this
  have hρR : (0 : ℝ) < D.rho := by exact_mod_cast hρ
  have hpi : Real.pi ≤ 315 / 100 := by have := Real.pi_lt_d2; norm_num at this ⊢; linarith
  refine ⟨hM, by exact_mod_cast hε0, by exact_mod_cast hε1, hr0, hW, hρR, hθ, hη,
    by exact_mod_cast hRc, by exact_mod_cast hcc, ?_, fun i => (F i).1, fun i => (F i).2.1,
    fun i => (F i).2.2.1, hmass, fun i => (F i).2.2.2.2.2.2.1, fun i => (F i).2.2.2.2.2.2.2.1,
    fun i => Fin.ext (by rw [tauF_val htauLt]; exact (hconjF i).2.2.2.2.2),
    ?_, ?_, fun i => (hconjF i).2.2.2.2.1, ?_, fun u hu hu1 => coverOk_sound hline u (by simpa using hu) (by simpa using hu1), hD⟩
  · exact_mod_cast hcert
  · intro i
    obtain ⟨a1, a2, -, -, -, -⟩ := hconjF i
    apply Complex.ext <;> simp [SplineData.A, a1, a2]
  · intro i
    obtain ⟨-, -, b1, b2, -, -⟩ := hconjF i
    apply Complex.ext <;> simp [SplineData.B, b1, b2]
  · calc Real.pi * (D.rho : ℝ) * Bs D.A D.B (fun i => (D.M i : ℝ))
        ≤ (315 / 100 : ℝ) * D.rho * Bs D.A D.B (fun i => (D.M i : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hBs0
          exact mul_le_mul_of_nonneg_right hpi hρR.le
      _ ≤ (315 / 100 : ℝ) * D.rho * D.BsQ := mul_le_mul_of_nonneg_left hBs (by positivity)
      _ ≤ D.lossS := hlossR

end SplineData

end CatalanCore.Uniform.Decay.Cert
