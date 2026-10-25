module
public import CatalanCore.Cert.QuarterCompute.ModelDefs
public import CatalanCore.Cert.QuarterContour.RealPolynomial
public import CatalanCore.Cert.QuarterContour.LogModelTube
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelSum
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterCompute.ModelFactors
open CatalanCore.Cert.QuarterContour.RealPolynomial

noncomputable def atom (p : Pt) (z : ℂ) : ℝ :=
  ((p.2.2 : ℝ)/2^32)*CatalanLambda.Decay.krho (1/2048 : ℝ) z (QuarterContour.cpt p)

lemma atom_eq (p : Pt) (z : ℂ) : atom p z =
    ((p.2.2 : ℝ)/2^32)*(-(1/2 : ℝ)*Real.log
      ((z.re-(p.1 : ℝ)/2^40)^2+(z.im-(p.2.1 : ℝ)/2^40)^2+(1/2048 : ℝ)^2)) := by
  unfold atom CatalanLambda.Decay.krho QuarterContour.cpt
  change ((p.2.2 : ℝ)/2^32)*(-(1/2 : ℝ)*Real.log
    (‖(⟨z.re,z.im⟩ : ℂ)-⟨(p.1 : ℝ)/2^40,(p.2.1 : ℝ)/2^40⟩‖^2+(1/2048 : ℝ)^2)) = _
  rw [SigmaP6.norm_sq_mk]

lemma Usig_cons (p : Pt) (ps : List Pt) (z : ℂ) :
    SigmaP6.Usig (p::ps) z.re z.im = atom p z+SigmaP6.Usig ps z.re z.im := by
  rw [atom_eq]
  rfl

noncomputable def jetTerm (S : ℕ) (v : ℝ) (j : Jet) : ℝ :=
  -(1/2 : ℝ)*((j.2.2 : ℝ)/2^32)*LogModel.poly 15
    (((j.1 : ℝ)*v+(j.2.1 : ℝ)*v^2)/(S : ℝ))

noncomputable def polySum (S : ℕ) (v : ℝ) (js : List Jet) : ℝ :=
  -(1/2 : ℝ)*(js.map (fun j => ((j.2.2 : ℝ)/2^32)*LogModel.poly 15
    (((j.1 : ℝ)*v+(j.2.1 : ℝ)*v^2)/(S : ℝ)))).sum

lemma polySum_cons (S : ℕ) (v : ℝ) (j : Jet) (js : List Jet) :
    polySum S v (j::js) = jetTerm S v j+polySum S v js := by
  simp only [polySum,jetTerm,List.map_cons,List.sum_cons]
  ring

noncomputable def atomLower (S : ℕ) (m : Model.Params) (v : ℝ) (p : Pt) (j : Jet) : ℝ :=
  -((p.2.2 : ℝ)*(Model.logUpS (Model.centreArg m p) : ℝ))/2^97 + jetTerm S v j -
    (Model.errorCeil S j : ℝ)/2^64

noncomputable def lower (S : ℕ) (m : Model.Params) (v : ℝ) (ps : List Pt) (js : List Jet) : ℝ :=
  -(Model.baseSum m ps : ℝ)/2^97+polySum S v js-(Model.errorSum S js : ℝ)/2^64

lemma lower_cons (S : ℕ) (m : Model.Params) (v : ℝ) (p : Pt) (j : Jet)
    (ps : List Pt) (js : List Jet) :
    lower S m v (p::ps) (j::js) = atomLower S m v p j+lower S m v ps js := by
  simp only [lower,atomLower,Model.baseSum,Model.errorSum,polySum_cons]
  push_cast
  ring

/-- Pairwise atom bounds aggregate without evaluating any concrete witness. -/
theorem lower_of_forall2 (S : ℕ) (m : Model.Params) (v : ℝ) (z : ℂ)
    (ps : List Pt) (js : List Jet)
    (h : List.Forall₂ (fun p j => atomLower S m v p j ≤ atom p z) ps js) :
    lower S m v ps js ≤ SigmaP6.Usig ps z.re z.im := by
  induction h with
  | nil => simp [lower,polySum,Model.baseSum,Model.errorSum,SigmaP6.Usig]
  | cons hp ht ih =>
    rw [lower_cons,Usig_cons]
    exact add_le_add hp ih

theorem forall2_of_inputs (S : ℕ) (m : Model.Params) (ps : List Pt) (js : List Jet)
    (h : Model.inputsOK S m ps js = true) :
    List.Forall₂ (fun p j => Model.validJet S m p j = true) ps js := by
  induction ps generalizing js with
  | nil =>
    cases js with
    | nil => exact List.Forall₂.nil
    | cons j js => simp [Model.inputsOK] at h
  | cons p ps ih =>
    cases js with
    | nil => simp [Model.inputsOK] at h
    | cons j js =>
      have hh : Model.validJet S m p j = true ∧ Model.inputsOK S m ps js = true := by
        simpa only [Model.inputsOK,Bool.and_eq_true] using h
      exact List.Forall₂.cons hh.1 (ih js hh.2)

/-- Replaces the polynomial sum by the exact coefficient compiler's real evaluation. -/
theorem sigma_lower_forall2 (S : ℕ) (hS : S ≠ 0) (m : Model.Params) (v : ℝ) (z : ℂ)
    (ps : List Pt) (js : List Jet)
    (h : List.Forall₂ (fun p j => atomLower S m v p j ≤ atom p z) ps js) :
    -(Model.baseSum m ps : ℝ)/2^97 +
      evalReal v (allCoeffs (factorList S) js)/(denominatorFor S : ℝ) -
      (Model.errorSum S js : ℝ)/2^64 ≤ SigmaP6.Usig ps z.re z.im := by
  rw [normalized_for S hS]
  exact lower_of_forall2 S m v z ps js h

/-- The geometric checker supplies each atom bound; all remaining aggregation is generic. -/
theorem sigma_lower_of_inputs (m : Model.Params) (v : ℝ) (z : ℂ)
    (ps : List Pt) (js : List Jet) (hi : Model.inputsOK inputScale m ps js = true)
    (hp : ∀ p j, Model.validJet inputScale m p j = true →
      atomLower inputScale m v p j ≤ atom p z) :
    -(Model.baseSum m ps : ℝ)/2^97+evalReal v (allCoeffs factors js)/(denominator : ℝ)-
      (Model.errorSum inputScale js : ℝ)/2^64 ≤ SigmaP6.Usig ps z.re z.im := by
  apply sigma_lower_forall2 inputScale (by decide) m v z ps js
  have h := forall2_of_inputs inputScale m ps js hi
  clear hi
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hv ht ih => exact List.Forall₂.cons (hp _ _ hv) ih

/-- Decoded coefficients can be substituted without reopening any numerical computation. -/
theorem sigma_lower_decoded (m : Model.Params) (v : ℝ) (z : ℂ)
    (ps : List Pt) (js : List Jet) (cs : List ℤ)
    (hi : Model.inputsOK inputScale m ps js = true)
    (hp : ∀ p j, Model.validJet inputScale m p j = true →
      atomLower inputScale m v p j ≤ atom p z)
    (hc : allCoeffs factors js = cs) :
    -(Model.baseSum m ps : ℝ)/2^97+evalReal v cs/(denominator : ℝ)-
      (Model.errorSum inputScale js : ℝ)/2^64 ≤ SigmaP6.Usig ps z.re z.im := by
  rw [← hc]
  exact sigma_lower_of_inputs m v z ps js hi hp

/-- Extend a model on the ray centreline across the permitted horizontal tube. -/
theorem sigma_tube_lower (ps : List Pt) (z z0 : ℂ) (W L : ℝ) (hW : 0 ≤ W)
    (hd : ‖z-z0‖ ≤ W) (hprob : ∑ k, QuarterContour.masses ps k = 1)
    (hL : L ≤ SigmaP6.Usig ps z0.re z0.im) :
    L-(W/(1/2048 : ℝ)+(W/(1/2048 : ℝ))^2)/2 ≤ SigmaP6.Usig ps z.re z.im := by
  have hs := LogModel.Usig_shift (by norm_num : (0 : ℝ) < 1/2048) hW
    (QuarterContour.positions ps) (QuarterContour.masses ps) (QuarterContour.mass_nonneg ps)
    hprob z z0 hd
  have h0 := QuarterContour.Usig_bridge ps z0.re z0.im
  have hz := QuarterContour.Usig_bridge ps z.re z.im
  change CatalanLambda.Decay.Usig (1/2048 : ℝ) (QuarterContour.positions ps)
    (QuarterContour.masses ps) z0 = _ at h0
  change CatalanLambda.Decay.Usig (1/2048 : ℝ) (QuarterContour.positions ps)
    (QuarterContour.masses ps) z = _ at hz
  rw [h0,hz] at hs
  linarith only [hs,hL]
end CatalanCore.Cert.QuarterContour.ModelSum
#print axioms CatalanCore.Cert.QuarterContour.ModelSum.sigma_lower_decoded
#print axioms CatalanCore.Cert.QuarterContour.ModelSum.sigma_tube_lower