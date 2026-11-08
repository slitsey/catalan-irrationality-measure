module

public import CatalanMeasure.GenD.Analytic.GaussianHorner

@[expose] public section
namespace CatalanMeasure.GenD.Analytic.GaussianCertificate
open Polynomial GaussianHorner
noncomputable section

theorem norm_castPair_le_of_square {a : ℤ × ℤ} {u : ℤ}
    (hu : 0 ≤ u) (hsq : a.1 ^ 2 + a.2 ^ 2 ≤ u ^ 2) : ‖castPair a‖ ≤ (u : ℝ) := by
  have hR : (a.1 : ℝ) ^ 2 + (a.2 : ℝ) ^ 2 ≤ (u : ℝ) ^ 2 := by exact_mod_cast hsq
  have huR : (0 : ℝ) ≤ u := by exact_mod_cast hu
  have hn : ‖castPair a‖ ^ 2 = (a.1 : ℝ) ^ 2 + (a.2 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [castPair, pow_two]
  nlinarith [norm_nonneg (castPair a)]

def normsOK : List (ℤ × ℤ) → List ℤ → Bool
  | [], [] => true
  | a :: as, u :: U => decide (0 ≤ u ∧ a.1 ^ 2 + a.2 ^ 2 ≤ u ^ 2) && normsOK as U
  | _, _ => false

theorem normsOK_sound {as : List (ℤ × ℤ)} {U : List ℤ} (h : normsOK as U = true) :
    List.Forall₂ (fun a u => ‖castPair a‖ ≤ u) as (U.map (fun (u : ℤ) => (u : ℝ))) := by
  induction as generalizing U with
  | nil =>
    cases U <;> simp_all [normsOK]
  | cons a as ih =>
    cases U with
    | nil => simp [normsOK] at h
    | cons u U =>
      simp only [normsOK, Bool.and_eq_true, decide_eq_true_eq] at h
      exact List.Forall₂.cons (norm_castPair_le_of_square h.1.1 h.1.2) (ih h.2)

def positiveStep (x den : ℤ) (state : ℤ × ℤ) (a : ℤ) : ℤ × ℤ :=
  (state.1 * x + a * state.2, state.2 * den)

def positiveHorner (as : List ℤ) (x den : ℤ) : ℤ :=
  (as.reverse.foldl (positiveStep x den) (0, 1)).1

theorem evalPairs_real_eq_normHorner (as : List ℤ) (r : ℝ) :
    evalPairs (as.map (fun a => (a,0))) (r : ℂ) =
      ((normHorner (as.map (fun (a : ℤ) => (a : ℝ))) r : ℝ) : ℂ) := by
  induction as with
  | nil => simp [evalPairs, normHorner]
  | cons a as ih =>
    simp only [List.map_cons, evalPairs, normHorner, castPair_real, ih]
    push_cast
    rfl

/-- The positive homogeneous integer checker denotes the rational Horner bound.
This identity uses the same hot loop measured in the shared-block pilot. -/
theorem positiveHorner_sound (as : List ℤ) (x den : ℤ) (hden : den ≠ 0) :
    (positiveHorner as x den : ℝ) * (den : ℝ) = (den : ℝ) ^ as.length *
      normHorner (as.map (fun (a : ℤ) => (a : ℝ))) ((x : ℝ) / (den : ℝ)) := by
  have hv : ∀ state a, ((positiveStep x den state a).1 : ℂ) =
      (x : ℂ) * (state.1 : ℂ) + (a : ℂ) * (state.2 : ℂ) := by
    intro state a
    simp only [positiveStep, Int.cast_add, Int.cast_mul]
    ring
  have hp : ∀ state a, (positiveStep x den state a).2 = state.2 * den := fun _ _ => rfl
  have ht := homogeneous_fold_invariant (positiveStep x den) (fun state => (state.1 : ℂ))
    (fun state => state.2) hden (x : ℂ) hv hp as.reverse (0, 1) 0 (by simp)
  have hpower := fold_power (positiveStep x den) (fun state => state.2) den hp as.reverse (0, 1)
  rw [hpower, one_mul, Int.cast_pow, List.length_reverse, reverse_fold_horner] at ht
  have hratio : (x : ℂ) / (den : ℂ) = (((x : ℝ) / (den : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hratio, evalPairs_real_eq_normHorner] at ht
  apply Complex.ofReal_injective
  push_cast
  exact ht

end
end CatalanMeasure.GenD.Analytic.GaussianCertificate
#print axioms CatalanMeasure.GenD.Analytic.GaussianCertificate.norm_castPair_le_of_square
#print axioms CatalanMeasure.GenD.Analytic.GaussianCertificate.normsOK_sound
#print axioms CatalanMeasure.GenD.Analytic.GaussianCertificate.evalPairs_real_eq_normHorner
#print axioms CatalanMeasure.GenD.Analytic.GaussianCertificate.positiveHorner_sound
