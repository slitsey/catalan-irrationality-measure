import CatalanCore.Uniform.Decay.PairEnergy.Oracle
import CatalanCore.Uniform.Decay.PolyChain.Check
set_option Elab.async false

/-!
# Energy rule for the polygon chain (lane D, package D6c)

`polyEnergyOk E D` has the type of `PolyCellRules.energyOk` (`SplineData → Bool`) and
`polyEnergyOk_sound : polyEnergyOk E D = true → I0 ≤ Ibound` is the field `energy_sound`, with the
same pair oracle.  The elementary facts needed by `I0_eq_sum_pairE` (`A ≠ B`, density lists nonempty,
Bernstein nonnegativity) are checked by the Boolean `efOk` itself, so no `basicOk` is assumed.
(Proofs are the D6 ones, restated for `EnergyFacts`.)
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.Tools

variable {D : SplineData}

structure EnergyFacts (D : SplineData) : Prop where
  hAB : ∀ i, D.A i ≠ D.B i
  hne : ∀ i, D.l i ≠ []
  hbern : ∀ i, bernOkK (D.l i) 0 (D.M i) = true

def efOk (D : SplineData) : Bool :=
  (List.finRange D.n).all fun i =>
    decide ((D.seg i).ax ≠ (D.seg i).bx ∨ (D.seg i).ay ≠ (D.seg i).byy) &&
    decide ((D.seg i).coef ≠ []) && bernOkK (D.seg i).coef 0 (D.seg i).M

theorem efOk_sound (h : efOk D = true) : EnergyFacts D := by
  have h' : ∀ i : Fin D.n, (decide ((D.seg i).ax ≠ (D.seg i).bx ∨ (D.seg i).ay ≠ (D.seg i).byy) &&
      decide ((D.seg i).coef ≠ []) && bernOkK (D.seg i).coef 0 (D.seg i).M) = true := by
    intro i; exact List.all_eq_true.1 h i (List.mem_finRange i)
  refine ⟨fun i hi => ?_, fun i => ?_, fun i => ?_⟩
  · have := h' i
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨h1, _⟩, _⟩ := this
    have e1 : (D.seg i).ax = (D.seg i).bx ∧ (D.seg i).ay = (D.seg i).byy := by
      have hre := congrArg Complex.re hi
      have him := congrArg Complex.im hi
      simp only [SplineData.A, SplineData.B] at hre him
      exact ⟨by exact_mod_cast hre, by exact_mod_cast him⟩
    rcases h1 with h1 | h1
    · exact h1 e1.1
    · exact h1 e1.2
  · have := h' i
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.2
  · have := h' i
    simp only [Bool.and_eq_true] at this
    exact this.2

theorem density_bounds' (EF : EnergyFacts D) (i : Fin D.n) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (0 : ℝ) ≤ D.f i t ∧ D.f i t ≤ (D.M i : ℝ) := by
  have := ratPoly_bounds (EF.hne i) (EF.hbern i) h0 h1
  unfold SplineData.f
  simpa using this

theorem segU_continuous' (EF : EnergyFacts D) (j : Fin D.n) : Continuous (segU D j) := by
  rw [segU_eq_U0]
  have hf0 : ∀ i : Fin 1, ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (fun _ : Fin 1 => D.f j) i t :=
    fun i t ht => (density_bounds' EF j t ht.1 ht.2).1
  refine continuous_of_modulus (K := Real.pi * Bs (fun _ : Fin 1 => D.A j) (fun _ : Fin 1 => D.B j)
    (fun _ => (D.M j : ℝ))) (V := Vp (fun _ : Fin 1 => D.f j)) ?_ ?_ ?_
  · refine mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun i _ => div_nonneg ?_ (norm_nonneg _))
    have h2 := density_bounds' EF j 0 le_rfl zero_le_one
    exact h2.1.trans h2.2
  · exact Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg zero_le_one
      (fun t _ => abs_nonneg _)
  · intro a ha z w
    have := U0_modulus (fun _ => EF.hAB j) (fun _ => density_cont j) hf0
      (fun _ t ht => by
        have := density_bounds' EF j t ht.1 ht.2
        simpa [abs_of_nonneg this.1] using this.2) ha z w
    linarith

theorem I0_eq_sum_pairE' (EF : EnergyFacts D) :
    I0 D.A D.B D.f = ∑ i, ∑ j, pairE D i j := by
  unfold I0 pairE
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : ∀ j, Continuous (fun s => D.f i s * segU D j (pt D.A D.B i s)) := fun j =>
    (density_cont i).mul ((segU_continuous' EF j).comp (continuous_pt D.A D.B i))
  have : (fun s => D.f i s * U0 D.A D.B D.f (pt D.A D.B i s)) =
      fun s => ∑ j, D.f i s * segU D j (pt D.A D.B i s) := by
    funext s
    rw [U0_eq_sum, Finset.mul_sum]
  rw [this, intervalIntegral.integral_finsetSum]
  intro j _
  exact (hc j).intervalIntegrable _ _

/-- Polygon energy rule: facts check, pair table, total. -/
def polyEnergyOk (E : List (List ℚ)) (D : SplineData) : Bool :=
  efOk D && energyOkOf pairOracle E D

theorem polyEnergyOk_sound (E : List (List ℚ)) (D : SplineData) (h : polyEnergyOk E D = true) :
    I0 D.A D.B D.f ≤ D.Ibound := by
  simp only [polyEnergyOk, Bool.and_eq_true] at h
  obtain ⟨hef, h⟩ := h
  have EF := efOk_sound hef
  simp only [energyOkOf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hall, hsum⟩ := h
  rw [I0_eq_sum_pairE' EF]
  have hpair : ∀ i j : Fin D.n, pairE D i j ≤ (((E.getD i.1 []).getD j.1 0 : ℚ) : ℝ) := by
    intro i j
    refine pairOk_sound D i j _ ?_
    have h1 := List.all_eq_true.1 hall i (List.mem_finRange i)
    exact List.all_eq_true.1 h1 j (List.mem_finRange j)
  calc ∑ i, ∑ j, pairE D i j ≤ ∑ i : Fin D.n, ∑ j : Fin D.n, (((E.getD i.1 []).getD j.1 0 : ℚ) : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ((tabSum D E : ℚ) : ℝ) := by unfold tabSum; push_cast; rfl
    _ ≤ D.Ibound := by exact_mod_cast hsum

end CatalanCore.Uniform.Decay.PairEnergy
