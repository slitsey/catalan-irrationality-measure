module

public import CatalanCore.Uniform.Decay.Cells.Rules

@[expose] public section

/-!
# The energy rule: pairwise decomposition (lane D, package D6)

`I0 = Σ_i ∫ f_i U0(p_i) = Σ_{i,j} E_ij` with the pair energy
`E_ij = ∫_0^1 f_i(s) U_j(p_i(s)) ds`, `U_j` the potential of the single segment `j`.
All integrals are of continuous functions (`U_j` is continuous by the global modulus applied to
the one-segment family), so the decomposition is proved, not assumed.  The rule `energyOkOf`
checks a table `E` of pair-energy upper bounds against an oracle and `Σ E ≤ Ibound`.
-/

namespace CatalanCore.Uniform.Decay.Cells

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Assembly

variable {D : SplineData}

/-- Potential of the single segment `j`. -/
noncomputable def segU (D : SplineData) (j : Fin D.n) (z : ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, D.f j t * (-Real.log ‖z - pt D.A D.B j t‖)

/-- Pair energy `E_ij`. -/
noncomputable def pairE (D : SplineData) (i j : Fin D.n) : ℝ :=
  ∫ s in (0 : ℝ)..1, D.f i s * segU D j (pt D.A D.B i s)

theorem U0_eq_sum (z : ℂ) : U0 D.A D.B D.f z = ∑ j, segU D j z := rfl

theorem segU_eq_U0 (j : Fin D.n) :
    segU D j = U0 (fun _ : Fin 1 => D.A j) (fun _ : Fin 1 => D.B j) (fun _ : Fin 1 => D.f j) := by
  funext z
  simp [U0, segU, pt]

theorem segU_continuous (B : SplineData.BasicFacts D) (j : Fin D.n) : Continuous (segU D j) := by
  rw [segU_eq_U0]
  have hf0 : ∀ i : Fin 1, ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (fun _ : Fin 1 => D.f j) i t :=
    fun i t ht => (density_bounds B j t ht.1 ht.2).1
  refine continuous_of_modulus (K := Real.pi * Bs (fun _ : Fin 1 => D.A j) (fun _ : Fin 1 => D.B j)
    (fun _ => (D.M j : ℝ))) (V := Vp (fun _ : Fin 1 => D.f j)) ?_ ?_ ?_
  · refine mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun i _ => div_nonneg ?_ (norm_nonneg _))
    have h2 := density_bounds B j 0 le_rfl zero_le_one
    exact h2.1.trans h2.2
  · exact Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg zero_le_one
      (fun t _ => abs_nonneg _)
  · intro a ha z w
    have := U0_modulus (fun _ => B.hAB j) (fun _ => density_cont j) hf0
      (fun _ => density_abs B j) ha z w
    simp only at this ⊢
    linarith

/-- **Pair decomposition of the energy.** -/
theorem I0_eq_sum_pairE (B : SplineData.BasicFacts D) :
    I0 D.A D.B D.f = ∑ i, ∑ j, pairE D i j := by
  unfold I0 pairE
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : ∀ j, Continuous (fun s => D.f i s * segU D j (pt D.A D.B i s)) := fun j =>
    (density_cont i).mul ((segU_continuous B j).comp (continuous_pt D.A D.B i))
  have : (fun s => D.f i s * U0 D.A D.B D.f (pt D.A D.B i s)) =
      fun s => ∑ j, D.f i s * segU D j (pt D.A D.B i s) := by
    funext s
    rw [U0_eq_sum, Finset.mul_sum]
  rw [this, intervalIntegral.integral_finsetSum]
  intro j _
  exact (hc j).intervalIntegrable _ _

/-- Oracle for pair energies. -/
structure PairOracle where
  pairOk : SplineData → ℕ → ℕ → ℚ → Bool
  pair_sound : ∀ D : SplineData, D.basicOk = true → ∀ (i j : Fin D.n) (E : ℚ),
    pairOk D i.1 j.1 E = true → pairE D i j ≤ E

/-- Sum of a rational table `E : List (List ℚ)` over `Fin n × Fin n`. -/
def tabSum (D : SplineData) (E : List (List ℚ)) : ℚ :=
  ∑ i : Fin D.n, ∑ j : Fin D.n, (E.getD i.1 []).getD j.1 0

/-- The energy checker. -/
def energyOkOf (O : PairOracle) (E : List (List ℚ)) (D : SplineData) : Bool :=
  (List.finRange D.n).all (fun i => (List.finRange D.n).all fun j =>
    O.pairOk D i.1 j.1 ((E.getD i.1 []).getD j.1 0)) && decide (tabSum D E ≤ D.Ibound)

theorem energyOkOf_sound (O : PairOracle) (E : List (List ℚ)) (D : SplineData)
    (hb : D.basicOk = true) (h : energyOkOf O E D = true) : I0 D.A D.B D.f ≤ D.Ibound := by
  simp only [energyOkOf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hall, hsum⟩ := h
  have B := SplineData.basicOk_sound hb
  rw [I0_eq_sum_pairE B]
  have hpair : ∀ i j : Fin D.n, pairE D i j ≤ (((E.getD i.1 []).getD j.1 0 : ℚ) : ℝ) := by
    intro i j
    refine O.pair_sound D hb i j _ ?_
    have h1 := List.all_eq_true.1 hall i (List.mem_finRange i)
    exact List.all_eq_true.1 h1 j (List.mem_finRange j)
  calc ∑ i, ∑ j, pairE D i j ≤ ∑ i : Fin D.n, ∑ j : Fin D.n, (((E.getD i.1 []).getD j.1 0 : ℚ) : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ((tabSum D E : ℚ) : ℝ) := by unfold tabSum; push_cast; rfl
    _ ≤ D.Ibound := by exact_mod_cast hsum

end CatalanCore.Uniform.Decay.Cells
