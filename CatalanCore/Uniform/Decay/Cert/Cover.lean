module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

/-!
# Boolean interval-cover checker (lane D, package D5)

`coverOk a b L` checks, with structural recursion over the list `L` of closed rational intervals,
that `L` covers `[a, b]`: the first cell contains `a`, and every later cell that starts at or before
the current reach extends it.  `coverOk_sound` is the real-number statement used for the
`ray_cover` and `line_cover` fields of `SplineCert`.
-/

namespace CatalanCore.Uniform.Decay.Cert

/-- Extend the covered range `[a, reach]` by the remaining cells. -/
def chainOk (b : ℚ) : ℚ → List (ℚ × ℚ) → Bool
  | reach, [] => decide (b ≤ reach)
  | reach, p :: ps => chainOk b (if p.1 ≤ reach then max reach p.2 else reach) ps

/-- `L` covers `[a, b]` (first cell contains `a`, then chain). -/
def coverOk (a b : ℚ) : List (ℚ × ℚ) → Bool
  | [] => false
  | p :: ps => decide (p.1 ≤ a) && decide (a ≤ p.2) && chainOk b p.2 ps

theorem chainOk_sound (a b : ℚ) (L : List (ℚ × ℚ)) :
    ∀ (ps : List (ℚ × ℚ)) (reach : ℚ), (∀ p ∈ ps, p ∈ L) → a ≤ reach →
      (∀ u : ℝ, (a : ℝ) ≤ u → u ≤ reach → ∃ p ∈ L, (p.1 : ℝ) ≤ u ∧ u ≤ p.2) →
      chainOk b reach ps = true →
      ∀ u : ℝ, (a : ℝ) ≤ u → u ≤ b → ∃ p ∈ L, (p.1 : ℝ) ≤ u ∧ u ≤ p.2 := by
  intro ps
  induction ps with
  | nil =>
    intro reach _ hr hcov h u hu hub
    simp only [chainOk, decide_eq_true_eq] at h
    exact hcov u hu (le_trans hub (by exact_mod_cast h))
  | cons p ps ih =>
    intro reach hps hr hcov h
    simp only [chainOk] at h
    have hp : p ∈ L := hps p (List.mem_cons_self)
    have hps' : ∀ q ∈ ps, q ∈ L := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    by_cases hc : p.1 ≤ reach
    · rw [if_pos hc] at h
      refine ih (max reach p.2) hps' (le_trans hr (le_max_left _ _)) ?_ h
      intro u hu hur
      by_cases hu1 : u ≤ reach
      · exact hcov u hu hu1
      · push_neg at hu1
        refine ⟨p, hp, ?_, ?_⟩
        · have : (p.1 : ℝ) ≤ reach := by exact_mod_cast hc
          linarith
        · have hm : ((max reach p.2 : ℚ) : ℝ) = max (reach : ℝ) (p.2 : ℝ) := by push_cast; rfl
          rw [hm] at hur
          rcases max_cases (reach : ℝ) (p.2 : ℝ) with ⟨h1, _⟩ | ⟨h1, _⟩
          · rw [h1] at hur; linarith
          · rw [h1] at hur; exact hur
    · rw [if_neg hc] at h
      exact ih reach hps' hr hcov h

/-- **Soundness of the cover checker.** -/
theorem coverOk_sound {a b : ℚ} {L : List (ℚ × ℚ)} (h : coverOk a b L = true) :
    ∀ u : ℝ, (a : ℝ) ≤ u → u ≤ b → ∃ p ∈ L, (p.1 : ℝ) ≤ u ∧ u ≤ p.2 := by
  cases L with
  | nil => simp [coverOk] at h
  | cons p ps =>
    simp only [coverOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine chainOk_sound a b (p :: ps) ps p.2 (fun q hq => List.mem_cons_of_mem _ hq) h2 ?_ h3
    intro u hu hup
    refine ⟨p, List.mem_cons_self, ?_, hup⟩
    have : (p.1 : ℝ) ≤ a := by exact_mod_cast h1
    linarith

end CatalanCore.Uniform.Decay.Cert
