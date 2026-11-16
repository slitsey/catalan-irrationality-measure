module

public import CatalanCore.Zeta5.Cells.RegionB
public import CatalanCore.Zeta5.Cells.Cover
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Z5-CELLS, part 10: ZD18, region B as a Lean proposition and the reduction from the cover check

`ZD18 c0 yb α wt N M0` is `∀ x ∈ [0, 3], g_B(x) ≤ M₀` (ledger row ZD18, `x = w_T = 3`).
`regionB_sound`: if a list of cells `(ρ, r, zB)` covers `[0, 3]` (first `ρ = 1`, last `ρ ≥ 449/100`,
so `2 log ρ ≥ 3`; consecutive overlap `2(ρ'/ρ − 1) ≤ r + r'`, from `log u ≤ u − 1`) and every cell
passes `cellOkB`, then `ZD18` holds.  `three_le_two_log` is the fact `log (449/100) ≥ 3/2`
(`e³ < 20.0856 < 4.49²`).
-/

namespace CatalanCore.Zeta5.Cells

open Set Real

noncomputable section

def ZD18 (c0 yb α : ℝ) (wt : ℕ → ℝ) (N : ℕ) (M0 : ℝ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 3, gB c0 yb α wt N x ≤ M0

theorem three_le_two_log : (3 : ℝ) ≤ 2 * Real.log (449 / 100) := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.exp (3 / 2) ≤ 449 / 100 := by
    by_contra hc
    have hc' := not_le.mp hc
    have : (449 / 100 : ℝ) ^ 2 < Real.exp (3 / 2) ^ 2 := by
      apply pow_lt_pow_left₀ hc' (by norm_num) (by norm_num)
    have h4 : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
    nlinarith
  have := (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 449 / 100)).mpr h3
  linarith

def chainOkB : List CellB → Bool
  | [] => true
  | [c] => decide (0 < c.r)
  | c :: d :: t =>
      decide (1 ≤ c.ρ ∧ c.ρ ≤ d.ρ ∧ 0 < c.r ∧ 2 * (d.ρ / c.ρ - 1) ≤ c.r + d.r) &&
        chainOkB (d :: t)

def coverOkB (cells : List CellB) : Bool :=
  match cells with
  | [] => false
  | c :: _ => decide (c.ρ = 1) &&
      (match cells.getLast? with | some d => decide (449 / 100 ≤ d.ρ) | none => false) &&
      chainOkB cells

def cellsOkB (des : DesB) (tab : TabB) (cells : List CellB) : Bool := cells.all (cellOkB des tab)

def cellPairB (c : CellB) : ℝ × ℝ := (2 * Real.log (c.ρ : ℝ), (c.r : ℝ))

theorem chainOkB_spec : ∀ cells : List CellB, chainOkB cells = true →
    Chain (cells.map cellPairB) ∧ ∀ c ∈ cells, 0 < c.r
  | [], _ => ⟨trivial, by simp⟩
  | [c], h => by
    simp only [chainOkB, decide_eq_true_eq] at h
    exact ⟨trivial, by simpa using h⟩
  | c :: d :: t, h => by
    simp only [chainOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, h1, h2, h3⟩, h4⟩ := h
    obtain ⟨ih1, ih2⟩ := chainOkB_spec (d :: t) h4
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, Chain, cellPairB] at ih1 ⊢
      have hc : (0 : ℝ) < (c.ρ : ℝ) := by
        have : (1 : ℝ) ≤ (c.ρ : ℝ) := by exact_mod_cast h0
        linarith
      have hd : (c.ρ : ℝ) ≤ (d.ρ : ℝ) := by exact_mod_cast h1
      refine ⟨?_, ?_, ih1⟩
      · have := Real.log_le_log hc hd
        linarith
      · have hd0 : (0 : ℝ) < (d.ρ : ℝ) := by linarith
        have hl : Real.log (d.ρ : ℝ) - Real.log (c.ρ : ℝ) ≤ (d.ρ : ℝ) / (c.ρ : ℝ) - 1 := by
          rw [← Real.log_div hd0.ne' hc.ne']
          exact Real.log_le_sub_one_of_pos (by positivity)
        have h3' : 2 * ((d.ρ : ℝ) / (c.ρ : ℝ) - 1) ≤ (c.r : ℝ) + d.r := by exact_mod_cast h3
        linarith
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact h2
      · exact ih2 e he

theorem regionB_sound (des : DesB) (tab : TabB) (wt : ℕ → ℝ)
    (hdes : desOkB des = true)
    (hw : ∀ k < des.ws.length, wt k = ((des.ws.getD k 0 : ℚ) : ℝ))
    (hW0 : tab.W0 = wTabB 0 0 des.ws) (hW1 : tab.W1 = wTabB 0 1 des.ws)
    (hW2 : tab.W2 = wTabB 0 2 des.ws) (hW3 : tab.W3 = wTabB 0 3 des.ws)
    (hW4 : tab.W4 = wTabB 0 4 des.ws)
    (hL : CatalanMeasure.GenD.Signed.LogEval.Enc (Real.log ((des.yb : ℝ) ^ 2 / 4)) tab.L0)
    (cells : List CellB) (hcov : coverOkB cells = true) (hcells : cellsOkB des tab cells = true) :
    ZD18 (des.lam : ℝ) (des.yb : ℝ) (des.α : ℝ) wt des.ws.length (des.M0 : ℝ) := by
  intro x hx
  cases hc : cells with
  | nil => simp [coverOkB, hc] at hcov
  | cons c t =>
    rw [hc] at hcov hcells
    simp only [coverOkB, Bool.and_eq_true, decide_eq_true_eq] at hcov
    obtain ⟨⟨hρ0, hlast⟩, hch⟩ := hcov
    obtain ⟨hchain, hrad⟩ := chainOkB_spec _ hch
    have hne : c :: t ≠ [] := by simp
    have hl : 449 / 100 ≤ ((c :: t).getLast hne).ρ := by
      rw [List.getLast?_eq_getLast_of_ne_nil hne] at hlast
      simpa using hlast
    have hc0 : (c.r : ℝ) ≥ 0 := by exact_mod_cast (hrad c (by simp)).le
    obtain ⟨p, hp, hpz⟩ := chain_cover (t.map cellPairB) (2 * Real.log (c.ρ : ℝ)) (c.r : ℝ) hc0
      (fun p hp => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
        have := hrad e (by simp [he])
        simp only [cellPairB]; exact_mod_cast this.le)
      (by simpa [cellPairB] using hchain) x
      (by rw [hρ0]; simpa using hx.1)
      (by
        show x ≤ (((c :: t).map cellPairB).getLast (by simp)).1
        have h2 : ((c :: t).map cellPairB).getLast (by simp) =
            cellPairB ((c :: t).getLast hne) :=
          List.getLast_map (f := cellPairB) (l := c :: t) _
        rw [h2]
        simp only [cellPairB]
        have h449 : (449 / 100 : ℝ) ≤ (((c :: t).getLast hne).ρ : ℝ) := by
          have := (Rat.cast_le (K := ℝ)).mpr hl
          push_cast at this
          exact this
        have := Real.log_le_log (by norm_num) h449
        have h3 := three_le_two_log
        have := hx.2
        push_cast at *
        linarith)
    obtain ⟨e, he, rfl⟩ : ∃ e ∈ c :: t, cellPairB e = p := by
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨c, by simp, rfl⟩
      · obtain ⟨e, he, he2⟩ := List.mem_map.mp hp'
        exact ⟨e, by simp [he], he2⟩
    have hok : cellOkB des tab e = true := by
      simp only [cellsOkB, List.all_eq_true] at hcells
      exact hcells e he
    refine cellB_sound des tab e wt hdes hw hW0 hW1 hW2 hW3 hW4 hL hok x ?_
    simp only [cellPairB] at hpz
    rw [abs_le] at hpz
    constructor <;> linarith [hpz.1, hpz.2]

end

end CatalanCore.Zeta5.Cells
