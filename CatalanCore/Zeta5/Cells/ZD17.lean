module

public import CatalanCore.Zeta5.Cells.RegionA
public import CatalanCore.Zeta5.Cells.Cover

@[expose] public section

/-!
# Z5-CELLS, part 8: ZD17, region A as a Lean proposition and the reduction from the cover check

`ZD17 c0 yb α w N M0` is the statement `∀ φ ∈ [0, π/2], g_A(φ) ≤ M₀` (ledger row ZD17, with
`t = b cos²φ`, `y = y_b cos φ`).  `regionA_sound`: if a list of cells covers `[0, π/2]`
(first centre `m = 0`, last `m = 1`, overlap tested rationally) and every cell passes
`cellOkA`, then `ZD17` holds.  The cover test needs no transcendental value
(`arctan_sub_le`).
-/

namespace CatalanCore.Zeta5.Cells

open Set Real

noncomputable section

/-- **ZD17**: the region-A pointwise inequality. -/
def ZD17 (c0 yb α : ℝ) (w : ℕ → ℝ) (N : ℕ) (M0 : ℝ) : Prop :=
  ∀ φ ∈ Icc (0 : ℝ) (π / 2), gA c0 yb α w N φ ≤ M0

/-- overlap test of consecutive cells (rational) -/
def chainOkA : List CellA → Bool
  | [] => true
  | [c] => decide (0 < c.r)
  | c :: d :: t =>
      decide (0 ≤ c.m ∧ c.m ≤ d.m ∧ 0 < c.r ∧ d.m - c.m ≤ (c.r + d.r) / 2 * (1 + c.m * d.m)) &&
        chainOkA (d :: t)

/-- the cover test: first centre `φ = 0`, last centre `φ = π/2`, chain of overlaps -/
def coverOkA (cells : List CellA) : Bool :=
  match cells with
  | [] => false
  | c :: _ => decide (c.m = 0) && decide ((cells.getLast?).map (fun c => c.m) = some 1) &&
      chainOkA cells

def cellsOkA (des : DesA) (tab : TabA) (cells : List CellA) : Bool := cells.all (cellOkA des tab)

def cellPair (c : CellA) : ℝ × ℝ := (2 * Real.arctan (c.m : ℝ), (c.r : ℝ))

theorem chainOkA_spec : ∀ cells : List CellA, chainOkA cells = true →
    Chain (cells.map cellPair) ∧ ∀ c ∈ cells, 0 < c.r
  | [], _ => ⟨trivial, by simp⟩
  | [c], h => by
    simp only [chainOkA, decide_eq_true_eq] at h
    exact ⟨trivial, by simpa using h⟩
  | c :: d :: t, h => by
    simp only [chainOkA, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, h1, h2, h3⟩, h4⟩ := h
    obtain ⟨ih1, ih2⟩ := chainOkA_spec (d :: t) h4
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, Chain, cellPair] at ih1 ⊢
      refine ⟨?_, ?_, ih1⟩
      · have : Real.arctan (c.m : ℝ) ≤ Real.arctan (d.m : ℝ) :=
          Real.arctan_strictMono.monotone (by exact_mod_cast h1)
        linarith
      · have hm : (0 : ℝ) ≤ (c.m : ℝ) := by exact_mod_cast h0
        have hmm : (c.m : ℝ) ≤ (d.m : ℝ) := by exact_mod_cast h1
        have hs := arctan_sub_le hm hmm
        have hpos : (0 : ℝ) < 1 + (c.m : ℝ) * (d.m : ℝ) := by nlinarith
        have h3' : ((d.m : ℝ) - c.m) ≤ ((c.r : ℝ) + d.r) / 2 * (1 + (c.m : ℝ) * d.m) := by
          exact_mod_cast h3
        have : ((d.m : ℝ) - c.m) / (1 + (c.m : ℝ) * d.m) ≤ ((c.r : ℝ) + d.r) / 2 := by
          rw [div_le_iff₀ hpos]; exact h3'
        linarith
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact h2
      · exact ih2 e he

theorem regionA_sound (des : DesA) (tab : TabA) (w : ℕ → ℝ)
    (hα : 0 < des.α) (hyb : 0 < des.yb)
    (hw : ∀ k < des.ws.length, w k = ((des.ws.getD k 0 : ℚ) : ℝ))
    (hW0 : tab.W0 = wTabAux 0 0 des.ws) (hW1 : tab.W1 = wTabAux 0 1 des.ws)
    (hW2 : tab.W2 = wTabAux 0 2 des.ws) (hW3 : tab.W3 = wTabAux 0 3 des.ws)
    (hW4 : tab.W4 = wTabAux 0 4 des.ws) (hTR : tab.TR = trA des.ws)
    (hL : CatalanMeasure.GenD.Signed.LogEval.Enc (Real.log ((des.yb : ℝ) ^ 2 / 4)) tab.L0)
    (cells : List CellA) (hcov : coverOkA cells = true) (hcells : cellsOkA des tab cells = true) :
    ZD17 (des.lam : ℝ) (des.yb : ℝ) (des.α : ℝ) w des.ws.length (des.M0 : ℝ) := by
  intro φ hφ
  cases hc : cells with
  | nil => simp [coverOkA, hc] at hcov
  | cons c t =>
    rw [hc] at hcov hcells
    simp only [coverOkA, Bool.and_eq_true, decide_eq_true_eq] at hcov
    obtain ⟨⟨hm0, hmlast⟩, hch⟩ := hcov
    obtain ⟨hchain, hrad⟩ := chainOkA_spec _ hch
    have hne : c :: t ≠ [] := by simp
    have hl : ((c :: t).getLast hne).m = 1 := by
      have := hmlast
      rw [List.getLast?_eq_getLast_of_ne_nil hne] at this
      simpa using this
    have hc0 : (c.r : ℝ) ≥ 0 := by exact_mod_cast (hrad c (by simp)).le
    obtain ⟨p, hp, hpz⟩ := chain_cover (t.map cellPair) (2 * Real.arctan (c.m : ℝ)) (c.r : ℝ) hc0
      (fun p hp => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
        have := hrad e (by simp [he])
        simp only [cellPair]; exact_mod_cast this.le)
      (by simpa [cellPair] using hchain) φ
      (by rw [hm0]; simpa using hφ.1)
      (by
        show φ ≤ (((c :: t).map cellPair).getLast (by simp)).1
        have h2 : ((c :: t).map cellPair).getLast (by simp) = cellPair ((c :: t).getLast hne) :=
          List.getLast_map (f := cellPair) (l := c :: t) _
        rw [h2]
        simp only [cellPair, hl]
        rw [Rat.cast_one, Real.arctan_one]
        have := hφ.2
        push_cast
        linarith)
    obtain ⟨e, he, rfl⟩ : ∃ e ∈ c :: t, cellPair e = p := by
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨c, by simp, rfl⟩
      · obtain ⟨e, he, he2⟩ := List.mem_map.mp hp'
        exact ⟨e, by simp [he], he2⟩
    have hok : cellOkA des tab e = true := by
      simp only [cellsOkA, List.all_eq_true] at hcells
      exact hcells e he
    refine cellA_sound des tab e w hα hyb hw hW0 hW1 hW2 hW3 hW4 hTR hL hok φ ?_
    simp only [cellPair] at hpz
    rw [abs_le] at hpz
    constructor <;> linarith [hpz.1, hpz.2]

end

end CatalanCore.Zeta5.Cells
