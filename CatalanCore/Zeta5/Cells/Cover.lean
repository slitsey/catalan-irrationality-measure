module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# Z5-CELLS, part 7: covering an interval by a chain of cells

`Chain L` says that the cells `(centre, radius)` of `L` are ordered and consecutive cells
overlap (`b − a ≤ ra + rb`).  `chain_cover`: then every point between the first and the last
centre lies in some cell.  `arctan_sub_le`: `arctan m' − arctan m ≤ (m'−m)/(1+mm')` for
`0 ≤ m ≤ m'`, which turns the overlap condition of region A into a rational test
(centres `2 arctan m`, no transcendental value is needed for the cover).
-/

namespace CatalanCore.Zeta5.Cells

open Real

noncomputable section

def Chain : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | (a, ra) :: (b, rb) :: t => a ≤ b ∧ b - a ≤ ra + rb ∧ Chain ((b, rb) :: t)

theorem chain_cover : ∀ (L : List (ℝ × ℝ)) (a ra : ℝ), 0 ≤ ra → (∀ p ∈ L, 0 ≤ p.2) →
    Chain ((a, ra) :: L) → ∀ z : ℝ, a ≤ z → z ≤ (((a, ra) :: L).getLast (by simp)).1 →
    ∃ p ∈ (a, ra) :: L, |z - p.1| ≤ p.2 := by
  intro L
  induction L with
  | nil =>
    intro a ra hra _ _ z hz1 hz2
    simp only [List.getLast_singleton] at hz2
    refine ⟨(a, ra), by simp, ?_⟩
    have : z = a := le_antisymm hz2 hz1
    simp [this, hra]
  | cons q t ih =>
    obtain ⟨b, rb⟩ := q
    intro a ra hra hL hch z hz1 hz2
    obtain ⟨hab, hov, hch'⟩ := hch
    have hrb : 0 ≤ rb := hL (b, rb) (by simp)
    by_cases hza : z ≤ a + ra
    · exact ⟨(a, ra), by simp, by rw [abs_le]; constructor <;> linarith⟩
    · have hza := not_le.mp hza
      by_cases hzb : z < b
      · refine ⟨(b, rb), by simp, ?_⟩
        rw [abs_le]; constructor <;> linarith
      · have hzb := not_lt.mp hzb
        have hz2' : z ≤ (((b, rb) :: t).getLast (by simp)).1 := by
          rw [List.getLast_cons (by simp)] at hz2
          exact hz2
        obtain ⟨p, hp, hpz⟩ := ih b rb hrb (fun p hp => hL p (by simp [hp])) hch' z hzb hz2'
        exact ⟨p, by simp at hp ⊢; tauto, hpz⟩

theorem arctan_sub_le {m m' : ℝ} (hm : 0 ≤ m) (hmm : m ≤ m') :
    Real.arctan m' - Real.arctan m ≤ (m' - m) / (1 + m * m') := by
  have hpos : 0 < 1 + m * m' := by nlinarith
  have h := Real.arctan_add (x := m') (y := -m) (by nlinarith)
  rw [Real.arctan_neg] at h
  have h2 : Real.arctan m' - Real.arctan m = Real.arctan ((m' + -m) / (1 - m' * -m)) := by
    rw [← h]; ring
  rw [h2]
  have : (m' + -m) / (1 - m' * -m) = (m' - m) / (1 + m * m') := by
    congr 1 <;> ring
  rw [this]
  exact Real.arctan_le_self (div_nonneg (by linarith) hpos.le)

end

end CatalanCore.Zeta5.Cells
