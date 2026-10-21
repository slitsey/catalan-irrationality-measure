module

public import CatalanCore.Cert.SigmaQuarter.Box

@[expose] public section

namespace CatalanCore.Cert.SigmaQuarter

/-- A linear-time certificate that a finite list of rational intervals covers
the requested interval. Extra intervals after the first successful endpoint
are harmless. -/
def chainCovers : List (ℚ × ℚ) → ℚ → ℚ → Bool
  | [], _, _ => false
  | (a,b) :: ps, lo, hi => decide (a ≤ lo) && (decide (hi ≤ b) || chainCovers ps b hi)

theorem chainCovers_sound (ps : List (ℚ × ℚ)) (lo hi : ℚ)
    (hc : chainCovers ps lo hi = true) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    ∃ p ∈ ps, (p.1 : ℝ) ≤ x ∧ x ≤ (p.2 : ℝ) := by
  induction ps generalizing lo with
  | nil => simp [chainCovers] at hc
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    simp only [chainCovers, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hc
    have ha : (a : ℝ) ≤ x := (Rat.cast_le.mpr hc.1).trans hlo
    by_cases hb : x ≤ (b : ℝ)
    · exact ⟨(a,b), by simp, ha, hb⟩
    · have htail : chainCovers ps b hi = true := by
        rcases hc.2 with hc | hc
        · have hh : (hi : ℝ) ≤ b := Rat.cast_le.mpr hc
          exact False.elim (hb (hhi.trans hh))
        · exact hc
      obtain ⟨p,hp,h1,h2⟩ := ih b htail (le_of_not_ge hb)
      exact ⟨p, by simp [hp], h1, h2⟩

/-- Semantic coverage composes without retaining a long Boolean evaluation. -/
def IntervalCovers (ps : List (ℚ × ℚ)) (lo hi : ℚ) : Prop :=
  ∀ x : ℝ, (lo : ℝ) ≤ x → x ≤ (hi : ℝ) →
    ∃ p ∈ ps, (p.1 : ℝ) ≤ x ∧ x ≤ (p.2 : ℝ)

theorem intervalCovers_append {a b : List (ℚ × ℚ)} {lo mid start hi : ℚ}
    (ha : IntervalCovers a lo mid) (hb : IntervalCovers b start hi)
    (hgap : start ≤ mid) : IntervalCovers (a ++ b) lo hi := by
  intro x hx hy
  by_cases hm : x ≤ (mid : ℝ)
  · obtain ⟨p, hp, h1, h2⟩ := ha x hx hm
    exact ⟨p, List.mem_append_left _ hp, h1, h2⟩
  · have hs : (start : ℝ) ≤ x := (Rat.cast_le.mpr hgap).trans (le_of_not_ge hm)
    obtain ⟨p, hp, h1, h2⟩ := hb x hs hy
    exact ⟨p, List.mem_append_right _ hp, h1, h2⟩

theorem intervalCovers_restrict {ps : List (ℚ × ℚ)} {lo hi lo' hi' : ℚ}
    (h : IntervalCovers ps lo hi) (hl : lo ≤ lo') (hh : hi' ≤ hi) :
    IntervalCovers ps lo' hi' := by
  intro x hx hy
  exact h x ((Rat.cast_le.mpr hl).trans hx) (hy.trans (Rat.cast_le.mpr hh))
end CatalanCore.Cert.SigmaQuarter
