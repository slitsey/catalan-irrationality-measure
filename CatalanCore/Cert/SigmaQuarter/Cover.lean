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

end CatalanCore.Cert.SigmaQuarter
