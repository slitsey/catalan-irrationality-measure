module

public import CatalanCore.Uniform.Decay.Corners.Split

@[expose] public section

/-!
# Boundary-energy identity on every rectangle, positive definite form

* `BE_nonneg_quadrant`: rectangles in the closed first quadrant `0 ≤ a ≤ b`, `0 ≤ c ≤ d` (smooth
  if `a > 0` or `c > 0`, the singular corner `[0,b]×[0,d]` by `boundary_energy_corner`, and the
  degenerate zero-width cases directly).
* the other three corner orientations by the reflections `BE_negS_iff`, `BE_negT_iff`
  (`B ↦ -B`);
* a singular point in the interior of a rectangle or of an edge: the rectangle is cut at `0`
  (`BE_glue_s`, `BE_glue_t`) into at most four quadrant rectangles, the cut edges cancel.

Final statement: **`BE_pd`**, the identity for every rectangle `[a,b] × [c,d]` (any position of
the singular point `(0,0)`), and `BE_posdef` (from `A, C > 0`, `B² < A C`).
-/

namespace CatalanCore.Uniform.Decay.Corners

open Set intervalIntegral MeasureTheory
open CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Assembly

variable {A B C m K : ℝ}

theorem BE_nonneg_quadrant (h : PD A B C m K) (i j : ℕ) {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) : BE A B C i j a b c d := by
  rcases ha.lt_or_eq with ha' | ha'
  · exact boundary_energy_identity A B C i j hab hcd fun s hs t _ =>
      h.qf_pos (Or.inl (lt_of_lt_of_le ha' hs.1).ne')
  rcases hc.lt_or_eq with hc' | hc'
  · exact boundary_energy_identity A B C i j hab hcd fun s _ t ht =>
      h.qf_pos (Or.inr (lt_of_lt_of_le hc' ht.1).ne')
  subst ha'; subst hc'
  rcases hab.lt_or_eq with hb | hb
  · rcases hcd.lt_or_eq with hd | hd
    · exact boundary_energy_corner h i j hb hd
    · subst hd; simp [BE, BEL, BER]
  · subst hb; simp [BE, BEL, BER]

theorem BE_strip_pos (h : PD A B C m K) (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hcd : c ≤ d) : BE A B C i j a b c d := by
  have left : ∀ {a b : ℝ}, a ≤ b → b ≤ 0 → BE A B C i j a b c d := fun {a b} hab hb =>
    (BE_negS_iff A B C i j a b c d).1
      (BE_nonneg_quadrant h.neg i j (by linarith) (by linarith) hc hcd)
  rcases le_total 0 a with ha | ha
  · exact BE_nonneg_quadrant h i j ha hab hc hcd
  rcases le_total b 0 with hb | hb
  · exact left hab hb
  · exact BE_glue_s h i j ha hb hcd (left ha le_rfl) (BE_nonneg_quadrant h i j le_rfl hb hc hcd)

theorem BE_strip_neg (h : PD A B C m K) (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hd : d ≤ 0) : BE A B C i j a b c d :=
  (BE_negT_iff A B C i j a b c d).1 (BE_strip_pos h.neg i j hab (by linarith) (by linarith))

/-- **Boundary-energy identity for a positive definite form on every rectangle**
(the singular point `(0,0)` may be a vertex, on an edge, in the interior, or outside). -/
theorem BE_pd (h : PD A B C m K) (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    BE A B C i j a b c d := by
  rcases le_total 0 c with hc | hc
  · exact BE_strip_pos h i j hab hc hcd
  rcases le_total d 0 with hd | hd
  · exact BE_strip_neg h i j hab hcd hd
  · exact BE_glue_t h i j hab hc hd (BE_strip_neg h i j hab hc le_rfl) (BE_strip_pos h i j hab le_rfl hd)

/-- Unfolded form of `BE_pd`. -/
theorem boundary_energy_pd (h : PD A B C m K) (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) :
    ((i : ℝ) + j + 2) * ∫ s in a..b, ∫ t in c..d, s ^ i * t ^ j * Lq A B C s t
      = (∫ t in c..d, (b ^ (i + 1) * t ^ j * Lq A B C b t - a ^ (i + 1) * t ^ j * Lq A B C a t))
        + (∫ s in a..b, (s ^ i * d ^ (j + 1) * Lq A B C s d
            - s ^ i * c ^ (j + 1) * Lq A B C s c))
        - (b ^ (i + 1) - a ^ (i + 1)) * (d ^ (j + 1) - c ^ (j + 1))
            / (((i : ℝ) + 1) * ((j : ℝ) + 1)) :=
  BE_pd h i j hab hcd

/-- Same, for `A, C > 0`, `B² < A C` (two non-parallel supporting lines). -/
theorem boundary_energy_posdef {A B C : ℝ} (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 < A * C)
    (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ((i : ℝ) + j + 2) * ∫ s in a..b, ∫ t in c..d, s ^ i * t ^ j * Lq A B C s t
      = (∫ t in c..d, (b ^ (i + 1) * t ^ j * Lq A B C b t - a ^ (i + 1) * t ^ j * Lq A B C a t))
        + (∫ s in a..b, (s ^ i * d ^ (j + 1) * Lq A B C s d
            - s ^ i * c ^ (j + 1) * Lq A B C s c))
        - (b ^ (i + 1) - a ^ (i + 1)) * (d ^ (j + 1) - c ^ (j + 1))
            / (((i : ℝ) + 1) * ((j : ℝ) + 1)) :=
  BE_pd (PD.of_posdef hA hC hB) i j hab hcd

end CatalanCore.Uniform.Decay.Corners
