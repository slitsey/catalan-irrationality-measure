module
public import CatalanCore.Uniform.Decay.Nodes.Closed
public import CatalanCore.Uniform.Decay.Nodes.Count
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
@[expose] public section

/-!
# Interval-uniform node measures: limiting measures, potentials, separate energies

A periodic block `{u r ≤ j < v r, j ≡ residue (mod d)}` has limiting measure `(1/d) Leb[u, v]`
(the single residue; a residue set `S` is the sum over `S`, giving `|S|/d`).  A `Piece` is a
weighted interval; a node measure is a list of pieces.

* `Piece.pot`, closed form (log and linear terms) of the logarithmic potential on the real line;
* `mutE` / `nodeEnergy`: the exact bilinear energy, and `nodeEnergy = (I(μR) + I(μQ))/2`,
  the AVERAGE of the separate row and column energies;
* `nodeEnergy_eq_avg_add`: it differs from the energy of the averaged measure `ν = (μR+μQ)/2`
  by `(I(μR) + I(μQ) - I(μR,μQ) - I(μQ,μR))/4 = I(μR - μQ)/4`; the gap is `log 2` in an
  explicit example (`nodeEnergy_gap_example`).
* The limiting CDF `Piece.cdf` is the Lebesgue measure of `[lo,hi] ∩ (-∞, s]`, and
  `PeriodicBlock.prefixMass_eq_cdf` matches it to the counting prefix prediction of `Count`.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open CatalanCore.Uniform

/-- A weighted interval: density `w` on `[lo, hi]`. -/
structure Piece where
  w : ℝ
  lo : ℝ
  hi : ℝ

namespace Piece

/-- Total mass `w (hi - lo)`. -/
def mass (P : Piece) : ℝ := P.w * (P.hi - P.lo)

/-- Logarithmic potential `-w ∫ log|x - t| dt` at a real point: log and linear terms only. -/
noncomputable def pot (P : Piece) (x : ℝ) : ℝ := -P.w * (Lam (x - P.lo) - Lam (x - P.hi))

theorem pot_eq_integral (P : Piece) (x : ℝ) :
    P.pot x = ∫ t in P.lo..P.hi, -P.w * Real.log |x - t| := by
  have h : ∀ t : ℝ, -P.w * Real.log |x - t| = P.w * (-Real.log |x - t|) := fun t => by ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_neg_log_abs]
  unfold pot
  ring

/-- Limiting cumulative distribution function. -/
noncomputable def cdf (P : Piece) (s : ℝ) : ℝ := P.w * max 0 (min s P.hi - P.lo)

theorem cdf_eq_volume (P : Piece) (s : ℝ) :
    P.cdf s = P.w * (MeasureTheory.volume (Set.Ioc P.lo P.hi ∩ Set.Iic s)).toReal := by
  rw [Set.Ioc_inter_Iic, Real.volume_Ioc, ENNReal.toReal_ofReal']
  unfold cdf
  rw [min_comm, max_comm]

end Piece

/-- Mutual energy of two pieces, from the exact interval formula. -/
noncomputable def pairInteraction (P Q : Piece) : ℝ :=
  P.w * Q.w * pairEnergy P.lo P.hi Q.lo Q.hi

theorem pairInteraction_comm (P Q : Piece) : pairInteraction P Q = pairInteraction Q P := by
  unfold pairInteraction
  rw [pairEnergy_comm]
  ring

/-- Total mass of a node measure. -/
def pmass (A : List Piece) : ℝ := (A.map Piece.mass).sum

/-- Potential of a node measure at a real point. -/
noncomputable def ppot (A : List Piece) (x : ℝ) : ℝ := (A.map fun P => P.pot x).sum

/-- Bilinear energy. -/
noncomputable def mutE (A B : List Piece) : ℝ :=
  (A.map fun P => (B.map fun Q => pairInteraction P Q).sum).sum

/-- Multiplication of the density by a constant. -/
noncomputable def pscale (c : ℝ) (A : List Piece) : List Piece := A.map fun P => { P with w := c * P.w }

theorem mutE_nil_left (B : List Piece) : mutE [] B = 0 := by simp [mutE]

theorem mutE_nil_right (A : List Piece) : mutE A [] = 0 := by simp [mutE]

theorem mutE_cons_left (P : Piece) (A B : List Piece) :
    mutE (P :: A) B = (B.map fun Q => pairInteraction P Q).sum + mutE A B := by
  simp [mutE]

theorem mutE_append_left (A A' B : List Piece) :
    mutE (A ++ A') B = mutE A B + mutE A' B := by
  simp [mutE]

theorem mutE_append_right (A B B' : List Piece) :
    mutE A (B ++ B') = mutE A B + mutE A B' := by
  induction A with
  | nil => simp [mutE_nil_left]
  | cons P A ih =>
    rw [mutE_cons_left, mutE_cons_left, mutE_cons_left, ih]
    simp only [List.map_append, List.sum_append]
    ring

theorem mutE_comm (A B : List Piece) : mutE A B = mutE B A := by
  induction A with
  | nil => rw [mutE_nil_left, mutE_nil_right]
  | cons P A ih =>
    have h1 : mutE B (P :: A) = mutE B [P] + mutE B A := mutE_append_right B [P] A
    have h2 : mutE B [P] = (B.map fun Q => pairInteraction Q P).sum := by simp [mutE]
    rw [mutE_cons_left, ih, h1, h2]
    congr 1
    exact congrArg List.sum (List.map_congr_left fun Q _ => pairInteraction_comm P Q)

theorem mutE_pscale_left (c : ℝ) (A B : List Piece) :
    mutE (pscale c A) B = c * mutE A B := by
  induction A with
  | nil => simp [pscale, mutE_nil_left]
  | cons P A ih =>
    have h : pscale c (P :: A) = { P with w := c * P.w } :: pscale c A := rfl
    rw [h, mutE_cons_left, mutE_cons_left, ih, mul_add]
    congr 1
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun Q _ => ?_)
    unfold pairInteraction
    ring

theorem mutE_pscale_right (c : ℝ) (A B : List Piece) :
    mutE A (pscale c B) = c * mutE A B := by
  rw [mutE_comm, mutE_pscale_left, mutE_comm]

/-- The separate energy of a node measure. -/
noncomputable def selfEnergy (A : List Piece) : ℝ := mutE A A

/-- The node energy of a row measure `R` and column measure `Q`: the AVERAGE of the separate
energies, `J_node = (I(R) + I(Q))/2`. -/
noncomputable def nodeEnergy (R Q : List Piece) : ℝ := (selfEnergy R + selfEnergy Q) / 2

/-- The averaged measure `ν = (R + Q)/2`. -/
noncomputable def avgMeasure (R Q : List Piece) : List Piece := pscale (1 / 2) R ++ pscale (1 / 2) Q

/-- `J_node = I(ν) + I(R - Q)/4`: the node energy is NOT the energy of the averaged measure. -/
theorem nodeEnergy_eq_avg_add (R Q : List Piece) :
    nodeEnergy R Q = selfEnergy (avgMeasure R Q) +
      (selfEnergy R + selfEnergy Q - 2 * mutE R Q) / 4 := by
  unfold nodeEnergy selfEnergy avgMeasure
  simp only [mutE_append_left, mutE_append_right, mutE_pscale_left, mutE_pscale_right]
  rw [mutE_comm Q R]
  ring

end CatalanCore.Uniform.Decay.Nodes
