module

public import CatalanCore.Uniform.Decay.PairEnergy.Red4

@[expose] public section

/-!
# The pair energy as a computable linear form (lane D, package D6c)

`pairLF P` is a computable `LF` (rational data, `QC` arithmetic, log/arg atoms) whose value is the
pair energy `∫₀¹ f₁(s) ∫₀¹ f₂(t) (-log ‖p₁(s) - p₂(t)‖) dt ds` of two segments with Gaussian rational
endpoints and rational polynomial densities, given a common point `p₁(s₀) = p₂(t₀)`
(`s₀, t₀` rational, checked by the Boolean `relOk`).
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset Set intervalIntegral MeasureTheory

def listOf (f : ℕ → ℚ) (N : ℕ) : List ℚ := (List.range N).map f

theorem length_listOf (f : ℕ → ℚ) (N : ℕ) : (listOf f N).length = N := by simp [listOf]

theorem getD_listOf (f : ℕ → ℚ) (N l : ℕ) (hl : l < N) : (listOf f N).getD l 0 = f l := by
  simp [listOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]

theorem evalL_listOf (f : ℕ → ℚ) (N : ℕ) (T : ℝ) :
    evalL (listOf f N) T = ∑ l ∈ range N, ((f l : ℚ) : ℝ) * T ^ l := by
  rw [evalL_eq_sum _ _ N (by simp [length_listOf])]
  exact Finset.sum_congr rfl fun l hl => by rw [getD_listOf f N l (Finset.mem_range.1 hl)]

/-- Data of a pair: Gaussian rational segments, polynomial densities, common-point parameters. -/
structure PairData where
  A1 : QC
  B1 : QC
  A2 : QC
  B2 : QC
  a : List ℚ
  b : List ℚ
  s0 : ℚ
  t0 : ℚ

namespace PairData

def al (P : PairData) : List ℚ := pshift P.a P.s0
def be (P : PairData) : List ℚ := pshift P.b P.t0

/-- Weight list of the `t`-edge polynomials. -/
def cw (P : PairData) (e : ℚ) : ℕ → ℚ := fun l =>
  P.be.getD l 0 * sumR (fun k => P.al.getD k 0 * e ^ (k + 1) / ((k : ℚ) + l + 2)) P.al.length

/-- Weight list of the `s`-edge polynomials. -/
def dw (P : PairData) (e : ℚ) : ℕ → ℚ := fun k =>
  P.al.getD k 0 * sumR (fun l => P.be.getD l 0 * e ^ (l + 1) / ((k : ℚ) + l + 2)) P.be.length

/-- The rational constant. -/
def qc (P : PairData) : ℚ :=
  sumR (fun k => sumR (fun l => P.al.getD k 0 * P.be.getD l 0 / ((k : ℚ) + l + 2) *
    ((((1 - P.s0) ^ (k + 1) - (0 - P.s0) ^ (k + 1)) * ((1 - P.t0) ^ (l + 1) - (0 - P.t0) ^ (l + 1)))
      / (((k : ℚ) + 1) * ((l : ℚ) + 1)))) P.be.length) P.al.length

/-- Relation `A₁ - A₂ + s₀ (B₁ - A₁) - t₀ (B₂ - A₂)` in `QC`. -/
def rel (P : PairData) : QC :=
  QC.sub (QC.add (QC.sub P.A1 P.A2) (QC.qmul P.s0 (QC.sub P.B1 P.A1))) (QC.qmul P.t0 (QC.sub P.B2 P.A2))

def pairLF (P : PairData) : LF :=
  let Nb := P.be.length
  let Na := P.al.length
  let Pb := potLF P.A2 P.B2 P.B1 (pshift (listOf (P.cw (1 - P.s0)) Nb) (-P.t0))
  let Pa := potLF P.A2 P.B2 P.A1 (pshift (listOf (P.cw (0 - P.s0)) Nb) (-P.t0))
  let Pd := potLF P.A1 P.B1 P.B2 (pshift (listOf (P.dw (1 - P.t0)) Na) (-P.s0))
  let Pc := potLF P.A1 P.B1 P.A2 (pshift (listOf (P.dw (0 - P.t0)) Na) (-P.s0))
  LF.smul (-1) ((Pb.add (Pa.smul (-1))).add ((Pd.add (Pc.smul (-1))).add (LF.const (-P.qc))))

end PairData

end CatalanCore.Uniform.Decay.PairEnergy
