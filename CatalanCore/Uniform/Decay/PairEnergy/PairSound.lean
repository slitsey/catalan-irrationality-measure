module

public import CatalanCore.Uniform.Decay.PairEnergy.PairLF

@[expose] public section

/-!
# Soundness of the pair linear form (lane D, package D6c)

`pairLF_val`: the value of `P.pairLF` is the pair energy.
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset Set intervalIntegral MeasureTheory

theorem poly_ptwise (f : ℕ → ℚ) (N : ℕ) (x : ℚ) (t : ℝ) :
    evalL (pshift (listOf f N) (-x)) t = ∑ l ∈ range N, ((f l : ℚ) : ℝ) * (t - (x : ℝ)) ^ l := by
  rw [evalL_pshift, evalL_listOf]
  simp only [sub_eq_add_neg]
  push_cast
  rfl

theorem evalL_centred (a : List ℚ) (x : ℚ) (s : ℝ) :
    evalL a s = ∑ k ∈ range (pshift a x).length, (((pshift a x).getD k 0 : ℚ) : ℝ) * (s - (x : ℝ)) ^ k := by
  rw [← evalL_eq_sum _ _ _ le_rfl, evalL_pshift]
  congr 1; ring

namespace PairData

theorem cw_cast (P : PairData) (e : ℚ) (l : ℕ) :
    ((P.cw e l : ℚ) : ℝ) = ((P.be.getD l 0 : ℚ) : ℝ) * ∑ k ∈ range P.al.length,
      ((P.al.getD k 0 : ℚ) : ℝ) * (e : ℝ) ^ (k + 1) / ((k : ℝ) + l + 2) := by
  unfold cw; rw [sumR_eq]; push_cast; rfl

theorem dw_cast (P : PairData) (e : ℚ) (k : ℕ) :
    ((P.dw e k : ℚ) : ℝ) = ((P.al.getD k 0 : ℚ) : ℝ) * ∑ l ∈ range P.be.length,
      ((P.be.getD l 0 : ℚ) : ℝ) * (e : ℝ) ^ (l + 1) / ((k : ℝ) + l + 2) := by
  unfold dw; rw [sumR_eq]; push_cast; rfl

theorem qc_cast (P : PairData) : ((P.qc : ℚ) : ℝ) = ∑ k ∈ range P.al.length, ∑ l ∈ range P.be.length,
    ((P.al.getD k 0 : ℚ) : ℝ) * ((P.be.getD l 0 : ℚ) : ℝ) / ((k : ℝ) + l + 2) *
      (((1 - (P.s0 : ℝ)) ^ (k + 1) - (0 - (P.s0 : ℝ)) ^ (k + 1)) *
        ((1 - (P.t0 : ℝ)) ^ (l + 1) - (0 - (P.t0 : ℝ)) ^ (l + 1)) / (((k : ℝ) + 1) * ((l : ℝ) + 1))) := by
  unfold qc; simp only [sumR_eq]; push_cast; rfl

theorem rel_complex (P : PairData) (h : P.rel = QC.zero) :
    P.A1.toC - P.A2.toC + (((P.s0 : ℚ) : ℝ) : ℂ) * (P.B1.toC - P.A1.toC)
      - (((P.t0 : ℚ) : ℝ) : ℂ) * (P.B2.toC - P.A2.toC) = 0 := by
  have := congrArg QC.toC h
  simpa [rel, QC.toC_sub, QC.toC_add, QC.toC_qmul] using this

end PairData

/-- **The pair linear form computes the pair energy.** -/
theorem pairLF_val (P : PairData) (hu : (QC.sub P.B1 P.A1).toC ≠ 0) (hv : (QC.sub P.B2 P.A2).toC ≠ 0)
    (hrel : P.rel = QC.zero) :
    P.pairLF.val = ∫ s in (0 : ℝ)..1, evalL P.a s * ∫ t in (0 : ℝ)..1, evalL P.b t *
      (-Real.log ‖(P.A1.toC + (s : ℂ) * (P.B1.toC - P.A1.toC)) -
        (P.A2.toC + (t : ℂ) * (P.B2.toC - P.A2.toC))‖) := by
  have hu' : P.B1.toC - P.A1.toC ≠ 0 := by simpa [QC.toC_sub] using hu
  have hv' : P.B2.toC - P.A2.toC ≠ 0 := by simpa [QC.toC_sub] using hv
  have hrelC := P.rel_complex hrel
  -- rewrite the densities in centred form
  have hl : ∀ s : ℝ, evalL P.a s = ∑ k ∈ range P.al.length,
      (((P.al.getD k 0 : ℚ) : ℝ)) * (s - (P.s0 : ℝ)) ^ k := fun s => evalL_centred P.a P.s0 s
  have hr : ∀ t : ℝ, evalL P.b t = ∑ l ∈ range P.be.length,
      (((P.be.getD l 0 : ℚ) : ℝ)) * (t - (P.t0 : ℝ)) ^ l := fun t => evalL_centred P.b P.t0 t
  simp only [hl, hr]
  rw [pair_formula_real P.A1.toC P.B1.toC P.A2.toC P.B2.toC hu' hv' (P.s0 : ℝ) (P.t0 : ℝ) hrelC
    (fun k => ((P.al.getD k 0 : ℚ) : ℝ)) (fun l => ((P.be.getD l 0 : ℚ) : ℝ)) P.al.length P.be.length]
  unfold PairData.pairLF
  simp only [LF.val_smul, LF.val_add, LF.val_const]
  rw [potLF_val _ _ _ _ hv, potLF_val _ _ _ _ hv, potLF_val _ _ _ _ hu, potLF_val _ _ _ _ hu]
  simp only [Rat.cast_neg, Rat.cast_one]
  rw [PairData.qc_cast]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero, add_sub_cancel]
  have e1 : ∀ (e : ℚ) (t : ℝ), evalL (pshift (listOf (P.cw e) P.be.length) (-P.t0)) t
      = ∑ l ∈ range P.be.length, (((P.be.getD l 0 : ℚ) : ℝ) * ∑ k ∈ range P.al.length,
        ((P.al.getD k 0 : ℚ) : ℝ) * (e : ℝ) ^ (k + 1) / ((k : ℝ) + l + 2)) * (t - (P.t0 : ℝ)) ^ l := by
    intro e t; rw [poly_ptwise]
    exact Finset.sum_congr rfl fun l _ => by rw [PairData.cw_cast]
  have e2 : ∀ (e : ℚ) (s : ℝ), evalL (pshift (listOf (P.dw e) P.al.length) (-P.s0)) s
      = ∑ k ∈ range P.al.length, (((P.al.getD k 0 : ℚ) : ℝ) * ∑ l ∈ range P.be.length,
        ((P.be.getD l 0 : ℚ) : ℝ) * (e : ℝ) ^ (l + 1) / ((k : ℝ) + l + 2)) * (s - (P.s0 : ℝ)) ^ k := by
    intro e s; rw [poly_ptwise]
    exact Finset.sum_congr rfl fun k _ => by rw [PairData.dw_cast]
  simp only [e1, e2]
  push_cast
  ring

end CatalanCore.Uniform.Decay.PairEnergy
