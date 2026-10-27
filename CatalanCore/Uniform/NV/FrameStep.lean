module
public import CatalanCore.Uniform.NV.FramePoles
public import CatalanCore.Uniform.NV.Corank
public import Mathlib.Algebra.BigOperators.Intervals
@[expose] public section
open Polynomial Finset
namespace CatalanCore.Uniform.NV

/-- Scalar rational prefixes on the original natural nodes. -/
def framePrefix (Fr : Frame) (a : ℕ) : ℚ := (∑ k ∈ Icc 1 a,Fr.Delta k)/Fr.norm
def frameJet (Fr : Frame) (U : ℚ) (a : ℕ) : ℚ := U-(∑ k ∈ Icc 1 a,Fr.Dsq k)/Fr.norm
noncomputable def onNaturals (g : ℕ → ℚ) : ℚ → ℚ :=
  Function.extend (Nat.cast : ℕ → ℚ) g (fun _ => 0)
@[simp] theorem onNaturals_nat (g : ℕ → ℚ) (a : ℕ) : onNaturals g (a:ℚ) = g a :=
  Nat.cast_injective.extend_apply g _ a

theorem prefix_add_sum (g : ℕ → ℚ) (a L : ℕ) :
    (∑ k ∈ Icc 1 (a+L),g k)-(∑ k ∈ Icc 1 a,g k) = ∑ j ∈ range L,g (a+j+1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.add_succ,Finset.sum_Icc_succ_top (by omega : 1 ≤ a+L+1),Finset.sum_range_succ]
    linear_combination ih

/-- The actual frame's length-L reciprocal sums, for either value or jet power. -/
theorem frame_pole_increment (Fr : Frame) (a L e : ℕ) :
    (∑ j ∈ range L,∑ i : Fin Fr.d,(Fr.w i:ℚ)/(((a+j+1:ℕ):ℚ)-1+Fr.μ i)^e)/Fr.norm =
      ∑ b ∈ framePoleSet Fr L,frameResidue Fr L b/((a:ℚ)-b)^e := by
  rw [sum_framePoleSet Fr L (fun b c => c/((a:ℚ)-b)^e)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_div]
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [framePole,framePoleWeight]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (Fr.w i:ℚ)/Fr.norm/((a:ℚ)-(-Fr.μ i-(j:ℚ)))^e) L]
  apply Finset.sum_congr rfl
  intro j _

  have he : (((a+j+1:ℕ):ℚ)-1+Fr.μ i) = (a:ℚ)-(-Fr.μ i-(j:ℚ)) := by push_cast;ring
  rw [he]
  ring

theorem framePrefix_step (Fr : Frame) (a L : ℕ) :
    framePrefix Fr (a+L)-framePrefix Fr a =
      ∑ b ∈ framePoleSet Fr L,frameResidue Fr L b/((a:ℚ)-b) := by
  unfold framePrefix
  rw [← sub_div,prefix_add_sum]
  simpa only [Frame.Delta,pow_one] using frame_pole_increment Fr a L 1

theorem frameJet_step (Fr : Frame) (U : ℚ) (a L : ℕ) :
    frameJet Fr U (a+L)-frameJet Fr U a =
      -(∑ b ∈ framePoleSet Fr L,frameResidue Fr L b/((a:ℚ)-b)^2) := by
  have he := frame_pole_increment Fr a L 2
  have hp := prefix_add_sum Fr.Dsq a L
  unfold frameJet
  rw [show U-(∑ k ∈ Icc 1 (a+L),Fr.Dsq k)/Fr.norm-
      (U-(∑ k ∈ Icc 1 a,Fr.Dsq k)/Fr.norm) =
        -(((∑ k ∈ Icc 1 (a+L),Fr.Dsq k)-(∑ k ∈ Icc 1 a,Fr.Dsq k))/Fr.norm) by ring]
  rw [hp]
  simpa only [Frame.Dsq] using congrArg Neg.neg he

/-- Every actual rational frame supplies the cleared step equations.
Pole/source certificates are explicit finite products, not nonvanishing premises. -/
noncomputable def frameStepData (Fr : Frame) (U : ℚ) (L : ℕ) :
    StepData L (poleDenominator (framePoleSet Fr L))
      (poleNumerator (framePoleSet Fr L) (frameResidue Fr L))
      (onNaturals (framePrefix Fr)) (onNaturals (frameJet Fr U)) where
  value a := by
    have hx : (a:ℚ) ∉ framePoleSet Fr L := by
      intro h
      have := (framePole_strip Fr L _ h).2
      have : 0 ≤ (a:ℚ) := Nat.cast_nonneg a
      linarith
    have hv := framePrefix_step Fr a L
    rw [← Nat.cast_add,onNaturals_nat,onNaturals_nat,hv]
    exact pole_value_cleared _ _ _ hx
  jet a := by
    have hx : (a:ℚ) ∉ framePoleSet Fr L := by
      intro h
      have := (framePole_strip Fr L _ h).2
      have : 0 ≤ (a:ℚ) := Nat.cast_nonneg a
      linarith
    have hv := framePrefix_step Fr a L
    have ht := frameJet_step Fr U a L
    rw [← Nat.cast_add,onNaturals_nat,onNaturals_nat,onNaturals_nat,onNaturals_nat,hv,ht]
    simpa only [mul_neg,sub_eq_add_neg] using pole_jet_cleared _ _ _ hx
end CatalanCore.Uniform.NV




