import CatalanCore.Uniform.Bank.Thirds.Geom
import CatalanCore.Uniform.Bank.Thirds.Numerics
import CatalanCore.Uniform.Content.Shape.Reindex
import CatalanCore.Uniform.Content.Bridge.Hybrid
import CatalanCore.Measure.Scaling
import CatalanFrames.Thirds.TargetConstants
import CatalanFrames.Thirds.Assembly
set_option Elab.async false

/-! The irrationality measure of `L(2,χ₋₃) ± π²/9` from the thirds block family `G310.family Fr depth`
(lane B, B4).  CONDITIONAL assembly: the two analytic inputs are explicit hypotheses
(`ThirdsContent`, `ThirdsDecay`), everything else (selection `HasNV0`, even reindexing, numerical
contract, affine target transport for both signs) is proved. -/

namespace CatalanCore.Uniform.Bank.Thirds
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanFrames.Thirds
  CatalanFrames.P6

/-- Coefficient content of the thirds family at even scales: price `LamT`. -/
def ThirdsContent (Fr : Frame) (depth : ℕ) : Prop :=
  HasScaledContent ((G310.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) G310.scale LamT

/-- Window decay of the thirds family (all members): `D = DtT`, `c = ctT`. -/
def ThirdsDecay (Fr : Frame) (depth : ℕ) : Prop :=
  HasScaledDecay (G310.family Fr depth) G310.scale (DtT : ℝ) (ctT : ℝ)

/-- A selection depth that works for the thirds geometry (period `L = 2`). -/
noncomputable def depth0 (Fr : Frame) : ℕ := G310.selectionDepth Fr 2

theorem thirds_nv0 (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) :
    HasNV0 (G310.family Fr (depth0 Fr)) G310.scale :=
  G310.hasNV0 Fr 2 (depth0 Fr) (by norm_num) hd hw
    (fun i => by simp [G310, altGeom, single, commonB])
    (fun i => by simp [G310, altGeom, single, rowB])
    (fun i => by simp [G310, altGeom, single, colB]) le_rfl

/-- **Measure of the thirds family** (conditional on content and decay). -/
theorem thirds_measureLB (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hS : ThirdsContent Fr (depth0 Fr)) (hD : ThirdsDecay Fr (depth0 Fr)) :
    (G310.family Fr (depth0 Fr)).MeasureLB
      ((1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - LamT)) := by
  have hmass : (G310.common.mass : ℝ) = 1 := by rw [G310_common_mass]; norm_num
  have hD' : HasScaledDecay ((G310.family Fr (depth0 Fr)).restrictAdm (fun i => i.1 % 2 = 0))
      G310.scale (DtT : ℝ) (ctT : ℝ) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD ε hε
    exact ⟨R0, fun n hn => h n hn.1⟩
  have hc : (0 : ℝ) < (ctT : ℝ) := by unfold ctT; norm_num
  have key := measure_of_family_nv0_even
    ((G310.family Fr (depth0 Fr)).restrictAdm (fun i => i.1 % 2 = 0)) G310.scale
    (γ := 1) (K := G310.common.n) hS hD' LamT_lt_Dt hc one_pos (Nat.cast_nonneg _)
    (fun n hn => by
      have := G310.degree_bound Fr (depth0 Fr) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := thirds_nv0 Fr hd hw
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by have : G310.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  exact key

theorem thirds_X_le : (1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - LamT) ≤ ((952671 / 100000 : ℚ) : ℝ) := by
  rw [one_mul]; exact ratio_le

theorem thirds_w_ne : ∀ i, thirdsAc.w i ≠ 0 := by
  intro i; fin_cases i <;> simp [thirdsAc, thirdsFrame]

theorem thirds_w_ne' : ∀ i, thirdsBc.w i ≠ 0 := by
  intro i; fin_cases i <;> simp [thirdsBc, thirdsFrame]

/-- **`μ(L(2,χ₋₃) + π²/9) ≤ 9.52671`** (thirds+, a = 1), conditional on content and decay. -/
theorem thirds_measure_plus_of
    (hS : ThirdsContent thirdsAc (depth0 thirdsAc)) (hD : ThirdsDecay thirdsAc (depth0 thirdsAc)) :
    Measure.MeasureLBAt (chi3L2 + Real.pi ^ 2 / 9) ((952671 / 100000 : ℚ) : ℝ) := by
  have h0 := thirds_measureLB thirdsAc (by show 1 ≤ 2; norm_num) thirds_w_ne hS hD
  have h1 := (Measure.MeasureLB_iff _ _).mp h0
  have h' : Measure.MeasureLBAt thirdsAc.const ((952671 / 100000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono thirds_X_le h1
  exact measureLBAt_of_const (Fam := G310.family thirdsAc (depth0 thirdsAc)) (a := -1 / 2)
    (by norm_num) (by norm_num) thirdsAc_const ((Measure.MeasureLB_iff _ _).mpr h')

/-- **`μ(L(2,χ₋₃) − π²/9) ≤ 9.52671`** (thirds−, a = 2), conditional on content and decay. -/
theorem thirds_measure_minus_of
    (hS : ThirdsContent thirdsBc (depth0 thirdsBc)) (hD : ThirdsDecay thirdsBc (depth0 thirdsBc)) :
    Measure.MeasureLBAt (chi3L2 - Real.pi ^ 2 / 9) ((952671 / 100000 : ℚ) : ℝ) := by
  have h0 := thirds_measureLB thirdsBc (by show 1 ≤ 2; norm_num) thirds_w_ne' hS hD
  have h1 := (Measure.MeasureLB_iff _ _).mp h0
  have h' : Measure.MeasureLBAt thirdsBc.const ((952671 / 100000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono thirds_X_le h1
  exact measureLBAt_of_const (Fam := G310.family thirdsBc (depth0 thirdsBc)) (a := 1 / 2)
    (by norm_num) (by norm_num) thirdsBc_const ((Measure.MeasureLB_iff _ _).mpr h')

end CatalanCore.Uniform.Bank.Thirds
