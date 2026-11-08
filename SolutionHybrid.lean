module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public import CatalanCore.Uniform.Bank.FourthsContent.Level3Bound
public import CatalanCore.Uniform.Bank.Chi3.KContent.Bound
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Bound
public import CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound
public import CatalanCore.Uniform.Bank.HalvesContent.Bound
public import CatalanCore.Uniform.Bank.Irrational
public import CatalanCore.Uniform.Bank.FourthsContent.Level3Data

public section

/-!
Proofs of the statements in `ChallengeHybrid.lean`, from the `Level3Bound` theorems of the trigamma-difference
banks (`CatalanCore.Uniform.Bank.*Content.Level3Bound`, `HalvesContent.Bound` and `Chi3.KContent.Bound`).
Each bank proves a measure at its exact exponent `c / (D - Λ)`, which is below the stated exponent `μ`.
Each constant is irrational (`CatalanCore.Uniform.Bank.Irrational`), so the bound for reduced fractions
extends to all fractions (`MeasureLBAt.all_of_irrational`), and the gap to `μ` removes the error term
(`Aux.eventually_of_exact`). For `G ± 5π²/48` the target is rewritten first.
-/

namespace TrigammaDifferences

namespace Aux

open CatalanCore

theorem X_nonneg {c D Λ : ℝ} (hc : 0 < c) (hΛ : Λ < D) : 0 ≤ (1 : ℝ) * c / (D - Λ) := by
  have : 0 < D - Λ := by linarith
  positivity

/-- A measure at the exact exponent `c / (D - Λ)`, with `c < B (D - Λ)`, gives the bound with exponent `B` and no
error term, for all fractions with large denominator. -/
theorem eventually_of_exact {x : ℝ} {c D Λ B : ℚ} (hc : 0 < c) (hΛ : Λ < D) (hB : c < B * (D - Λ))
    (hx : Irrational x) (h : Measure.MeasureLBAt x ((1 : ℝ) * (c : ℝ) / ((D : ℝ) - (Λ : ℝ)))) :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ, (b : ℝ) ^ (-((B : ℚ) : ℝ)) < |x - a / b| := by
  have hD : (0 : ℝ) < (D : ℝ) - (Λ : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 hΛ; linarith
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hX0 : (0 : ℝ) ≤ (1 : ℝ) * (c : ℝ) / ((D : ℝ) - (Λ : ℝ)) := by positivity
  have hlt : (1 : ℝ) * (c : ℝ) / ((D : ℝ) - (Λ : ℝ)) < (B : ℝ) := by
    rw [one_mul, div_lt_iff₀ hD]
    have h3 := (Rat.cast_lt (K := ℝ)).2 hB
    push_cast at h3
    linarith
  obtain ⟨q₀, hq⟩ := Measure.MeasureLBAt.all_of_irrational hX0 hx h _ (sub_pos.2 hlt)
  filter_upwards [Filter.eventually_ge_atTop q₀] with b hb a
  have h1 := hq a b hb
  have e : (1 : ℝ) * (c : ℝ) / ((D : ℝ) - (Λ : ℝ)) + ((B : ℝ) - (1 : ℝ) * (c : ℝ) / ((D : ℝ) - (Λ : ℝ))) =
      (B : ℝ) := by ring
  rw [e] at h1
  exact h1

open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Fourths
  CatalanCore.Uniform.Bank.FourthsContent.Level3Auto CatalanCore.Uniform.Bank.FourthsContent.Level3Measure in
theorem lambda_final (sgn : Bool) :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((78219 / 2500 : ℚ) : ℝ)) < |lambdaTarget sgn - a / b| := by
  have hD := CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.lambda_decay sgn
  have hmass : (FL.common.mass : ℝ) = 1 := by rw [FL_common_mass]; norm_num
  have hc : (0 : ℝ) < (cL : ℝ) := by unfold cL; norm_num
  have hd : 1 ≤ (lambdaFrame sgn).d := by rw [lambdaFrame_d]; norm_num
  have key := measure_of_family_nv0_even
    ((FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)).restrictAdm (fun i => i.1 % 2 = 0)) FL.scale
    (γ := 1) (K := FL.common.n) (content_auto sgn)
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) lam_lt_DL hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := FL.degree_bound (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := FL_nv0 (lambdaFrame sgn) hd (lambdaFrame_w_ne sgn) (FL.selectionDepth (lambdaFrame sgn) 2) le_rfl
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : FL.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  have h' : Measure.MeasureLBAt (lambdaFrame sgn).const
      ((1 : ℝ) * (cL : ℝ) / ((DL : ℝ) - ((bankData.Λ : ℚ) : ℝ))) :=
    (Measure.MeasureLB_iff _ _).1 key
  have hX : Measure.MeasureLBAt (lambdaTarget sgn)
      ((1 : ℝ) * (cL : ℝ) / ((DL : ℝ) - ((bankData.Λ : ℚ) : ℝ))) := by
    have he : lambdaTarget sgn = ((2 : ℚ) : ℝ) * (lambdaFrame sgn).const + ((0 : ℚ) : ℝ) := by
      rw [lambdaFrame_const sgn]; push_cast; ring
    rw [he]
    exact h'.affine (X_nonneg hc lam_lt_DL) 2 0 (by norm_num)
  exact eventually_of_exact (by unfold cL; norm_num) (by rw [bankData_Λ]; unfold DL; norm_num)
    (by rw [bankData_Λ]; unfold cL DL; norm_num)
    (CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.lambda_irrational sgn) hX

open CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanFrames.Thirds CatalanFrames.P6 CatalanCore.Uniform.Bank.ThirdsContent
  CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto CatalanCore.Uniform.Bank.ThirdsContent.Level3Measure in
theorem thirds_plus_final :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((47499 / 5000 : ℚ) : ℝ)) < |(chi3L2 + Real.pi ^ 2 / 9) - (a : ℝ) / b| := by
  have h0 := thirds_measureLB_lam thirdsAc (by show 1 ≤ 2; norm_num) thirds_w_ne bankData.Λ lam_lt_Dt
    (thirdsAc_content_autoUF _ (depth0_le rfl))
    CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirdsAc_decay
  have hc : (0 : ℝ) < (ctT : ℝ) := by unfold ctT; norm_num
  have h' : Measure.MeasureLBAt thirdsAc.const
      ((1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - ((bankData.Λ : ℚ) : ℝ))) :=
    (Measure.MeasureLB_iff _ _).mp h0
  have hX : Measure.MeasureLBAt (chi3L2 + Real.pi ^ 2 / 9)
      ((1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - ((bankData.Λ : ℚ) : ℝ))) := by
    have he : chi3L2 + Real.pi ^ 2 / 9 = ((-2 : ℚ) : ℝ) * thirdsAc.const + ((0 : ℚ) : ℝ) := by
      rw [thirdsAc_const]; push_cast; ring
    rw [he]
    exact h'.affine (X_nonneg hc lam_lt_Dt) (-2) 0 (by norm_num)
  exact eventually_of_exact (by unfold ctT; norm_num) (by rw [bankData_Λ]; unfold DtT; norm_num)
    (by rw [bankData_Λ]; unfold ctT DtT; norm_num)
    CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_plus_irrational hX

open CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanFrames.Thirds CatalanFrames.P6 CatalanCore.Uniform.Bank.ThirdsContent
  CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto CatalanCore.Uniform.Bank.ThirdsContent.Level3Measure in
theorem thirds_minus_final :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((47499 / 5000 : ℚ) : ℝ)) < |(chi3L2 - Real.pi ^ 2 / 9) - (a : ℝ) / b| := by
  have h0 := thirds_measureLB_lam thirdsBc (by show 1 ≤ 2; norm_num) thirds_w_ne' bankData.Λ lam_lt_Dt
    (thirdsBc_content_autoUF _ (depth0_le rfl))
    CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirdsBc_decay
  have hc : (0 : ℝ) < (ctT : ℝ) := by unfold ctT; norm_num
  have h' : Measure.MeasureLBAt thirdsBc.const
      ((1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - ((bankData.Λ : ℚ) : ℝ))) :=
    (Measure.MeasureLB_iff _ _).mp h0
  have hX : Measure.MeasureLBAt (chi3L2 - Real.pi ^ 2 / 9)
      ((1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - ((bankData.Λ : ℚ) : ℝ))) := by
    have he : chi3L2 - Real.pi ^ 2 / 9 = ((2 : ℚ) : ℝ) * thirdsBc.const + ((0 : ℚ) : ℝ) := by
      rw [thirdsBc_const]; push_cast; ring
    rw [he]
    exact h'.affine (X_nonneg hc lam_lt_Dt) 2 0 (by norm_num)
  exact eventually_of_exact (by unfold ctT; norm_num) (by rw [bankData_Λ]; unfold DtT; norm_num)
    (by rw [bankData_Λ]; unfold ctT DtT; norm_num)
    CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_minus_irrational hX

open CatalanCore.Uniform CatalanFrames.P6 CatalanCore.Uniform.Bank.Chi3New CatalanCore.Uniform.Bank.Chi3
  CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Bank.Chi3.KContent in
theorem chi3_final :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((137046 / 10000 : ℚ) : ℝ)) < |chi3L2 - a / b| := by
  have h' : Measure.MeasureLBAt p6Frame.const ((1 : ℝ) * ((37521870783566737 / 5000000000000000 : ℚ) : ℝ) /
      (((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) - ((kData.Λ : ℚ) : ℝ))) :=
    (Measure.MeasureLB_iff _ _).mp chi3_measureLB_k
  have hΛ : (kData.Λ : ℚ) < 4643511791526209475773 / 1000000000000000000000 := by
    rw [kData_Λ_eq]; norm_num
  have hX : Measure.MeasureLBAt chi3L2 ((1 : ℝ) * ((37521870783566737 / 5000000000000000 : ℚ) : ℝ) /
      (((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) - ((kData.Λ : ℚ) : ℝ))) := by
    have he : chi3L2 = ((4 : ℚ) : ℝ) * p6Frame.const + ((0 : ℚ) : ℝ) := by
      rw [p6Frame_const]; push_cast; ring
    rw [he]
    exact h'.affine (X_nonneg (by norm_num) (by exact_mod_cast hΛ)) 4 0 (by norm_num)
  exact eventually_of_exact (by norm_num) hΛ (by rw [kData_Λ_eq]; norm_num)
    CatalanCore.Uniform.Bank.Chi3.KContent.chi3_irrational hX

open CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.FifthsContent.Level3Auto CatalanCore.Uniform.Bank.FifthsContent.Level3Measure
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Fifths.Cover
  CatalanCore.Uniform.Bank.FifthsContent.Level3Bound in
theorem fifths_final (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) {target : ℝ}
    (hconst : Fr.const = ((-1 / 25 : ℚ) : ℝ) * target) (hirr : Irrational target)
    (hS : HasScaledContent ((F5.family Fr (F5.selectionDepth Fr 2)).restrictAdm (fun i => i.1 % 2 = 0))
      F5.scale ((bankData.Λ : ℚ) : ℝ))
    (hD : HasScaledDecay (F5.family Fr (F5.selectionDepth Fr 2)) F5.scale (Dchi.Dt : ℝ) (c5 : ℝ)) :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((14892 / 625 : ℚ) : ℝ)) < |target - a / b| := by
  have hlam : ((bankData.Λ : ℚ) : ℝ) < (Dchi.Dt : ℝ) := by exact_mod_cast lam_lt
  have hmass : (F5.common.mass : ℝ) = 1 := by rw [F5_common_mass]; norm_num
  have hc : (0 : ℝ) < (c5 : ℝ) := by unfold c5; norm_num
  have key := measure_of_family_nv0_even
    ((F5.family Fr (F5.selectionDepth Fr 2)).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
    (γ := 1) (K := F5.common.n) hS
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) hlam hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := F5.degree_bound Fr (F5.selectionDepth Fr 2) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := F5_nv0 Fr hd hw (F5.selectionDepth Fr 2) le_rfl
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : F5.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  have h' : Measure.MeasureLBAt Fr.const ((1 : ℝ) * (c5 : ℝ) / ((Dchi.Dt : ℝ) - ((bankData.Λ : ℚ) : ℝ))) :=
    (Measure.MeasureLB_iff _ _).1 key
  have hX : Measure.MeasureLBAt target ((1 : ℝ) * (c5 : ℝ) / ((Dchi.Dt : ℝ) - ((bankData.Λ : ℚ) : ℝ))) := by
    have he : target = ((-25 : ℚ) : ℝ) * Fr.const + ((0 : ℚ) : ℝ) := by
      rw [hconst]; push_cast; ring
    rw [he]
    exact h'.affine (X_nonneg hc hlam) (-25) 0 (by norm_num)
  exact eventually_of_exact (by unfold c5; norm_num) lam_lt (by rw [bankData_Λ]; decide +kernel) hirr hX

open CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.FifthsContent.Level3Auto CatalanCore.Uniform.Bank.FifthsContent.Level3Measure
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Fifths.Cover
  CatalanCore.Uniform.Bank.FifthsContent.Level3Bound in
theorem fifths1_final :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((14892 / 625 : ℚ) : ℝ)) < |fifthsTarget 1 - a / b| :=
  fifths_final fifths1 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths1_const fifths1_irrational
    (fifths1_content_auto _ (depth_le rfl))
    (decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      (m0_le _ _ _ _ _ _ (by norm_num)) _)

open CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.FifthsContent.Level3Auto CatalanCore.Uniform.Bank.FifthsContent.Level3Measure
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Fifths.Cover
  CatalanCore.Uniform.Bank.FifthsContent.Level3Bound in
theorem fifths2_final :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((14892 / 625 : ℚ) : ℝ)) < |fifthsTarget 2 - a / b| :=
  fifths_final fifths2 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths2_const fifths2_irrational
    (fifths2_content_auto _ (depth_le rfl))
    (decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      (m0_le _ _ _ _ _ _ (by norm_num)) _)

open CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.FifthsContent.Level3Auto CatalanCore.Uniform.Bank.FifthsContent.Level3Measure
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Fifths.Cover
  CatalanCore.Uniform.Bank.FifthsContent.Level3Bound in
theorem fifths3_final :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((14892 / 625 : ℚ) : ℝ)) < |fifthsTarget 3 - a / b| :=
  fifths_final fifths3 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths3_const fifths3_irrational
    (fifths3_content_auto _ (depth_le rfl))
    (decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      (m0_le _ _ _ _ _ _ (by norm_num)) _)

open CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.FifthsContent.Level3Auto CatalanCore.Uniform.Bank.FifthsContent.Level3Measure
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Fifths.Cover
  CatalanCore.Uniform.Bank.FifthsContent.Level3Bound in
theorem fifths4_final :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((14892 / 625 : ℚ) : ℝ)) < |fifthsTarget 4 - a / b| :=
  fifths_final fifths4 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths4_const fifths4_irrational
    (fifths4_content_auto _ (depth_le rfl))
    (decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      (m0_le _ _ _ _ _ _ (by norm_num)) _)

open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Sevenths
  CatalanCore.Uniform.Bank.SeventhsContent.Level3Auto CatalanCore.Uniform.Bank.SeventhsContent.Level3Measure in
theorem sevenths_final (a : Fin 6) :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a' : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) < |seventhsTarget (seventhNumerator a) - a' / b| := by
  have hD := CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_decay a
  have hmass : (F7.common.mass : ℝ) = 1 := by rw [F7_common_mass]; norm_num
  have hc : (0 : ℝ) < (c7 : ℝ) := by unfold c7; norm_num
  have hd2 : (seventhsFrameAt a).d = 2 := rfl
  have key := measure_of_family_nv0_even
    ((F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2)).restrictAdm (fun i => i.1 % 2 = 0)) F7.scale
    (γ := 1) (K := F7.common.n) (sevenths_content_auto a _ (depth_le hd2))
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) lam_lt_D7 hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := F7.degree_bound (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := F7_nv0 (seventhsFrameAt a) (by rw [hd2]; norm_num) (seventhsFrameAt_w_ne a) (F7.selectionDepth (seventhsFrameAt a) 2) le_rfl
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : F7.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  have h' : Measure.MeasureLBAt (seventhsFrameAt a).const
      ((1 : ℝ) * (c7 : ℝ) / ((D7 : ℝ) - ((bankData.Λ : ℚ) : ℝ))) :=
    (Measure.MeasureLB_iff _ _).1 key
  have hX : Measure.MeasureLBAt (seventhsTarget (seventhNumerator a))
      ((1 : ℝ) * (c7 : ℝ) / ((D7 : ℝ) - ((bankData.Λ : ℚ) : ℝ))) := by
    have he : seventhsTarget (seventhNumerator a) =
        ((-49 : ℚ) : ℝ) * (seventhsFrameAt a).const + ((0 : ℚ) : ℝ) := by
      rw [seventhsFrameAt_const a]; push_cast; ring
    rw [he]
    exact h'.affine (X_nonneg hc lam_lt_D7) (-49) 0 (by norm_num)
  exact eventually_of_exact (by unfold c7; norm_num) (by rw [bankData_Λ]; unfold D7; norm_num)
    (by rw [bankData_Λ]; unfold c7 D7; norm_num)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_irrational a) hX

open CatalanCore.Uniform CatalanCore.Uniform.Bank.Halves CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.HalvesContent.Auto CatalanCore.Uniform.Bank.HalvesContent.AutoMeasure
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Halves.Cover in
theorem pi2_final :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((65253 / 10000 : ℚ) : ℝ)) < |Real.pi ^ 2 - a / b| := by
  have hD := CatalanCore.Uniform.Bank.HalvesContent.Bound.decay (FH.selectionDepth halves 2)
  have hl := CatalanCore.Uniform.Bank.HalvesContent.Bound.lam_lt
  have hlam : ((bankData.Λ : ℚ) : ℝ) < (Dchi.Dt : ℝ) := by exact_mod_cast hl
  have hmass : (FH.common.mass : ℝ) = 1 := by rw [FH_common_mass]; norm_num
  have hc : (0 : ℝ) < (cH : ℝ) := by unfold cH; norm_num
  have hd : 1 ≤ halves.d := by show 1 ≤ 2; norm_num
  have key := measure_of_family_nv0_even
    ((FH.family halves (FH.selectionDepth halves 2)).restrictAdm (fun i => i.1 % 2 = 0)) FH.scale
    (γ := 1) (K := FH.common.n) (halves_content_auto _ (depth_le rfl))
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) hlam hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := FH.degree_bound halves (FH.selectionDepth halves 2) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := FH_nv0 halves hd halves_w_ne (FH.selectionDepth halves 2) le_rfl
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : FH.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  have h' : Measure.MeasureLBAt halves.const ((1 : ℝ) * (cH : ℝ) / ((Dchi.Dt : ℝ) - ((bankData.Λ : ℚ) : ℝ))) :=
    (Measure.MeasureLB_iff _ _).1 key
  have hX : Measure.MeasureLBAt (Real.pi ^ 2)
      ((1 : ℝ) * (cH : ℝ) / ((Dchi.Dt : ℝ) - ((bankData.Λ : ℚ) : ℝ))) := by
    have he : Real.pi ^ 2 = ((-12 : ℚ) : ℝ) * halves.const + ((0 : ℚ) : ℝ) := by
      rw [halves_const]; push_cast; ring
    rw [he]
    exact h'.affine (X_nonneg hc hlam) (-12) 0 (by norm_num)
  exact eventually_of_exact (by unfold cH; norm_num) hl (by rw [bankData_Λ]; decide +kernel)
    CatalanCore.Uniform.Bank.HalvesContent.Bound.pi2_irrational hX

end Aux


open CatalanCore

theorem lambda_minus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((78219 / 2500 : ℚ) : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48) - (a : ℝ) / b| := by
    have h := Aux.lambda_final false
    have e : CatalanCore.Uniform.Bank.Fourths.lambdaTarget false = (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48 := by
      simp [CatalanCore.Uniform.Bank.Fourths.lambdaTarget, sub_eq_add_neg]
    rw [e] at h
    exact h

theorem lambda_plus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((78219 / 2500 : ℚ) : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48) - (a : ℝ) / b| := by
    have h := Aux.lambda_final true
    have e : CatalanCore.Uniform.Bank.Fourths.lambdaTarget true = (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48 := by
      simp [CatalanCore.Uniform.Bank.Fourths.lambdaTarget]
    rw [e] at h
    exact h

theorem chi3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((137046 / 10000 : ℚ) : ℝ)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - (a : ℝ) / b| := by
  exact Aux.chi3_final

theorem chi3_plus_pi2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((47499 / 5000 : ℚ) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 9) - (a : ℝ) / b| := by
  exact Aux.thirds_plus_final

theorem chi3_minus_pi2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((47499 / 5000 : ℚ) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 9) - (a : ℝ) / b| := by
  exact Aux.thirds_minus_final

theorem fifths1_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((14892 / 625 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.fifths1_final

theorem fifths2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((14892 / 625 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.fifths2_final

theorem fifths3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((14892 / 625 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.fifths3_final

theorem fifths4_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((14892 / 625 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.fifths4_final

theorem sevenths1_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨0, by decide⟩

theorem sevenths2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨1, by decide⟩

theorem sevenths3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨2, by decide⟩

theorem sevenths4_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨3, by decide⟩

theorem sevenths5_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((5 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨4, by decide⟩

theorem sevenths6_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((6 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  exact Aux.sevenths_final ⟨5, by decide⟩

theorem pi2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((65253 / 10000 : ℚ) : ℝ)) <
        |Real.pi ^ 2 - (a : ℝ) / b| := by
  exact Aux.pi2_final

#print axioms lambda_minus_measure
#print axioms lambda_plus_measure
#print axioms chi3_measure
#print axioms chi3_plus_pi2_measure
#print axioms chi3_minus_pi2_measure
#print axioms fifths1_measure
#print axioms fifths2_measure
#print axioms fifths3_measure
#print axioms fifths4_measure
#print axioms sevenths1_measure
#print axioms sevenths2_measure
#print axioms sevenths3_measure
#print axioms sevenths4_measure
#print axioms sevenths5_measure
#print axioms sevenths6_measure
#print axioms pi2_measure

end TrigammaDifferences
