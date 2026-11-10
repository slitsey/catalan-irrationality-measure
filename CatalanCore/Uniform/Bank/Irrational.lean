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
public import CatalanCore.Uniform.Bank.Plane1.Measure
public import CatalanCore.Uniform.Bank.Plane2.Measure
public import CatalanCore.Uniform.Bank.Plane2.Zeta3
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Bank227P
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Bank227M
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Bank127P
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Bank127M
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Bank118P
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Bank118M

public import CatalanCore.Uniform.Bank.Plane3.Measure
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.FourthsContent.Level3Bound
theorem lambda_irrational (sgn : Bool) := (lambda_point_exact sgn).2
end CatalanCore.Uniform.Bank.FourthsContent.Level3Bound
namespace CatalanCore.Uniform.Bank.Chi3.KContent
theorem chi3_irrational := (chi3_point_exact).2
end CatalanCore.Uniform.Bank.Chi3.KContent
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound
theorem thirds_plus_irrational := (thirds_plus_point_exact).2
theorem thirds_minus_irrational := (thirds_minus_point_exact).2
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Bound
theorem fifths1_irrational := (fifths1_point_exact).2
theorem fifths2_irrational := (fifths2_point_exact).2
theorem fifths3_irrational := (fifths3_point_exact).2
theorem fifths4_irrational := (fifths4_point_exact).2
end CatalanCore.Uniform.Bank.FifthsContent.Level3Bound
namespace CatalanCore.Uniform.Bank.HalvesContent.Bound
theorem pi2_irrational := (pi2_point_exact).2
end CatalanCore.Uniform.Bank.HalvesContent.Bound
namespace CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Sevenths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.SeventhsContent.Level3Auto CatalanCore.Uniform.Bank.SeventhsContent.Level3Measure

/-- `ψ′((a + 1)/7) − π²/6` is irrational for each of the six members. -/
theorem sevenths_irrational (a : Fin 6) : Irrational (seventhsTarget (seventhNumerator a)) := by
  have hmass : (F7.common.mass : ℝ) = 1 := by rw [F7_common_mass]; norm_num
  have hc : (0 : ℝ) < (c7 : ℝ) := by unfold c7; norm_num
  have hd2 : (seventhsFrameAt a).d = 2 := rfl
  have key := irrational_of_family_nv0_even
    ((F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2)).restrictAdm (fun i => i.1 % 2 = 0)) F7.scale
    (γ := 1) (K := F7.common.n) (sevenths_content_auto a _ (depth_le hd2))
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := sevenths_decay a ε hε
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
  exact Measure.irrational_of_eq_mul (by norm_num) key (seventhsFrameAt_const a)

end CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound


namespace TrigammaDifferences.Aux
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


theorem eventually_of_point {x E M : ℝ} (hE : 0≤E) (hM : E<M)
    (h : Measure.MeasureLBAt x E ∧ Irrational x) :
    ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,(q:ℝ)^(-M)<|x-(p:ℝ)/q| := by
  obtain ⟨q0,hq⟩ := Measure.MeasureLBAt.all_of_irrational hE h.2 h.1 (M-E) (sub_pos.mpr hM)
  filter_upwards [Filter.eventually_ge_atTop q0] with q hqq p
  simpa only [show E+(M-E)=M by ring] using hq p q hqq

open CatalanCore.Uniform.Bank.FourthsContent.Level3Bound in
theorem lambda_final (sgn : Bool) : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((311973/10000:ℚ):ℝ))<|(CatalanCore.Uniform.Bank.Fourths.lambdaTarget sgn)-(p:ℝ)/q| := by
  have h := lambda_point_exact sgn
  have hη := (Rat.cast_lt (K:=ℝ)).2 eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 cc_pos
  apply eventually_of_point ?_ (by exact_mod_cast mu_strict) h
  positivity

open CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound in
theorem thirds_plus_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((94913/10000:ℚ):ℝ))<|(CatalanFrames.P6.chi3L2+Real.pi^2/9)-(p:ℝ)/q| := by
  have h := thirds_plus_point_exact
  have hη := (Rat.cast_lt (K:=ℝ)).2 eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 cc_pos
  apply eventually_of_point ?_ (by exact_mod_cast mu_strict) h
  positivity

open CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound in
theorem thirds_minus_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((94913/10000:ℚ):ℝ))<|(CatalanFrames.P6.chi3L2-Real.pi^2/9)-(p:ℝ)/q| := by
  have h := thirds_minus_point_exact
  have hη := (Rat.cast_lt (K:=ℝ)).2 eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 cc_pos
  apply eventually_of_point ?_ (by exact_mod_cast mu_strict) h
  positivity

open CatalanCore.Uniform.Bank.Chi3.KContent in
theorem chi3_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((136839/10000:ℚ):ℝ))<|CatalanFrames.P6.chi3L2-(p:ℝ)/q| := by
  have h := chi3_point_exact
  have hη := (Rat.cast_lt (K:=ℝ)).2 chi3_eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 chi3_cc
  apply eventually_of_point ?_ (by exact_mod_cast chi3_ratio) h
  positivity

open CatalanCore.Uniform.Bank.FifthsContent.Level3Bound in
theorem fifths1_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((59439/2500:ℚ):ℝ))<|(CatalanCore.Uniform.Bank.Fifths.fifthsTarget 1)-(p:ℝ)/q| := by
  have h := fifths1_point_exact
  have hη := (Rat.cast_lt (K:=ℝ)).2 eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 cc_pos
  apply eventually_of_point ?_ (by exact_mod_cast mu_strict) h
  positivity

open CatalanCore.Uniform.Bank.FifthsContent.Level3Bound in
theorem fifths2_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((59439/2500:ℚ):ℝ))<|(CatalanCore.Uniform.Bank.Fifths.fifthsTarget 2)-(p:ℝ)/q| := by
  have h := fifths2_point_exact
  have hη := (Rat.cast_lt (K:=ℝ)).2 eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 cc_pos
  apply eventually_of_point ?_ (by exact_mod_cast mu_strict) h
  positivity

open CatalanCore.Uniform.Bank.FifthsContent.Level3Bound in
theorem fifths3_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((59439/2500:ℚ):ℝ))<|(CatalanCore.Uniform.Bank.Fifths.fifthsTarget 3)-(p:ℝ)/q| := by
  have h := fifths3_point_exact
  have hη := (Rat.cast_lt (K:=ℝ)).2 eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 cc_pos
  apply eventually_of_point ?_ (by exact_mod_cast mu_strict) h
  positivity

open CatalanCore.Uniform.Bank.FifthsContent.Level3Bound in
theorem fifths4_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((59439/2500:ℚ):ℝ))<|(CatalanCore.Uniform.Bank.Fifths.fifthsTarget 4)-(p:ℝ)/q| := by
  have h := fifths4_point_exact
  have hη := (Rat.cast_lt (K:=ℝ)).2 eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 cc_pos
  apply eventually_of_point ?_ (by exact_mod_cast mu_strict) h
  positivity

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

open CatalanCore.Uniform.Bank.HalvesContent.Bound
  CatalanCore.Uniform.Bank.HalvesContent.Auto CatalanCore.Uniform.Bank.Halves.Cover in
theorem pi2_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((32607/5000:ℚ):ℝ))<|Real.pi^2-(p:ℝ)/q| := by
  have hη := (Rat.cast_lt (K:=ℝ)).2 lam_lt
  have hc := (Rat.cast_lt (K:=ℝ)).2 cc_pos
  apply eventually_of_point ?_ ?_ pi2_point_exact
  · positivity
  · have h : Dchi.ccert/(Dchi.Dt-bankData.Λ)<(32607/5000:ℚ) := by
      rw [bankData_Λ];decide +kernel
    exact_mod_cast h

/-- A measure at the exact rational exponent `c / (D - Λ)`, with `c < B (D - Λ)`, gives the bound with exponent `B`. -/
theorem eventually_of_q {x : ℝ} {c D Λ B : ℚ} (hc : 0 < c) (hΛ : Λ < D) (hB : c < B * (D - Λ))
    (hx : Irrational x) (h : Measure.MeasureLBAt x (((c / (D - Λ) : ℚ)) : ℝ)) :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ, (b : ℝ) ^ (-((B : ℚ) : ℝ)) < |x - a / b| := by
  refine eventually_of_exact hc hΛ hB hx ?_
  have e : (((c / (D - Λ) : ℚ)) : ℝ) = (1 : ℝ) * (c : ℝ) / ((D : ℝ) - (Λ : ℝ)) := by push_cast; ring
  rw [← e]; exact h

open CatalanCore.Uniform CatalanCore.Measure CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Plane1
  CatalanCore.Uniform.Bank.Plane1.Data in
theorem plane1_final (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-((206622 / 10000 : ℚ) : ℝ)) <
      |((a : ℝ) * CatalanFrames.P6.chi3L2 + (b : ℝ) * Real.pi ^ 2) - p / q| := by
  obtain ⟨h1, h2⟩ := plane_point_ab a b hab planeContent_data planeDecay_cover plane1_eta plane1_cc
  refine eventually_of_exact plane1_cc plane1_eta (by decide +kernel) h2 ?_
  rw [one_mul]; exact h1

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.Plane2 in
theorem plane2_final (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-((33520 / 100 : ℚ) : ℝ)) <
      |((a : ℝ) * (riemannZeta 3).re + (b : ℝ) * Real.pi ^ 2) - p / q| := by
  obtain ⟨h1, h2⟩ := plane2_point_ab_of_content plane2Lam_le_max
    (B := Cover.Dchi.ccert / (Cover.Dchi.Dt - plane2Lam)) le_rfl plane2Content_inst plane2ContentZeta_inst
    (hasScaledContent_mono PiContent.plane2ContentPi (by exact_mod_cast piLam_le_plane2Lam)) a b hab
  exact eventually_of_q p2_cc (lt_of_le_of_lt plane2Lam_le_max p2_eta) (by unfold plane2Lam; decide +kernel) h2 h1

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Bank.Halves CatalanCore.Uniform.Bank.Halves.Cover
  CatalanCore.Uniform.Bank.Plane2 in
theorem zeta3_final :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ, (b : ℝ) ^ (-((60382 / 10000 : ℚ) : ℝ)) < |(riemannZeta 3).re - a / b| := by
  obtain ⟨hl, -⟩ := zeta3_numeric
  have hne : Dchi.Dt - zLam ≠ 0 := sub_ne_zero.2 (ne_of_gt hl)
  have h := zeta3_measure_le (B := Dchi.ccert / (Dchi.Dt - zLam)) (div_mul_cancel₀ _ hne).ge
  have hx : Irrational (riemannZeta 3).re := by
    simpa using (CatalanCore.Uniform.Bank.Plane2.plane2_measure 1 0 (Or.inl one_ne_zero)).2
  exact eventually_of_q CatalanCore.Uniform.Bank.HalvesContent.Bound.cc_pos hl (by unfold zLam; decide +kernel) hx h

open CatalanCore.Uniform.Bank.Plane1 CatalanCore.Uniform.Bank.Plane1.Dips
  CatalanCore.Uniform.Bank.Plane1.Data CatalanCore.Uniform.Bank.Plane1.Dips.Data.F227 in
theorem dip_2_27_plus_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((14:ℚ):ℝ))<|(CatalanFrames.P6.chi3L2+((2/27:ℚ):ℝ)*Real.pi^2)-(p:ℝ)/q| := by
  have h := dip_point planeC planeC_pos planeDepth Support.plus 2 (-1) (-1)
    (by norm_num) (by norm_num) bankP (CatalanCore.Uniform.Content.BankShared.SmallBudget.add (CatalanCore.Uniform.Content.SmallPrimes.SmallBudget.sqrtLog 5 10) CatalanCore.Uniform.Content.BankShared.SmallBudget.unit) 0 bankP_ok
    (planeDecay_cover Support.plus 2 (-1) (-1) (by norm_num))
    (by exact_mod_cast bankP_eta) (by exact_mod_cast plane1_cc)
    (plane_nv0_even Support.plus 2 (-1) (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) planeDepth le_rfl)
  have ht : planeT Support.plus 2 (-1)=(2/27:ℚ) := by simp only [planeT,Support.sgn];norm_num
  rw [ht] at h
  have hη := (Rat.cast_lt (K:=ℝ)).2 bankP_eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 plane1_cc
  apply eventually_of_point ?_ ?_ h
  · positivity
  · have hn : Dp1.ccert/(Dp1.Dt-bankP.Λ)<(14:ℚ) := by decide +kernel
    exact_mod_cast hn

open CatalanCore.Uniform.Bank.Plane1 CatalanCore.Uniform.Bank.Plane1.Dips
  CatalanCore.Uniform.Bank.Plane1.Data CatalanCore.Uniform.Bank.Plane1.Dips.Data.F227 in
theorem dip_2_27_minus_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((14:ℚ):ℝ))<|(CatalanFrames.P6.chi3L2+((-2/27:ℚ):ℝ)*Real.pi^2)-(p:ℝ)/q| := by
  have h := dip_point planeC planeC_pos planeDepth Support.minus 2 (-1) (-1)
    (by norm_num) (by norm_num) bankM (CatalanCore.Uniform.Content.BankShared.SmallBudget.add (CatalanCore.Uniform.Content.SmallPrimes.SmallBudget.sqrtLog 5 10) CatalanCore.Uniform.Content.BankShared.SmallBudget.unit) 0 bankM_ok
    (planeDecay_cover Support.minus 2 (-1) (-1) (by norm_num))
    (by exact_mod_cast bankM_eta) (by exact_mod_cast plane1_cc)
    (plane_nv0_even Support.minus 2 (-1) (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) planeDepth le_rfl)
  have ht : planeT Support.minus 2 (-1)=(-2/27:ℚ) := by simp only [planeT,Support.sgn];norm_num
  rw [ht] at h
  have hη := (Rat.cast_lt (K:=ℝ)).2 bankM_eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 plane1_cc
  apply eventually_of_point ?_ ?_ h
  · positivity
  · have hn : Dp1.ccert/(Dp1.Dt-bankM.Λ)<(14:ℚ) := by decide +kernel
    exact_mod_cast hn

open CatalanCore.Uniform.Bank.Plane1 CatalanCore.Uniform.Bank.Plane1.Dips
  CatalanCore.Uniform.Bank.Plane1.Data CatalanCore.Uniform.Bank.Plane1.Dips.Data.F127 in
theorem dip_1_27_plus_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((15359/1000:ℚ):ℝ))<|(CatalanFrames.P6.chi3L2+((1/27:ℚ):ℝ)*Real.pi^2)-(p:ℝ)/q| := by
  have h := dip_point planeC planeC_pos planeDepth Support.minus 1 (-2) (1)
    (by norm_num) (by norm_num) bankM (CatalanCore.Uniform.Content.BankShared.SmallBudget.add (CatalanCore.Uniform.Content.SmallPrimes.SmallBudget.sqrtLog 5 10) CatalanCore.Uniform.Content.BankShared.SmallBudget.unit) 0 bankM_ok
    (planeDecay_cover Support.minus 1 (-2) (1) (by norm_num))
    (by exact_mod_cast bankM_eta) (by exact_mod_cast plane1_cc)
    (plane_nv0_even Support.minus 1 (-2) (1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) planeDepth le_rfl)
  have ht : planeT Support.minus 1 (-2)=(1/27:ℚ) := by simp only [planeT,Support.sgn];norm_num
  rw [ht] at h
  have hη := (Rat.cast_lt (K:=ℝ)).2 bankM_eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 plane1_cc
  apply eventually_of_point ?_ ?_ h
  · positivity
  · have hn : Dp1.ccert/(Dp1.Dt-bankM.Λ)<(15359/1000:ℚ) := by decide +kernel
    exact_mod_cast hn

open CatalanCore.Uniform.Bank.Plane1 CatalanCore.Uniform.Bank.Plane1.Dips
  CatalanCore.Uniform.Bank.Plane1.Data CatalanCore.Uniform.Bank.Plane1.Dips.Data.F127 in
theorem dip_1_27_minus_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((15359/1000:ℚ):ℝ))<|(CatalanFrames.P6.chi3L2+((-1/27:ℚ):ℝ)*Real.pi^2)-(p:ℝ)/q| := by
  have h := dip_point planeC planeC_pos planeDepth Support.plus 1 (-2) (1)
    (by norm_num) (by norm_num) bankP (CatalanCore.Uniform.Content.BankShared.SmallBudget.add (CatalanCore.Uniform.Content.SmallPrimes.SmallBudget.sqrtLog 5 10) CatalanCore.Uniform.Content.BankShared.SmallBudget.unit) 0 bankP_ok
    (planeDecay_cover Support.plus 1 (-2) (1) (by norm_num))
    (by exact_mod_cast bankP_eta) (by exact_mod_cast plane1_cc)
    (plane_nv0_even Support.plus 1 (-2) (1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) planeDepth le_rfl)
  have ht : planeT Support.plus 1 (-2)=(-1/27:ℚ) := by simp only [planeT,Support.sgn];norm_num
  rw [ht] at h
  have hη := (Rat.cast_lt (K:=ℝ)).2 bankP_eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 plane1_cc
  apply eventually_of_point ?_ ?_ h
  · positivity
  · have hn : Dp1.ccert/(Dp1.Dt-bankP.Λ)<(15359/1000:ℚ) := by decide +kernel
    exact_mod_cast hn

open CatalanCore.Uniform.Bank.Plane1.Dips
  CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118 in
theorem dip_1_18_plus_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((4373/250:ℚ):ℝ))<|(CatalanFrames.P6.chi3L2+((1/18:ℚ):ℝ)*Real.pi^2)-(p:ℝ)/q| := by
  have hη := (Rat.cast_lt (K:=ℝ)).2 dip18_eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 dip18_cc
  apply eventually_of_point ?_ (by exact_mod_cast dip18_mu) dip_1_18_plus_point
  positivity

open CatalanCore.Uniform.Bank.Plane1.Dips
  CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118 in
theorem dip_1_18_minus_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-((4373/250:ℚ):ℝ))<|(CatalanFrames.P6.chi3L2+((-1/18:ℚ):ℝ)*Real.pi^2)-(p:ℝ)/q| := by
  have hη := (Rat.cast_lt (K:=ℝ)).2 dip18_eta
  have hc := (Rat.cast_lt (K:=ℝ)).2 dip18_cc
  apply eventually_of_point ?_ (by exact_mod_cast dip18_mu) dip_1_18_minus_point
  positivity

end TrigammaDifferences.Aux
#print axioms CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.lambda_irrational
#print axioms CatalanCore.Uniform.Bank.Chi3.KContent.chi3_irrational
#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_plus_irrational
#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_minus_irrational
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths1_irrational
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths2_irrational
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths3_irrational
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths4_irrational
#print axioms CatalanCore.Uniform.Bank.HalvesContent.Bound.pi2_irrational
#print axioms TrigammaDifferences.Aux.X_nonneg
#print axioms TrigammaDifferences.Aux.eventually_of_exact
#print axioms TrigammaDifferences.Aux.eventually_of_point
#print axioms TrigammaDifferences.Aux.lambda_final
#print axioms TrigammaDifferences.Aux.thirds_plus_final
#print axioms TrigammaDifferences.Aux.thirds_minus_final
#print axioms TrigammaDifferences.Aux.chi3_final
#print axioms TrigammaDifferences.Aux.fifths1_final
#print axioms TrigammaDifferences.Aux.fifths2_final
#print axioms TrigammaDifferences.Aux.fifths3_final
#print axioms TrigammaDifferences.Aux.fifths4_final
#print axioms TrigammaDifferences.Aux.sevenths_final
#print axioms TrigammaDifferences.Aux.pi2_final
#print axioms TrigammaDifferences.Aux.eventually_of_q
#print axioms TrigammaDifferences.Aux.plane1_final
#print axioms TrigammaDifferences.Aux.plane2_final
#print axioms TrigammaDifferences.Aux.zeta3_final
#print axioms TrigammaDifferences.Aux.dip_2_27_plus_final
#print axioms TrigammaDifferences.Aux.dip_2_27_minus_final
#print axioms TrigammaDifferences.Aux.dip_1_27_plus_final
#print axioms TrigammaDifferences.Aux.dip_1_27_minus_final
#print axioms TrigammaDifferences.Aux.dip_1_18_plus_final
#print axioms TrigammaDifferences.Aux.dip_1_18_minus_final
