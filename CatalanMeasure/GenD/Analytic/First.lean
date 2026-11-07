module

public import CatalanMeasure.GenD.Analytic.Fields
public import CatalanMeasure.GenD.Analytic.CommonField
public import CatalanMeasure.FreePopulationFields
public import CatalanMeasure.Parametric.WeightedPopulationValue

@[expose] public section

/-!
# Analytic layer: the first-population trial contract and its energy bound (design-generic)

`FirstTrialBounds P` is the generic form of `FirstTrialBoundsAt`; `first_energy` the generic form
of `first_energy_with_trial`.  The design enters through `gC0`, `gC1` and the two ratios
`(b0+q0+2g0)/n0` (the `A/n` weight, `2/5` at P20) and `g0/n0` (`1/10` at P20).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric OAI.InternalCatalan Filter Set Finset
open scoped Topology BigOperators

noncomputable section

theorem gC1_eq (P : Parameters) (hP : Admissible P) :
    gC1 P = 2 - ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0 := by
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  unfold gC1 gKappa gRes
  field_simp
  ring

/-- Pure algebra behind `physical_one_constant_le`. -/
theorem one_constant_alg {n n0 N k m p : ℝ} (hn0 : n0 ≠ 0) (hN : N ≠ 0)
    (hn : n = n0 * N) (hp : p = n - m) :
    ((n + k * N - 1) / n + p * (p - 1) / (2 * n ^ 2)) - (n - 1) / (2 * n) -
        (3 / 2 : ℝ) * (p / n) ^ 2 =
      (-(1 / 2 - k / n0) + 2 * (m / n) - (m / n) ^ 2) - (n + p) / (2 * n ^ 2) := by
  subst hn hp
  field_simp
  ring

/-- Generic form of `twenty_physical_one_constant_le`. -/
theorem physical_one_constant_le {P : Parameters} (hP : Admissible P) {N p m : ℕ} (hN : 0 < N)
    (hpm : p + m = P.n N) :
    populationPhysicalOneConstant P N p -
        (3 / 2 : ℝ) * ((p : ℝ) / (P.n N : ℝ)) ^ 2 * Real.log 2 ≤
      (-gC0 P + 2 * ((m : ℝ) / (P.n N : ℝ)) - ((m : ℝ) / (P.n N : ℝ)) ^ 2) * Real.log 2 := by
  have hg := two_g_lt_n hP hN
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnpos := n_pos hP hN
  have hC := C_nat P N
  have hCsub : 1 ≤ P.C N := by omega
  have hCR : ((P.C N - 1 : ℕ) : ℝ) = (P.n N : ℝ) + ((P.b0 : ℝ) + P.q0 + P.g0) * N - 1 := by
    rw [Nat.cast_sub hCsub, hC]; push_cast; ring
  have hp : (p : ℝ) = (P.n N : ℝ) - (m : ℝ) := by
    have h : (p : ℝ) + (m : ℝ) = (P.n N : ℝ) := by exact_mod_cast hpm
    linarith only [h]
  have halg := one_constant_alg (k := (P.b0 : ℝ) + P.q0 + P.g0) hn0 hNR (n_cast P N) hp
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hT : 0 ≤ ((P.n N : ℝ) + (p : ℝ)) / (2 * (P.n N : ℝ) ^ 2) := by positivity
  have hdef : populationPhysicalOneConstant P N p -
      (3 / 2 : ℝ) * ((p : ℝ) / (P.n N : ℝ)) ^ 2 * Real.log 2 =
      ((((P.n N : ℝ) + ((P.b0 : ℝ) + P.q0 + P.g0) * N - 1) / (P.n N : ℝ) +
        (p : ℝ) * ((p : ℝ) - 1) / (2 * (P.n N : ℝ) ^ 2)) - ((P.n N : ℝ) - 1) / (2 * (P.n N : ℝ)) -
        (3 / 2 : ℝ) * ((p : ℝ) / (P.n N : ℝ)) ^ 2) * Real.log 2 := by
    unfold populationPhysicalOneConstant populationPhysicalConstant
    rw [hCR]
    ring
  rw [hdef]
  have hkey : ((((P.n N : ℝ) + ((P.b0 : ℝ) + P.q0 + P.g0) * N - 1) / (P.n N : ℝ) +
        (p : ℝ) * ((p : ℝ) - 1) / (2 * (P.n N : ℝ) ^ 2)) - ((P.n N : ℝ) - 1) / (2 * (P.n N : ℝ)) -
        (3 / 2 : ℝ) * ((p : ℝ) / (P.n N : ℝ)) ^ 2) ≤
      (-gC0 P + 2 * ((m : ℝ) / (P.n N : ℝ)) - ((m : ℝ) / (P.n N : ℝ)) ^ 2) := by
    unfold gC0 gKappa
    linarith only [halg, hT]
  exact mul_le_mul_of_nonneg_right hkey hl2

/-- Generic first-population trial contract. -/
structure FirstTrialBounds (P : Parameters) (target cost : ℝ) where
  p : ℕ → ℝ
  v : ℕ → ℝ
  lambda : ℝ
  MX : ℝ
  MY : ℝ
  normCap : ℝ
  fieldCap : ℝ
  lambda_nonneg : 0 ≤ lambda
  p_summable : Summable (fun j => |p j|)
  v_summable : Summable (fun j => |v j|)
  norm_le : barrierTrialNormSq p + barrierTrialNormSq v / 2 ≤ normCap
  field_sum : MX + MY = fieldCap
  row : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalOneFreeField P N x + lambda * paramCaseField P N x -
        2 * barrierTrialT p x - barrierTrialS v x -
        Real.log (1 - x) / (2 * (P.n N : ℝ)) ≤ MX + ε
  column : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ s ∈ Ioo (0 : ℝ) 1,
      populationEndpointColumnField P N 0 s + 2 * barrierTrialT v s -
        Real.log (1 - s) / (P.n N : ℝ) ≤ MY + ε
  budget : ∀ a : ℝ,
    (-gC0 P + gC1 P * a - a ^ 2) * Real.log 2 +
      normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
      a * (2 * lambda * ((P.g0 : ℝ) / P.n0)) ≤
        -target + Real.log 2 / 2 + cost * a

set_option maxHeartbeats 1600000 in
/-- Generic `first_energy_with_trial`. -/
theorem first_energy {P : Parameters} (hP : Admissible P) {target c : ℝ}
    (D : FirstTrialBounds P target c) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ j, s j ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-(1 : ℝ) < ∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) →
      weightedPopulationOneValue P N (((m : ℝ) / (P.n N : ℝ))) x y s ≤
        -target + Real.log 2 / 2 + c * ((m : ℝ) / (P.n N : ℝ)) + δ := by
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hlambda := D.lambda_nonneg
  obtain ⟨e, he, herr⟩ := firstDampingError_eventually hP D.lambda D.p D.v hε
  filter_upwards [D.row hε, D.column hε,
      log_reciprocal_eventually hP hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hsmall herror hN p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  let ν : ℝ := P.n N
  let α : ℝ := (m : ℝ) / ν
  have hν : 0 < ν := by dsimp only [ν]; exact_mod_cast n_pos hP hN
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (p : ℝ) / ν = 1 - α := by
    have hh := population_fractions hP hN hpm
    dsimp only [α, ν]
    linarith only [hh]
  have hbound := free_population_fields_dual_bound
    (constant := populationPhysicalOneConstant P N p) hν he hlambda
    (by dsimp only [ν]; exact_mod_cast (show p ≤ P.n N by omega))
    (populationPhysicalOneFreeField P N)
    (fun u => populationPhysicalOneFixedField P N u - populationCommonLog P N u / ν)
    (populationEndpointColumnField P N α) (paramCaseField P N)
    x y s hx hs hxi hsi hcase D.p D.v D.p_summable D.v_summable
    D.norm_le
    (fun i => hrow (x i) (population_row_domain (hx i) (hx0 i)))
    (fun j => by
      have hc := marked_first_field_after_common hP hN (hy j) (hy0 j) hlambda
      have hsq : y j ^ 2 ≤ 1 := by nlinarith only [(hy j).1, (hy j).2]
      have hl : Real.log (1 + y j ^ 2) ≤ Real.log 2 :=
        Real.log_le_log (by positivity) (by linarith only [hsq])
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hcorr := div_le_div_of_nonneg_right (show Real.log (1 + y j ^ 2) ≤ 2 * Real.log 2 by
        linarith only [hl, hl2]) (show (0 : ℝ) ≤ 2 * ν by positivity)
      have heq : 2 * Real.log 2 / (2 * ν) = Real.log 2 / ν := by ring
      rw [heq] at hcorr
      change populationPhysicalOneFixedField P N (y j) - populationCommonLog P N (y j) / ν +
        D.lambda * paramCaseField P N (y j) ≤
          -(((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) * Real.log 2 +
            2 * D.lambda * ((P.g0 : ℝ) / P.n0) + ε
      unfold populationPhysicalOneFixedField populationCommonLog
      dsimp only [ν] at hcorr ⊢
      ring_nf at hc hcorr hsmall ⊢
      linarith only [hc, hcorr, hsmall])
    (fun j => by
      have hc := hcol (s j) (hs j)
      have hl : Real.log (1 + s j) ≤ Real.log 2 :=
        Real.log_le_log (by linarith [(hs j).1]) (by linarith [(hs j).2])
      have hm := mul_le_mul_of_nonneg_left hl hα
      have hid : populationEndpointColumnField P N α (s j) =
          populationEndpointColumnField P N 0 (s j) + α * Real.log (1 + s j) := by
        unfold populationEndpointColumnField
        ring
      rw [hid]
      exact (by linarith only [hc, hm] :
        populationEndpointColumnField P N 0 (s j) + α * Real.log (1 + s j) +
          2 * barrierTrialT D.v (s j) - Real.log (1 - s j) / ν ≤
            D.MY + ε + α * Real.log 2))
  have hbound' : weightedPopulationOneValue P N α x y s ≤
      populationPhysicalOneConstant P N p - (3 / 2 : ℝ) * ((p : ℝ) / ν) ^ 2 * Real.log 2 +
      D.normCap + ((p : ℝ) / ν) * (D.MX + ε +
        (D.MY + ε + α * Real.log 2)) +
      α * (-(((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) * Real.log 2 +
        2 * D.lambda * ((P.g0 : ℝ) / P.n0) + ε) +
      firstDampingError P D.lambda e D.p D.v N := by
    unfold weightedPopulationOneValue
    convert hbound using 1
    unfold firstDampingError α
    dsimp only [ν]
    rw [n_cast]
    ring
  have hconst := physical_one_constant_le hP hN hpm
  have hbudget := D.budget α
  rw [gC1_eq P hP] at hbudget
  have hfields := congrArg (fun t : ℝ => (1 - α) * t) D.field_sum
  have hεα := mul_nonneg hε.le hα
  rw [hfree] at hbound' hconst
  dsimp only [α, ν, ε] at hbound' hconst hbudget hfields hεα herror ⊢
  ring_nf at hbound' hconst hbudget hfields herror hεα ⊢
  nlinarith only [hbound', hconst, hbudget, hfields, herror, hεα, hδ]


/-- The marked field after the common factor, with the correction `d` and the cap `M₁` on
`lambda · paramCaseField + d` (GP §7.2): the middle term `-(1/2 - g/n) log (1 + x²)` is at most
`0`, so the field plus `lambda · paramCaseField + d` is at most `-(A/n) log 2 + M₁`. -/
theorem marked_first_field_after_common_d {P : Parameters} (hP : Admissible P) {N : ℕ}
    (hN : 0 < N) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) {lambda M₁ dx : ℝ}
    (hlambda : 0 ≤ lambda) (hM : lambda * paramCaseField P N x + dx ≤ M₁) :
    paramPopulationRowField P N 1 x + lambda * paramCaseField P N x + dx -
      Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)| / (P.n N : ℝ) ≤
        -(((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) * Real.log 2 + M₁ := by
  have he := population_row_field_sub_common_full hP hN 1 hx hx0
  have hA := ratio_A P hP hN
  have hν : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
  have h2g : (2 * (P.g N : ℝ)) ≤ P.n N := by exact_mod_cast (two_g_lt_n hP hN).le
  have hcoef : (P.g N : ℝ) / (P.n N : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hν]
    linarith only [h2g]
  have hlog : 0 ≤ Real.log (1 + x ^ 2) := Real.log_nonneg (by nlinarith only [sq_nonneg x])
  have hmid : 0 ≤ (1 / 2 - (P.g N : ℝ) / (P.n N : ℝ)) * Real.log (1 + x ^ 2) :=
    mul_nonneg (by linarith only [hcoef]) hlog
  rw [neg_div, hA] at he
  norm_num only at he
  linarith only [he, hmid, hM]

/-- First-population trial contract (GP §8) with a window `W` of fractions `a = m / n`, a column
field `Cf N s`, a node correction `d` (the `δ̂ / 58` of GP §7), and a cap `M₁` on the marked term
`lambda · paramCaseField + d` on the window `G`.  With `d = 0`, `W` the set `{a | α₁ ≤ a}` or
`univ`, `Cf N = populationEndpointColumnField P N 0` and `M₁ = 2 lambda g₀ / n₀` it is the
original endpoint contract (no `α log (1 + s)` term, no `a (1 - a) log 2` in the budget). -/
structure FirstTrialBoundsEnd (P : Parameters) (W : Set ℝ) (Cf : ℕ → ℝ → ℝ) (d : ℝ → ℝ)
    (G : ℝ → Prop) (target cost : ℝ) where
  p : ℕ → ℝ
  v : ℕ → ℝ
  lambda : ℝ
  MX : ℝ
  MY : ℝ
  normCap : ℝ
  fieldCap : ℝ
  M₁ : ℝ
  lambda_nonneg : 0 ≤ lambda
  p_summable : Summable (fun j => |p j|)
  v_summable : Summable (fun j => |v j|)
  norm_le : barrierTrialNormSq p + barrierTrialNormSq v / 2 ≤ normCap
  field_sum : MX + MY = fieldCap
  row : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalOneFreeField P N x + lambda * paramCaseField P N x -
        2 * barrierTrialT p x - barrierTrialS v x -
        Real.log (1 - x) / (2 * (P.n N : ℝ)) ≤ MX + ε
  marked : ∀ {N : ℕ}, 0 < N → ∀ {x : ℝ}, x ∈ Ioo (-1 : ℝ) 1 → x ≠ 0 → G x →
    lambda * paramCaseField P N x + d x ≤ M₁
  column : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ s ∈ Ioo (0 : ℝ) 1,
      Cf N s + 2 * barrierTrialT v s - Real.log (1 - s) / (P.n N : ℝ) ≤ MY + ε
  budget : ∀ a ∈ W,
    (-gC0 P + gC1 P * a - a ^ 2) * Real.log 2 +
      normCap + (1 - a) * fieldCap + a * M₁ ≤
        -target + Real.log 2 / 2 + cost * a

/-- The original endpoint contract: window `univ`, column field `populationEndpointColumnField P N 0`,
no correction `d`, no window `G`. -/
abbrev FirstTrialBoundsEnd0 (P : Parameters) (target cost : ℝ) :=
  FirstTrialBoundsEnd P Set.univ (fun N => populationEndpointColumnField P N 0) (fun _ => 0)
    (fun _ => True) target cost

set_option maxHeartbeats 1600000 in
/-- **GP Lemma 8.0, first case.**  `first_energy` for the record with window `W`, column field
`Cf` and node correction `d`: the value with the marked field `… + d` is at most the target,
for every configuration with `m / n ∈ W` and `G (y j)`. -/
theorem first_energy_end {P : Parameters} (hP : Admissible P) {W : Set ℝ} {Cf : ℕ → ℝ → ℝ}
    {d : ℝ → ℝ} {G : ℝ → Prop} {target c : ℝ}
    (D : FirstTrialBoundsEnd P W Cf d G target c) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ j, s j ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-(1 : ℝ) < ∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) →
      ((m : ℝ) / (P.n N : ℝ)) ∈ W →
      freePopulationValueWithFields (P.n N : ℝ) (populationPhysicalOneConstant P N p)
        (populationPhysicalOneFreeField P N)
        (fun u => populationPhysicalOneFixedField P N u - populationCommonLog P N u / (P.n N : ℝ)
          + d u)
        (Cf N) x y s ≤
        -target + Real.log 2 / 2 + c * ((m : ℝ) / (P.n N : ℝ)) + δ := by
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hlambda := D.lambda_nonneg
  obtain ⟨e, he, herr⟩ := firstDampingError_eventually hP D.lambda D.p D.v hε
  filter_upwards [D.row hε, D.column hε,
      log_reciprocal_eventually hP hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hsmall herror hN p m hpm x y s hx hx0 hy hy0 hyG hs hxi hsi hcase hW
  let ν : ℝ := P.n N
  let α : ℝ := (m : ℝ) / ν
  have hν : 0 < ν := by dsimp only [ν]; exact_mod_cast n_pos hP hN
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (p : ℝ) / ν = 1 - α := by
    have hh := population_fractions hP hN hpm
    dsimp only [α, ν]
    linarith only [hh]
  have hbound := free_population_fields_dual_bound
    (constant := populationPhysicalOneConstant P N p) hν he hlambda
    (by dsimp only [ν]; exact_mod_cast (show p ≤ P.n N by omega))
    (populationPhysicalOneFreeField P N)
    (fun u => populationPhysicalOneFixedField P N u - populationCommonLog P N u / ν + d u)
    (Cf N) (paramCaseField P N)
    x y s hx hs hxi hsi hcase D.p D.v D.p_summable D.v_summable
    D.norm_le
    (fun i => hrow (x i) (population_row_domain (hx i) (hx0 i)))
    (fun j => by
      have hc := marked_first_field_after_common_d hP hN (hy j) (hy0 j) hlambda
        (D.marked hN (hy j) (hy0 j) (hyG j))
      have hsq : y j ^ 2 ≤ 1 := by nlinarith only [(hy j).1, (hy j).2]
      have hl : Real.log (1 + y j ^ 2) ≤ Real.log 2 :=
        Real.log_le_log (by positivity) (by linarith only [hsq])
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hcorr := div_le_div_of_nonneg_right (show Real.log (1 + y j ^ 2) ≤ 2 * Real.log 2 by
        linarith only [hl, hl2]) (show (0 : ℝ) ≤ 2 * ν by positivity)
      have heq : 2 * Real.log 2 / (2 * ν) = Real.log 2 / ν := by ring
      rw [heq] at hcorr
      change populationPhysicalOneFixedField P N (y j) - populationCommonLog P N (y j) / ν +
        d (y j) + D.lambda * paramCaseField P N (y j) ≤
          -(((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) * Real.log 2 + D.M₁ + ε
      unfold populationPhysicalOneFixedField populationCommonLog
      dsimp only [ν] at hcorr ⊢
      ring_nf at hc hcorr hsmall ⊢
      linarith only [hc, hcorr, hsmall])
    (fun j => by
      have hc := hcol (s j) (hs j)
      exact (by linarith only [hc] :
        Cf N (s j) +
          2 * barrierTrialT D.v (s j) - Real.log (1 - s j) / ν ≤ D.MY + ε))
  have hbound' : freePopulationValueWithFields (P.n N : ℝ) (populationPhysicalOneConstant P N p)
        (populationPhysicalOneFreeField P N)
        (fun u => populationPhysicalOneFixedField P N u - populationCommonLog P N u / (P.n N : ℝ)
          + d u)
        (Cf N) x y s ≤
      populationPhysicalOneConstant P N p - (3 / 2 : ℝ) * ((p : ℝ) / ν) ^ 2 * Real.log 2 +
      D.normCap + ((p : ℝ) / ν) * (D.MX + ε + (D.MY + ε)) +
      α * (-(((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) * Real.log 2 +
        D.M₁ + ε) +
      firstDampingError P D.lambda e D.p D.v N := by
    convert hbound using 1
    unfold firstDampingError α
    dsimp only [ν]
    rw [n_cast]
    ring
  have hconst := physical_one_constant_le hP hN hpm
  have hbudget := D.budget α (by simpa only [α, ν] using hW)
  rw [gC1_eq P hP] at hbudget
  have hfields := congrArg (fun t : ℝ => (1 - α) * t) D.field_sum
  have hεα' : 0 ≤ ((P.n N : ℕ) : ℝ)⁻¹ * (m : ℝ) * δ := by positivity
  generalize freePopulationValueWithFields (P.n N : ℝ) (populationPhysicalOneConstant P N p)
        (populationPhysicalOneFreeField P N)
        (fun u => populationPhysicalOneFixedField P N u - populationCommonLog P N u / (P.n N : ℝ)
          + d u)
        (Cf N) x y s = V at hbound' ⊢
  rw [hfree] at hbound' hconst
  dsimp only [α, ν, ε] at hbound' hconst hbudget hfields herror ⊢
  ring_nf at hbound' hconst hbudget hfields herror ⊢
  nlinarith only [hbound', hconst, hbudget, hfields, hεα', herror, hδ]

end
end Analytic
end CatalanMeasure.GenD
#print axioms CatalanMeasure.GenD.Analytic.marked_first_field_after_common_d
#print axioms CatalanMeasure.GenD.Analytic.first_energy_end

