module

public import CatalanMeasure.GenD.Signed.RouteI.CapFields
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section
set_option Elab.async false

/-!
# Route I `CompactSource`: source-side facts for the C4 compact caps (data-free)

For an admissible `CapSource S` (module `RouteI.CapFields`):

* the radial kernel series is dominated termwise by `gk k = q^k (1/k + strength + curvature k)`,
  and the tail of that majorant is exactly the retained `auxTail`;
* hence `Dominates` (exact field <= finite degree-`K` upper surrogate) holds for the free rows,
  the ordinary marked rows and the Near field (`row_dominates`, `ord_dominates`, `near_dominates`);
* the reflection moments of the positive species are nonnegative, so `reflPoly y >= 0` for `y >= 0`;
* zero geometry of the Near source: for `0 < y <= 1/10`,
  `nearField t y <= (24/29) log y + log (1+y) - kappa pos + auxTail t pos`
  (the fixed tail is retained; the version without it is false).

Nothing here depends on cell data. The hypotheses `strength <= 1/10`, `curvature <= 1/10`,
`auxMass pos <= 37/100` are plain numerical facts the instance provider discharges.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompactSource

open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open Real Set

noncomputable section

variable (S : CapSource)

/-! ### Elementary facts on `q`, `strength`, `curvature` -/

theorem q_pos : 0 < S.q := Real.exp_pos _

theorem q_lt_one (hS : S.Admissible) : S.q < 1 := by
  unfold CapSource.q
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith [hS.eps_pos])

theorem one_sub_q_sq_pos (hS : S.Admissible) : 0 < 1 - S.q ^ 2 := by
  nlinarith [q_pos S, q_lt_one S hS]

theorem normalizer_pos (hS : S.Admissible) : 0 < S.normalizer := by
  unfold CapSource.normalizer
  exact div_pos (by positivity) (pow_pos (one_sub_q_sq_pos S hS) 2)

theorem strength_nonneg (hS : S.Admissible) : 0 ≤ S.strength := by
  unfold CapSource.strength
  exact div_nonneg (by positivity)
    (mul_pos (mul_pos two_pos (one_sub_q_sq_pos S hS)) (normalizer_pos S hS)).le

theorem curvature_nonneg (hS : S.Admissible) : 0 ≤ S.curvature := by
  unfold CapSource.curvature
  exact (one_div_pos.mpr (mul_pos two_pos (normalizer_pos S hS))).le

theorem rad_pos (i : ℕ) : 0 < S.rad i := Real.exp_pos _

theorem rad_le_one (hS : S.Admissible) (i : ℕ) : S.rad i ≤ 1 := by
  unfold CapSource.rad
  exact Real.exp_le_one_iff.mpr (by linarith [hS.sigma_nonneg i])

theorem one_div_nat_le_one (k : ℕ) : (1 : ℝ) / k ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · simp
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast h

/-! ### The majorant `gk` and the tail `tailB` -/

/-- Termwise majorant of the radial kernel coefficient: `|coef k| = gk k` for `k >= 1`. -/
def gk (k : ℕ) : ℝ := S.q ^ k * (1 / (k : ℝ) + S.strength + S.curvature * k)

/-- The geometric tail of the majorant beyond degree `K`; `auxTail (finite K) σ` is this times
the auxiliary mass (times `2` for the negative species). -/
def tailB (K : ℕ) : ℝ :=
  S.q ^ (K + 1) * ((1 / ((K : ℝ) + 1) + S.strength) * (1 / (1 - S.q)) +
    S.curvature * (((K : ℝ) + 1) * (1 / (1 - S.q)) + S.q * (1 / (1 - S.q)) ^ 2))

theorem auxTail_exact (σ : Sign) : S.auxTail Trunc.exact σ = 0 := rfl

theorem auxTail_finite (K : ℕ) (σ : Sign) :
    S.auxTail (Trunc.finite K) σ =
      tailB S K * S.auxMass σ * (if σ = Sign.neg then 2 else 1) := rfl

theorem gk_nonneg (hS : S.Admissible) (k : ℕ) : 0 ≤ gk S k := by
  have h1 := strength_nonneg S hS
  have h2 := curvature_nonneg S hS
  have h3 := q_pos S
  unfold gk
  positivity

theorem abs_coef (hS : S.Admissible) {k : ℕ} (hk : 1 ≤ k) : |S.coef k| = gk S k := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 := strength_nonneg S hS
  have h2 := curvature_nonneg S hS
  have h3 := q_pos S
  unfold CapSource.coef gk
  rw [abs_neg, abs_of_nonneg (by positivity)]
  field_simp

/-- Termwise bound of the kernel series: `|coef k * u^k * cos θ| <= gk k * y^k` for `|u| <= y`. -/
theorem abs_term_le (hS : S.Admissible) {k : ℕ} (hk : 1 ≤ k) {u θ y : ℝ} (hu : |u| ≤ y) :
    |S.coef k * u ^ k * Real.cos θ| ≤ gk S k * y ^ k := by
  rw [abs_mul, abs_mul, abs_coef S hS hk, abs_pow]
  have hg := gk_nonneg S hS k
  have h1 : |u| ^ k ≤ y ^ k := pow_le_pow_left₀ (abs_nonneg _) hu k
  have h2 : gk S k * |u| ^ k ≤ gk S k * y ^ k := mul_le_mul_of_nonneg_left h1 hg
  have h3 : gk S k * |u| ^ k * |Real.cos θ| ≤ gk S k * |u| ^ k :=
    mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one θ)
  linarith

theorem abs_term_le_one (hS : S.Admissible) {k : ℕ} (hk : 1 ≤ k) {u θ : ℝ} (hu : |u| ≤ 1) :
    |S.coef k * u ^ k * Real.cos θ| ≤ gk S k := by
  simpa using abs_term_le S hS hk (y := 1) hu

theorem summable_gk (hS : S.Admissible) : Summable (gk S) := by
  have hq0 := (q_pos S).le
  have hq1 := q_lt_one S hS
  have hn : ‖S.q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have h1 : Summable fun k : ℕ => (1 + S.strength) * S.q ^ k :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have h2 : Summable fun k : ℕ => S.curvature * ((k : ℝ) * S.q ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hn).summable.mul_left _
  refine Summable.of_nonneg_of_le (gk_nonneg S hS) (fun k => ?_) (h1.add h2)
  have hs := strength_nonneg S hS
  have hc := curvature_nonneg S hS
  have hqk : 0 ≤ S.q ^ k := pow_nonneg hq0 k
  have := one_div_nat_le_one k
  unfold gk
  nlinarith [mul_le_mul_of_nonneg_left this hqk]

theorem hasSum_tail (hS : S.Admissible) (K : ℕ) :
    HasSum (fun i : ℕ => S.q ^ (K + 1) * (S.q ^ i *
      ((1 / ((K : ℝ) + 1) + S.strength + S.curvature * ((K : ℝ) + 1)) + S.curvature * i)))
      (tailB S K) := by
  have hq0 := (q_pos S).le
  have hq1 := q_lt_one S hS
  have hn : ‖S.q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have h1 := hasSum_geometric_of_lt_one hq0 hq1
  have h2 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have h := ((h1.mul_left (1 / ((K : ℝ) + 1) + S.strength + S.curvature * ((K : ℝ) + 1))).add
    (h2.mul_left S.curvature)).mul_left (S.q ^ (K + 1))
  convert h using 1
  · funext i
    ring
  · unfold tailB
    have : (1 - S.q) ≠ 0 := (sub_pos.mpr hq1).ne'
    field_simp
    ring

/-- Tail estimate: `|sum_exact - sum_finite K| <= tailB K` for any series dominated by `gk`. -/
theorem abs_sum_diff_le (hS : S.Admissible) (K : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k, 1 ≤ k → |f k| ≤ gk S k) :
    |Trunc.exact.sum f - (Trunc.finite K).sum f| ≤ tailB S K := by
  have hsum : Summable fun k => f (k + 1) := by
    refine Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr (summable_gk S hS)) fun i => ?_
    simpa using hf (i + 1) (by omega)
  have h := hsum.sum_add_tsum_nat_add K
  have e : Trunc.exact.sum f - (Trunc.finite K).sum f = ∑' i, f (i + K + 1) := by
    simp only [Trunc.sum]
    linarith [h]
  rw [e]
  have := tsum_of_norm_bounded (hasSum_tail S hS K) (f := fun i => f (i + K + 1)) (fun i => by
    rw [Real.norm_eq_abs]
    refine (hf (i + K + 1) (by omega)).trans ?_
    have hq0 := (q_pos S).le
    have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hle : (1 : ℝ) / ((i + K + 1 : ℕ) : ℝ) ≤ 1 / ((K : ℝ) + 1) := by
      apply one_div_le_one_div_of_le hKpos
      push_cast
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hpow : S.q ^ (i + K + 1) = S.q ^ (K + 1) * S.q ^ i := by
      rw [← pow_add]; congr 1; omega
    have hqq : 0 ≤ S.q ^ (K + 1) * S.q ^ i := by positivity
    have hc := curvature_nonneg S hS
    unfold gk
    rw [hpow]
    push_cast at hle ⊢
    calc S.q ^ (K + 1) * S.q ^ i * (1 / ((i : ℝ) + K + 1) + S.strength + S.curvature * ((i : ℝ) + K + 1))
        ≤ S.q ^ (K + 1) * S.q ^ i * ((1 / ((K : ℝ) + 1) + S.strength + S.curvature * ((K : ℝ) + 1)) + S.curvature * i) := by
          apply mul_le_mul_of_nonneg_left _ hqq
          nlinarith
      _ = _ := by ring)
  simpa [Real.norm_eq_abs] using this

/-! ### Dominance of the exact fields by the finite surrogates -/

/-- `list_sum_le`: termwise `f a <= g a + w a * c` with `w >= 0` sums. -/
theorem list_sum_le {α : Type*} (l : List α) (f g w : α → ℝ) (c : ℝ)
    (h : ∀ a ∈ l, f a ≤ g a + w a * c) :
    (l.map f).sum ≤ (l.map g).sum + (l.map w).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [add_mul]
    linarith

theorem abs_psi_le (r x : ℝ) (hr : 0 < r) : |psi r x| ≤ 1 := by
  unfold psi
  split_ifs with h
  · have hx : 0 < |x| := lt_trans hr h
    rw [abs_div, abs_of_pos hr, div_le_one hx]
    exact h.le
  · rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact not_lt.mp h

theorem abs_rad_mul_le (hS : S.Admissible) (i : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |S.rad i * x| ≤ 1 := by
  rw [abs_mul, abs_of_pos (rad_pos S i)]
  have := rad_le_one S hS i
  nlinarith [abs_nonneg x, rad_pos S i]

/-- Exact radial part `<=` finite radial part plus the retained tail (without the factor of the
auxiliary mass). -/
theorem radialA_exact_le (hS : S.Admissible) (K : ℕ) (σ : Sign) {x : ℝ} (hx : |x| ≤ 1) :
    S.radialA Trunc.exact σ x ≤ S.radialA (Trunc.finite K) σ x +
      tailB S K * S.auxMass σ * (if σ = Sign.neg then 2 else 1) := by
  unfold CapSource.radialA
  have key := list_sum_le (S.aux σ)
    (fun e => e.w * (Real.log (max |x| (S.rad e.rad)) +
      Trunc.exact.sum (fun k => S.coef k * (psi (S.rad e.rad) x) ^ k * Real.cos (k * e.phase)) +
      (if σ = Sign.neg then
        Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
       else 0)))
    (fun e => e.w * (Real.log (max |x| (S.rad e.rad)) +
      (Trunc.finite K).sum (fun k => S.coef k * (psi (S.rad e.rad) x) ^ k * Real.cos (k * e.phase)) +
      (if σ = Sign.neg then
        (Trunc.finite K).sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
       else 0)))
    (fun e => e.w) (tailB S K * (if σ = Sign.neg then 2 else 1)) (by
      intro e _
      have hd := abs_sum_diff_le S hS K
        (fun k => S.coef k * (psi (S.rad e.rad) x) ^ k * Real.cos (k * e.phase))
        (fun k hk => abs_term_le_one S hS hk (abs_psi_le _ _ (rad_pos S e.rad)))
      have hd' := (abs_le.mp hd).2
      have hw := e.w_nonneg
      by_cases hσ : σ = Sign.neg
      · have hm := abs_sum_diff_le S hS K
          (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
          (fun k hk => abs_term_le_one S hS hk (abs_rad_mul_le S hS e.rad hx))
        have hm' := (abs_le.mp hm).2
        simp only [if_pos hσ]
        nlinarith [mul_nonneg hw (sub_nonneg.mpr hd'), mul_nonneg hw (sub_nonneg.mpr hm')]
      · simp only [if_neg hσ]
        nlinarith [mul_nonneg hw (sub_nonneg.mpr hd')])
  calc _ ≤ _ := key
    _ = _ := by unfold CapSource.auxMass; ring

/-- Dominance of any row field (free or marked, any references) on `|x| <= 1`. -/
theorem rowField_exact_le (hS : S.Admissible) (K : ℕ) (σ : Sign) (fl : Flavor)
    (ref : Option (Fin 2)) {x : ℝ} (hx : |x| ≤ 1) :
    S.rowField Trunc.exact σ fl ref x ≤ S.rowField (Trunc.finite K) σ fl ref x := by
  have h := radialA_exact_le S hS K σ hx
  unfold CapSource.rowField
  rw [auxTail_exact, auxTail_finite]
  linarith

theorem abs_signed_le (σ : Sign) {s : ℝ} (hs : s ∈ ordDom σ) :
    |(if σ = Sign.neg then (-1 : ℝ) else 1) * s| ≤ 1 := by
  have h : 0 ≤ s ∧ s ≤ 1 := by
    cases σ <;> simp only [ordDom, mem_Icc] at hs <;> constructor <;> linarith [hs.1, hs.2]
  cases σ <;> simp [abs_mul, abs_of_nonneg h.1, h.2]

/-- `Dominates.row`. -/
theorem row_dominates (hS : S.Admissible) (K : ℕ) :
    ∀ a, ∀ x ∈ rowDom, S.freeRow Trunc.exact a x ≤ S.freeRow (Trunc.finite K) a x := by
  intro a x hx
  refine rowField_exact_le S hS K _ _ _ ?_
  rw [abs_le]
  rcases hx with hx | hx
  · exact ⟨hx.1, by linarith [hx.2]⟩
  · exact ⟨by linarith [hx.1], hx.2.le⟩

/-- `Dominates.ord`. -/
theorem ord_dominates (hS : S.Admissible) (K : ℕ) :
    ∀ σ, ∀ s ∈ ordDom σ,
      S.ordField Trunc.exact σ ((if σ = Sign.neg then -1 else 1) * s) ≤
        S.ordField (Trunc.finite K) σ ((if σ = Sign.neg then -1 else 1) * s) :=
  fun σ s hs => rowField_exact_le S hS K _ _ _ (abs_signed_le σ hs)

/-- `Dominates.near`. -/
theorem near_dominates (hS : S.Admissible) (K : ℕ) :
    ∀ y ∈ Ioo (0 : ℝ) 1, S.nearField Trunc.exact y ≤ S.nearField (Trunc.finite K) y := by
  intro y hy
  have hy1 : |y| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hy.1], hy.2.le⟩
  have key := list_sum_le (S.aux Sign.pos)
    (fun e => e.w * Trunc.exact.sum
      (fun k => S.coef k * (S.rad e.rad * y) ^ k * Real.cos (k * e.phase)))
    (fun e => e.w * (Trunc.finite K).sum
      (fun k => S.coef k * (S.rad e.rad * y) ^ k * Real.cos (k * e.phase)))
    (fun e => e.w) (tailB S K) (by
      intro e _
      have hd := abs_sum_diff_le S hS K
        (fun k => S.coef k * (S.rad e.rad * y) ^ k * Real.cos (k * e.phase))
        (fun k hk => abs_term_le_one S hS hk (abs_rad_mul_le S hS e.rad hy1))
      have hd' := (abs_le.mp hd).2
      nlinarith [mul_nonneg e.w_nonneg (sub_nonneg.mpr hd')])
  unfold CapSource.nearField
  rw [auxTail_exact, auxTail_finite]
  have hm : S.auxMass Sign.pos = ((S.aux Sign.pos).map fun e => e.w).sum := rfl
  rw [hm]
  simp only [if_neg (by decide : ¬ (Sign.pos = Sign.neg)), mul_one]
  linarith

/-! ### Reflection moments and `reflPoly >= 0` -/

theorem physX_nonneg {Y : ℝ} (h : 0 ≤ Y) : 0 ≤ YCell.physX Y := by
  unfold YCell.physX
  rw [if_pos h]
  exact div_nonneg two_pos.le (add_nonneg h (Real.sqrt_nonneg _))

theorem phys_pow_nonneg (c : YCell) (hc : 2 ≤ c.lo) (k : ℕ) :
    0 ≤ c.phys fun x => x ^ k := by
  unfold YCell.phys YCell.avg
  refine mul_nonneg (div_nonneg c.w_nonneg (sub_pos.mpr c.lo_lt).le) ?_
  refine intervalIntegral.integral_nonneg c.lo_lt.le fun Y hY => ?_
  exact pow_nonneg (physX_nonneg (by linarith [hY.1])) k

theorem reflMoment_nonneg (hS : S.Admissible) (k : ℕ) : 0 ≤ S.reflMoment k := by
  unfold CapSource.reflMoment physL
  refine List.sum_nonneg fun a ha => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact phys_pow_nonneg c (hS.gas_pos c hc) k

theorem reflPoly_nonneg (hS : S.Admissible) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ S.reflPoly y := by
  unfold CapSource.reflPoly
  refine Finset.sum_nonneg fun k _ => ?_
  have := reflMoment_nonneg S hS (k + 1)
  positivity

/-! ### Zero geometry of the Near source -/

/-- Majorant `(11/10 + k/10) y^k` of the Near radial series on `0 < y <= 1/10`. -/
theorem near_radial_abs_le (hS : S.Admissible) (hs : S.strength ≤ 1 / 10)
    (hc : S.curvature ≤ 1 / 10) (t : Trunc) {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1 / 10)
    (e : AuxEntry) (θ : ℕ → ℝ) :
    t.sum (fun k => S.coef k * (S.rad e.rad * y) ^ k * Real.cos (θ k)) ≤ 109 / 81 * y := by
  have hy : y < 1 := by linarith
  have hn : ‖y‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hy0]; exact hy
  have hG : (1 - y)⁻¹ ≤ 10 / 9 := by
    have h9 : (9 / 10 : ℝ) ≤ 1 - y := by linarith
    calc (1 - y)⁻¹ ≤ (9 / 10 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h9
      _ = 10 / 9 := by norm_num
  have hG0 : 0 ≤ (1 - y)⁻¹ := inv_nonneg.mpr (by linarith)
  -- majorant h i = y * (y^i * (12/10 + i/10)) = (11/10 + (i+1)/10) y^(i+1)
  have h1 := hasSum_geometric_of_lt_one hy0.le hy
  have h2 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have hh := ((h1.mul_left (12 / 10 : ℝ)).add (h2.mul_left (1 / 10 : ℝ))).mul_left y
  have hB : y * (12 / 10 * (1 - y)⁻¹ + 1 / 10 * (y / (1 - y) ^ 2)) ≤ 109 / 81 * y := by
    have hsq : (y / (1 - y) ^ 2) ≤ 10 / 81 := by
      have : y / (1 - y) ^ 2 = y * ((1 - y)⁻¹) ^ 2 := by
        field_simp
      rw [this]
      have : ((1 - y)⁻¹) ^ 2 ≤ (10 / 9) ^ 2 := pow_le_pow_left₀ hG0 hG 2
      nlinarith
    nlinarith
  have hterm : ∀ k : ℕ, 1 ≤ k →
      |S.coef k * (S.rad e.rad * y) ^ k * Real.cos (θ k)| ≤ (11 / 10 + (k : ℝ) / 10) * y ^ k := by
    intro k hk
    have hu : |S.rad e.rad * y| ≤ y := by
      rw [abs_mul, abs_of_pos (rad_pos S e.rad), abs_of_pos hy0]
      nlinarith [rad_le_one S hS e.rad]
    refine (abs_term_le S hS hk hu).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hq1 : S.q ^ k ≤ 1 := pow_le_one₀ (q_pos S).le (q_lt_one S hS).le
    have hk1 : (1 : ℝ) / k ≤ 1 := one_div_nat_le_one k
    have hkpos : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hin : 1 / (k : ℝ) + S.strength + S.curvature * k ≤ 11 / 10 + (k : ℝ) / 10 := by
      nlinarith
    have hnn : 0 ≤ 1 / (k : ℝ) + S.strength + S.curvature * k := by
      have := strength_nonneg S hS
      have := curvature_nonneg S hS
      positivity
    unfold gk
    calc S.q ^ k * (1 / (k : ℝ) + S.strength + S.curvature * k)
        ≤ 1 * (1 / (k : ℝ) + S.strength + S.curvature * k) :=
          mul_le_mul_of_nonneg_right hq1 hnn
      _ ≤ _ := by linarith
  have hterm' : ∀ i : ℕ, |S.coef (i + 1) * (S.rad e.rad * y) ^ (i + 1) * Real.cos (θ (i + 1))| ≤
      y * (12 / 10 * y ^ i + 1 / 10 * ((i : ℝ) * y ^ i)) := fun i =>
    (hterm (i + 1) (by omega)).trans_eq (by push_cast; ring)
  have hgnn : ∀ i : ℕ, 0 ≤ y * (12 / 10 * y ^ i + 1 / 10 * ((i : ℝ) * y ^ i)) := fun i => by
    positivity
  cases t with
  | exact =>
    simp only [Trunc.sum]
    refine le_trans (le_abs_self _) ?_
    refine le_trans (Real.norm_eq_abs _ ▸ tsum_of_norm_bounded hh (fun i => ?_)) hB
    rw [Real.norm_eq_abs]
    exact hterm' i
  | finite K =>
    simp only [Trunc.sum]
    refine le_trans (le_abs_self _) ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => hterm' i) ?_
    exact le_trans (sum_le_hasSum (Finset.range K) (fun i _ => hgnn i) hh) hB

theorem near_zero_geometry (hS : S.Admissible) (t : Trunc) (hs : S.strength ≤ 1 / 10)
    (hc : S.curvature ≤ 1 / 10) (hM : S.auxMass Sign.pos ≤ 37 / 100) {y : ℝ} (hy0 : 0 < y)
    (hy1 : y ≤ 1 / 10) :
    S.nearField t y ≤ (24 / 29) * Real.log y + Real.log (1 + y) - kappa Sign.pos +
      S.auxTail t Sign.pos := by
  have hrad := list_sum_le (S.aux Sign.pos)
    (fun e => e.w * t.sum (fun k => S.coef k * (S.rad e.rad * y) ^ k * Real.cos (k * e.phase)))
    (fun _ => 0) (fun e => e.w) (109 / 81 * y) (fun e _ => by
      have h := near_radial_abs_le S hS hs hc t hy0 hy1 e (fun k => k * e.phase)
      simp only [zero_add]
      exact mul_le_mul_of_nonneg_left h e.w_nonneg)
  have h0 : ((S.aux Sign.pos).map fun _ : AuxEntry => (0 : ℝ)).sum = 0 := by simp
  rw [h0, zero_add] at hrad
  have hm : S.auxMass Sign.pos = ((S.aux Sign.pos).map fun e => e.w).sum := rfl
  rw [← hm] at hrad
  have hrad' : ((S.aux Sign.pos).map fun e => e.w * t.sum
      (fun k => S.coef k * (S.rad e.rad * y) ^ k * Real.cos (k * e.phase))).sum ≤
      4033 / 8100 * y := by
    have : S.auxMass Sign.pos * (109 / 81 * y) ≤ 37 / 100 * (109 / 81 * y) :=
      mul_le_mul_of_nonneg_right hM (by positivity)
    linarith
  have hl : y / (1 + y) ≤ Real.log (1 + y) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + y by linarith)
    have e : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
    linarith
  have h2 : 4033 / 8100 * y ≤ y / (1 + y) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hR := reflPoly_nonneg S hS hy0.le
  have hlog2 : 0 ≤ Real.log (1 + y ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg y])
  unfold CapSource.nearField
  have e48 : (48 : ℝ) / 58 = 24 / 29 := by norm_num
  rw [e48]
  linarith

end

end CatalanMeasure.GenD.Signed.RouteI.CompactSource

#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactSource.abs_sum_diff_le
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactSource.row_dominates
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactSource.ord_dominates
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactSource.near_dominates
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactSource.near_zero_geometry
