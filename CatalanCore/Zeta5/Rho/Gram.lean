module

public import CatalanCore.Zeta5.Port.Positivity
public import CatalanCore.Zeta5.Rho.Residue
public import CatalanCore.Zeta5.Rho.Riemann

@[expose] public section

/-!
# The Gram lower bound (ledger ZR02)

`xᵀ G x ≥ A_K c_{a,b} exp(-K W) ∫_a^b p²`, `c_{a,b} = (2π)⁴ a³ / (24 (1 + b))`,
for every `W ≥ sup_{[a,b]} V`, where `G = G_K(ζ(5))`, `p(t) = q(K² t)`.

Keep the `ℓ = 1` term of the weight `w`, restrict the integral to `y ∈ [K√a, K√b]`, substitute
`y = K√t`, and apply the Riemann-sum product bound `prod_ratio_lower`.
-/

namespace CatalanCore.Zeta5.Rho

open Apery MeasureTheory Set Finset Real Polynomial Matrix

/-- `D_m(s) = ∏_{l ≤ m} (s + l²)` over `ℝ`. -/
noncomputable def Dr (m : ℕ) (s : ℝ) : ℝ := ∏ l ∈ Icc 1 m, (s + (l : ℝ) ^ 2)

theorem aeval_D_eq (m : ℕ) (s : ℝ) : aeval s (D m) = Dr m s := by
  simp only [D, Dr, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow,
    Rat.cast_natCast]

theorem Dr_pos (m : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 < Dr m s := by
  unfold Dr
  refine Finset.prod_pos fun l hl => ?_
  have : (1 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.mp hl).1
  positivity

theorem continuous_Dr_sq (m : ℕ) : Continuous (fun y : ℝ => Dr m (y ^ 2)) := by
  unfold Dr
  exact continuous_finset_prod _ (fun l _ => by fun_prop)

/-- The explicit continuous minorant of the integrand (first term of the weight kept). -/
noncomputable def glow (n : ℕ) (x : Fin (37 * n) → ℝ) (y : ℝ) : ℝ :=
  (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * (Dr (3 * n) (y ^ 2)) ^ 6 / Dr (40 * n) (y ^ 2) *
    ((2 * Real.pi) ^ 4 * y ^ 5 / 12 * Real.exp (-(2 * Real.pi * y)))

theorem continuous_glow (n : ℕ) (x : Fin (37 * n) → ℝ) : Continuous (glow n x) := by
  unfold glow
  refine Continuous.mul (Continuous.div ?_ (continuous_Dr_sq _) fun y => (Dr_pos _ (sq_nonneg y)).ne') ?_
  · exact ((continuous_finset_sum _ (fun i _ => by fun_prop)).pow 2).mul
      ((continuous_Dr_sq _).pow 6)
  · fun_prop

theorem w_ge {y : ℝ} (hy : 0 < y) :
    (2 * Real.pi) ^ 4 * y ^ 5 / 12 * Real.exp (-(2 * Real.pi * y)) ≤ w y := by
  unfold w
  have h1 : Real.exp (-(2 * Real.pi * y)) ≤ wS y := by
    have := (summable_w_term hy).le_tsum 0 (fun j _ => by positivity)
    simpa [wS] using this
  have h2 : 0 ≤ (2 * Real.pi) ^ 4 * y ^ 5 / 12 := by positivity
  exact mul_le_mul_of_nonneg_left h1 h2

theorem glow_le {n : ℕ} (x : Fin (37 * n) → ℝ) {y : ℝ} (hy : 0 < y) :
    glow n x y ≤ (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y := by
  unfold glow ν
  rw [aeval_D_eq, aeval_D_eq]
  have hD1 := Dr_pos (3 * n) (sq_nonneg y)
  have hD2 := Dr_pos (40 * n) (sq_nonneg y)
  have hq : 0 ≤ Dr (3 * n) (y ^ 2) ^ 6 / Dr (40 * n) (y ^ 2) := by positivity
  calc (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * Dr (3 * n) (y ^ 2) ^ 6 / Dr (40 * n) (y ^ 2) *
        ((2 * Real.pi) ^ 4 * y ^ 5 / 12 * Real.exp (-(2 * Real.pi * y)))
      = (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * (Dr (3 * n) (y ^ 2) ^ 6 / Dr (40 * n) (y ^ 2) *
        ((2 * Real.pi) ^ 4 * y ^ 5 / 12 * Real.exp (-(2 * Real.pi * y)))) := by ring
    _ ≤ _ := by gcongr; exact w_ge hy

theorem Pfun_continuous (n : ℕ) (x : Fin (37 * n) → ℝ) : Continuous (Pfun n x) := by
  unfold Pfun
  exact continuous_finset_sum _ (fun i _ => by fun_prop)

/-- The pointwise comparison after the substitution `y = K √t`. -/
theorem glow_pointwise (n : ℕ) (hn : 0 < n) (x : Fin (37 * n) → ℝ) {t : ℝ} (ht : 0 < t) :
    AK n * ((2 * Real.pi) ^ 4 * t ^ 3 / (24 * (1 + t))) *
        Real.exp (-((40 * n : ℝ) * Vf t)) * (Pfun n x t) ^ 2 ≤
      glow n x ((40 * n : ℝ) * √t) * ((40 * n : ℝ) * (1 / (2 * √t))) := by
  have hKr : (0 : ℝ) < 40 * n := by positivity
  set Kr : ℝ := 40 * n with hKrdef
  have hs : 0 < √t := Real.sqrt_pos.mpr ht
  set s : ℝ := √t with hsdef
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht.le
  have hy2 : (Kr * s) ^ 2 = Kr ^ 2 * t := by rw [mul_pow, hs2]
  have hP : (∑ i, x i * ((Kr * s) ^ 2) ^ (i : ℕ)) = Pfun n x t := by
    unfold Pfun; rw [hy2]
  have hB := prod_ratio_lower ht (40 * n) (3 * n) (by omega)
  have hα : ((3 * n : ℕ) : ℝ) / ((40 * n : ℕ) : ℝ) = 3 / 40 := by
    push_cast; field_simp
  rw [hα] at hB
  push_cast at hB
  unfold glow
  rw [hP]
  simp only [Dr, hy2]
  set Rr : ℝ := (∏ l ∈ Icc 1 (3 * n), (Kr ^ 2 * t + (l : ℝ) ^ 2)) ^ 6 /
    ∏ k ∈ Icc 1 (40 * n), (Kr ^ 2 * t + (k : ℝ) ^ 2) with hRr
  have hRr' : ((∏ l ∈ Icc 1 (3 * n), (Kr ^ 2 * t + (l : ℝ) ^ 2)) ^ 6 *
      1) / ∏ k ∈ Icc 1 (40 * n), (Kr ^ 2 * t + (k : ℝ) ^ 2) = Rr := by rw [hRr, mul_one]
  have hexpsplit : Real.exp (-(Kr * Vf t)) =
      Real.exp (-(2 * Real.pi * (Kr * s))) * Real.exp (-(Kr * (Jf t 1 - 6 * Jf t (3 / 40)))) := by
    rw [← Real.exp_add]; congr 1; unfold Vf; rw [← hsdef]; ring
  set B : ℝ := Kr ^ (12 * (3 * n)) / Kr ^ (2 * (40 * n)) * (t / (1 + t)) *
    Real.exp (-(Kr * (Jf t 1 - 6 * Jf t (3 / 40)))) with hBdef
  have hBle : B ≤ Rr := hB
  set Q : ℝ := (2 * Real.pi) ^ 4 * Kr ^ 6 * t ^ 2 / 24 * Real.exp (-(2 * Real.pi * (Kr * s)))
    with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  have hL : AK n * ((2 * Real.pi) ^ 4 * t ^ 3 / (24 * (1 + t))) *
        Real.exp (-(Kr * Vf t)) * (Pfun n x t) ^ 2 = (Pfun n x t) ^ 2 * (B * Q) := by
    rw [hexpsplit]
    simp only [AK, hBdef, hQdef, ← hKrdef]
    rw [pow_add]
    field_simp
  have hR : ((Pfun n x t) ^ 2 * (∏ l ∈ Icc 1 (3 * n), (Kr ^ 2 * t + (l : ℝ) ^ 2)) ^ 6 /
        (∏ k ∈ Icc 1 (40 * n), (Kr ^ 2 * t + (k : ℝ) ^ 2))) *
      ((2 * Real.pi) ^ 4 * (Kr * s) ^ 5 / 12 * Real.exp (-(2 * Real.pi * (Kr * s)))) *
      (Kr * (1 / (2 * s))) = (Pfun n x t) ^ 2 * (Rr * Q) := by
    rw [hRr, hQdef]
    have hne : s ≠ 0 := hs.ne'
    have hs4 : s ^ 4 = t ^ 2 := by rw [← hs2]; ring
    have : (Kr * s) ^ 5 * (Kr * (1 / (2 * s))) = Kr ^ 6 * t ^ 2 / 2 := by
      rw [← hs4]; field_simp
    calc ((Pfun n x t) ^ 2 * (∏ l ∈ Icc 1 (3 * n), (Kr ^ 2 * t + (l : ℝ) ^ 2)) ^ 6 /
        (∏ k ∈ Icc 1 (40 * n), (Kr ^ 2 * t + (k : ℝ) ^ 2))) *
      ((2 * Real.pi) ^ 4 * (Kr * s) ^ 5 / 12 * Real.exp (-(2 * Real.pi * (Kr * s)))) *
      (Kr * (1 / (2 * s)))
        = (Pfun n x t) ^ 2 * ((∏ l ∈ Icc 1 (3 * n), (Kr ^ 2 * t + (l : ℝ) ^ 2)) ^ 6 /
          (∏ k ∈ Icc 1 (40 * n), (Kr ^ 2 * t + (k : ℝ) ^ 2))) *
          ((2 * Real.pi) ^ 4 / 12 * ((Kr * s) ^ 5 * (Kr * (1 / (2 * s)))) *
            Real.exp (-(2 * Real.pi * (Kr * s)))) := by ring
      _ = _ := by rw [this]; ring
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBle hQ0) (sq_nonneg _)

/-- **ZR02.**  `xᵀ G_K(ζ(5)) x ≥ A_K c_{a,b} exp(-K W) ∫_a^b p²` for every `W ≥ sup_{[a,b]} V`. -/
theorem gram_lower (n : ℕ) (hn : 0 < n) (x : Fin (37 * n) → ℝ) {a b W : ℝ} (ha : 0 < a)
    (hab : a < b) (hW : ∀ t ∈ Icc a b, Vf t ≤ W) :
    AK n * ((2 * Real.pi) ^ 4 * a ^ 3 / (24 * (1 + b))) * Real.exp (-((40 * n : ℝ) * W)) *
        ∫ t in a..b, (Pfun n x t) ^ 2 ≤
      star x ⬝ᵥ (((G n).map (aeval zeta5)) *ᵥ x) := by
  have hKr : (0 : ℝ) < 40 * n := by positivity
  set Kr : ℝ := 40 * n with hKrdef
  have hsa : 0 < √a := Real.sqrt_pos.mpr ha
  have hsab : √a < √b := Real.sqrt_lt_sqrt ha.le hab
  have hlow : Kr * √a < Kr * √b := mul_lt_mul_of_pos_left hsab hKr
  have hpos : 0 < Kr * √a := mul_pos hKr hsa
  -- substitution
  have hsub : ∫ y in (Kr * √a)..(Kr * √b), glow n x y =
      ∫ t in a..b, glow n x (Kr * √t) * (Kr * (1 / (2 * √t))) := by
    have := intervalIntegral.integral_comp_mul_deriv (a := a) (b := b)
      (f := fun t => Kr * √t) (f' := fun t => Kr * (1 / (2 * √t))) (g := glow n x)
      (fun t ht => by
        have ht0 : t ≠ 0 := (lt_of_lt_of_le ha (by rw [Set.uIcc_of_le hab.le] at ht; exact ht.1)).ne'
        exact (Real.hasDerivAt_sqrt ht0).const_mul Kr |>.congr_deriv (by ring))
      (by
        refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
          (continuousOn_const.mul Real.continuous_sqrt.continuousOn) fun t ht => ?_)
        rw [Set.uIcc_of_le hab.le] at ht
        have := Real.sqrt_pos.mpr (lt_of_lt_of_le ha ht.1)
        positivity)
      (continuous_glow n x)
    simpa using this.symm
  -- comparison with the Gram integral
  have hle : (Kr * √a) ≤ (Kr * √b) := hlow.le
  have hint := (gram_quadForm n x).1
  have hQ : ∫ y in (Kr * √a)..(Kr * √b), glow n x y ≤ star x ⬝ᵥ (((G n).map (aeval zeta5)) *ᵥ x) := by
    rw [(gram_quadForm n x).2, intervalIntegral.integral_of_le hle]
    have hsub0 : Ioc (Kr * √a) (Kr * √b) ⊆ Ioi 0 := fun y hy => lt_trans hpos hy.1
    calc ∫ y in Ioc (Kr * √a) (Kr * √b), glow n x y
        ≤ ∫ y in Ioc (Kr * √a) (Kr * √b), (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y := by
          refine setIntegral_mono_on ?_ (hint.mono_set hsub0) measurableSet_Ioc
            (fun y hy => glow_le x (lt_trans hpos hy.1))
          exact (continuous_glow n x).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      _ ≤ ∫ y in Ioi 0, (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y := by
          refine setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall hsub0)
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
          exact mul_nonneg (sq_nonneg _) (ν_pos n hy).le
  refine le_trans ?_ hQ
  rw [hsub]
  have hmono : ∫ t in a..b, AK n * ((2 * Real.pi) ^ 4 * a ^ 3 / (24 * (1 + b))) *
        Real.exp (-(Kr * W)) * (Pfun n x t) ^ 2 ≤
      ∫ t in a..b, glow n x (Kr * √t) * (Kr * (1 / (2 * √t))) := by
    refine intervalIntegral.integral_mono_on hab.le ?_ ?_ ?_
    · exact (continuous_const.mul ((Pfun_continuous n x).pow 2)).intervalIntegrable _ _
    · refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.mul ((continuous_glow n x).comp
        (continuous_const.mul Real.continuous_sqrt)).continuousOn ?_
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
          (continuousOn_const.mul Real.continuous_sqrt.continuousOn) fun t ht => ?_)
      rw [Set.uIcc_of_le hab.le] at ht
      have := Real.sqrt_pos.mpr (lt_of_lt_of_le ha ht.1)
      positivity
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      refine le_trans ?_ (glow_pointwise n hn x ht0)
      have hAK : 0 ≤ AK n := by unfold AK; positivity
      have hc : (2 * Real.pi) ^ 4 * a ^ 3 / (24 * (1 + b)) ≤
          (2 * Real.pi) ^ 4 * t ^ 3 / (24 * (1 + t)) := by
        have h1 : a ^ 3 / (1 + b) ≤ t ^ 3 / (1 + t) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          have : a ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ ha.le ht.1 3
          have : t ^ 3 * (1 + b) ≥ a ^ 3 * (1 + t) := by
            nlinarith [pow_pos ht0 3, pow_pos ha 3, ht.2, ht.1]
          linarith
        have h2 : (2 * Real.pi) ^ 4 * a ^ 3 / (24 * (1 + b)) =
            (2 * Real.pi) ^ 4 / 24 * (a ^ 3 / (1 + b)) := by field_simp
        have h3 : (2 * Real.pi) ^ 4 * t ^ 3 / (24 * (1 + t)) =
            (2 * Real.pi) ^ 4 / 24 * (t ^ 3 / (1 + t)) := by field_simp
        rw [h2, h3]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hexp : Real.exp (-(Kr * W)) ≤ Real.exp (-(Kr * Vf t)) :=
        Real.exp_le_exp.mpr (by nlinarith [hW t ht])
      have hP2 : 0 ≤ (Pfun n x t) ^ 2 := sq_nonneg _
      have hcexp : 0 ≤ Real.exp (-(Kr * W)) := (Real.exp_pos _).le
      gcongr
  refine le_trans ?_ hmono
  rw [intervalIntegral.integral_const_mul]

end CatalanCore.Zeta5.Rho
