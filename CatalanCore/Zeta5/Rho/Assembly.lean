module

public import CatalanCore.Zeta5.Rho.Gram
public import CatalanCore.Zeta5.Rho.NodeBound
public import CatalanCore.Zeta5.Rho.Legendre
public import CatalanCore.Zeta5.Rho.Concave

@[expose] public section

/-!
# The joint norm estimate (ledger ZR05, ZR09)

For `0 < a < b`, `W ≥ sup_{[a,b]} V`, `Pb ≥ sup_{α<u≤1} Φ_{a,b}`, and every `x`:

  `|xᵀ M_K x| ≤ h³ / ((b - a) c_{a,b}) · exp(K (W + Pb)) · xᵀ G_K(ζ(5)) x`,

with `K = 40 n`, `h = 37 n`, `c_{a,b} = (2π)⁴ a³ / (24 (1 + b))`.  This is `‖T_K‖ ≤ …` for
`T_K = G^{-1/2} M_K G^{-1/2}` in Rayleigh form (`G` is positive definite).  Then the
polynomial prefactor is absorbed by any strict exponent gap (ZR09).
-/

namespace CatalanCore.Zeta5.Rho

open Apery MeasureTheory Set Finset Real Polynomial Matrix

/-- **ZR05.** -/
theorem norm_bound (n : ℕ) (hn : 0 < n) (x : Fin (37 * n) → ℝ) {a b W Pb : ℝ} (ha : 0 < a)
    (hab : a < b) (hW : ∀ t ∈ Icc a b, Vf t ≤ W)
    (hP : ∀ u : ℝ, 3 / 40 < u → u ≤ 1 → Phi a b u ≤ Pb) :
    |x ⬝ᵥ (M0 n *ᵥ x)| ≤
      (((37 * n : ℝ) ^ 3 / ((b - a) * ((2 * Real.pi) ^ 4 * a ^ 3 / (24 * (1 + b))))) *
        Real.exp ((40 * n : ℝ) * (W + Pb))) *
        (star x ⬝ᵥ (((G n).map (aeval zeta5)) *ᵥ x)) := by
  have hba : 0 < b - a := by linarith
  have hb : 0 < b := by linarith
  have hKr : (0 : ℝ) < 40 * n := by positivity
  have hhr : (0 : ℝ) < 37 * n := by positivity
  set I : ℝ := ∫ t in a..b, (Pfun n x t) ^ 2 with hI
  have hI0 : 0 ≤ I := by
    rw [hI]
    exact intervalIntegral.integral_nonneg hab.le (fun t _ => sq_nonneg _)
  set c : ℝ := (2 * Real.pi) ^ 4 * a ^ 3 / (24 * (1 + b)) with hc
  have hc0 : 0 < c := by positivity
  have hAK : 0 < AK n := by unfold AK; positivity
  have hG := gram_lower n hn x ha hab hW
  -- residue side
  have hres := residue_identity n hn x
  have hterm : ∀ j ∈ Finset.Ioc (3 * n) (40 * n),
      |rj n j * (Pfun n x (-(uu n j) ^ 2)) ^ 2| ≤
        (37 * n : ℝ) ^ 2 / (b - a) * Real.exp ((40 * n : ℝ) * Pb) * I := by
    intro j hj
    have hj' := Finset.mem_Ioc.mp hj
    have hr := rj_abs_le n hn hj
    have hpoly : (Pfun n x (-(uu n j) ^ 2)) ^ 2 ≤
        (37 * n : ℝ) ^ 2 * Real.exp (2 * (37 * n : ℕ) *
          Real.arcosh ((2 * (uu n j) ^ 2 + a + b) / (b - a))) / (b - a) * I := by
      have := node_bound (h := 37 * n) (P := Ppoly n x) (natDegree_Ppoly_lt n hn x) (a := a) (b := b)
        (uu n j) hab ha.le
      rw [eval_Ppoly] at this
      simpa [hI, eval_Ppoly] using this
    have hu1 : 3 / 40 < uu n j := by
      unfold uu
      rw [lt_div_iff₀ hKr]
      have : (3 * n : ℝ) < j := by exact_mod_cast hj'.1
      linarith
    have hu2 : uu n j ≤ 1 := by
      unfold uu
      rw [div_le_one hKr]
      have : (j : ℝ) ≤ 40 * n := by exact_mod_cast hj'.2
      linarith
    have hPhi := hP _ hu1 hu2
    unfold Phi at hPhi
    have hexp : Real.exp ((40 * n : ℝ) * Lg (3 / 40) (uu n j)) *
        Real.exp (2 * ((37 * n : ℕ) : ℝ) * Real.arcosh ((2 * (uu n j) ^ 2 + a + b) / (b - a))) ≤
        Real.exp ((40 * n : ℝ) * Pb) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e : Yf a b (uu n j) = (2 * (uu n j) ^ 2 + a + b) / (b - a) := rfl
      rw [e] at hPhi
      push_cast
      nlinarith [hPhi]
    have hrj0 : |rj n j| ≤ Real.exp ((40 * n : ℝ) * Lg (3 / 40) ((j : ℝ) / (40 * n : ℝ))) := hr
    have huu : (uu n j) = (j : ℝ) / (40 * n : ℝ) := rfl
    rw [← huu] at hrj0
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Pfun n x (-(uu n j) ^ 2)))]
    calc |rj n j| * (Pfun n x (-(uu n j) ^ 2)) ^ 2
        ≤ Real.exp ((40 * n : ℝ) * Lg (3 / 40) (uu n j)) *
          ((37 * n : ℝ) ^ 2 * Real.exp (2 * (37 * n : ℕ) *
            Real.arcosh ((2 * (uu n j) ^ 2 + a + b) / (b - a))) / (b - a) * I) :=
          mul_le_mul hrj0 hpoly (sq_nonneg _) (Real.exp_pos _).le
      _ = ((Real.exp ((40 * n : ℝ) * Lg (3 / 40) (uu n j)) *
            Real.exp (2 * ((37 * n : ℕ) : ℝ) * Real.arcosh ((2 * (uu n j) ^ 2 + a + b) / (b - a))))) *
            ((37 * n : ℝ) ^ 2 / (b - a) * I) := by push_cast; ring
      _ ≤ Real.exp ((40 * n : ℝ) * Pb) * ((37 * n : ℝ) ^ 2 / (b - a) * I) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = _ := by ring
  have hsum : |∑ j ∈ Finset.Ioc (3 * n) (40 * n), rj n j * (Pfun n x (-(uu n j) ^ 2)) ^ 2| ≤
      (37 * n : ℝ) * ((37 * n : ℝ) ^ 2 / (b - a) * Real.exp ((40 * n : ℝ) * Pb) * I) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have : 40 * n - 3 * n = 37 * n := by omega
    rw [this]; push_cast; exact le_refl _
  rw [hres, abs_mul, abs_of_pos hAK]
  have hAKI : AK n * c * Real.exp (-((40 * n : ℝ) * W)) * I ≤
      star x ⬝ᵥ (((G n).map (aeval zeta5)) *ᵥ x) := hG
  have hexpW : 0 < Real.exp ((40 * n : ℝ) * W) := Real.exp_pos _
  have hAKI' : AK n * I ≤ star x ⬝ᵥ (((G n).map (aeval zeta5)) *ᵥ x) *
      Real.exp ((40 * n : ℝ) * W) / c := by
    rw [le_div_iff₀ hc0]
    have hEE : Real.exp (-((40 * n : ℝ) * W)) * Real.exp ((40 * n : ℝ) * W) = 1 := by
      rw [← Real.exp_add]; simp
    have : AK n * I * c = (AK n * c * Real.exp (-((40 * n : ℝ) * W)) * I) *
        Real.exp ((40 * n : ℝ) * W) := by
      calc AK n * I * c = AK n * c * I * (Real.exp (-((40 * n : ℝ) * W)) *
            Real.exp ((40 * n : ℝ) * W)) := by rw [hEE]; ring
        _ = _ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hAKI hexpW.le
  calc AK n * |∑ j ∈ Finset.Ioc (3 * n) (40 * n), rj n j * (Pfun n x (-(uu n j) ^ 2)) ^ 2|
      ≤ AK n * ((37 * n : ℝ) * ((37 * n : ℝ) ^ 2 / (b - a) * Real.exp ((40 * n : ℝ) * Pb) * I)) :=
        mul_le_mul_of_nonneg_left hsum hAK.le
    _ = ((37 * n : ℝ) ^ 3 / (b - a) * Real.exp ((40 * n : ℝ) * Pb)) * (AK n * I) := by ring
    _ ≤ ((37 * n : ℝ) ^ 3 / (b - a) * Real.exp ((40 * n : ℝ) * Pb)) *
        (star x ⬝ᵥ (((G n).map (aeval zeta5)) *ᵥ x) * Real.exp ((40 * n : ℝ) * W) / c) :=
        mul_le_mul_of_nonneg_left hAKI' (by positivity)
    _ = _ := by
      rw [mul_add, Real.exp_add]
      field_simp


theorem gram_nonneg (n : ℕ) (hn : 0 < n) (x : Fin (37 * n) → ℝ) :
    0 ≤ star x ⬝ᵥ (((G n).map (aeval zeta5)) *ᵥ x) := by
  rw [(gram_quadForm n x).2]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun y hy => ?_
  exact mul_nonneg (sq_nonneg _) (ν_pos n hy).le

/-- **ZR09.**  A polynomial prefactor is `e^{o(K)}`: `A n³ ≤ exp(40 n δ)` for large `n`. -/
theorem poly_le_exp (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n → A * (n : ℝ) ^ 3 ≤ Real.exp (40 * n * δ) := by
  obtain ⟨n0, hn0⟩ := exists_nat_gt (24 * |A| / (40 * δ) ^ 4)
  refine ⟨n0 + 1, Nat.succ_pos _, fun n hn => ?_⟩
  have hnr : (n0 : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n := by linarith [(Nat.cast_nonneg n0 : (0 : ℝ) ≤ n0)]
  have h1 : (40 * n * δ) ^ 4 / 24 ≤ Real.exp (40 * n * δ) := by
    have := Real.pow_div_factorial_le_exp (40 * n * δ) (by positivity) 4
    simpa [Nat.factorial] using this
  have h2 : A * (n : ℝ) ^ 3 ≤ (40 * n * δ) ^ 4 / 24 := by
    have hpos : 0 < (40 * δ) ^ 4 := by positivity
    have hn' : 24 * |A| / (40 * δ) ^ 4 < n := by linarith
    rw [div_lt_iff₀ hpos] at hn'
    have : (40 * n * δ) ^ 4 / 24 = (40 * δ) ^ 4 * n * (n : ℝ) ^ 3 / 24 := by ring
    rw [this]
    have h3 : A * (n : ℝ) ^ 3 ≤ |A| * (n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
    have h4 : |A| * (n : ℝ) ^ 3 ≤ (40 * δ) ^ 4 * n * (n : ℝ) ^ 3 / 24 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 24)]
      have : 24 * |A| ≤ (40 * δ) ^ 4 * n := by linarith [hn']
      nlinarith [pow_pos hn1 3]
    linarith
  linarith

/-- **ZR10 (abstract form).**  If `W + Pb < ρ`, then for all large `n` and every `x`:
`|xᵀ M_K x| ≤ exp(ρ K) xᵀ G_K(ζ(5)) x`, `K = 40 n`. -/
theorem norm_eventually {a b W Pb ρ : ℝ} (ha : 0 < a) (hab : a < b)
    (hW : ∀ t ∈ Icc a b, Vf t ≤ W) (hP : ∀ u : ℝ, 3 / 40 < u → u ≤ 1 → Phi a b u ≤ Pb)
    (hρ : W + Pb < ρ) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n → ∀ x : Fin (37 * n) → ℝ,
      |x ⬝ᵥ (M0 n *ᵥ x)| ≤ Real.exp (ρ * (40 * n : ℝ)) *
        (star x ⬝ᵥ (((G n).map (aeval zeta5)) *ᵥ x)) := by
  have hba : 0 < b - a := by linarith
  have hb : 0 < b := by linarith
  set c : ℝ := (2 * Real.pi) ^ 4 * a ^ 3 / (24 * (1 + b)) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨n0, hn0, hn⟩ := poly_le_exp (37 ^ 3 / ((b - a) * c)) (sub_pos.mpr hρ)
  refine ⟨n0, hn0, fun n hnn x => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le hn0 hnn
  have hnb := norm_bound n hn1 x ha hab hW hP
  have hG0 := gram_nonneg n hn1 x
  refine le_trans hnb ?_
  refine mul_le_mul_of_nonneg_right ?_ hG0
  have h1 := hn n hnn
  have e1 : (37 * n : ℝ) ^ 3 / ((b - a) * c) = 37 ^ 3 / ((b - a) * c) * (n : ℝ) ^ 3 := by ring
  rw [e1]
  calc 37 ^ 3 / ((b - a) * c) * (n : ℝ) ^ 3 * Real.exp ((40 * n : ℝ) * (W + Pb))
      ≤ Real.exp (40 * n * (ρ - (W + Pb))) * Real.exp ((40 * n : ℝ) * (W + Pb)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end CatalanCore.Zeta5.Rho
