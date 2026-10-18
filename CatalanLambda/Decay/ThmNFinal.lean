import CatalanLambda.Decay.ThmNInteg

/-!
# Theorem N_ρ (node-removal bound for every principal minor of `T`)
-/

open Finset MeasureTheory CatalanLambda.Decay

namespace CatalanLambda.Decay

/-- The explicit error term `E(h) = R(h) + h log(2 r0 h + c_ε + 1)`; it is `O(h log h)`. -/
noncomputable def Eerr {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) (h : ℕ) : ℝ :=
  Rerr h (∑ i, max ((F.mprime : ℝ) - F.segG i) 0) ρ (max (Real.log R.Aco) 0)
    + h * Real.log (2 * F.r0 * h + 2 * (R.Aco ^ ε / R.betaE ε) + 1)

/-- **Theorem N_ρ.**  For `h ≥ 5/(8W)`, every injective node family `s : Fin k → Fin h`
(a principal submatrix of `T` of size `k = h - j`):
`|det T[S]| ≤ exp(-h² D_cert + h j c_cert + E(h))`. -/
theorem theoremN {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h k : ℕ} (hh : 0 < h) (hW : 5 / (8 * (F.W : ℝ)) ≤ h)
    (s : Fin k → Fin h) (hs : Function.Injective s) :
    |(Matrix.of fun i j : Fin k => Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ))).det|
      ≤ Real.exp (-(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert + Eerr F h) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hkh : k ≤ h := by simpa using Fintype.card_le_of_injective s hs
  have hkh' : (k : ℝ) ≤ h := by exact_mod_cast hkh
  set M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) with hM
  have hcast : (Matrix.of fun i j : Fin k => ((16 * Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) : ℝ) : ℂ))
      = Complex.ofRealHom.mapMatrix ((16 : ℝ) • M) := by
    ext i j; simp [hM]
  have hdet : ‖(Matrix.of fun i j : Fin k => ((16 * Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) : ℝ) : ℂ)).det‖
      = 16 ^ k * |M.det| := by
    rw [hcast, ← RingHom.map_det, Matrix.det_smul]
    simp [Complex.norm_real, abs_mul]
  have hb := R.det16_bound F hh hW s hs
  rw [hdet] at hb
  set N0 := ⌊(F.r0 : ℝ) * h⌋₊ with hN0
  set cE : ℝ := 2 * (R.Aco ^ ε / R.betaE ε) with hcE
  have hcE0 : 0 ≤ cE := by
    have := R.Aco_pos
    have := R.betaE_pos F.hε0
    positivity
  have hN1 : (N0 : ℝ) ≤ F.r0 * h := Nat.floor_le (by
    have : (0 : ℝ) ≤ F.r0 := by exact_mod_cast F.r0_pos.le
    positivity)
  set M0 : ℝ := 2 * F.r0 * h + cE + 1 with hM0
  have hM01 : 1 ≤ M0 := by
    have : (0 : ℝ) ≤ F.r0 := by exact_mod_cast F.r0_pos.le
    have : 0 ≤ 2 * (F.r0 : ℝ) * h := by positivity
    linarith
  have hbase : 2 * (N0 : ℝ) + 2 * (R.Aco ^ ε / R.betaE ε) ≤ M0 := by
    rw [hM0]; nlinarith [hN1]
  have hbase0 : 0 ≤ 2 * (N0 : ℝ) + 2 * (R.Aco ^ ε / R.betaE ε) := by
    have := R.Aco_pos
    have := R.betaE_pos F.hε0
    positivity
  have hpow : (2 * (N0 : ℝ) + 2 * (R.Aco ^ ε / R.betaE ε)) ^ k ≤ M0 ^ h :=
    (pow_le_pow_left₀ hbase0 hbase k).trans (pow_le_pow_right₀ hM01 hkh)
  have hMh : M0 ^ h = Real.exp (h * Real.log M0) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith)]; simp
  have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have h16 : (1 : ℝ) ≤ 16 ^ k := one_le_pow₀ (by norm_num)
  have hE0 := Real.exp_pos (R.Texp F h k)
  have step : 16 ^ k * |M.det| ≤ Real.exp (R.Texp F h k) * M0 ^ h := by
    refine hb.trans ?_
    calc (1 / (k.factorial : ℝ)) * (Real.exp (R.Texp F h k)
          * (2 * (N0 : ℝ) + 2 * (R.Aco ^ ε / R.betaE ε)) ^ k)
        ≤ 1 * (Real.exp (R.Texp F h k) * (2 * (N0 : ℝ) + 2 * (R.Aco ^ ε / R.betaE ε)) ^ k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by linarith)]; exact hfac
      _ ≤ Real.exp (R.Texp F h k) * M0 ^ h := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hE0.le
  have : |M.det| ≤ Real.exp (R.Texp F h k) * M0 ^ h := by
    have h1 : |M.det| ≤ 16 ^ k * |M.det| := by
      nlinarith [abs_nonneg M.det]
    exact h1.trans step
  refine this.trans (le_of_eq ?_)
  rw [hMh, ← Real.exp_add]
  congr 1
  unfold R.Texp Eerr
  ring

end CatalanLambda.Decay
