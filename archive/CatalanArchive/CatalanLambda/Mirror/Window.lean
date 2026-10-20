module

public import CatalanLambda.Mirror.Integ
public import CatalanLambda.Decay.ThmNAsymp

@[expose] public section

/-!
# Mirror constant: Theorem N, the window corollary, and `E(h) = o(h²)`
-/

open Finset MeasureTheory Filter Topology

namespace CatalanLambda.Mirror

open CatalanLambda.Decay
open CatalanLambda.Decay.R (Aco Aco_pos betaE betaE_pos)

/-- The explicit error term `E(h) = R(h) + h log(2 r0 h + c_ε + 1)`; it is `O(h log h)`. -/
noncomputable def EerrB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) (h : ℕ) : ℝ :=
  RerrB h (∑ i, max ((F.mprime : ℝ) - F.segG i) 0) ρ (max (Real.log Aco) 0)
    + h * Real.log (2 * F.r0 * h + 2 * (Aco ^ ε / betaE ε) + 1)

/-- **Theorem N_ρ.**  For `h ≥ 5/(8W)`, every injective node family `s : Fin k → Fin h`
(a principal submatrix of `T` of size `k = h - j`):
`|det T[S]| ≤ exp(-h² D_cert + h j c_cert + E(h))`. -/
theorem theoremNB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h k : ℕ} (hh : 0 < h) (hW : 11 / (8 * (F.W : ℝ)) ≤ h)
    (hN1 : 1 ≤ ⌊(F.r0 : ℝ) * h⌋₊) (s : Fin k → Fin h) (hs : Function.Injective s) :
    |(Matrix.of fun i j : Fin k => TbarEnt (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ))).det|
      ≤ Real.exp (-(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert + EerrB F h) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hkh : k ≤ h := by simpa using Fintype.card_le_of_injective s hs
  have hkh' : (k : ℝ) ≤ h := by exact_mod_cast hkh
  set M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => TbarEnt (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) with hM
  have hcast : (Matrix.of fun i j : Fin k => ((16 * TbarEnt (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) : ℝ) : ℂ))
      = Complex.ofRealHom.mapMatrix ((16 : ℝ) • M) := by
    ext i j; simp [hM]
  have hdet : ‖(Matrix.of fun i j : Fin k => ((16 * TbarEnt (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) : ℝ) : ℂ)).det‖
      = 16 ^ k * |M.det| := by
    rw [hcast, ← RingHom.map_det, Matrix.det_smul]
    simp [Complex.norm_real, abs_mul]
  have hb := det16_boundB F hh hW s hs hN1
  rw [hdet] at hb
  set N0 := ⌊(F.r0 : ℝ) * h⌋₊ with hN0
  set cE : ℝ := 2 * (Aco ^ ε / betaE ε) with hcE
  have hcE0 : 0 ≤ cE := by
    have := Aco_pos
    have := betaE_pos F.hε0
    positivity
  have hN1 : (N0 : ℝ) ≤ F.r0 * h := Nat.floor_le (by
    have : (0 : ℝ) ≤ F.r0 := by exact_mod_cast F.r0_pos.le
    positivity)
  set M0 : ℝ := 2 * F.r0 * h + cE + 1 with hM0
  have hM01 : 1 ≤ M0 := by
    have : (0 : ℝ) ≤ F.r0 := by exact_mod_cast F.r0_pos.le
    have : 0 ≤ 2 * (F.r0 : ℝ) * h := by positivity
    linarith
  have hbase : 2 * (N0 : ℝ) + 2 * (Aco ^ ε / betaE ε) ≤ M0 := by
    rw [hM0]; nlinarith [hN1]
  have hbase0 : 0 ≤ 2 * (N0 : ℝ) + 2 * (Aco ^ ε / betaE ε) := by
    have := Aco_pos
    have := betaE_pos F.hε0
    positivity
  have hpow : (2 * (N0 : ℝ) + 2 * (Aco ^ ε / betaE ε)) ^ k ≤ M0 ^ h :=
    (pow_le_pow_left₀ hbase0 hbase k).trans (pow_le_pow_right₀ hM01 hkh)
  have hMh : M0 ^ h = Real.exp (h * Real.log M0) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith)]; simp
  have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have h16 : (1 : ℝ) ≤ 16 ^ k := one_le_pow₀ (by norm_num)
  have hE0 := Real.exp_pos (TexpB F h k)
  have step : 16 ^ k * |M.det| ≤ Real.exp (TexpB F h k) * M0 ^ h := by
    refine hb.trans ?_
    calc (1 / (k.factorial : ℝ)) * (Real.exp (TexpB F h k)
          * (2 * (N0 : ℝ) + 2 * (Aco ^ ε / betaE ε)) ^ k)
        ≤ 1 * (Real.exp (TexpB F h k) * (2 * (N0 : ℝ) + 2 * (Aco ^ ε / betaE ε)) ^ k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by linarith)]; exact hfac
      _ ≤ Real.exp (TexpB F h k) * M0 ^ h := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hE0.le
  have : |M.det| ≤ Real.exp (TexpB F h k) * M0 ^ h := by
    have h1 : |M.det| ≤ 16 ^ k * |M.det| := by
      nlinarith [abs_nonneg M.det]
    exact h1.trans step
  refine this.trans (le_of_eq ?_)
  rw [hMh, ← Real.exp_add]
  congr 1
  unfold TexpB EerrB
  ring


/-- The real `h × h` matrix `T` (entries `TbarEnt a b`). -/
noncomputable def TmatB (h : ℕ) : Matrix (Fin h) (Fin h) ℝ := Matrix.of fun a b => TbarEnt a b

/-- Theorem N_ρ for a principal submatrix indexed by a finset of `Fin h`. -/
theorem minor_boundB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h : ℕ} (hh : 0 < h) (hW : 11 / (8 * (F.W : ℝ)) ≤ h)
    (hN1 : 1 ≤ ⌊(F.r0 : ℝ) * h⌋₊) (k : ℕ) (s : Finset (Fin h)) (hs : s.card = k) :
    |((TmatB h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
      ≤ Real.exp (-(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert + EerrB F h) := by
  let e := s.orderIsoOfFin hs
  let sf : Fin k → Fin h := fun i => (e i).1
  have hsf : Function.Injective sf := fun a b hab => e.injective (Subtype.ext hab)
  have hdet : ((TmatB h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det
      = (Matrix.of fun i j : Fin k => TbarEnt (((sf i : Fin h) : ℕ)) (((sf j : Fin h) : ℕ))).det := by
    rw [← Matrix.det_submatrix_equiv_self e.toEquiv]
    congr 1
  rw [hdet]
  exact theoremNB F hh hW hN1 sf hsf

/-- **Window corollary.**  For `h ≥ 5/(8W)` and `|t| ≤ e^{-c_cert h}`,
`|det(T + t I)| ≤ exp(-h² D_cert + E(h) + h log 2)`. -/
theorem windowB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h : ℕ} (hh : 0 < h) (hW : 11 / (8 * (F.W : ℝ)) ≤ h)
    (hN1 : 1 ≤ ⌊(F.r0 : ℝ) * h⌋₊) {t : ℝ} (ht : |t| ≤ Real.exp (-(F.ccert : ℝ) * h)) :
    |(TmatB h + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det|
      ≤ Real.exp (-(h : ℝ) ^ 2 * F.Dcert + EerrB F h + h * Real.log 2) := by
  rw [CatalanLambda.Decay.det_add_scalar_expansion]
  set B : ℝ := Real.exp (-(h : ℝ) ^ 2 * F.Dcert + EerrB F h) with hB
  have hB0 : 0 < B := Real.exp_pos _
  have hterm : ∀ k ∈ range (h + 1), |t ^ (h - k) *
      ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
        ((TmatB h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
      ≤ B * (h.choose k) := by
    intro k hk
    have hk' : k ≤ h := by have := Finset.mem_range.1 hk; omega
    have hts : |t| * Real.exp (F.ccert * h) ≤ 1 := by
      calc |t| * Real.exp (F.ccert * h) ≤ Real.exp (-(F.ccert : ℝ) * h) * Real.exp (F.ccert * h) :=
            mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [abs_mul, abs_pow]
    calc |t| ^ (h - k) * |∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
            ((TmatB h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
        ≤ |t| ^ (h - k) * ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
            Real.exp (-(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert + EerrB F h) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun s hs => ?_))
          exact minor_boundB F hh hW hN1 k s (Finset.mem_powersetCard.1 hs).2
      _ = (|t| * Real.exp (F.ccert * h)) ^ (h - k) * B * (h.choose k) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          have : Real.exp (-(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert + EerrB F h)
              = Real.exp (F.ccert * h) ^ (h - k) * B := by
            rw [hB, ← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            have : ((h - k : ℕ) : ℝ) = (h : ℝ) - k := by rw [Nat.cast_sub hk']
            rw [this]; ring
          rw [this, mul_pow]; ring
      _ ≤ B * (h.choose k) := by
          have h1 : (|t| * Real.exp (F.ccert * h)) ^ (h - k) ≤ 1 :=
            pow_le_one₀ (by positivity) hts
          have : (0 : ℝ) ≤ (h.choose k) := Nat.cast_nonneg _
          nlinarith [mul_nonneg hB0.le this]
  calc |∑ k ∈ range (h + 1), t ^ (h - k) *
        ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
          ((TmatB h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
      ≤ ∑ k ∈ range (h + 1), |t ^ (h - k) *
        ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
          ((TmatB h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (h + 1), B * (h.choose k) := Finset.sum_le_sum hterm
    _ = B * 2 ^ h := by
        rw [← Finset.mul_sum]
        congr 1
        exact_mod_cast Nat.sum_range_choose h
    _ = _ := by
        rw [hB, show (2 : ℝ) ^ h = Real.exp (h * Real.log 2) by
          rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]; simp, ← Real.exp_add]


/-- `E(h) ≤ K h + 5 h log h`, and `E(h) ≥ 0`, for `h ≥ 1`. -/
theorem EerrB_bound {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) :
    ∃ C : ℝ, ∀ h : ℕ, 1 ≤ h → 0 ≤ EerrB F h ∧ EerrB F h ≤ h * C + 5 * h * Real.log h := by
  have hA := Aco_pos
  have hb := betaE_pos F.hε0
  set cE : ℝ := 2 * (Aco ^ ε / betaE ε) with hcE
  have hcE0 : 0 ≤ cE := by positivity
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  set Γ : ℝ := ∑ i, max ((F.mprime : ℝ) - F.segG i) 0 with hΓ
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  set Cl : ℝ := max (Real.log Aco) 0 with hCl
  have hCl0 : 0 ≤ Cl := le_max_right _ _
  refine ⟨4 * Γ + |Real.log ρ| + 3 + Cl
      + 2 * Real.log (4 + 1) + Real.log (2 * F.r0 + cE + 1) + 1 / 2, ?_⟩
  intro h hh
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg h1
  have e1 : Real.log (1 + 4 * (h : ℝ)) ≤ Real.log (4 + 1) + Real.log h := by
    have := log_lin_le 4 1 (by norm_num) le_rfl hh
    have e : (1 + 4 * (h : ℝ)) = 4 * h + 1 := by ring
    rw [e]; exact this
  have e2 : Real.log (2 * F.r0 * h + cE + 1) ≤ Real.log (2 * F.r0 + cE + 1) + Real.log h := by
    have := log_lin_le (2 * F.r0) (cE + 1) (by positivity) (by linarith) hh
    have e : 2 * (F.r0 : ℝ) * h + cE + 1 = 2 * F.r0 * h + (cE + 1) := by ring
    rw [e]
    have e' : 2 * (F.r0 : ℝ) + (cE + 1) = 2 * F.r0 + cE + 1 := by ring
    rw [e'] at this; exact this
  have h83 : (0 : ℝ) ≤ 4 * h := by positivity
  have hl1 : 0 ≤ Real.log (1 + 4 * (h : ℝ)) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (2 * F.r0 * h + cE + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ 2 * F.r0 * h := by positivity
    linarith)
  have hl8 : 0 ≤ Real.log (4 + 1 : ℝ) := Real.log_nonneg (by norm_num)
  have hl9 : 0 ≤ Real.log (2 * (F.r0 : ℝ) + cE + 1) := Real.log_nonneg (by linarith)
  unfold EerrB RerrB
  rw [← hΓ, ← hCl, ← hcE]
  constructor
  · have : 0 ≤ (h : ℝ) * Real.log (2 * F.r0 * h + cE + 1) := by positivity
    have : 0 ≤ 4 * (h : ℝ) * Γ := by positivity
    have : 0 ≤ (h : ℝ) * |Real.log ρ| := by positivity
    have : 0 ≤ 2 * (h : ℝ) * Real.log h := by positivity
    have : 0 ≤ 2 * (h : ℝ) * Real.log (1 + 4 * h) := by positivity
    have : 0 ≤ (h : ℝ) * Cl := by positivity
    nlinarith
  · have t1 : 2 * (h : ℝ) * Real.log (1 + 4 * h) ≤ 2 * h * (Real.log (4 + 1) + Real.log h) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have t2 : (h : ℝ) * Real.log (2 * F.r0 * h + cE + 1)
        ≤ h * (Real.log (2 * F.r0 + cE + 1) + Real.log h) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    generalize Real.log (4 + 1) = L5 at *
    have h2 : (1 : ℝ) / 2 ≤ h * (1 / 2) := by linarith
    nlinarith

theorem EerrB_div_tendsto {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) :
    Tendsto (fun h : ℕ => EerrB F h / (h : ℝ) ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := EerrB_bound F
  have hup : Tendsto (fun h : ℕ => C / (h : ℝ) + 5 * (Real.log h / h)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun h : ℕ => C / (h : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using h1.add (CatalanLambda.Decay.tendsto_log_div_nat.const_mul 5)
  refine squeeze_zero' ?_ ?_ hup
  · filter_upwards [eventually_ge_atTop 1] with h hh
    exact div_nonneg (hC h hh).1 (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have h1 : (0 : ℝ) < h := by exact_mod_cast hh
    rw [div_le_iff₀ (by positivity)]
    have := (hC h hh).2
    have e : (C / (h : ℝ) + 5 * (Real.log h / h)) * (h : ℝ) ^ 2
        = h * C + 5 * h * Real.log h := by field_simp
    rw [e]; exact this

/-- **Liminf form of the window corollary.**  For every `δ > 0` there is `h₀` such that for all
`h ≥ h₀` and all `|t| ≤ e^{-c_cert h}`: `|det(T̄_h + t I)| ≤ exp(-(D_cert - δ) h²)`. -/
theorem window_liminfB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∀ t : ℝ, |t| ≤ Real.exp (-(F.ccert : ℝ) * h) →
      |(TmatB h + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det|
        ≤ Real.exp (-((F.Dcert : ℝ) - δ) * (h : ℝ) ^ 2) := by
  have h1 := EerrB_div_tendsto F
  have h2 : Tendsto (fun h : ℕ => Real.log 2 / (h : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h3 := h1.add h2
  rw [add_zero] at h3
  have hev := (tendsto_order.1 h3).2 δ hδ
  have hW : ∀ᶠ h : ℕ in atTop, 11 / (8 * (F.W : ℝ)) ≤ h :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  have hN : ∀ᶠ h : ℕ in atTop, 1 ≤ ⌊(F.r0 : ℝ) * h⌋₊ := by
    have : ∀ᶠ h : ℕ in atTop, 1 / (F.r0 : ℝ) ≤ h :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [this] with h hh
    apply Nat.le_floor
    rw [div_le_iff₀ hr0] at hh
    push_cast
    linarith
  obtain ⟨h₀, hh₀⟩ := eventually_atTop.1 (hev.and (hW.and ((eventually_ge_atTop 1).and hN)))
  refine ⟨h₀, fun h hh t ht => ?_⟩
  obtain ⟨hs, hW', hh1, hN1⟩ := hh₀ h hh
  have hpos : 0 < h := hh1
  have hh' : (0 : ℝ) < h := by exact_mod_cast hpos
  refine (windowB F hpos hW' hN1 ht).trans (Real.exp_le_exp.2 ?_)
  have : EerrB F h / (h : ℝ) ^ 2 + Real.log 2 / h < δ := hs
  have h4 : EerrB F h + h * Real.log 2 < δ * (h : ℝ) ^ 2 := by
    have := mul_lt_mul_of_pos_right this (show (0 : ℝ) < (h : ℝ) ^ 2 by positivity)
    have e : (EerrB F h / (h : ℝ) ^ 2 + Real.log 2 / h) * (h : ℝ) ^ 2
        = EerrB F h + h * Real.log 2 := by field_simp
    rw [e] at this; exact this
  nlinarith

/-- `T̄_h - t I = -((λ' + t) I + N₀)` as real matrices. -/
theorem TmatB_sub_eq (h : ℕ) (t : ℝ) :
    TmatB h + (-t) • (1 : Matrix (Fin h) (Fin h) ℝ)
      = -((lamB + t) • (1 : Matrix (Fin h) (Fin h) ℝ) + (N0 h).map (Rat.cast : ℚ → ℝ)) := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp [TmatB, TbarEnt, N0]; ring
  · have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
    simp [TmatB, TbarEnt, N0, hab, hab']

/-- The window corollary for `P̄_h(λ' + t)`. -/
theorem window_liminf_PB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∀ t : ℝ, |t| ≤ Real.exp (-(F.ccert : ℝ) * h) →
      |((lamB + t) • (1 : Matrix (Fin h) (Fin h) ℝ)
          + (N0 h).map (Rat.cast : ℚ → ℝ)).det|
        ≤ Real.exp (-((F.Dcert : ℝ) - δ) * (h : ℝ) ^ 2) := by
  obtain ⟨h₀, H⟩ := window_liminfB F hδ
  refine ⟨h₀, fun h hh t ht => ?_⟩
  have := H h hh (-t) (by rwa [abs_neg])
  rw [TmatB_sub_eq, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at this
  exact this

end CatalanLambda.Mirror
