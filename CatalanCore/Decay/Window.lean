module

public import CatalanCore.Decay.Integ
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# The window corollary for a general frame (WP2b)

From `theoremN` (node-removal bound for every principal minor of `T`) to
`|det (T_h + t I)| ≤ exp (-(D - δ) h²)` for `|t| ≤ e^{-c h}` and `h` large (`window_liminf`).
Generalises legacy `ThmNWindow` and `ThmNAsymp`.
-/

open Finset Filter Topology

namespace CatalanCore


lemma tendsto_log_div_nat : Tendsto (fun h : ℕ => Real.log h / h) atTop (𝓝 0) := by
  have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simp only [pow_one, one_mul, add_zero] at this
  exact this.comp tendsto_natCast_atTop_atTop

lemma log_lin_le (A B : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B) {h : ℕ} (hh : 1 ≤ h) :
    Real.log (A * h + B) ≤ Real.log (A + B) + Real.log h := by
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have : A * h + B ≤ (A + B) * h := by nlinarith
  calc Real.log (A * h + B) ≤ Real.log ((A + B) * h) :=
        Real.log_le_log (by nlinarith) this
    _ = _ := Real.log_mul (by linarith) (by linarith)

namespace Frame

open Decay

variable {Fr : Frame}

/-- `det(T + t I) = ∑_S t^{h-|S|} det T[S]`. -/
theorem det_add_scalar_expansion {h : ℕ} (T : Matrix (Fin h) (Fin h) ℝ) (t : ℝ) :
    (T + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det
      = ∑ k ∈ range (h + 1), t ^ (h - k) *
          ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
            (T.submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det := by
  have h1 : (T + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det = (-T).charpoly.eval t := by
    rw [Matrix.eval_charpoly]
    congr 1
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    simp [sub_neg_eq_add, add_comm]
  rw [h1, Polynomial.eval_eq_sum_range]
  have hnd : (-T).charpoly.natDegree = h := by
    simpa using (-T).charpoly_natDegree_eq_dim
  rw [hnd, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ h := by have := Finset.mem_range.1 hk; omega
  have e : h + 1 - 1 - k = h - k := by omega
  rw [e]
  have hc := Matrix.charpoly_coeff_eq_sum_minors (-T) k (by rw [Fintype.card_fin]; omega)
  rw [Fintype.card_fin] at hc
  have hsum : (-1 : ℝ) ^ k * ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
        ((-T).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det
      = ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
        (T.submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hcard : s.card = k := (Finset.mem_powersetCard.1 hs).2
    have hn : (-T).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)
        = -(T.submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)) := by
      ext i j; simp
    rw [hn, Matrix.det_neg, Fintype.card_coe, hcard, ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul]
    simp
  rw [hc, hsum]; ring

/-- The real `h × h` matrix `T` (entries `Tent a b`). -/
noncomputable def Tmat (Fr : Frame) (h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  Matrix.of fun a b => Fr.Tent a b

/-- The goodness conditions on `h` for `theoremN`: `n0off ≤ ⌊r0 h⌋` and `hW`. -/
def Good {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (Fr : Frame) (F : Cert.CertCore K ρ ε c m) (h : ℕ) : Prop :=
  Fr.n0off ≤ ⌊(F.r0 : ℝ) * h⌋₊ ∧ (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * h

theorem eventually_good {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (Fr : Frame) (F : Cert.CertCore K ρ ε c m) : ∀ᶠ h : ℕ in atTop, Good Fr F h := by
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  have hW0 : (0 : ℝ) < F.W := by exact_mod_cast F.W_pos
  have h1 : ∀ᶠ h : ℕ in atTop, (Fr.n0off : ℝ) + 1 + Fr.xs ≤ F.W * h := by
    have : Tendsto (fun h : ℕ => (F.W : ℝ) * h) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hW0
    exact this.eventually_ge_atTop _
  have h2 : ∀ᶠ h : ℕ in atTop, (Fr.n0off : ℝ) ≤ F.r0 * h := by
    have : Tendsto (fun h : ℕ => (F.r0 : ℝ) * h) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hr0
    exact this.eventually_ge_atTop _
  filter_upwards [h1, h2] with h hh1 hh2
  exact ⟨Nat.le_floor hh2, hh1⟩

/-- Theorem N for a principal submatrix indexed by a finset of `Fin h`. -/
theorem minor_bound {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hFr : Fr.DecayOKs' 3) (F : Cert.CertCore K ρ ε c m) {D : ℝ}
    (hD : D ≤ 2 * ((F.mprime : ℝ) + Fr.d * F.Sbase) - F.Ibound + 3 / 2)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {h : ℕ} (hh : 0 < h) (hg : Good Fr F h)
    (k : ℕ) (s : Finset (Fin h)) (hs : s.card = k) :
    |((Tmat Fr h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
      ≤ Real.exp (-(h : ℝ) ^ 2 * D + h * ((h : ℝ) - k) * F.ccert + Eerr Fr F m0 h) := by
  let e := s.orderIsoOfFin hs
  let sf : Fin k → Fin h := fun i => (e i).1
  have hsf : Function.Injective sf := fun a b hab => e.injective (Subtype.ext hab)
  have hdet : ((Tmat Fr h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det
      = (Matrix.of fun i j : Fin k => Fr.Tent (((sf i : Fin h) : ℕ)) (((sf j : Fin h) : ℕ))).det := by
    rw [← Matrix.det_submatrix_equiv_self e.toEquiv]
    congr 1
  rw [hdet]
  exact theoremN hFr F hD hm0 hm0xs hm0μ hh (N0 := ⌊(F.r0 : ℝ) * h⌋₊ - Fr.n0off)
    (by have := hg.1; omega) hg.2 sf hsf

/-- **Window corollary.**  For `h` good and `|t| ≤ e^{-c_cert h}`,
`|det(T + t I)| ≤ exp(-h² D + E(h) + h log 2)`. -/
theorem window {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hFr : Fr.DecayOKs' 3) (F : Cert.CertCore K ρ ε c m) {D : ℝ}
    (hD : D ≤ 2 * ((F.mprime : ℝ) + Fr.d * F.Sbase) - F.Ibound + 3 / 2)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {h : ℕ} (hh : 0 < h) (hg : Good Fr F h)
    {t : ℝ} (ht : |t| ≤ Real.exp (-(F.ccert : ℝ) * h)) :
    |(Tmat Fr h + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det|
      ≤ Real.exp (-(h : ℝ) ^ 2 * D + Eerr Fr F m0 h + h * Real.log 2) := by
  rw [det_add_scalar_expansion]
  set B : ℝ := Real.exp (-(h : ℝ) ^ 2 * D + Eerr Fr F m0 h) with hB
  have hB0 : 0 < B := Real.exp_pos _
  have hterm : ∀ k ∈ range (h + 1), |t ^ (h - k) *
      ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
        ((Tmat Fr h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
      ≤ B * (h.choose k) := by
    intro k hk
    have hk' : k ≤ h := by have := Finset.mem_range.1 hk; omega
    have hts : |t| * Real.exp (F.ccert * h) ≤ 1 := by
      calc |t| * Real.exp (F.ccert * h) ≤ Real.exp (-(F.ccert : ℝ) * h) * Real.exp (F.ccert * h) :=
            mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [abs_mul, abs_pow]
    calc |t| ^ (h - k) * |∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
            ((Tmat Fr h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
        ≤ |t| ^ (h - k) * ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
            Real.exp (-(h : ℝ) ^ 2 * D + h * ((h : ℝ) - k) * F.ccert + Eerr Fr F m0 h) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun s hs => ?_))
          exact minor_bound hFr F hD hm0 hm0xs hm0μ hh hg k s (Finset.mem_powersetCard.1 hs).2
      _ = (|t| * Real.exp (F.ccert * h)) ^ (h - k) * B * (h.choose k) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          have : Real.exp (-(h : ℝ) ^ 2 * D + h * ((h : ℝ) - k) * F.ccert + Eerr Fr F m0 h)
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
          ((Tmat Fr h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det|
      ≤ ∑ k ∈ range (h + 1), |t ^ (h - k) *
        ∑ s ∈ (univ : Finset (Fin h)).powersetCard k,
          ((Tmat Fr h).submatrix (Subtype.val : s → Fin h) (Subtype.val : s → Fin h)).det| :=
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
theorem Eerr_bound {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hC : Fr.ContourOK) (F : Cert.CertCore K ρ ε c m) {m0 : ℝ} (hm0 : 0 < m0) :
    ∃ C : ℝ, ∀ h : ℕ, 1 ≤ h → 0 ≤ Eerr Fr F m0 h ∧ Eerr Fr F m0 h ≤ h * C + 5 * h * Real.log h := by
  have hA := Aco_pos hC
  have hb := betaE_pos (show (0:ℝ) < 3 by norm_num) F.hε0
  set cE : ℝ := 2 * (Fr.Aco ^ ε / betaE 3 ε) with hcE
  have hcE0 : 0 ≤ cE := by positivity
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  have hW0 := Fr.Wabs_nonneg
  set Γ : ℝ := Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0 with hΓ
  have hΓ0 : 0 ≤ Γ := by
    have : 0 ≤ ∑ i, max ((F.mprime : ℝ) - F.segG i) 0 := Finset.sum_nonneg (fun i _ => le_max_right _ _)
    positivity
  set Cl : ℝ := max (Real.log Fr.Aco) 0 with hCl
  have hCl0 : 0 ≤ Cl := le_max_right _ _
  set B2 : ℝ := Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + cE + 1 with hB2
  have hB21 : 1 ≤ B2 := by
    have : (0 : ℝ) ≤ Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by positivity
    linarith
  refine ⟨2 * Γ + |Real.log ρ| + 3 + Cl
      + 2 * Real.log (1 / m0 + 1) + Real.log (Fr.Wabs * F.r0 + B2) + 1 / 2, ?_⟩
  intro h hh
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg h1
  have e1 : Real.log (1 + (h : ℝ) / m0) ≤ Real.log (1 / m0 + 1) + Real.log h := by
    have := log_lin_le (1 / m0) 1 (by positivity) le_rfl hh
    have e : (1 + (h : ℝ) / m0) = 1 / m0 * h + 1 := by ring
    rw [e]; exact this
  have e2 : Real.log (Fr.Wabs * F.r0 * h + B2) ≤ Real.log (Fr.Wabs * F.r0 + B2) + Real.log h := by
    exact log_lin_le (Fr.Wabs * F.r0) B2 (by positivity) hB21 hh
  have hl1 : 0 ≤ Real.log (1 + (h : ℝ) / m0) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ h / m0 := by positivity
    linarith)
  have hl2 : 0 ≤ Real.log (Fr.Wabs * F.r0 * h + B2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ Fr.Wabs * F.r0 * h := by positivity
    linarith)
  have hl8 : 0 ≤ Real.log (1 / m0 + 1 : ℝ) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ 1 / m0 := by positivity
    linarith)
  have hl9 : 0 ≤ Real.log (Fr.Wabs * F.r0 + B2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ Fr.Wabs * F.r0 := by positivity
    linarith)
  have hE : Eerr Fr F m0 h = 2 * h * Γ + h * |Real.log ρ| + 2 * h * Real.log h + 3 * h + 1 / 2
      + 2 * h * Real.log (1 + (h : ℝ) / m0) + h * Cl
      + h * Real.log (Fr.Wabs * F.r0 * h + B2) := by
    unfold Eerr Rerr
    rw [← hΓ, ← hCl]
  rw [hE]
  constructor
  · have : 0 ≤ (h : ℝ) * Real.log (Fr.Wabs * F.r0 * h + B2) := by positivity
    have : 0 ≤ 2 * (h : ℝ) * Γ := by positivity
    have : 0 ≤ (h : ℝ) * |Real.log ρ| := by positivity
    have : 0 ≤ 2 * (h : ℝ) * Real.log h := by positivity
    have : 0 ≤ 2 * (h : ℝ) * Real.log (1 + (h : ℝ) / m0) := by positivity
    have : 0 ≤ (h : ℝ) * Cl := by positivity
    nlinarith
  · have t1 : 2 * (h : ℝ) * Real.log (1 + (h : ℝ) / m0)
        ≤ 2 * h * (Real.log (1 / m0 + 1) + Real.log h) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have t2 : (h : ℝ) * Real.log (Fr.Wabs * F.r0 * h + B2)
        ≤ h * (Real.log (Fr.Wabs * F.r0 + B2) + Real.log h) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith

theorem Eerr_div_tendsto {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hC : Fr.ContourOK) (F : Cert.CertCore K ρ ε c m) {m0 : ℝ} (hm0 : 0 < m0) :
    Tendsto (fun h : ℕ => Eerr Fr F m0 h / (h : ℝ) ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hCb⟩ := Eerr_bound hC F hm0
  have hup : Tendsto (fun h : ℕ => C / (h : ℝ) + 5 * (Real.log h / h)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun h : ℕ => C / (h : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using h1.add (tendsto_log_div_nat.const_mul 5)
  refine squeeze_zero' ?_ ?_ hup
  · filter_upwards [eventually_ge_atTop 1] with h hh
    exact div_nonneg (hCb h hh).1 (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have h1 : (0 : ℝ) < h := by exact_mod_cast hh
    rw [div_le_iff₀ (by positivity)]
    have := (hCb h hh).2
    have e : (C / (h : ℝ) + 5 * (Real.log h / h)) * (h : ℝ) ^ 2
        = h * C + 5 * h * Real.log h := by field_simp
    rw [e]; exact this

/-- **Liminf form of the window corollary.**  For every `δ > 0` there is `h₀` such that for all
`h ≥ h₀` and all `|t| ≤ e^{-c_cert h}`: `|det(T_h + t I)| ≤ exp(-(D - δ) h²)`. -/
theorem window_liminf {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hFr : Fr.DecayOKs' 3) (F : Cert.CertCore K ρ ε c m) {D : ℝ}
    (hD : D ≤ 2 * ((F.mprime : ℝ) + Fr.d * F.Sbase) - F.Ibound + 3 / 2)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∀ t : ℝ, |t| ≤ Real.exp (-(F.ccert : ℝ) * h) →
      |(Tmat Fr h + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det|
        ≤ Real.exp (-(D - δ) * (h : ℝ) ^ 2) := by
  have h1 := Eerr_div_tendsto hFr.contour F hm0
  have h2 : Tendsto (fun h : ℕ => Real.log 2 / (h : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h3 := h1.add h2
  rw [add_zero] at h3
  have hev := (tendsto_order.1 h3).2 δ hδ
  obtain ⟨h₀, hh₀⟩ := eventually_atTop.1 (hev.and ((eventually_good Fr F).and (eventually_ge_atTop 1)))
  refine ⟨h₀, fun h hh t ht => ?_⟩
  obtain ⟨hs, hg, hh1⟩ := hh₀ h hh
  have hpos : 0 < h := hh1
  have hh' : (0 : ℝ) < h := by exact_mod_cast hpos
  refine (window hFr F hD hm0 hm0xs hm0μ hpos hg ht).trans (Real.exp_le_exp.2 ?_)
  have : Eerr Fr F m0 h / (h : ℝ) ^ 2 + Real.log 2 / h < δ := hs
  have h4 : Eerr Fr F m0 h + h * Real.log 2 < δ * (h : ℝ) ^ 2 := by
    have := mul_lt_mul_of_pos_right this (show (0 : ℝ) < (h : ℝ) ^ 2 by positivity)
    have e : (Eerr Fr F m0 h / (h : ℝ) ^ 2 + Real.log 2 / h) * (h : ℝ) ^ 2
        = Eerr Fr F m0 h + h * Real.log 2 := by field_simp
    rw [e] at this; exact this
  nlinarith

end Frame
end CatalanCore
