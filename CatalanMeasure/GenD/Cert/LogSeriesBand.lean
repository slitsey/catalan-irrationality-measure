module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import OAI.NumberTheory.Catalan.Energy.BarrierChebyshevLogFormula
public import CatalanMeasure.GenD.Signed.ChebSquare
public import CatalanMeasure.GenD.Cert.ResW
public import CatalanMeasure.GenD.Cert.WLog

@[expose] public section

/-!
# Log-series bands for the residual field (G32c)

On a band `x = m + h y`, `y ∈ [-1,1]`, the residual field `-ρ log(1+x²) - 2 Σ a_i T_{i+1}(x) +
Re Σ_t r_t Log(1 - 2 x z_t + z_t²)` is bounded by a Chebyshev polynomial in `y` plus an explicit error.
Each logarithm term is affine in `y`; `Log (A - B y)` is compared with `Log (1 - 2 y w + w²)` for a rational
pole parameter `w` (drift bound `‖2wA - B(1+w²)‖ / (m₁ m₂)`, mean value theorem), and the latter is the
Chebyshev series `-2 Σ w^k T_k(y)/k` truncated with a closed geometric tail.  `band_field_le` is the
decidable-checker form (`bandCheck`); the polynomial is recomputed exactly (series coefficients, composition
of the degree-160 trial polynomial with `x = m + h y`) and compared with the dyadic data.
-/

namespace CatalanMeasure.GenD.Cert.LogSeriesBand
open Complex Set Polynomial OAI.InternalCatalan

theorem quad_mem_slitPlane {w : ℂ} (hw : ‖w‖ < 1) {y : ℝ} (hy : |y| ≤ 1) :
    (1 - 2 * (y : ℂ) * w + w ^ 2) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have hn : w.re ^ 2 + w.im ^ 2 < 1 := by
    have h1 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
    rw [Complex.sq_norm, Complex.normSq_apply] at h1
    nlinarith
  have hre : (1 - 2 * (y : ℂ) * w + w ^ 2).re = 1 - 2 * y * w.re + w.re ^ 2 - w.im ^ 2 := by
    simp [pow_two]; ring
  have him : (1 - 2 * (y : ℂ) * w + w ^ 2).im = 2 * w.im * (w.re - y) := by
    simp [pow_two]; ring
  rw [hre, him]
  by_cases h : 2 * w.im * (w.re - y) = 0
  · left
    rcases mul_eq_zero.mp h with h | h
    · have hi : w.im = 0 := by linarith
      rw [hi]
      have hr : |w.re| < 1 := by
        rw [← sq_lt_one_iff_abs_lt_one]; nlinarith
      have hxy : y * w.re ≤ |w.re| := by
        calc y * w.re ≤ |y * w.re| := le_abs_self _
          _ = |y| * |w.re| := abs_mul _ _
          _ ≤ 1 * |w.re| := by gcongr
          _ = |w.re| := one_mul _
      have : |w.re| ^ 2 = w.re ^ 2 := sq_abs _
      nlinarith [abs_nonneg w.re]
    · have : w.re = y := by linarith
      rw [this] at hn ⊢
      nlinarith
  · right; exact h

theorem div_aux (B B' a a' N : ℂ) (n1 : a ≠ 0) (n2 : a' ≠ 0) (h : -B * a' + B' * a = N) :
    -B / a - -B' / a' = N / (a * a') := by
  rw [← h]; field_simp; ring

/-- the drift of `Log (A - B y) - Log (A' - B' y)` along `[-1,1]` is controlled by the constant
`B' A - B A'` and the two moduli. -/
theorem log_affine_drift (A B A' B' : ℂ) (m m' : ℝ) (hm : 0 < m) (hm' : 0 < m')
    (ha : ∀ y : ℝ, |y| ≤ 1 → A - B * (y : ℂ) ∈ slitPlane)
    (ha' : ∀ y : ℝ, |y| ≤ 1 → A' - B' * (y : ℂ) ∈ slitPlane)
    (hma : ∀ y : ℝ, |y| ≤ 1 → m ≤ ‖A - B * (y : ℂ)‖)
    (hma' : ∀ y : ℝ, |y| ≤ 1 → m' ≤ ‖A' - B' * (y : ℂ)‖)
    {y : ℝ} (hy : |y| ≤ 1) :
    ‖(Complex.log (A - B * (y : ℂ)) - Complex.log (A' - B' * (y : ℂ))) -
        (Complex.log A - Complex.log A')‖ ≤ ‖B' * A - B * A'‖ / (m * m') * |y| := by
  set f : ℝ → ℂ := fun t => Complex.log (A - B * (t : ℂ)) - Complex.log (A' - B' * (t : ℂ)) with hf
  set f' : ℝ → ℂ := fun t => (B' * A - B * A') / ((A - B * (t : ℂ)) * (A' - B' * (t : ℂ))) with hf'
  have hid : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := fun t => by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hderiv : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f (f' t) (Icc (-1 : ℝ) 1) t := by
    intro t ht
    have htabs : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have h1 : HasDerivAt (fun s : ℝ => A - B * (s : ℂ)) (-B) t := by
      simpa using ((hid t).const_mul B).const_sub A
    have h2 : HasDerivAt (fun s : ℝ => A' - B' * (s : ℂ)) (-B') t := by
      simpa using ((hid t).const_mul B').const_sub A'
    have l1 := h1.clog_real (ha t htabs)
    have l2 := h2.clog_real (ha' t htabs)
    have := (l1.sub l2).hasDerivWithinAt (s := Icc (-1 : ℝ) 1)
    refine this.congr_deriv ?_
    have n1 : A - B * (t : ℂ) ≠ 0 := slitPlane_ne_zero (ha t htabs)
    have n2 : A' - B' * (t : ℂ) ≠ 0 := slitPlane_ne_zero (ha' t htabs)
    simp only [hf']
    exact div_aux B B' _ _ _ n1 n2 (by ring)
  have hbound : ∀ t ∈ Icc (-1 : ℝ) 1, ‖f' t‖ ≤ ‖B' * A - B * A'‖ / (m * m') := by
    intro t ht
    have htabs : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    simp only [hf', norm_div, norm_mul]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hm hm')
    exact mul_le_mul (hma t htabs) (hma' t htabs) hm'.le (norm_nonneg _)
  have key := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (x := 0) (y := y) (by simp) (abs_le.mp hy |> fun h => ⟨h.1, h.2⟩)
  simpa [hf] using key


/-- the Chebyshev difference term `w^(k+1) (T_{k+1}(y) - T_{k+1}(0)) / (k+1)` -/
noncomputable def dTerm (w : ℂ) (y : ℝ) (k : ℕ) : ℂ :=
  w ^ (k + 1) * (((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y - (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval 0 : ℝ) : ℂ)
    / ((k + 1 : ℕ) : ℂ)

theorem norm_dTerm_le {w : ℂ} {r : ℝ} (hw : ‖w‖ ≤ r) {y : ℝ} (hy : |y| ≤ 1) (k : ℕ) :
    ‖dTerm w y k‖ ≤ 2 * r ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  unfold dTerm
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have h1 := Chebyshev.abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) hy
  have h2 := Chebyshev.abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) (x := 0) (by simp)
  have h3 : |(Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y - (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval 0| ≤ 2 := by
    have := abs_sub ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y) ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval 0)
    linarith
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have : ‖((k + 1 : ℕ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ) := Complex.norm_natCast _
  rw [this]
  have hp : ‖w‖ ^ (k + 1) ≤ r ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) hw _
  rw [div_le_div_iff_of_pos_right hk]
  calc ‖w‖ ^ (k + 1) * |(Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y - (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval 0|
      ≤ r ^ (k + 1) * 2 := mul_le_mul hp h3 (abs_nonneg _) (le_trans (norm_nonneg _) hw |> fun h => pow_nonneg h _)
    _ = 2 * r ^ (k + 1) := by ring

theorem log_series_trunc {w : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hw : ‖w‖ ≤ r) {y : ℝ} (hy : |y| ≤ 1)
    (K : ℕ) :
    ‖(Complex.log (1 - 2 * (y : ℂ) * w + w ^ 2) - Complex.log (1 - 2 * (((0 : ℝ)) : ℂ) * w + w ^ 2)) +
        2 * ∑ k ∈ Finset.range K, dTerm w y k‖ ≤ 4 * r ^ (K + 1) / ((K + 1 : ℕ) * (1 - r)) := by
  have hwn : ‖w‖ < 1 := lt_of_le_of_lt hw hr
  have h0 : |(0 : ℝ)| ≤ 1 := by simp
  have hy1 := barrier_hasSum_chebyshev_log hy hwn
  have hy0 := barrier_hasSum_chebyshev_log h0 hwn
  have hd : HasSum (dTerm w y) (-(1 / 2 : ℂ) * (Complex.log (1 - 2 * (y : ℂ) * w + w ^ 2) -
      Complex.log (1 - 2 * (((0 : ℝ)) : ℂ) * w + w ^ 2))) := by
    have := hy1.sub hy0
    convert this using 1
    · funext k
      simp only [dTerm, Pi.sub_apply]
      push_cast
      ring
    · ring
  have hsum := hd.summable
  have hsplit := hsum.sum_add_tsum_nat_add K
  rw [hd.tsum_eq] at hsplit
  have hgeo : HasSum (fun i : ℕ => 2 * r ^ (K + 1) / ((K + 1 : ℕ) : ℝ) * r ^ i)
      (2 * r ^ (K + 1) / ((K + 1 : ℕ) : ℝ) * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr).mul_left _
  have hK : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have htail : ‖∑' i : ℕ, dTerm w y (i + K)‖ ≤ 2 * r ^ (K + 1) / ((K + 1 : ℕ) : ℝ) * (1 - r)⁻¹ := by
    refine tsum_of_norm_bounded hgeo (fun i => ?_)
    refine (norm_dTerm_le hw hy (i + K)).trans ?_
    have hpos : (0 : ℝ) < ((i + K + 1 : ℕ) : ℝ) := by positivity
    have hle : ((K + 1 : ℕ) : ℝ) ≤ ((i + K + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : K + 1 ≤ i + K + 1)
    have : r ^ (i + K + 1) = r ^ (K + 1) * r ^ i := by rw [← pow_add]; congr 1; omega
    rw [show i + K + 1 = (i + K) + 1 from rfl]
    have e : 2 * r ^ (i + K + 1) / ((i + K + 1 : ℕ) : ℝ) ≤ 2 * r ^ (K + 1) / ((K + 1 : ℕ) : ℝ) * r ^ i := by
      rw [this, show 2 * (r ^ (K + 1) * r ^ i) = (2 * r ^ (K + 1) * r ^ i) by ring]
      have h2 : 0 ≤ 2 * r ^ (K + 1) * r ^ i := by positivity
      calc 2 * r ^ (K + 1) * r ^ i / ((i + K + 1 : ℕ) : ℝ) ≤ 2 * r ^ (K + 1) * r ^ i / ((K + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_left h2 hK hle
        _ = _ := by ring
    exact e
  have heq : (Complex.log (1 - 2 * (y : ℂ) * w + w ^ 2) - Complex.log (1 - 2 * (((0 : ℝ)) : ℂ) * w + w ^ 2)) +
      2 * ∑ k ∈ Finset.range K, dTerm w y k = -2 * ∑' i : ℕ, dTerm w y (i + K) := by
    have : ∑ k ∈ Finset.range K, dTerm w y k + ∑' i : ℕ, dTerm w y (i + K) =
        -(1 / 2 : ℂ) * (Complex.log (1 - 2 * (y : ℂ) * w + w ^ 2) -
          Complex.log (1 - 2 * (((0 : ℝ)) : ℂ) * w + w ^ 2)) := hsplit
    linear_combination (2 : ℂ) * this
  rw [heq, norm_mul]
  have h2 : ‖(-2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have hr1 : (0 : ℝ) < 1 - r := by linarith
  calc 2 * ‖∑' i : ℕ, dTerm w y (i + K)‖ ≤ 2 * (2 * r ^ (K + 1) / ((K + 1 : ℕ) : ℝ) * (1 - r)⁻¹) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 4 * r ^ (K + 1) / ((K + 1 : ℕ) * (1 - r)) := by field_simp; ring



/-- **One logarithmic term on a band.**  `Re (c (Log (A - B y) - Log A))` is bounded by its Chebyshev
series (in the pole parameter `w`) plus an explicit error. -/
theorem term_le (c A B w : ℂ) (r m1 m2 dbar : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) (hw : ‖w‖ ≤ r)
    (hm1 : 0 < m1) (hm2 : 0 < m2)
    (ha : ∀ y : ℝ, |y| ≤ 1 → A - B * (y : ℂ) ∈ slitPlane)
    (hma : ∀ y : ℝ, |y| ≤ 1 → m1 ≤ ‖A - B * (y : ℂ)‖)
    (hmu : ∀ y : ℝ, |y| ≤ 1 → m2 ≤ ‖(1 + w ^ 2) - (2 * w) * (y : ℂ)‖)
    (hd : ‖2 * w * A - B * (1 + w ^ 2)‖ ≤ dbar) (K : ℕ) {y : ℝ} (hy : |y| ≤ 1) :
    (c * (Complex.log (A - B * (y : ℂ)) - Complex.log A)).re ≤
      -2 * (c * ∑ k ∈ Finset.range K, dTerm w y k).re +
        ‖c‖ * (dbar / (m1 * m2) + 4 * r ^ (K + 1) / ((K + 1 : ℕ) * (1 - r))) := by
  have hwn : ‖w‖ < 1 := lt_of_le_of_lt hw hr
  have hu : ∀ y : ℝ, (1 + w ^ 2) - (2 * w) * (y : ℂ) = 1 - 2 * (y : ℂ) * w + w ^ 2 := fun y => by ring
  have hslu : ∀ y : ℝ, |y| ≤ 1 → (1 + w ^ 2) - (2 * w) * (y : ℂ) ∈ slitPlane := fun y hy => by
    rw [hu]; exact quad_mem_slitPlane hwn hy
  have hdr := log_affine_drift A B (1 + w ^ 2) (2 * w) m1 m2 hm1 hm2 ha hslu hma hmu hy
  have hser := log_series_trunc hr0 hr hw hy K
  have h0 : (1 - 2 * (((0 : ℝ)) : ℂ) * w + w ^ 2) = 1 + w ^ 2 := by simp
  rw [h0] at hser
  rw [← hu y] at hser
  set Ea := Complex.log (A - B * (y : ℂ)) - Complex.log A with hEa
  set Eu := Complex.log ((1 + w ^ 2) - (2 * w) * (y : ℂ)) - Complex.log (1 + w ^ 2) with hEu
  set S := ∑ k ∈ Finset.range K, dTerm w y k with hS
  set E1 := Ea - Eu with hE1
  set R := Eu + 2 * S with hR
  have hE1n : ‖E1‖ ≤ dbar / (m1 * m2) := by
    have h1 : ‖E1‖ ≤ ‖(1 + w ^ 2) * 0 + (2 * w) * A - B * (1 + w ^ 2)‖ / (m1 * m2) * |y| := by
      have : E1 = (Complex.log (A - B * (y : ℂ)) - Complex.log ((1 + w ^ 2) - (2 * w) * (y : ℂ))) -
          (Complex.log A - Complex.log (1 + w ^ 2)) := by simp only [hE1, hEa, hEu]; ring
      rw [this]
      simpa [mul_comm] using hdr
    have h2 : ‖2 * w * A - B * (1 + w ^ 2)‖ / (m1 * m2) * |y| ≤ dbar / (m1 * m2) := by
      have hmm : 0 < m1 * m2 := mul_pos hm1 hm2
      calc ‖2 * w * A - B * (1 + w ^ 2)‖ / (m1 * m2) * |y| ≤ ‖2 * w * A - B * (1 + w ^ 2)‖ / (m1 * m2) * 1 :=
            mul_le_mul_of_nonneg_left hy (by positivity)
        _ ≤ dbar / (m1 * m2) := by rw [mul_one]; exact div_le_div_of_nonneg_right hd hmm.le
    refine h1.trans ?_
    convert h2 using 2
    simp [mul_comm]
  have hRn : ‖R‖ ≤ 4 * r ^ (K + 1) / ((K + 1 : ℕ) * (1 - r)) := hser
  have hsplit : Ea = -2 * S + (R + E1) := by simp only [hR, hE1]; ring
  rw [hsplit, mul_add, Complex.add_re]
  have hc : (c * (-2 * S)).re = -2 * (c * S).re := by
    have : c * (-2 * S) = -2 * (c * S) := by ring
    rw [this]; simp
  rw [hc]
  have hb : (c * (R + E1)).re ≤ ‖c‖ * (dbar / (m1 * m2) + 4 * r ^ (K + 1) / ((K + 1 : ℕ) * (1 - r))) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _)
  linarith


/-! ### Rational Gaussian arithmetic and the decidable per-term check -/

abbrev QC := ℚ × ℚ

def QC.toC (p : QC) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ)⟩

def cmul (a b : QC) : QC := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
def cadd (a b : QC) : QC := (a.1 + b.1, a.2 + b.2)
def csub (a b : QC) : QC := (a.1 - b.1, a.2 - b.2)
def cns (a : QC) : ℚ := a.1 * a.1 + a.2 * a.2

theorem toC_mul (a b : QC) : (cmul a b).toC = a.toC * b.toC := by
  apply Complex.ext <;> simp [QC.toC, cmul] <;> ring
theorem toC_add (a b : QC) : (cadd a b).toC = a.toC + b.toC := by
  apply Complex.ext <;> simp [QC.toC, cadd]
theorem toC_sub (a b : QC) : (csub a b).toC = a.toC - b.toC := by
  apply Complex.ext <;> simp [QC.toC, csub]
theorem toC_one : QC.toC ((1 : ℚ), (0 : ℚ)) = 1 := by
  apply Complex.ext <;> simp [QC.toC]
theorem toC_two : QC.toC ((2 : ℚ), (0 : ℚ)) = 2 := by
  apply Complex.ext <;> simp [QC.toC]
theorem sq_norm_toC (a : QC) : ‖a.toC‖ ^ 2 = ((cns a : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [QC.toC, cns]

/-- `∀ y ∈ [-1,1], M ≤ α - 2 β y + γ y²`, decidably. -/
def quadGe (α β γ M : ℚ) : Bool :=
  decide (0 ≤ γ) && (decide (γ ≤ β ∧ M ≤ α - 2 * β + γ) || decide (β ≤ -γ ∧ M ≤ α + 2 * β + γ) ||
    decide (-γ < β ∧ β < γ ∧ β ^ 2 + γ * M ≤ γ * α))

theorem quadGe_sound {α β γ M : ℚ} (h : quadGe α β γ M = true) {y : ℝ} (hy : |y| ≤ 1) :
    (M : ℝ) ≤ α - 2 * β * y + γ * y ^ 2 := by
  simp only [quadGe, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hg, h⟩ := h
  have hg' : (0 : ℝ) ≤ γ := by exact_mod_cast hg
  obtain ⟨h1, h2⟩ := abs_le.mp hy
  rcases h with (⟨hb, hM⟩ | ⟨hb, hM⟩) | ⟨hb1, hb2, hM⟩
  · have hb' : (γ : ℝ) ≤ β := by exact_mod_cast hb
    have hM' : (M : ℝ) ≤ α - 2 * β + γ := by exact_mod_cast hM
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr hb'), mul_nonneg (sub_nonneg.mpr h2) hg',
      mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h2), mul_nonneg hg' (sub_nonneg.mpr h2)]
  · have hb' : (β : ℝ) ≤ -γ := by exact_mod_cast hb
    have hM' : (M : ℝ) ≤ α + 2 * β + γ := by exact_mod_cast hM
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (by linarith : (β : ℝ) ≤ -γ)),
      mul_nonneg (sub_nonneg.mpr h1) hg']
  · have hb1' : (-γ : ℝ) < β := by exact_mod_cast hb1
    have hb2' : (β : ℝ) < γ := by exact_mod_cast hb2
    have hM' : (β : ℝ) ^ 2 + γ * M ≤ γ * α := by exact_mod_cast hM
    have hgp : (0 : ℝ) < γ := by linarith
    have : (γ : ℝ) * M ≤ γ * (α - 2 * β * y + γ * y ^ 2) := by
      nlinarith [sq_nonneg ((γ : ℝ) * y - β)]
    exact le_of_mul_le_mul_left this hgp

/-- per-term data: pole parameter `w` (rational Gaussian), its radius bound `r`, the two modulus lower bounds
and the drift bound -/
structure BT where
  w : QC
  r : ℚ
  m1 : ℚ
  m2 : ℚ
  dbar : ℚ

def u0 (w : QC) : QC := cadd (1, 0) (cmul w w)
def u1 (w : QC) : QC := cmul (2, 0) w
def ncomb (w A B : QC) : QC := csub (cmul (u1 w) A) (cmul B (u0 w))

def termOK (A B : QC) (b : BT) : Bool :=
  decide (0 ≤ b.r ∧ b.r < 1 ∧ cns b.w ≤ b.r ^ 2) && decide (0 < b.m1 ∧ 0 < b.m2 ∧ 0 ≤ b.dbar) &&
  decide (cns (ncomb b.w A B) ≤ b.dbar ^ 2) &&
  quadGe (cns A) (A.1 * B.1 + A.2 * B.2) (cns B) (b.m1 ^ 2) &&
  quadGe (cns (u0 b.w)) ((u0 b.w).1 * (u1 b.w).1 + (u0 b.w).2 * (u1 b.w).2) (cns (u1 b.w)) (b.m2 ^ 2)

def trunc (r : ℚ) (K : ℕ) : ℚ := 4 * r ^ (K + 1) / ((K + 1 : ℕ) * (1 - r))

def termErr (c : QC) (b : BT) (K : ℕ) : ℚ :=
  (|c.1| + |c.2|) * (b.dbar / (b.m1 * b.m2) + trunc b.r K)

theorem norm_ge_of_quad {A B : QC} {M : ℚ} (hM : 0 ≤ M) (h : quadGe (cns A) (A.1 * B.1 + A.2 * B.2) (cns B) (M ^ 2) = true)
    {y : ℝ} (hy : |y| ≤ 1) : (M : ℝ) ≤ ‖A.toC - B.toC * (y : ℂ)‖ := by
  have hq := quadGe_sound h hy
  have hn : ‖A.toC - B.toC * (y : ℂ)‖ ^ 2 = (cns A : ℝ) - 2 * ((A.1 * B.1 + A.2 * B.2 : ℚ) : ℝ) * y + (cns B : ℝ) * y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [QC.toC, cns]; ring
  have hM' : (0 : ℝ) ≤ M := by exact_mod_cast hM
  push_cast at hq hn
  by_contra hlt
  have hlt' := not_le.mp hlt
  have := pow_lt_pow_left₀ hlt' (norm_nonneg _) (two_ne_zero)
  linarith

theorem term_le' (c A B : QC) (b : BT) (K : ℕ) (hok : termOK A B b = true)
    (ha : ∀ y : ℝ, |y| ≤ 1 → A.toC - B.toC * (y : ℂ) ∈ slitPlane) {y : ℝ} (hy : |y| ≤ 1) :
    (c.toC * (Complex.log (A.toC - B.toC * (y : ℂ)) - Complex.log A.toC)).re ≤
      -2 * (c.toC * ∑ k ∈ Finset.range K, dTerm b.w.toC y k).re + (termErr c b K : ℝ) := by
  simp only [termOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hr0, hr1, hrw⟩, hm1, hm2, hd0⟩, hdd⟩, hq1⟩, hq2⟩ := hok
  have hr0' : (0 : ℝ) ≤ b.r := by exact_mod_cast hr0
  have hr1' : (b.r : ℝ) < 1 := by exact_mod_cast hr1
  have hw : ‖b.w.toC‖ ≤ b.r := by
    have : ‖b.w.toC‖ ^ 2 ≤ (b.r : ℝ) ^ 2 := by
      rw [sq_norm_toC]; exact_mod_cast hrw
    exact abs_le_of_sq_le_sq' this hr0' |>.2
  have hm1' : (0 : ℝ) < b.m1 := by exact_mod_cast hm1
  have hm2' : (0 : ℝ) < b.m2 := by exact_mod_cast hm2
  have hd : ‖2 * b.w.toC * A.toC - B.toC * (1 + b.w.toC ^ 2)‖ ≤ b.dbar := by
    have hN : (ncomb b.w A B).toC = 2 * b.w.toC * A.toC - B.toC * (1 + b.w.toC ^ 2) := by
      simp only [ncomb, u1, u0, toC_sub, toC_mul, toC_add, toC_one, toC_two]; ring
    rw [← hN]
    have : ‖(ncomb b.w A B).toC‖ ^ 2 ≤ (b.dbar : ℝ) ^ 2 := by
      rw [sq_norm_toC]; exact_mod_cast hdd
    have hdb : (0 : ℝ) ≤ b.dbar := by exact_mod_cast hd0
    exact abs_le_of_sq_le_sq' this hdb |>.2
  have hma : ∀ y : ℝ, |y| ≤ 1 → (b.m1 : ℝ) ≤ ‖A.toC - B.toC * (y : ℂ)‖ := fun y hy =>
    norm_ge_of_quad hm1.le hq1 hy
  have hmu : ∀ y : ℝ, |y| ≤ 1 → (b.m2 : ℝ) ≤ ‖(1 + b.w.toC ^ 2) - (2 * b.w.toC) * (y : ℂ)‖ := fun y hy => by
    have := norm_ge_of_quad (A := u0 b.w) (B := u1 b.w) hm2.le hq2 hy
    have e1 : (u0 b.w).toC = 1 + b.w.toC ^ 2 := by simp only [u0, toC_add, toC_mul, toC_one]; ring
    have e2 : (u1 b.w).toC = 2 * b.w.toC := by simp only [u1, toC_mul, toC_two]
    rwa [e1, e2] at this
  have := term_le c.toC A.toC B.toC b.w.toC b.r b.m1 b.m2 b.dbar hr0' hr1' hw hm1' hm2' ha hma hmu hd K hy
  have hcn : ‖c.toC‖ ≤ ((|c.1| + |c.2| : ℚ) : ℝ) := by
    have := Complex.norm_le_abs_re_add_abs_im c.toC
    simpa [QC.toC] using this
  push_cast at hcn
  have hE : 0 ≤ (b.dbar : ℝ) / (b.m1 * b.m2) + 4 * (b.r : ℝ) ^ (K + 1) / (((K : ℝ) + 1) * (1 - b.r)) := by
    have : (0 : ℝ) < 1 - b.r := by linarith
    positivity
  calc _ ≤ _ := this
    _ ≤ -2 * (c.toC * ∑ k ∈ Finset.range K, dTerm b.w.toC y k).re + (termErr c b K : ℝ) := by
      have h2 : ‖c.toC‖ * ((b.dbar : ℝ) / (b.m1 * b.m2) + 4 * (b.r : ℝ) ^ (K + 1) / ((K + 1 : ℕ) * (1 - b.r))) ≤
          (termErr c b K : ℝ) := by
        unfold termErr trunc
        push_cast
        exact mul_le_mul_of_nonneg_right hcn hE
      linarith

/-! ### Chebyshev lists over `ℚ`: addition, multiplication by `y`, composition with `x = m + h y` -/

open CatalanMeasure.Signed.ChebSquare in
noncomputable def qSum : List ℚ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | a :: t, k, x => (a : ℝ) * basis k x + qSum t (k + 1) x

def addQ : List ℚ → List ℚ → List ℚ
  | [], b => b
  | a, [] => a
  | x :: s, y :: t => (x + y) :: addQ s t

def smulQ (a : ℚ) (l : List ℚ) : List ℚ := l.map (a * ·)

section
open CatalanMeasure.Signed.ChebSquare

@[simp] theorem qSum_nil (k : ℕ) (x : ℝ) : qSum [] k x = 0 := rfl
@[simp] theorem qSum_cons (a : ℚ) (t : List ℚ) (k : ℕ) (x : ℝ) :
    qSum (a :: t) k x = (a : ℝ) * basis k x + qSum t (k + 1) x := rfl

theorem qSum_addQ (a b : List ℚ) (k : ℕ) (x : ℝ) : qSum (addQ a b) k x = qSum a k x + qSum b k x := by
  induction a generalizing b k with
  | nil => simp [addQ]
  | cons u s ih =>
    cases b with
    | nil => simp [addQ]
    | cons v t =>
      simp only [addQ, qSum_cons, ih]
      push_cast; ring

theorem qSum_smulQ (a : ℚ) (l : List ℚ) (k : ℕ) (x : ℝ) : qSum (smulQ a l) k x = a * qSum l k x := by
  induction l generalizing k with
  | nil => simp [smulQ]
  | cons u s ih =>
    simp only [smulQ, List.map_cons, qSum_cons] at ih ⊢
    rw [ih]; push_cast; ring

def downQ : List ℚ → List ℚ
  | [] => []
  | [a] => [0, a]
  | a :: b :: rest => b :: (a + rest.headD 0) :: rest.tail

def mulYQ (l : List ℚ) : List ℚ := smulQ (1 / 2) (addQ (0 :: l) (downQ l))

noncomputable def sdSum : ℕ → List ℚ → ℝ → ℝ
  | _, [], _ => 0
  | j, a :: t, x => (a : ℝ) * basis ((1 : ℤ) - j).natAbs x + sdSum (j + 1) t x

theorem mulY_aux (l : List ℚ) (j : ℕ) (x : ℝ) : 2 * x * qSum l j x = qSum l (j + 1) x + sdSum j l x := by
  induction l generalizing j with
  | nil => simp [sdSum]
  | cons a t ih =>
    have h := basis_mul 1 j x
    have h1 : basis 1 x = x := by simp [basis]
    rw [h1] at h
    have e : ((1 : ℕ) : ℤ) - j = (1 : ℤ) - j := by simp
    simp only [qSum_cons, sdSum]
    have ih' := ih (j + 1)
    rw [add_comm 1 j] at h
    simp only [Nat.cast_one] at h
    have : 2 * x * ((a : ℝ) * basis j x + qSum t (j + 1) x) =
        (a : ℝ) * (2 * x * basis j x) + 2 * x * qSum t (j + 1) x := by ring
    rw [this, h, ih']
    ring

theorem sd_shift (l : List ℚ) (j : ℕ) (hj : 2 ≤ j) (x : ℝ) : sdSum j l x = qSum l (j - 1) x := by
  induction l generalizing j with
  | nil => simp [sdSum]
  | cons a t ih =>
    simp only [sdSum, qSum_cons]
    have e : ((1 : ℤ) - j).natAbs = j - 1 := by omega
    rw [e, ih (j + 1) (by omega)]
    have : j + 1 - 1 = (j - 1) + 1 := by omega
    rw [this]

theorem down_eval (l : List ℚ) (x : ℝ) : qSum (downQ l) 0 x = sdSum 0 l x := by
  match l with
  | [] => simp [downQ, sdSum]
  | [a] => simp [downQ, sdSum, basis]
  | a :: b :: rest =>
    simp only [downQ, qSum_cons, sdSum]
    have e1 : ((1 : ℤ) - ((0 : ℕ) : ℤ)).natAbs = 1 := by norm_num
    have e2 : ((1 : ℤ) - (((0 + 1 : ℕ)) : ℤ)).natAbs = 0 := by norm_num
    rw [e1, e2]
    match rest with
    | [] => simp [sdSum, basis]; ring
    | c :: r' =>
      simp only [List.headD_cons, List.tail_cons, qSum_cons, sdSum]
      have e3 : ((1 : ℤ) - (((0 + 1 + 1 : ℕ)) : ℤ)).natAbs = 1 := by norm_num
      rw [e3, sd_shift r' (0 + 1 + 1 + 1) (by omega) x]
      simp only [basis, zero_add]
      push_cast
      ring

theorem mulY_eval (l : List ℚ) (x : ℝ) : qSum (mulYQ l) 0 x = x * qSum l 0 x := by
  unfold mulYQ
  rw [qSum_smulQ, qSum_addQ, down_eval]
  have h := mulY_aux l 0 x
  have : qSum (0 :: l) 0 x = qSum l 1 x := by simp
  rw [this]
  push_cast
  linarith

end

section
open CatalanMeasure.Signed.ChebSquare

def nextT (m h : ℚ) (P Q : List ℚ) : List ℚ :=
  addQ (smulQ 2 (addQ (smulQ m Q) (smulQ h (mulYQ Q)))) (smulQ (-1) P)

def composeGo (m h : ℚ) : List ℚ → List ℚ → List ℚ → List ℚ
  | [], _, _ => []
  | a :: t, P, Q => addQ (smulQ a Q) (composeGo m h t Q (nextT m h P Q))

/-- `Σ_i a_i T_{i+1}(m + h y)` as a Chebyshev list in `y` -/
def compose (m h : ℚ) (a : List ℚ) : List ℚ := composeGo m h a [1] [m, h]

theorem nextT_eval (m h : ℚ) (P Q : List ℚ) (n : ℕ) (y : ℝ)
    (hP : qSum P 0 y = basis n ((m : ℝ) + h * y)) (hQ : qSum Q 0 y = basis (n + 1) ((m : ℝ) + h * y)) :
    qSum (nextT m h P Q) 0 y = basis (n + 2) ((m : ℝ) + h * y) := by
  unfold nextT
  rw [qSum_addQ, qSum_smulQ, qSum_addQ, qSum_smulQ, qSum_smulQ, mulY_eval, qSum_smulQ, hP, hQ]
  have := Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)
  have h2 := congrArg (Polynomial.eval ((m : ℝ) + h * y)) this
  simp only [basis]
  push_cast at h2 ⊢
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat] at h2
  rw [h2]
  simp only [basis] at *
  ring

theorem composeGo_eval (m h : ℚ) (y : ℝ) (a : List ℚ) : ∀ (P Q : List ℚ) (n : ℕ),
    qSum P 0 y = basis n ((m : ℝ) + h * y) → qSum Q 0 y = basis (n + 1) ((m : ℝ) + h * y) →
    qSum (composeGo m h a P Q) 0 y = qSum a (n + 1) ((m : ℝ) + h * y) := by
  induction a with
  | nil => intros; simp [composeGo]
  | cons u t ih =>
    intro P Q n hP hQ
    simp only [composeGo, qSum_cons]
    rw [qSum_addQ, qSum_smulQ, hQ, ih Q (nextT m h P Q) (n + 1) hQ (nextT_eval m h P Q n y hP hQ)]

theorem compose_eval (m h : ℚ) (a : List ℚ) (y : ℝ) :
    qSum (compose m h a) 0 y = qSum a 1 ((m : ℝ) + h * y) := by
  unfold compose
  refine composeGo_eval m h y a [1] [m, h] 0 ?_ ?_
  · simp [basis]
  · simp [basis, Polynomial.Chebyshev.T_one]

/-- `Σ_j l_j T_j(0)`, by the recurrence `T_{j+2}(0) = -T_j(0)` -/
def qZeroGo : List ℚ → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | a :: r, t0, t1 => a * t0 + qZeroGo r t1 (-t0)

theorem basis_add_two_zero (j : ℕ) : basis (j + 2) 0 = - basis j 0 := by
  have := Polynomial.Chebyshev.T_add_two ℝ (j : ℤ)
  have h2 := congrArg (Polynomial.eval (0 : ℝ)) this
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, mul_zero,
    zero_mul, zero_sub] at h2
  simp only [basis]
  push_cast
  exact h2

theorem qZeroGo_eval (l : List ℚ) : ∀ (j : ℕ) (t0 t1 : ℚ), (t0 : ℝ) = basis j 0 → (t1 : ℝ) = basis (j + 1) 0 →
    (qZeroGo l t0 t1 : ℝ) = qSum l j 0 := by
  induction l with
  | nil => intros; simp [qZeroGo]
  | cons a r ih =>
    intro j t0 t1 h0 h1
    simp only [qZeroGo, qSum_cons]
    push_cast
    rw [h0, ih (j + 1) t1 (-t0) h1 (by push_cast; rw [h0]; exact (basis_add_two_zero j).symm)]

def qZero (l : List ℚ) : ℚ := qZeroGo l 1 0

theorem qZero_eval (l : List ℚ) : (qZero l : ℝ) = qSum l 0 0 :=
  qZeroGo_eval l 0 1 0 (by simp [basis]) (by simp [basis, Polynomial.Chebyshev.T_one])

/-! series coefficients -/

def tcoefGo (c w : QC) : QC → ℕ → ℕ → List ℚ
  | _, _, 0 => []
  | cur, k, n + 1 => ((cmul c cur).1 / k) :: tcoefGo c w (cmul cur w) (k + 1) n

/-- the coefficient list of `Re (c Σ_{k=1}^K w^k T_k(y) / k)` -/
def termCoef (c w : QC) (K : ℕ) : List ℚ := 0 :: tcoefGo c w w 1 K

end

/-! ### Assembly: the band bound for the residual field -/

section
open CatalanMeasure.Signed.ChebSquare

theorem tcoef_eval (c w : QC) (y : ℝ) : ∀ (n : ℕ) (cur : QC) (k : ℕ),
    qSum (tcoefGo c w cur k n) k y =
      ∑ i ∈ Finset.range n, (c.toC * cur.toC * w.toC ^ i).re / ((k + i : ℕ) : ℝ) * basis (k + i) y := by
  intro n
  induction n with
  | zero => intro cur k; simp [tcoefGo]
  | succ n ih =>
    intro cur k
    rw [Finset.sum_range_succ']
    simp only [tcoefGo, qSum_cons]
    rw [ih (cmul cur w) (k + 1)]
    have e1 : ((cmul c cur).1 : ℝ) = (c.toC * cur.toC).re := by
      have := congrArg Complex.re (toC_mul c cur)
      simpa [QC.toC, cmul] using this.symm
    have e1' : (((cmul c cur).1 / (k : ℚ) : ℚ) : ℝ) = (c.toC * cur.toC).re / (k : ℝ) := by
      push_cast; rw [e1]
    rw [e1']
    have e2 : ∀ i : ℕ, (c.toC * (cmul cur w).toC * w.toC ^ i).re = (c.toC * cur.toC * w.toC ^ (i + 1)).re := by
      intro i; rw [toC_mul]; ring_nf
    have e3 : ∀ i : ℕ, k + 1 + i = k + (i + 1) := fun i => by omega
    have hsum : ∑ i ∈ Finset.range n, (c.toC * (cmul cur w).toC * w.toC ^ i).re / ((k + 1 + i : ℕ) : ℝ) * basis (k + 1 + i) y =
        ∑ i ∈ Finset.range n, (c.toC * cur.toC * w.toC ^ (i + 1)).re / ((k + (i + 1) : ℕ) : ℝ) * basis (k + (i + 1)) y :=
      Finset.sum_congr rfl (fun i _ => by rw [e2 i, e3 i])
    rw [hsum]
    simp only [pow_zero, mul_one, add_zero, Nat.cast_add]
    ring

theorem termCoef_diff (c w : QC) (K : ℕ) (y : ℝ) :
    (c.toC * ∑ k ∈ Finset.range K, dTerm w.toC y k).re =
      qSum (termCoef c w K) 0 y - qSum (termCoef c w K) 0 0 := by
  unfold termCoef
  simp only [qSum_cons, Rat.cast_zero, zero_mul, zero_add, tcoef_eval]
  rw [Finset.mul_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hd : dTerm w.toC y i = w.toC ^ (i + 1) * (((basis (i + 1) y - basis (i + 1) 0) / ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    unfold dTerm; simp only [basis]; push_cast; ring
  rw [hd, ← mul_assoc]
  have e : (1 + i : ℕ) = i + 1 := by omega
  have e' : c.toC * w.toC ^ (i + 1) = c.toC * w.toC * w.toC ^ i := by ring
  rw [e', Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [show (1 + i : ℕ) = i + 1 from e]
  push_cast
  ring

end

section
open CatalanMeasure.Signed.ChebSquare

abbrev Trip := QC × QC × QC

noncomputable def sumLogRe : List Trip → ℝ → ℝ
  | [], _ => 0
  | (c, A, B) :: L, y => (c.toC * Complex.log (A.toC - B.toC * (y : ℂ))).re + sumLogRe L y

def gList : List Trip → List BT → ℕ → List ℚ
  | (c, _, _) :: L, b :: bs, K => addQ (termCoef c b.w K) (gList L bs K)
  | _, _, _ => []

def errAll : List Trip → List BT → ℕ → ℚ
  | (c, _, _) :: L, b :: bs, K => termErr c b K + errAll L bs K
  | _, _, _ => 0

def okAll : List Trip → List BT → Bool
  | (_, A, B) :: L, b :: bs => termOK A B b && okAll L bs
  | [], [] => true
  | _, _ => false

theorem triples_le (K : ℕ) : ∀ (L : List Trip) (bts : List BT),
    (∀ tr ∈ L, ∀ y : ℝ, |y| ≤ 1 → tr.2.1.toC - tr.2.2.toC * (y : ℂ) ∈ slitPlane) →
    okAll L bts = true → ∀ y : ℝ, |y| ≤ 1 →
    sumLogRe L y ≤ sumLogRe L 0 + (-2 * (qSum (gList L bts K) 0 y - qSum (gList L bts K) 0 0)) +
      (errAll L bts K : ℝ) := by
  intro L
  induction L with
  | nil =>
    intro bts _ hok y _
    cases bts <;> simp [okAll, sumLogRe, gList, errAll] at hok ⊢
  | cons tr L ih =>
    intro bts hsl hok y hy
    obtain ⟨c, A, B⟩ := tr
    cases bts with
    | nil => simp [okAll] at hok
    | cons b bts' =>
      simp only [okAll, Bool.and_eq_true] at hok
      obtain ⟨h1, h2⟩ := hok
      have hs1 : ∀ y : ℝ, |y| ≤ 1 → A.toC - B.toC * (y : ℂ) ∈ slitPlane :=
        fun y hy => hsl (c, A, B) List.mem_cons_self y hy
      have hs2 : ∀ tr ∈ L, ∀ y : ℝ, |y| ≤ 1 → tr.2.1.toC - tr.2.2.toC * (y : ℂ) ∈ slitPlane :=
        fun tr htr => hsl tr (List.mem_cons_of_mem _ htr)
      have t1 := term_le' c A B b K h1 hs1 hy
      have t2 := ih bts' hs2 h2 y hy
      rw [termCoef_diff] at t1
      simp only [sumLogRe, gList, errAll, qSum_addQ]
      have e0 : (c.toC * (Complex.log (A.toC - B.toC * (y : ℂ)) - Complex.log A.toC)).re =
          (c.toC * Complex.log (A.toC - B.toC * (y : ℂ))).re - (c.toC * Complex.log A.toC).re := by
        rw [mul_sub, Complex.sub_re]
      have e1 : (c.toC * Complex.log (A.toC - B.toC * (((0 : ℝ)) : ℂ))).re = (c.toC * Complex.log A.toC).re := by
        simp
      rw [e1]
      push_cast
      linarith

end

section
open CatalanMeasure.Signed.ChebSquare CatalanMeasure.Cert CatalanMeasure.CellCert

/-- the terms of the residual field: the weight term, then the tails, as `(c, A, B)` with
`Log (A - B y)`, `x = m + h y` -/
def triples (ρ : ℚ) (P : List TailQ) (m h : ℚ) : List Trip :=
  ((-2 * ρ, 0), (1, m), (0, -h)) ::
    P.map (fun t => ((t.rr, t.ri), quadArg m t, (2 * h * t.zr, 2 * h * t.zi)))

/-- the residual field `-ρ log(1+x²) - 2 Σ a_i T_{i+1}(x) + Re Σ r_t Log(1 - 2xz_t + z_t²)` -/
noncomputable def Fa (ρ : ℚ) (P : List TailQ) (a : List ℚ) (x : ℝ) : ℝ :=
  -(ρ : ℝ) * Real.log (1 + x ^ 2) - 2 * qSum a 1 x +
    (((P.map TailQ.toC).map (fun zr : ℂ × ℂ =>
      zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum).re

theorem re_weight (ρ : ℚ) (x : ℝ) :
    (QC.toC (-2 * ρ, 0) * Complex.log ⟨1, x⟩).re = -(ρ : ℝ) * Real.log (1 + x ^ 2) := by
  rw [Complex.mul_re, Complex.log_re]
  have hn : ‖(⟨1, x⟩ : ℂ)‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp [sq]
  rw [hn, Real.log_sqrt (by positivity)]
  simp [QC.toC]
  ring

theorem weight_arg (m h : ℚ) (y : ℝ) :
    QC.toC ((1 : ℚ), m) - QC.toC ((0 : ℚ), -h) * (y : ℂ) = ⟨1, (m : ℝ) + h * y⟩ := by
  apply Complex.ext <;> simp [QC.toC] <;> ring

theorem tail_arg (m h : ℚ) (t : TailQ) (y : ℝ) :
    QC.toC (quadArg m t) - QC.toC (2 * h * t.zr, 2 * h * t.zi) * (y : ℂ) =
      1 - 2 * (((m : ℝ) + h * y : ℝ) : ℂ) * (TailQ.toC t).1 + (TailQ.toC t).1 ^ 2 := by
  have h1 := quadArg_spec m t
  have h2 : QC.toC (quadArg m t) = barrierComplex (quadArg m t).1 (quadArg m t).2 := rfl
  rw [h2, ← h1]
  apply Complex.ext <;> simp [QC.toC, TailQ.toC, barrierComplex] <;> ring

theorem sumLogRe_tails (m h : ℚ) (P : List TailQ) (y : ℝ) :
    sumLogRe (P.map (fun t => ((t.rr, t.ri), quadArg m t, (2 * h * t.zr, 2 * h * t.zi)))) y =
      (((P.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * ((((m : ℝ) + h * y : ℝ)) : ℂ) * zr.1 + zr.1 ^ 2))).sum).re := by
  induction P with
  | nil => simp [sumLogRe]
  | cons t P ih =>
    simp only [List.map_cons, sumLogRe, List.sum_cons, Complex.add_re]
    rw [ih, tail_arg]
    rfl

theorem Fa_eq (ρ : ℚ) (P : List TailQ) (a : List ℚ) (m h : ℚ) (y : ℝ) :
    Fa ρ P a ((m : ℝ) + h * y) = sumLogRe (triples ρ P m h) y - 2 * qSum a 1 ((m : ℝ) + h * y) := by
  unfold Fa triples
  simp only [sumLogRe]
  rw [weight_arg, re_weight, sumLogRe_tails]
  ring

theorem sumLogRe_zero (ρ : ℚ) (P : List TailQ) (m h : ℚ) :
    sumLogRe (triples ρ P m h) 0 = ((resTermsW ρ P m).map LogTerm.val).sum := by
  have h1 := sumLogRe_tails m h P 0
  have h2 := tailLog_T1 P m
  have h3 : ((m : ℝ) + h * ((0 : ℝ))) = m := by simp
  rw [h3] at h1
  have hw := weight_arg m h 0
  unfold triples
  simp only [sumLogRe, resTermsW, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [hw, re_weight, h1, ← h2, log_term_sq m]
  have : (m : ℝ) + h * 0 = m := by simp
  rw [this]
  push_cast
  ring

theorem triples_slit (ρ : ℚ) (P : List TailQ) (m h : ℚ) (hP : tailsInDisk P = true) (hmh : |(m : ℝ)| + |(h : ℝ)| ≤ 1) :
    ∀ tr ∈ triples ρ P m h, ∀ y : ℝ, |y| ≤ 1 → tr.2.1.toC - tr.2.2.toC * (y : ℂ) ∈ slitPlane := by
  intro tr htr y hy
  have hx : |(m : ℝ) + h * y| ≤ 1 := by
    calc |(m : ℝ) + h * y| ≤ |(m : ℝ)| + |(h : ℝ) * y| := abs_add_le _ _
      _ = |(m : ℝ)| + |(h : ℝ)| * |y| := by rw [abs_mul]
      _ ≤ |(m : ℝ)| + |(h : ℝ)| * 1 := by gcongr
      _ ≤ 1 := by linarith
  unfold triples at htr
  rcases List.mem_cons.mp htr with rfl | htr
  · simp only
    rw [weight_arg, Complex.mem_slitPlane_iff]
    left; simp
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp htr
    simp only
    rw [tail_arg]
    exact quad_mem_slitPlane (tailsInDisk_spec hP _ (List.mem_map.mpr ⟨t, ht, rfl⟩)) hx

end

section
open CatalanMeasure.Signed.ChebSquare CatalanMeasure.Cert CatalanMeasure.CellCert

/-- `∑ |p_i / D|` -/
def roundErrNil (D : ℚ) : List ℤ → ℚ
  | [] => 0
  | p :: ps => |(p : ℚ) / D| + roundErrNil D ps

/-- the total absolute difference between a rational Chebyshev list and `p / D` (missing entries are `0`);
structural on the first list, so the kernel can evaluate it -/
def roundErr (D : ℚ) : List ℚ → List ℤ → ℚ
  | [], p => roundErrNil D p
  | q :: qs, [] => |q| + roundErr D qs []
  | q :: qs, p :: ps => |q - (p : ℚ) / D| + roundErr D qs ps

theorem round_nil (D : ℕ) (hD : 0 < D) : ∀ (p : List ℤ) (k : ℕ) {x : ℝ}, x ∈ Set.Icc (-1 : ℝ) 1 →
    |qSum [] k x - rawSum p k x / D| ≤ (roundErrNil D p : ℝ) := by
  intro p
  induction p with
  | nil => intro k x hx; simp [roundErrNil]
  | cons a ps ih =>
    intro k x hx
    have hb := abs_basis_le_one k hx
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have := ih (k + 1) hx
    simp only [qSum_nil, roundErrNil, rawSum_cons] at this ⊢
    push_cast at this ⊢
    have e : (0 : ℝ) - ((a : ℝ) * basis k x + rawSum ps (k + 1) x) / D =
        -((a : ℝ) / D * basis k x) - (rawSum ps (k + 1) x / D) := by field_simp; ring
    rw [e]
    have h1 : |(a : ℝ) / D * basis k x| ≤ |(a : ℝ) / D| := by
      rw [abs_mul]; nlinarith [abs_nonneg ((a : ℝ) / D), abs_nonneg (basis k x)]
    have h2 : |-((a : ℝ) / D * basis k x) - rawSum ps (k + 1) x / D| ≤
        |(a : ℝ) / D * basis k x| + |0 - rawSum ps (k + 1) x / D| := by
      calc _ = |(-((a : ℝ) / D * basis k x)) + (0 - rawSum ps (k + 1) x / D)| := by ring_nf
        _ ≤ |-((a : ℝ) / D * basis k x)| + |0 - rawSum ps (k + 1) x / D| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    linarith

theorem round_le (D : ℕ) (hD : 0 < D) : ∀ (Q : List ℚ) (p : List ℤ) (k : ℕ) {x : ℝ}, x ∈ Set.Icc (-1 : ℝ) 1 →
    |qSum Q k x - rawSum p k x / D| ≤ (roundErr D Q p : ℝ) := by
  intro Q
  induction Q with
  | nil => intro p k x hx; exact round_nil D hD p k hx
  | cons q qs ih =>
    intro p k x hx
    have hb := abs_basis_le_one k hx
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    cases p with
    | nil =>
      have := ih [] (k + 1) hx
      simp only [qSum_cons, roundErr, rawSum_nil, zero_div, sub_zero] at this ⊢
      push_cast
      have h1 : |(q : ℝ) * basis k x| ≤ |(q : ℝ)| := by
        rw [abs_mul]; nlinarith [abs_nonneg (q : ℝ), abs_nonneg (basis k x)]
      calc |(q : ℝ) * basis k x + qSum qs (k + 1) x| ≤ |(q : ℝ) * basis k x| + |qSum qs (k + 1) x| := abs_add_le _ _
        _ ≤ _ := by linarith
    | cons a ps =>
      have := ih ps (k + 1) hx
      simp only [qSum_cons, roundErr, rawSum_cons] at this ⊢
      push_cast at this ⊢
      have e : (q : ℝ) * basis k x + qSum qs (k + 1) x - ((a : ℝ) * basis k x + rawSum ps (k + 1) x) / D =
          ((q : ℝ) - a / D) * basis k x + (qSum qs (k + 1) x - rawSum ps (k + 1) x / D) := by field_simp; ring
      rw [e]
      have h1 : |((q : ℝ) - a / D) * basis k x| ≤ |(q : ℝ) - a / D| := by
        rw [abs_mul]; nlinarith [abs_nonneg ((q : ℝ) - a / D), abs_nonneg (basis k x)]
      calc _ ≤ |((q : ℝ) - a / D) * basis k x| + |qSum qs (k + 1) x - rawSum ps (k + 1) x / D| := abs_add_le _ _
        _ ≤ _ := by linarith

def bandPoly (errT c0 : ℚ) (G : List ℚ) (m h : ℚ) (vs : List (List ℚ × List ℤ)) (D : ℕ) (eps : ℚ) : Bool :=
  vs.all (fun ap => decide (errT + roundErr D (addQ (addQ [c0 - qZero G] G) (smulQ (-2) (compose m h ap.1))) ap.2 ≤ eps))

/-- the certified upper bound `U` of the logarithm terms at the band centre -/
def logUpper (ρ : ℚ) (P : List TailQ) (m U : ℚ) : Bool :=
  match CatalanMeasure.WLog.sumLogsWI (resTermsW ρ P m) with
  | some (v, e) => decide (v + e ≤ U)
  | none => false

def bandCheck (ρ : ℚ) (P : List TailQ) (m h : ℚ) (K : ℕ) (bts : List BT) (U : ℚ)
    (vs : List (List ℚ × List ℤ)) (D : ℕ) (eps : ℚ) : Bool :=
  tailsInDisk P && decide (|m| + |h| ≤ 1) && decide (0 < D) && logUpper ρ P m U &&
  okAll (triples ρ P m h) bts &&
  bandPoly (errAll (triples ρ P m h) bts K) U (smulQ (-2) (gList (triples ρ P m h) bts K)) m h vs D eps

/-- **The band bound.**  If `bandCheck` holds, then on the band `x = m + h y`, `y ∈ [-1,1]`, the field
`Fa ρ P a` is at most the dyadic Chebyshev polynomial `chebSum p D y` plus `eps`, for every variant `(a, p)`. -/
theorem band_field_le (ρ : ℚ) (P : List TailQ) (m h : ℚ) (K : ℕ) (bts : List BT) (U : ℚ)
    (vs : List (List ℚ × List ℤ)) (D : ℕ) (eps : ℚ)
    (hchk : bandCheck ρ P m h K bts U vs D eps = true) :
    ∀ ap ∈ vs, ∀ y ∈ Set.Icc (-1 : ℝ) 1, Fa ρ P ap.1 ((m : ℝ) + h * y) ≤ chebSum ap.2 D y + (eps : ℝ) := by
  simp only [bandCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hP, hmh⟩, hD⟩, hlog⟩, hok⟩, hpoly⟩ := hchk
  have hlog' : ∃ v e, CatalanMeasure.WLog.sumLogsWI (resTermsW ρ P m) = some (v, e) ∧ v + e ≤ U := by
    unfold logUpper at hlog
    split at hlog
    · rename_i v e hve
      simp only [decide_eq_true_eq] at hlog
      exact ⟨v, e, hve, hlog⟩
    · simp at hlog
  obtain ⟨v, e, hve, hvU⟩ := hlog'
  intro ap hap y hy
  have hyabs : |y| ≤ 1 := abs_le.mpr ⟨hy.1, hy.2⟩
  have hmh' : |(m : ℝ)| + |(h : ℝ)| ≤ 1 := by exact_mod_cast hmh
  have hsl := triples_slit ρ P m h hP hmh'
  have hle := triples_le K (triples ρ P m h) bts hsl hok y hyabs
  have hz := CatalanMeasure.WLog.sumLogsWI_spec hve
  rw [← sumLogRe_zero] at hz
  have hz' := (abs_le.mp hz).2
  have hpo := List.all_eq_true.mp hpoly ap hap
  simp only [decide_eq_true_eq] at hpo
  set L := triples ρ P m h
  set G := smulQ (-2) (gList L bts K) with hG
  set Q := addQ (addQ [U - qZero G] G) (smulQ (-2) (compose m h ap.1)) with hQ
  have hrd := round_le D hD Q ap.2 0 hy
  have hQy : qSum Q 0 y = (U : ℚ) - qSum G 0 0 + qSum G 0 y - 2 * qSum ap.1 1 ((m : ℝ) + h * y) := by
    rw [hQ, qSum_addQ, qSum_addQ, qSum_smulQ (-2) (compose m h ap.1), compose_eval]
    simp only [qSum_cons, qSum_nil, basis_zero, mul_one, add_zero]
    rw [Rat.cast_sub, qZero_eval]
    push_cast
    ring
  have hG' : qSum G 0 y = -2 * qSum (gList L bts K) 0 y := by rw [hG, qSum_smulQ]; push_cast; ring
  have hG0 : qSum G 0 0 = -2 * qSum (gList L bts K) 0 0 := by rw [hG, qSum_smulQ]; push_cast; ring
  rw [Fa_eq]
  have hch : chebSum ap.2 D y = rawSum ap.2 0 y / D := rfl
  rw [hch]
  have hrd' := (abs_le.mp hrd).2
  have hpo' : ((errAll L bts K : ℚ) : ℝ) + (roundErr D Q ap.2 : ℝ) ≤ eps := by exact_mod_cast hpo
  have hvU' : (v : ℝ) + e ≤ U := by exact_mod_cast hvU
  push_cast at hQy hz' hpo' ⊢
  nlinarith [hle, hz', hrd', hQy, hG', hG0, hpo', hvU']

end

end CatalanMeasure.GenD.Cert.LogSeriesBand
#print axioms CatalanMeasure.GenD.Cert.LogSeriesBand.band_field_le
