module

public import CatalanCore.Decay.ComplexContour
public import CatalanCore.Decay.ComplexTaylor
public import CatalanCore.Zeta5.Energy.Stirling
public import CatalanMeasure.GenD.Signed.BinomVandermonde
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-!
# Lemma W: the weight bound on the contour (Lai decay, LD05)

Generic in the design `(e, r, B, K)` (`R_n(z) = ((Kn)!^r/(Bn)!^e) ∏_{N=1}^{Bn} (z-N)^e / ∏_{k=0}^{Kn} (z+k)^r`)
and the jet data `(J, c)` of `K_c`.  For `z` in the right half plane, off the real axis, with
`‖z‖ ≥ 1/2` and either `|Im z| ≥ 1` or `Re z ∈ ℤ + 1/2`:

`‖R_n z · K_c z‖ ≤ C_c exp (n V(z/n) + C₀ + (r/2 + e) log n + e log (1 + ‖z/n‖))`  (`norm_RKc_le`),

with `V = Φ - 2π|Im s|` (`vField`), and `log (C(Kn,k)^r C(Bn+k,k)^e) ≤ n ω(k/n)` for the atoms
(`log_atom_le`).  Proof: sums versus integrals for `log ‖z - x‖` (unimodal) and `log ‖z + x‖`
(monotone), Stirling for the prefactor, the entropy bound for the binomials, and the lattice jet
bounds for `K_c`.
-/

open MeasureTheory Set Real Filter Topology Finset CatalanCore.Decay.ComplexContour
  CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Decay.LemmaW

/-! ### 1. The unit-interval lower bound -/

lemma phi_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ (p + 1) * Real.log (p + 1) - p * Real.log p := by
  have h1 : 0 ≤ Real.log (p + 1) := Real.log_nonneg (by linarith)
  have h2 : p * Real.log p ≤ p * Real.log (p + 1) := by
    rcases hp.eq_or_lt with rfl | hp0
    · simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log hp0 (by linarith)) hp
  nlinarith

lemma phi_ge (p : ℝ) :
    -Real.log 2 ≤ (p + 1) * Real.log (p + 1) - p * Real.log p := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases le_or_gt 0 p with hp | hp
  · linarith [phi_nonneg hp]
  rcases le_or_gt p (-1) with hp1 | hp1
  · have h := phi_nonneg (p := -1 - p) (by linarith)
    have e1 : (-1 - p + 1) * Real.log (-1 - p + 1) = -(p * Real.log p) := by
      have : (-1 - p + 1) = -p := by ring
      rw [this, Real.log_neg_eq_log]; ring
    have e2 : (-1 - p) * Real.log (-1 - p) = -((p + 1) * Real.log (p + 1)) := by
      have : (-1 - p) = -(p + 1) := by ring
      rw [this, Real.log_neg_eq_log]; ring
    rw [e1, e2] at h
    linarith
  · -- -1 < p < 0 : binary entropy
    set q := -p with hq
    have hq0 : 0 < q := by linarith
    have hq1 : q < 1 := by linarith
    have hent := Real.binEntropy_le_log_two (p := q)
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def] at hent
    simp only [neg_mul] at hent
    have e1 : Real.log p = Real.log q := by rw [hq, Real.log_neg_eq_log]
    have e2 : p + 1 = 1 - q := by rw [hq]; ring
    rw [e2, e1]
    have : p = -q := by rw [hq]; ring
    rw [this]
    nlinarith

/-- `∫_J log |x - a| dx ≥ -1 - log 2` on a unit interval `J = [m, m+1]`. -/
lemma integral_log_sub_unit (m a : ℝ) :
    -1 - Real.log 2 ≤ ∫ x in m..m + 1, Real.log (x - a) := by
  have hint : IntervalIntegrable (fun x : ℝ => Real.log (x - a)) volume m (m + 1) :=
    by
      have := (intervalIntegral.intervalIntegrable_log' (a := m - a) (b := m + 1 - a)).comp_sub_right a
      simpa using this
  have h1 : ∫ x in m..m + 1, Real.log (x - a) = ∫ u in (m - a)..(m + 1 - a), Real.log u :=
    intervalIntegral.integral_comp_sub_right (fun u : ℝ => Real.log u) a
  rw [h1, integral_log]
  have := phi_ge (m - a)
  have e : (m + 1 - a) = (m - a + 1) := by ring
  rw [e]
  linarith

/-! ### 2. Sum versus integral -/

lemma norm_sub_ofReal_sq (z : ℂ) (x : ℝ) : ‖z - (x : ℂ)‖ ^ 2 = (z.re - x) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

lemma norm_add_ofReal_sq (z : ℂ) (x : ℝ) : ‖z + (x : ℂ)‖ ^ 2 = (z.re + x) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

lemma norm_sub_ofReal_pos {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) : 0 < ‖z - (x : ℂ)‖ := by
  refine norm_pos_iff.mpr fun h => hz ?_
  have := congrArg Complex.im h
  simpa using this

lemma norm_add_ofReal_pos {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) : 0 < ‖z + (x : ℂ)‖ := by
  refine norm_pos_iff.mpr fun h => hz ?_
  have := congrArg Complex.im h
  simpa using this

lemma le_of_sq' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push_neg at hc
  nlinarith

/-- `x ↦ log ‖z - x‖`. -/
noncomputable def gN (z : ℂ) (x : ℝ) : ℝ := Real.log ‖z - (x : ℂ)‖

/-- `x ↦ log ‖z + x‖`. -/
noncomputable def gD (z : ℂ) (x : ℝ) : ℝ := Real.log ‖z + (x : ℂ)‖

lemma continuous_gN {z : ℂ} (hz : z.im ≠ 0) : Continuous (gN z) := by
  unfold gN
  exact Continuous.log (by fun_prop) fun x => (norm_sub_ofReal_pos hz x).ne'

lemma continuous_gD {z : ℂ} (hz : z.im ≠ 0) : Continuous (gD z) := by
  unfold gD
  exact Continuous.log (by fun_prop) fun x => (norm_add_ofReal_pos hz x).ne'

lemma antitoneOn_gN {z : ℂ} (hz : z.im ≠ 0) : AntitoneOn (gN z) (Set.Iic z.re) := by
  intro x hx y hy hxy
  have hx' : x ≤ z.re := hx
  have hy' : y ≤ z.re := hy
  unfold gN
  refine Real.log_le_log (norm_sub_ofReal_pos hz y) ?_
  have h1 := norm_sub_ofReal_sq z x
  have h2 := norm_sub_ofReal_sq z y
  have : ‖z - (y : ℂ)‖ ^ 2 ≤ ‖z - (x : ℂ)‖ ^ 2 := by
    rw [h1, h2]; nlinarith
  exact le_of_sq' (norm_nonneg _) (norm_nonneg _) this

lemma monotoneOn_gN {z : ℂ} (hz : z.im ≠ 0) : MonotoneOn (gN z) (Set.Ici z.re) := by
  intro x hx y hy hxy
  have hx' : z.re ≤ x := hx
  unfold gN
  refine Real.log_le_log (norm_sub_ofReal_pos hz x) ?_
  have h1 := norm_sub_ofReal_sq z x
  have h2 := norm_sub_ofReal_sq z y
  have : ‖z - (x : ℂ)‖ ^ 2 ≤ ‖z - (y : ℂ)‖ ^ 2 := by
    rw [h1, h2]; nlinarith
  exact le_of_sq' (norm_nonneg _) (norm_nonneg _) this

lemma gN_le_log_add (z : ℂ) (hz : z.im ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    gN z x ≤ Real.log (‖z‖ + x) := by
  unfold gN
  refine Real.log_le_log (norm_sub_ofReal_pos hz x) ?_
  calc ‖z - (x : ℂ)‖ ≤ ‖z‖ + ‖(x : ℂ)‖ := norm_sub_le _ _
    _ = ‖z‖ + x := by rw [Complex.norm_real, Real.norm_of_nonneg hx]

/-- **Numerator sum versus integral** (Lemma W): `∑_{N=1}^{M} log ‖z - N‖ ≤ ∫_0^M log ‖z - x‖ dx
+ log (‖z‖ + M + 1) + 1 + log 2` for `Im z ≠ 0`. -/
theorem sum_gN_le {z : ℂ} (hz : z.im ≠ 0) (M : ℕ) :
    ∑ i ∈ range M, gN z (((i + 1 : ℕ) : ℝ)) ≤
      (∫ x in (0 : ℝ)..(M : ℝ), gN z x) + Real.log (‖z‖ + M + 1) + 1 + Real.log 2 := by
  have hc := continuous_gN hz
  have hii : ∀ a b : ℝ, IntervalIntegrable (gN z) volume a b := fun a b => hc.intervalIntegrable a b
  set m : ℕ := min M ⌊z.re⌋₊ with hmdef
  have hmM : m ≤ M := min_le_left _ _
  -- left sum
  have hleft : ∑ i ∈ range m, gN z (((i + 1 : ℕ) : ℝ)) ≤ ∫ x in (0 : ℝ)..(m : ℝ), gN z x := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · simp [h0]
    · have hre : 0 ≤ z.re := by
        by_contra hneg
        push_neg at hneg
        have : ⌊z.re⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        have : m = 0 := by rw [hmdef, this]; simp
        omega
      have hmle : (m : ℝ) ≤ z.re := by
        calc (m : ℝ) ≤ (⌊z.re⌋₊ : ℝ) := by exact_mod_cast min_le_right _ _
          _ ≤ z.re := Nat.floor_le hre
      have hanti : AntitoneOn (gN z) (Icc (0 : ℝ) (0 + m)) :=
        (antitoneOn_gN hz).mono fun x hx => by
          have := hx.2
          simp only [zero_add] at this
          exact le_trans this hmle
      have := hanti.sum_le_integral
      simpa using this
  -- right sum
  have hright : ∑ i ∈ range (M - m), gN z (((m + i + 1 : ℕ) : ℝ)) ≤
      ∫ x in ((m : ℝ) + 1)..((M : ℝ) + 1), gN z x := by
    rcases Nat.eq_zero_or_pos (M - m) with h0 | hpos
    · have : (M : ℝ) = m := by
        have : M = m := by omega
        rw [this]
      rw [h0, this]; simp
    · have hmlt : m < M := by omega
      have hmf : m = ⌊z.re⌋₊ := by
        rcases min_choice M ⌊z.re⌋₊ with h | h
        · rw [hmdef, h] at hmlt; omega
        · rw [hmdef, h]
      have hlt : z.re < (m : ℝ) + 1 := by
        rw [hmf]
        exact Nat.lt_floor_add_one _
      have hmono : MonotoneOn (gN z) (Icc ((m : ℝ) + 1) (((m : ℝ) + 1) + ((M - m : ℕ) : ℝ))) :=
        (monotoneOn_gN hz).mono fun x hx => le_trans hlt.le hx.1
      have := hmono.sum_le_integral
      have e1 : ((m : ℝ) + 1) + ((M - m : ℕ) : ℝ) = (M : ℝ) + 1 := by
        rw [Nat.cast_sub hmM]; ring
      rw [e1] at this
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      push_cast; ring
  have hsplit : ∑ i ∈ range M, gN z (((i + 1 : ℕ) : ℝ)) =
      ∑ i ∈ range m, gN z (((i + 1 : ℕ) : ℝ)) +
        ∑ i ∈ range (M - m), gN z (((m + i + 1 : ℕ) : ℝ)) := by
    have : M = m + (M - m) := by omega
    conv_lhs => rw [this, Finset.sum_range_add]
  -- integrals
  have hI1 : ∫ x in (0 : ℝ)..((M : ℝ) + 1), gN z x =
      (∫ x in (0 : ℝ)..(m : ℝ), gN z x) + (∫ x in (m : ℝ)..((m : ℝ) + 1), gN z x) +
        ∫ x in ((m : ℝ) + 1)..((M : ℝ) + 1), gN z x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  have hI2 : ∫ x in (0 : ℝ)..((M : ℝ) + 1), gN z x =
      (∫ x in (0 : ℝ)..(M : ℝ), gN z x) + ∫ x in (M : ℝ)..((M : ℝ) + 1), gN z x :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
  have hI3 : ∫ x in (M : ℝ)..((M : ℝ) + 1), gN z x ≤ Real.log (‖z‖ + M + 1) := by
    have : ∫ x in (M : ℝ)..((M : ℝ) + 1), gN z x ≤
        ∫ x in (M : ℝ)..((M : ℝ) + 1), Real.log (‖z‖ + M + 1) := by
      refine intervalIntegral.integral_mono_on (by linarith) (hii _ _) (by simp) fun x hx => ?_
      have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg M) hx.1
      refine (gN_le_log_add z hz hx0).trans ?_
      have hpos : 0 < ‖z‖ + x := by
        have := norm_nonneg z
        have hxp : 0 < x ∨ 0 < ‖z‖ := by
          rcases hx0.eq_or_lt with h | h
          · right
            refine norm_pos_iff.mpr fun h0 => hz ?_
            rw [h0]; simp
          · left; exact h
        rcases hxp with h | h <;> linarith
      exact Real.log_le_log hpos (by linarith [hx.2])
    simpa using this
  have hI4 : -1 - Real.log 2 ≤ ∫ x in (m : ℝ)..((m : ℝ) + 1), gN z x := by
    refine le_trans (integral_log_sub_unit (m : ℝ) z.re) ?_
    refine intervalIntegral.integral_mono_ae_restrict (by linarith) ?_ (hii _ _) ?_
    · have := (intervalIntegral.intervalIntegrable_log' (a := (m : ℝ) - z.re)
        (b := (m : ℝ) + 1 - z.re)).comp_sub_right z.re
      simpa using this
    · have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({z.re} : Set ℝ) :=
        (Set.countable_singleton z.re).ae_notMem volume
      filter_upwards [ae_restrict_of_ae hae] with x hx
      have hxr : x - z.re ≠ 0 := fun h => hx (by simp; linarith)
      unfold gN
      rw [← Real.log_abs]
      refine Real.log_le_log (abs_pos.mpr hxr) ?_
      refine le_of_sq' (abs_nonneg _) (norm_nonneg _) ?_
      rw [sq_abs, norm_sub_ofReal_sq]
      nlinarith [sq_nonneg z.im]
  rw [hsplit]
  have h5 := add_le_add hleft hright
  have h6 : (∫ x in (0 : ℝ)..(M : ℝ), gN z x) + ∫ x in (M : ℝ)..((M : ℝ) + 1), gN z x =
      ((∫ x in (0 : ℝ)..(m : ℝ), gN z x) + (∫ x in (m : ℝ)..((m : ℝ) + 1), gN z x)) +
        ∫ x in ((m : ℝ) + 1)..((M : ℝ) + 1), gN z x := by rw [← hI2, hI1]
  linarith [h5, h6, hI3, hI4]

/-! ### 3. Denominator sum versus integral -/

/-- **Denominator sum versus integral**: for `Re z ≥ 0` and `Im z ≠ 0`,
`∫_0^M log ‖z + x‖ dx + log ‖z‖ ≤ ∑_{k=0}^{M} log ‖z + k‖`. -/
theorem sum_gD_ge {z : ℂ} (hz : z.im ≠ 0) (hre : 0 ≤ z.re) (M : ℕ) :
    (∫ x in (0 : ℝ)..(M : ℝ), gD z x) + Real.log ‖z‖ ≤ ∑ k ∈ range (M + 1), gD z (k : ℝ) := by
  have hmono : MonotoneOn (gD z) (Icc (0 : ℝ) (0 + M)) := by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := hx.1
    unfold gD
    refine Real.log_le_log (norm_add_ofReal_pos hz x) ?_
    have h1 := norm_add_ofReal_sq z x
    have h2 := norm_add_ofReal_sq z y
    have : ‖z + (x : ℂ)‖ ^ 2 ≤ ‖z + (y : ℂ)‖ ^ 2 := by
      rw [h1, h2]; nlinarith
    exact le_of_sq' (norm_nonneg _) (norm_nonneg _) this
  have h := hmono.integral_le_sum
  rw [Finset.sum_range_succ']
  have h0 : gD z ((0 : ℕ) : ℝ) = Real.log ‖z‖ := by simp [gD]
  rw [h0]
  have e : ∑ i ∈ range M, gD z (((i + 1 : ℕ)) : ℝ) = ∑ i ∈ range M, gD z (0 + (((i + 1 : ℕ)) : ℝ)) := by
    simp
  rw [e]
  simpa using add_le_add_right h (Real.log ‖z‖)

/-! ### 4. Scaling of the integrals -/

lemma integral_gN_scale {z : ℂ} (hz : z.im ≠ 0) {n : ℝ} (hn : 0 < n) (B : ℝ) :
    ∫ x in (0 : ℝ)..(B * n), gN z x =
      n * (B * Real.log n + ∫ u in (0 : ℝ)..B, Real.log ‖z / n - (u : ℂ)‖) := by
  set s : ℂ := z / (n : ℂ) with hs
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have him : s.im ≠ 0 := by
    rw [hs, Complex.div_ofReal_im]; exact div_ne_zero hz hn.ne'
  have hpt : ∀ x : ℝ, gN z x = (fun u : ℝ => Real.log n + Real.log ‖s - (u : ℂ)‖) (x / n) := by
    intro x
    have hnorm : ‖z - (x : ℂ)‖ = n * ‖s - ((x / n : ℝ) : ℂ)‖ := by
      have : z - (x : ℂ) = (n : ℂ) * (s - ((x / n : ℝ) : ℂ)) := by
        rw [hs]; push_cast; field_simp
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hn.le]
    unfold gN
    rw [hnorm, Real.log_mul hn.ne' (norm_sub_ofReal_pos him _).ne']
  have hfun : (gN z) = fun x => (fun u : ℝ => Real.log n + Real.log ‖s - (u : ℂ)‖) (x / n) := funext hpt
  rw [hfun, intervalIntegral.integral_comp_div (fun u : ℝ => Real.log n + Real.log ‖s - (u : ℂ)‖) hn.ne']
  have hc : Continuous fun u : ℝ => Real.log ‖s - (u : ℂ)‖ :=
    Continuous.log (by fun_prop) fun x => (norm_sub_ofReal_pos him x).ne'
  rw [intervalIntegral.integral_add (by simp) (hc.intervalIntegrable _ _)]
  simp only [zero_div, mul_div_cancel_right₀ _ hn.ne', intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma integral_gD_scale {z : ℂ} (hz : z.im ≠ 0) {n : ℝ} (hn : 0 < n) (K : ℝ) :
    ∫ x in (0 : ℝ)..(K * n), gD z x =
      n * (K * Real.log n + ∫ u in (0 : ℝ)..K, Real.log ‖z / n + (u : ℂ)‖) := by
  set s : ℂ := z / (n : ℂ) with hs
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have him : s.im ≠ 0 := by
    rw [hs, Complex.div_ofReal_im]; exact div_ne_zero hz hn.ne'
  have hpt : ∀ x : ℝ, gD z x = (fun u : ℝ => Real.log n + Real.log ‖s + (u : ℂ)‖) (x / n) := by
    intro x
    have hnorm : ‖z + (x : ℂ)‖ = n * ‖s + ((x / n : ℝ) : ℂ)‖ := by
      have : z + (x : ℂ) = (n : ℂ) * (s + ((x / n : ℝ) : ℂ)) := by
        rw [hs]; push_cast; field_simp
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hn.le]
    unfold gD
    rw [hnorm, Real.log_mul hn.ne' (norm_add_ofReal_pos him _).ne']
  have hfun : (gD z) = fun x => (fun u : ℝ => Real.log n + Real.log ‖s + (u : ℂ)‖) (x / n) := funext hpt
  rw [hfun, intervalIntegral.integral_comp_div (fun u : ℝ => Real.log n + Real.log ‖s + (u : ℂ)‖) hn.ne']
  have hc : Continuous fun u : ℝ => Real.log ‖s + (u : ℂ)‖ :=
    Continuous.log (by fun_prop) fun x => (norm_add_ofReal_pos him x).ne'
  rw [intervalIntegral.integral_add (by simp) (hc.intervalIntegrable _ _)]
  simp only [zero_div, mul_div_cancel_right₀ _ hn.ne', intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ### 5. The rational function `R_n` of a design `(e, r, B, K)` -/

/-- The design rational function
`R_n(z) = ((Kn)!^r / (Bn)!^e) ∏_{N=1}^{Bn} (z - N)^e / ∏_{k=0}^{Kn} (z + k)^r`. -/
noncomputable def Rn (e r B K n : ℕ) (z : ℂ) : ℂ :=
  ((((K * n).factorial : ℂ) ^ r / ((B * n).factorial : ℂ) ^ e) *
      ∏ i ∈ range (B * n), (z - (((i + 1 : ℕ) : ℝ) : ℂ)) ^ e) /
    ∏ k ∈ range (K * n + 1), (z + ((k : ℝ) : ℂ)) ^ r

theorem log_norm_Rn {z : ℂ} (hz : z.im ≠ 0) (e r B K n : ℕ) :
    Real.log ‖Rn e r B K n z‖ =
      r * Real.log ((K * n).factorial) - e * Real.log ((B * n).factorial) +
        e * ∑ i ∈ range (B * n), gN z (((i + 1 : ℕ) : ℝ)) -
        r * ∑ k ∈ range (K * n + 1), gD z (k : ℝ) := by
  have hfK : (0 : ℝ) < ((K * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hfB : (0 : ℝ) < ((B * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hN : ∀ i ∈ range (B * n), ‖z - (((i + 1 : ℕ) : ℝ) : ℂ)‖ ^ e ≠ 0 := fun i _ =>
    (pow_pos (norm_sub_ofReal_pos hz _) e).ne'
  have hD : ∀ k ∈ range (K * n + 1), ‖z + ((k : ℝ) : ℂ)‖ ^ r ≠ 0 := fun k _ =>
    (pow_pos (norm_add_ofReal_pos hz _) r).ne'
  unfold Rn
  rw [norm_div, norm_mul, norm_div, norm_pow, norm_pow, norm_prod, norm_prod]
  simp only [norm_pow]
  have e1 : ‖((K * n).factorial : ℂ)‖ = ((K * n).factorial : ℝ) := by simp
  have e2 : ‖((B * n).factorial : ℂ)‖ = ((B * n).factorial : ℝ) := by simp
  rw [e1, e2]
  have hprodN : 0 < ∏ i ∈ range (B * n), ‖z - (((i + 1 : ℕ) : ℝ) : ℂ)‖ ^ e :=
    Finset.prod_pos fun i _ => pow_pos (norm_sub_ofReal_pos hz _) e
  have hprodD : 0 < ∏ k ∈ range (K * n + 1), ‖z + ((k : ℝ) : ℂ)‖ ^ r :=
    Finset.prod_pos fun k _ => pow_pos (norm_add_ofReal_pos hz _) r
  rw [Real.log_div (mul_pos (div_pos (pow_pos hfK r) (pow_pos hfB e)) hprodN).ne' hprodD.ne',
    Real.log_mul (div_pos (pow_pos hfK r) (pow_pos hfB e)).ne' hprodN.ne',
    Real.log_div (pow_pos hfK r).ne' (pow_pos hfB e).ne', Real.log_pow, Real.log_pow,
    Real.log_prod hN, Real.log_prod hD]
  simp only [Real.log_pow, ← Finset.mul_sum]
  unfold gN gD
  ring

/-! ### 6. Lemma W for `R_n` -/

/-- **Lemma W (R-part)**: for `n ≥ 1`, `Re z ≥ 0`, `Im z ≠ 0`, with `s = z / n`,
`log ‖R_n z‖ ≤ n · V₀(s) + r (log (Kn) / 2 + 1) + e (log (‖z‖ + Bn + 1) + 1 + log 2) - r log ‖z‖`,
`V₀ = vField e r B K 0`. -/
theorem log_norm_Rn_le {z : ℂ} (hz : z.im ≠ 0) (hre : 0 ≤ z.re) (e r B K n : ℕ)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (hn : 1 ≤ n) :
    Real.log ‖Rn e r B K n z‖ ≤
      (n : ℝ) * CatalanCore.Decay.ComplexTaylor.vField (e : ℝ) (r : ℝ) (B : ℝ) (K : ℝ) 0 (z / ((n : ℝ) : ℂ)) +
        r * (Real.log ((K : ℝ) * n) / 2 + 1) +
        e * (Real.log (‖z‖ + (B : ℝ) * n + 1) + 1 + Real.log 2) - r * Real.log ‖z‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  rw [log_norm_Rn hz]
  -- Stirling
  have hKn : 1 ≤ K * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hS1 := CatalanCore.Zeta5.Energy.log_factorial_le hKn
  have hS2 := CatalanCore.Zeta5.Energy.log_factorial_ge (B * n)
  push_cast at hS1 hS2
  -- sums
  have hnum := sum_gN_le hz (B * n)
  have hden := sum_gD_ge hz hre (K * n)
  simp only [Nat.cast_mul] at hnum hden
  have hIN := integral_gN_scale hz hn0 (B : ℝ)
  have hID := integral_gD_scale hz hn0 (K : ℝ)
  have hIN' : ∫ x in (0 : ℝ)..((B : ℝ) * n), gN z x =
      n * (B * Real.log n + ∫ u in (0 : ℝ)..(B : ℝ), Real.log ‖z / n - (u : ℂ)‖) := hIN
  have hlogKn : Real.log ((K : ℝ) * n) = Real.log K + Real.log n := Real.log_mul hK0.ne' hn0.ne'
  have hlogBn : Real.log ((B : ℝ) * n) = Real.log B + Real.log n := Real.log_mul hB0.ne' hn0.ne'
  unfold CatalanCore.Decay.ComplexTaylor.vField
  simp only [zero_mul, sub_zero]
  have eK : ((K : ℝ) * n) * Real.log ((K : ℝ) * n) = n * (K * Real.log K + K * Real.log n) := by
    rw [hlogKn]; ring
  have eB : ((B : ℝ) * n) * Real.log ((B : ℝ) * n) = n * (B * Real.log B + B * Real.log n) := by
    rw [hlogBn]; ring
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have c1 := mul_le_mul_of_nonneg_left hS1 hr0
  have c2 := mul_le_mul_of_nonneg_left hS2 he0
  have c3 := mul_le_mul_of_nonneg_left hnum he0
  have c4 := mul_le_mul_of_nonneg_left hden hr0
  rw [hIN'] at c3
  rw [hID] at c4
  nlinarith [c1, c2, c3, c4, eK, eB]

/-- Lemma W (R-part), explicit polynomial form: for `n ≥ 1`, `Re z ≥ 0`, `‖z‖ ≥ 1/2`, `Im z ≠ 0`,
`log ‖R_n z‖ ≤ n V₀(z/n) + C₀ + (r/2 + e) log n + e log (1 + ‖z/n‖)`. -/
noncomputable def RConst (e r B K : ℕ) : ℝ :=
  r * (Real.log K / 2 + 1) + e * (Real.log ((B : ℝ) + 1) + 1 + Real.log 2) + r * Real.log 2

theorem log_norm_Rn_le' {z : ℂ} (hz : z.im ≠ 0) (hre : 0 ≤ z.re) (hz2 : (1 : ℝ) / 2 ≤ ‖z‖)
    (e r B K n : ℕ) (hB : 1 ≤ B) (hK : 1 ≤ K) (hn : 1 ≤ n) :
    Real.log ‖Rn e r B K n z‖ ≤
      (n : ℝ) * CatalanCore.Decay.ComplexTaylor.vField (e : ℝ) (r : ℝ) (B : ℝ) (K : ℝ) 0
          (z / ((n : ℝ) : ℂ)) + RConst e r B K + ((r : ℝ) / 2 + e) * Real.log n +
        e * Real.log (1 + ‖z / ((n : ℝ) : ℂ)‖) := by
  have h := log_norm_Rn_le hz hre e r B K n hB hK hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  set s : ℂ := z / ((n : ℝ) : ℂ) with hs
  have hzs : ‖z‖ = n * ‖s‖ := by
    rw [hs, norm_div, Complex.norm_real, Real.norm_of_nonneg hn0.le]; field_simp
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg _
  have hz0 : 0 < ‖z‖ := by linarith
  -- log(‖z‖ + Bn + 1) ≤ log n + log (B+1) + log (1 + ‖s‖)
  have hlog1 : Real.log (‖z‖ + (B : ℝ) * n + 1) ≤
      Real.log n + Real.log ((B : ℝ) + 1) + Real.log (1 + ‖s‖) := by
    have hpos : 0 < ‖z‖ + (B : ℝ) * n + 1 := by positivity
    rw [← Real.log_mul hn0.ne' (by positivity), ← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log hpos ?_
    rw [hzs]
    nlinarith [mul_nonneg hs0 hB0, mul_nonneg hB0 hs0, mul_nonneg hn0.le hs0, mul_nonneg hn0.le hB0,
      mul_nonneg (mul_nonneg hn0.le hB0) hs0]
  have hlog2 : Real.log ((K : ℝ) * n) = Real.log K + Real.log n := Real.log_mul hK0.ne' hn0.ne'
  have hlog3 : -Real.log ‖z‖ ≤ Real.log 2 := by
    have : Real.log ((1 : ℝ) / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) hz2
    rw [one_div, Real.log_inv] at this
    linarith
  unfold RConst
  have c1 := mul_le_mul_of_nonneg_left hlog1 he0
  have c2 := mul_le_mul_of_nonneg_left hlog3 hr0
  rw [hlog2] at h
  nlinarith [c1, c2, h]

/-! ### 7. The binomial (atom) weights -/

/-- `x log x`. -/
noncomputable def xl (x : ℝ) : ℝ := x * Real.log x

lemma xl_scale {n a : ℝ} (hn : 0 < n) (ha : 0 ≤ a) :
    xl (n * a) = n * (a * Real.log n + xl a) := by
  unfold xl
  rcases ha.eq_or_lt with rfl | h
  · simp
  · rw [Real.log_mul hn.ne' h.ne']; ring

lemma mul_log_div' {a N : ℝ} (hN : 0 < N) (ha : 0 ≤ a) :
    a * Real.log (a / N) = a * (Real.log a - Real.log N) := by
  rcases ha.eq_or_lt with rfl | h
  · simp
  · rw [Real.log_div h.ne' hN.ne']

lemma N_binEntropy {N k : ℝ} (hN : 0 < N) (hk0 : 0 ≤ k) (hkN : k ≤ N) :
    N * Real.binEntropy (k / N) = xl N - xl k - xl (N - k) := by
  unfold xl
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  simp only [neg_mul]
  have h1 := mul_log_div' hN hk0
  have h2 : 1 - k / N = (N - k) / N := by field_simp
  have h3 := mul_log_div' hN (sub_nonneg.mpr hkN)
  rw [h2]
  have e1 : N * -(k / N * Real.log (k / N)) = -(k * Real.log (k / N)) := by field_simp
  have e2 : N * -((N - k) / N * Real.log ((N - k) / N)) = -((N - k) * Real.log ((N - k) / N)) := by
    field_simp
  rw [mul_add, e1, e2, h1, h3]
  ring

/-- The scaled log-coefficient rate `ω(x) = r [K log K - x log x - (K - x) log (K - x)]
+ e [(B + x) log (B + x) - x log x - B log B]`. -/
noncomputable def omegaFun (e r B K : ℕ) (x : ℝ) : ℝ :=
  r * (xl K - xl x - xl (K - x)) + e * (xl (B + x) - xl x - xl B)

/-- **Lemma W (atoms)**: `log (C(Kn, k)^r C(Bn + k, k)^e) ≤ n ω(k/n)` for `k ≤ Kn`. -/
theorem log_atom_le (e r B K n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ K * n) :
    Real.log (((K * n).choose k : ℝ) ^ r * (((B * n + k).choose k : ℝ)) ^ e) ≤
      (n : ℝ) * omegaFun e r B K ((k : ℝ) / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc1 : (0 : ℝ) < ((K * n).choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hc2 : (0 : ℝ) < (((B * n + k).choose k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [Real.log_mul (pow_pos hc1 r).ne' (pow_pos hc2 e).ne', Real.log_pow, Real.log_pow]
  have hKn : (0 : ℝ) < ((K * n : ℕ) : ℝ) ∨ K * n = 0 := by
    rcases Nat.eq_zero_or_pos (K * n) with h | h
    · right; exact h
    · left; exact_mod_cast h
  have hkR : (k : ℝ) ≤ (K : ℝ) * n := by exact_mod_cast hk
  set x : ℝ := (k : ℝ) / n with hx
  have hxn : (k : ℝ) = n * x := by rw [hx]; field_simp
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxK : x ≤ K := by
    rw [hx, div_le_iff₀ hn0]; linarith
  -- first coefficient
  have a1 : Real.log ((K * n).choose k : ℝ) ≤ n * (xl K - xl x - xl (K - x)) := by
    rcases hKn with hpos | hz
    · have h := CatalanMeasure.log_choose_le_mul_binEntropy (K * n) k hk
      refine h.trans (le_of_eq ?_)
      push_cast at hpos ⊢
      rw [N_binEntropy hpos (Nat.cast_nonneg k) hkR]
      have e1 : (K : ℝ) * n - k = n * (K - x) := by rw [hxn]; ring
      rw [e1, hxn, show (K : ℝ) * n = n * K by ring, xl_scale hn0 (Nat.cast_nonneg K),
        xl_scale hn0 hx0, xl_scale hn0 (sub_nonneg.mpr hxK)]
      ring
    · have hk0 : k = 0 := by omega
      subst hk0
      have : x = 0 := by rw [hx]; simp
      rw [this]
      simp [xl]
  -- second coefficient
  have a2 : Real.log ((B * n + k).choose k : ℝ) ≤ n * (xl (B + x) - xl x - xl B) := by
    have hle : k ≤ B * n + k := Nat.le_add_left _ _
    have h := CatalanMeasure.log_choose_le_mul_binEntropy (B * n + k) k hle
    have hpos : (0 : ℝ) < (((B * n + k : ℕ)) : ℝ) ∨ B * n + k = 0 := by
      rcases Nat.eq_zero_or_pos (B * n + k) with h | h
      · right; exact h
      · left; exact_mod_cast h
    rcases hpos with hp | hz
    · refine h.trans (le_of_eq ?_)
      push_cast at hp ⊢
      rw [N_binEntropy hp (Nat.cast_nonneg k) (by push_cast at *; linarith [mul_nonneg (Nat.cast_nonneg B) hn0.le])]
      have e1 : (B : ℝ) * n + k - k = n * B := by ring
      have e2 : (B : ℝ) * n + k = n * (B + x) := by rw [hxn]; ring
      rw [e1, e2, hxn, xl_scale hn0 (by positivity : (0 : ℝ) ≤ B + x), xl_scale hn0 hx0,
        xl_scale hn0 (Nat.cast_nonneg B)]
      ring
    · have hk0 : k = 0 := by omega
      have hb0 : B * n = 0 := by omega
      subst hk0
      have : x = 0 := by rw [hx]; simp
      rw [this]
      have hB0 : (B : ℝ) * n = 0 := by exact_mod_cast hb0
      have hB' : (B : ℝ) = 0 := by
        rcases mul_eq_zero.mp hB0 with h | h
        · exact h
        · exact absurd h hn0.ne'
      simp [xl, hB']
  unfold omegaFun
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  nlinarith [mul_le_mul_of_nonneg_left a1 hr0, mul_le_mul_of_nonneg_left a2 he0]

/-! ### 8. The jet kernel on the half-integer lines -/

lemma norm_sin_half {z : ℂ} {k : ℤ} (hz : z.re = (2 * k + 1) / 2) :
    (1 / 2 : ℝ) * Real.exp (Real.pi * |z.im|) ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  set w : ℂ := (Real.pi : ℂ) * z with hw
  have hwre : w.re = Real.pi * z.re := by simp [hw]
  have hwim : w.im = Real.pi * z.im := by simp [hw]
  have hcos : Real.cos w.re = 0 := by
    rw [Real.cos_eq_zero_iff]
    exact ⟨k, by rw [hwre, hz]; ring⟩
  have hsin : Real.sin w.re ^ 2 = 1 := by
    have h1 := Real.sin_sq_add_cos_sq w.re
    rw [hcos] at h1
    linarith
  have h4 : ‖Complex.sin w‖ = Real.cosh w.im := by
    have h := CatalanCore.Decay.norm_sin_sq w
    have h1 := Real.cosh_sq w.im
    refine (sq_eq_sq₀ (norm_nonneg _) (Real.cosh_pos _).le).1 ?_
    rw [h, hsin, h1]; ring
  have h3 : Real.cosh w.im ≤ ‖Complex.sin w‖ := h4.symm.le
  have h5 : (1 / 2 : ℝ) * Real.exp (Real.pi * |z.im|) ≤ Real.cosh w.im := by
    rw [hwim, ← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    have := Real.exp_pos (-(Real.pi * |z.im|))
    linarith
  linarith

/-- The jet bound on a half-integer line (no restriction on `Im z`):
`‖cotJet (n+1) z‖ ≤ (n+1)! · higherPoleK n (1/2) · e^{-2π|Im z|}`. -/
theorem norm_cotJet_succ_le_half (n : ℕ) {z : ℂ} {k : ℤ} (hz : z.re = (2 * k + 1) / 2) :
    ‖cotJet (n + 1) z‖ ≤
      ((n + 1).factorial : ℝ) * higherPoleK n (1 / 2) * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hsin := norm_sin_half hz
  have hne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsin
    have := Real.exp_pos (Real.pi * |z.im|)
    linarith
  rw [cotJet_succ n hne]
  have hb := norm_higherPoleClosed_le n (by norm_num : (0 : ℝ) < 1 / 2) hsin
  rw [norm_mul]
  have : ‖((n + 1).factorial : ℂ)‖ = ((n + 1).factorial : ℝ) := by simp
  rw [this, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- The constant of the half-line jet bound. -/
noncomputable def jetConstH (n : ℕ) : ℝ := ((n + 1).factorial : ℝ) * higherPoleK n (1 / 2)

/-- The constant of the combined `K_c` bound. -/
noncomputable def kcConst (J : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ j ∈ J, ‖c j‖ * (jetConst (j - 1) + jetConstH (j - 1))

lemma jetConst_nonneg (n : ℕ) : 0 ≤ jetConst n :=
  mul_nonneg (by positivity) (higherPoleK_nonneg n (by norm_num))

lemma jetConstH_nonneg (n : ℕ) : 0 ≤ jetConstH n :=
  mul_nonneg (by positivity) (higherPoleK_nonneg n (by norm_num))

/-- **Lemma W (`K_c`-part)**: on `|Im z| ≥ 1` and on every half-integer line `Re z = k + 1/2`,
`‖K_c z‖ ≤ kcConst J c · e^{-2π|Im z|}`. -/
theorem norm_Kc_le_good (J : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j) (c : ℕ → ℂ) {z : ℂ}
    (hz : 1 ≤ |z.im| ∨ ∃ k : ℤ, z.re = (2 * k + 1) / 2) :
    ‖Kc J c z‖ ≤ kcConst J c * Real.exp (-(2 * Real.pi * |z.im|)) := by
  unfold Kc kcConst
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by have := hJ j hj; omega⟩
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hn : n + 1 - 1 = n := by omega
  rw [hn]
  have hexp := Real.exp_pos (-(2 * Real.pi * |z.im|))
  rcases hz with h | ⟨k, hk⟩
  · have := norm_cotJet_succ_le n h
    have h2 : 0 ≤ jetConstH n := jetConstH_nonneg n
    have e : jetConst n = ((n + 1).factorial : ℝ) * higherPoleK n (1 / 4) := rfl
    rw [← e] at this
    nlinarith [this, mul_nonneg h2 hexp.le]
  · have := norm_cotJet_succ_le_half n hk
    have h2 : 0 ≤ jetConst n := jetConst_nonneg n
    have e : jetConstH n = ((n + 1).factorial : ℝ) * higherPoleK n (1 / 2) := rfl
    rw [← e] at this
    nlinarith [this, mul_nonneg h2 hexp.le]


/-! ### 9. The weight `R_n K_c` -/

lemma vField_two_pi (e r B K θ : ℝ) (s : ℂ) :
    CatalanCore.Decay.ComplexTaylor.vField e r B K θ s =
      CatalanCore.Decay.ComplexTaylor.vField e r B K 0 s - θ * |s.im| := by
  unfold CatalanCore.Decay.ComplexTaylor.vField
  ring

/-- **Lemma W** (LD05, weights): for `z` in the right half plane with `Im z ≠ 0`, `‖z‖ ≥ 1/2`, and
either `|Im z| ≥ 1` or `Re z ∈ ℤ + 1/2`,
`‖R_n z · K_c z‖ ≤ C_c · exp (n V(z/n) + C₀ + (r/2 + e) log n + e log (1 + ‖z/n‖))`,
where `V = vField e r B K (2π)` is the scaled field `Φ - 2π |Im s|`. -/
theorem norm_RKc_le {z : ℂ} (hz : z.im ≠ 0) (hre : 0 ≤ z.re) (hz2 : (1 : ℝ) / 2 ≤ ‖z‖)
    (hgood : 1 ≤ |z.im| ∨ ∃ k : ℤ, z.re = (2 * k + 1) / 2)
    (J : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j) (c : ℕ → ℂ) (e r B K n : ℕ)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (hn : 1 ≤ n) :
    ‖Rn e r B K n z * Kc J c z‖ ≤ kcConst J c *
      Real.exp ((n : ℝ) * CatalanCore.Decay.ComplexTaylor.vField (e : ℝ) (r : ℝ) (B : ℝ) (K : ℝ)
          (2 * Real.pi) (z / ((n : ℝ) : ℂ)) + RConst e r B K + ((r : ℝ) / 2 + e) * Real.log n +
        e * Real.log (1 + ‖z / ((n : ℝ) : ℂ)‖)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hRb := log_norm_Rn_le' hz hre hz2 e r B K n hB hK hn
  have hKb := norm_Kc_le_good J hJ c hgood
  have hexp : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos x).le
  have hRn : ‖Rn e r B K n z‖ ≤ Real.exp ((n : ℝ) *
      CatalanCore.Decay.ComplexTaylor.vField (e : ℝ) (r : ℝ) (B : ℝ) (K : ℝ) 0 (z / ((n : ℝ) : ℂ)) +
      RConst e r B K + ((r : ℝ) / 2 + e) * Real.log n + e * Real.log (1 + ‖z / ((n : ℝ) : ℂ)‖)) := by
    rcases (norm_nonneg (Rn e r B K n z)).eq_or_lt with h0 | hpos
    · rw [← h0]; exact hexp _
    · calc ‖Rn e r B K n z‖ = Real.exp (Real.log ‖Rn e r B K n z‖) := (Real.exp_log hpos).symm
        _ ≤ _ := Real.exp_le_exp.mpr hRb
  rw [norm_mul]
  have him : |(z / ((n : ℝ) : ℂ)).im| = |z.im| / n := by
    rw [Complex.div_ofReal_im, abs_div, abs_of_pos hn0]
  have hkc0 : 0 ≤ kcConst J c := by
    unfold kcConst
    exact Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _)
      (add_nonneg (jetConst_nonneg _) (jetConstH_nonneg _))
  calc ‖Rn e r B K n z‖ * ‖Kc J c z‖
      ≤ Real.exp ((n : ℝ) *
          CatalanCore.Decay.ComplexTaylor.vField (e : ℝ) (r : ℝ) (B : ℝ) (K : ℝ) 0 (z / ((n : ℝ) : ℂ)) +
          RConst e r B K + ((r : ℝ) / 2 + e) * Real.log n +
            e * Real.log (1 + ‖z / ((n : ℝ) : ℂ)‖)) *
        (kcConst J c * Real.exp (-(2 * Real.pi * |z.im|))) :=
        mul_le_mul hRn hKb (norm_nonneg _) (hexp _)
    _ = kcConst J c * Real.exp ((n : ℝ) *
          CatalanCore.Decay.ComplexTaylor.vField (e : ℝ) (r : ℝ) (B : ℝ) (K : ℝ) (2 * Real.pi)
            (z / ((n : ℝ) : ℂ)) + RConst e r B K + ((r : ℝ) / 2 + e) * Real.log n +
          e * Real.log (1 + ‖z / ((n : ℝ) : ℂ)‖)) := by
        rw [vField_two_pi _ _ _ _ (2 * Real.pi), him]
        have e1 : (n : ℝ) * (CatalanCore.Decay.ComplexTaylor.vField (e : ℝ) (r : ℝ) (B : ℝ) (K : ℝ) 0
            (z / ((n : ℝ) : ℂ)) - 2 * Real.pi * (|z.im| / n)) =
            (n : ℝ) * CatalanCore.Decay.ComplexTaylor.vField (e : ℝ) (r : ℝ) (B : ℝ) (K : ℝ) 0
              (z / ((n : ℝ) : ℂ)) - 2 * Real.pi * |z.im| := by
          field_simp
        rw [e1, mul_left_comm, ← Real.exp_add]
        congr 2
        ring

end CatalanCore.Decay.LemmaW
