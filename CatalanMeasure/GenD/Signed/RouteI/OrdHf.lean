module

public import CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
public import CatalanMeasure.GenD.Signed.RouteI.MomentSource
public import CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import CatalanMeasure.GenD.Signed.RouteI.CompactHf
public import CatalanMeasure.GenD.Signed.RouteI.MomentInputs
public import CatalanMeasure.GenD.Cert.WLog
public import CatalanMeasure.GenD.Signed.RouteI.AngularCap
public import CatalanMeasure.GenD.Signed.RouteI.CompactInstance
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Route I `OrdHf`: the ordinary compact fields of `capSource` lie below their polynomials

`posHf : PosHf capSource (Trunc.finite 384)` and `negHf : NegHf capSource (Trunc.finite 384)`.

The gas log potential is expanded in Chebyshev polynomials on `[0,1]`: the first 64 terms are exact,
and the tail is bounded by Bessel's inequality from a direct bound on the `L²` energy of the cell
densities. The reflection series is dropped by sign (positive species) or kept through the exact moments
(negative species). The radial field is a sum of 16 blocks, one for each radius. The polynomial part
goes exactly into the Chebyshev variable of the target; the part of degree at most 16 joins the blocks in a
one-dimensional function, bounded by a chord cover with the radii as nodes.

kcost: all `decide +kernel` of this file together measured 293 s of kernel time on 6 Nov, the largest 58 s;
heavy items are the rows (67 x 427 and 131 x 277 cell steps), the class
rows (16 x 94 cosine sums per species), and the node evaluations (62 and 63 nodes, 17 blocks of at most 96
terms each).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### The Poisson majorant of the direct kernel -/

theorem lsin_le_reg {r w : ℝ} (h0 : 0 < r) (h1 : r < 1) (hs : Real.sin (w / 2) ≠ 0) :
    lsin w ≤ reg r w + (1 / 2) * Real.log (1 / r) := by
  have hA : 4 * r * Real.sin (w / 2) ^ 2 ≤ 1 - 2 * r * Real.cos w + r ^ 2 := by
    rw [reg_arg]; nlinarith [sq_nonneg (1 - r)]
  have hp : 0 < 4 * r * Real.sin (w / 2) ^ 2 := by positivity
  have hl := Real.log_le_log hp hA
  have e : Real.log (4 * r * Real.sin (w / 2) ^ 2) =
      2 * Real.log 2 + Real.log r + 2 * Real.log (Real.sin (w / 2)) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      have : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [this, Real.log_pow]; push_cast; ring
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) h0.ne',
      Real.log_pow, h4]
    push_cast; ring
  rw [e] at hl
  have h3 : Real.log (1 / r) = -Real.log r := by rw [one_div, Real.log_inv]
  unfold lsin reg
  rw [h3]
  linarith

theorem reg_tail {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (w : ℝ) (M : ℕ) :
    |-(reg r w) - ∑ n ∈ Finset.range M, r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * w) / ((n : ℝ) + 1)|
      ≤ r ^ (M + 1) / (1 - r) := by
  have hs := (hasSum_nat_add_iff' (f := fun n : ℕ =>
    r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * w) / ((n : ℝ) + 1)) M).mpr (reg_hasSum h0 h1 w)
  have hg : HasSum (fun n : ℕ => r ^ (M + 1) * r ^ n) (r ^ (M + 1) * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one h0 h1).mul_left _
  have := hs.norm_le_of_bounded hg (fun n => ?_)
  · rw [Real.norm_eq_abs] at this
    rw [div_eq_mul_inv]; exact this
  · rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (pow_nonneg h0 _)]
    have hn : (1 : ℝ) ≤ |((n + M : ℕ) : ℝ) + 1| := by
      rw [abs_of_nonneg (by positivity)]
      have : (0 : ℝ) ≤ ((n + M : ℕ) : ℝ) := by positivity
      linarith
    have hc := Real.abs_cos_le_one ((((n + M : ℕ) : ℝ) + 1) * w)
    have e : r ^ (n + M + 1) = r ^ (M + 1) * r ^ n := by ring
    rw [e]
    calc r ^ (M + 1) * r ^ n * |Real.cos ((((n + M : ℕ) : ℝ) + 1) * w)| / |((n + M : ℕ) : ℝ) + 1|
        ≤ r ^ (M + 1) * r ^ n * |Real.cos ((((n + M : ℕ) : ℝ) + 1) * w)| := by
          exact div_le_self (by positivity) hn
      _ ≤ r ^ (M + 1) * r ^ n * 1 := by gcongr
      _ = r ^ (M + 1) * r ^ n := by ring

/-- Truncated Poisson majorant of `log|x - s|` on `(0,1]`. -/
theorem kernel_le {x s r : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1) (hne : s ≠ x)
    (h0 : 0 < r) (h1 : r < 1) (M : ℕ) :
    Real.log |x - s| + Real.log 4 ≤ Real.log (1 / r) -
      (∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) *
        (basis (n + 1) (2 * s - 1) * basis (n + 1) (2 * x - 1))) + 2 * (r ^ (M + 1) / (1 - r)) := by
  set θ := Real.arccos (2 * s - 1) with hθ
  set φ := Real.arccos (2 * x - 1) with hφ
  have es : sth θ = s := sth_arccos hs0.le hs1
  have ex : sth φ = x := sth_arccos hx0.le hx1
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hφ0 : 0 ≤ φ := Real.arccos_nonneg _
  have hθπ : θ ≤ π := Real.arccos_le_pi _
  have hφπ : φ ≤ π := Real.arccos_le_pi _
  have hφlt : φ < π := by
    refine lt_of_le_of_ne hφπ fun h => ?_
    have := sth_arccos hx0.le hx1
    rw [← hφ, h] at this
    have h2 : sth π = 0 := by simp [sth]
    rw [h2] at this
    linarith
  have hdiff : θ ≠ φ := by
    intro h
    apply hne
    rw [← es, ← ex, h]
  have hsub : Real.sin ((θ - φ) / 2) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    have hb1 : (θ - φ) / 2 < π := by nlinarith [Real.pi_pos]
    have hb2 : -π < (θ - φ) / 2 := by nlinarith [Real.pi_pos]
    rw [← hk] at hb1 hb2
    have hp := Real.pi_pos
    have k1 : (k : ℝ) < 1 := by nlinarith
    have k2 : -1 < (k : ℝ) := by nlinarith
    have : k = 0 := by
      have a1 : k < 1 := by exact_mod_cast k1
      have a2 : -1 < k := by exact_mod_cast k2
      omega
    rw [this] at hk
    apply hdiff
    simp only [Int.cast_zero, zero_mul] at hk
    linarith
  have hadd : Real.sin ((θ + φ) / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · rcases hθ0.lt_or_eq with h | h
      · linarith
      · rcases hφ0.lt_or_eq with h' | h'
        · linarith
        · exact absurd (by rw [← h, ← h']) hdiff
    · linarith
  have hk := log_sub_eq_lsin hadd hsub
  rw [es, ex] at hk
  have t1 := reg_tail h0.le h1 (θ + φ) M
  have t2 := reg_tail h0.le h1 (θ - φ) M
  have l1 := lsin_le_reg h0 h1 hadd
  have l2 := lsin_le_reg h0 h1 hsub
  have hpair : ∀ n ∈ Finset.range M,
      r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * (θ + φ)) / ((n : ℝ) + 1) +
        r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * (θ - φ)) / ((n : ℝ) + 1) =
      2 * r ^ (n + 1) / ((n : ℝ) + 1) *
        (basis (n + 1) (2 * s - 1) * basis (n + 1) (2 * x - 1)) := by
    intro n _
    have := cos_pair θ φ n
    have c1 : Real.cos θ = 2 * s - 1 := Real.cos_arccos (by linarith) (by linarith)
    have c2 : Real.cos φ = 2 * x - 1 := Real.cos_arccos (by linarith) (by linarith)
    rw [c1, c2] at this
    calc _ = r ^ (n + 1) * (Real.cos (((n : ℝ) + 1) * (θ + φ)) / ((n : ℝ) + 1) +
          Real.cos (((n : ℝ) + 1) * (θ - φ)) / ((n : ℝ) + 1)) := by ring
      _ = _ := by rw [this]; ring
  have hsum := Finset.sum_congr rfl hpair
  rw [Finset.sum_add_distrib] at hsum
  have u1 := (abs_le.mp t1).2
  have u2 := (abs_le.mp t2).2
  have u1' := (abs_le.mp t1).1
  have u2' := (abs_le.mp t2).1
  have h3 : Real.log (1 / r) = (1 / 2) * Real.log (1 / r) + (1 / 2) * Real.log (1 / r) := by ring
  linarith

/-! ### Integrating the majorant -/

/-- `n`-th Chebyshev moment of a cell in the physical variable. -/
def TF (n : ℕ) : ℝ → ℝ := fun s => basis n (2 * s - 1)

theorem phys_log_le {c : YCell} (h2 : 2 ≤ c.lo) {x r : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (h0 : 0 < r) (h1 : r < 1) (M : ℕ) :
    c.phys (fun s => Real.log |x - s|) + c.w * Real.log 4 ≤
      c.w * (Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r))) -
      ∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        c.phys (TF (n + 1)) := by
  have hlt := c.lo_lt
  have hd : 0 < c.hi - c.lo := by linarith
  set g := c.w / (c.hi - c.lo) with hg
  have hg0 : 0 ≤ g := div_nonneg c.w_nonneg hd.le
  set A : ℝ := Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r)) - Real.log 4 with hA
  set a : ℕ → ℝ := fun n => 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) with ha
  have hi1 := rowlog2_int h2 hlt hx0 hx1
  have hi2 : ∀ n ∈ Finset.range M, IntervalIntegrable
      (fun y => a n * basis (n + 1) (2 * YCell.physX y - 1)) volume c.lo c.hi :=
    fun n _ => (basisX_int h2 hlt (n + 1)).const_mul _
  have hi3 : IntervalIntegrable
      (fun y => ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX y - 1)) volume c.lo c.hi :=
    (IntervalIntegrable.sum (Finset.range M) hi2).congr (by
      intro y _
      simp [Finset.sum_apply])
  have hi4 : IntervalIntegrable
      (fun y => A - ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX y - 1))
      volume c.lo c.hi := intervalIntegrable_const.sub hi3
  have hle : ∫ y in c.lo..c.hi, Real.log |x - YCell.physX y| ≤
      ∫ y in c.lo..c.hi, (A - ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX y - 1)) := by
    apply intervalIntegral.integral_mono_ae_restrict hlt.le hi1 hi4
    have hae : ∀ᵐ Y ∂(volume : Measure ℝ), Y ∉ ({x + 1 / x} : Set ℝ) :=
      (Set.countable_singleton _).ae_notMem volume
    have hm := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Icc (a := c.lo) (b := c.hi))
    filter_upwards [ae_restrict_of_ae (s := Icc c.lo c.hi) hae, hm] with Y hY hYm
    have hY2 : 2 ≤ Y := h2.trans hYm.1
    obtain ⟨p0, p1⟩ := physX_mem hY2
    have hne : YCell.physX Y ≠ x := by
      intro he
      apply hY
      have := physX_add_inv hY2
      rw [he] at this
      exact Set.mem_singleton_iff.mpr this.symm
    have := kernel_le hx0 hx1 p0 p1 hne h0 h1 M
    have e : ∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) *
          (basis (n + 1) (2 * YCell.physX Y - 1) * basis (n + 1) (2 * x - 1)) =
        ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX Y - 1) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [ha]; ring
    rw [e] at this
    simp only [hA]
    linarith
  have hev : ∫ y in c.lo..c.hi, (A - ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX y - 1))
      = A * (c.hi - c.lo) - ∑ n ∈ Finset.range M, a n * ∫ y in c.lo..c.hi, basis (n + 1) (2 * YCell.physX y - 1) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi3, intervalIntegral.integral_const,
      intervalIntegral.integral_finsetSum hi2]
    simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  have hw : c.w = g * (c.hi - c.lo) := by rw [hg]; field_simp
  have hph : ∀ n, c.phys (TF n) = g * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1) := fun n => rfl
  have hl : c.phys (fun s => Real.log |x - s|) = g * ∫ y in c.lo..c.hi, Real.log |x - YCell.physX y| := rfl
  rw [hev] at hle
  have := mul_le_mul_of_nonneg_left hle hg0
  rw [hl]
  simp only [hph]
  have e2 : ∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        (g * ∫ y in c.lo..c.hi, basis (n + 1) (2 * YCell.physX y - 1)) =
      g * ∑ n ∈ Finset.range M, a n * ∫ y in c.lo..c.hi, basis (n + 1) (2 * YCell.physX y - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha]; ring
  rw [e2]
  have e3 : c.w * (Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r))) = g * (c.hi - c.lo) * (A + Real.log 4) := by
    rw [← hw]; simp only [hA]; ring
  rw [e3, hw]
  nlinarith [this]

theorem physL_log_le {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {x r : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (h0 : 0 < r) (h1 : r < 1) (M : ℕ) :
    physL l (fun s => Real.log |x - s|) + massL l * Real.log 4 ≤
      massL l * (Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r))) -
      ∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1)) := by
  induction l with
  | nil => simp [physL, massL]
  | cons c l ih =>
    have a1 := phys_log_le (h2 c (by simp)) hx0 hx1 h0 h1 M
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    have e2 : massL (c :: l) = c.w + massL l := by simp [massL]
    simp only [e1, e2, mul_add, Finset.sum_add_distrib, add_mul]
    linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### Cauchy-Schwarz tail and the limits -/

theorem sum_inv_sq_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ n ∈ Finset.Ico N M, (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rcases Nat.lt_or_ge M N with h | h
  · rw [Finset.Ico_eq_empty (by omega)]; simp
  have key : ∑ n ∈ Finset.Ico N M, (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
    induction M, h using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top hM]
      have hM0 : (0 : ℝ) < M := lt_of_lt_of_le hN0 (by exact_mod_cast hM)
      have : (1 / ((M : ℝ) + 1)) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ hM0.ne' (by positivity), div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  have : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
  linarith

theorem tail_cs {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (mu b : ℕ → ℝ) (hb : ∀ n, |b n| ≤ 1) {B T : ℝ}
    (hB : ∑ n ∈ Finset.Ico N M, (mu n) ^ 2 ≤ B) (hT : 0 ≤ T) (hBT : 4 * B ≤ (N : ℝ) * T ^ 2) :
    |∑ n ∈ Finset.Ico N M, 2 / ((n : ℝ) + 1) * b n * mu n| ≤ T := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico N M) (fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun n => 2 * b n * mu n)
  have e1 : ∑ n ∈ Finset.Ico N M, 1 / ((n : ℝ) + 1) * (2 * b n * mu n) =
      ∑ n ∈ Finset.Ico N M, 2 / ((n : ℝ) + 1) * b n * mu n :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [e1] at hcs
  have e2 : ∑ n ∈ Finset.Ico N M, (2 * b n * mu n) ^ 2 ≤ 4 * B := by
    calc ∑ n ∈ Finset.Ico N M, (2 * b n * mu n) ^ 2 ≤ ∑ n ∈ Finset.Ico N M, 4 * (mu n) ^ 2 := by
          refine Finset.sum_le_sum fun n _ => ?_
          have : (b n) ^ 2 ≤ 1 := by
            have := hb n
            rw [← sq_abs]
            nlinarith [abs_nonneg (b n)]
          nlinarith [sq_nonneg (mu n)]
      _ = 4 * ∑ n ∈ Finset.Ico N M, (mu n) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * B := by linarith
  have e3 := sum_inv_sq_le hN M
  have hpos : 0 ≤ ∑ n ∈ Finset.Ico N M, (2 * b n * mu n) ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have hpos1 : 0 ≤ ∑ n ∈ Finset.Ico N M, (1 / ((n : ℝ) + 1)) ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have hB0 : 0 ≤ 4 * B := hpos.trans e2
  have e4 : (∑ n ∈ Finset.Ico N M, 2 / ((n : ℝ) + 1) * b n * mu n) ^ 2 ≤ T ^ 2 := by
    calc _ ≤ (∑ n ∈ Finset.Ico N M, (1 / ((n : ℝ) + 1)) ^ 2) *
          ∑ n ∈ Finset.Ico N M, (2 * b n * mu n) ^ 2 := hcs
      _ ≤ (1 / (N : ℝ)) * (4 * B) := mul_le_mul e3 e2 hpos (by positivity)
      _ ≤ T ^ 2 := by
        rw [one_div, inv_mul_le_iff₀ hN0]; exact hBT
  exact abs_le_of_sq_le_sq e4 hT

/-- **Gas direct term.** The truncated Chebyshev upper bound of the direct potential, the tail
being controlled by any `L²` bound `B` of the moment tail. -/
theorem gas_upper {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {B T : ℝ}
    (hB : ∀ M, ∑ n ∈ Finset.Ico N M, (physL l (TF (n + 1))) ^ 2 ≤ B) (hT : 0 ≤ T)
    (hBT : 4 * B ≤ (N : ℝ) * T ^ 2) :
    physL l (fun s => Real.log |x - s|) + massL l * Real.log 4 ≤
      T - ∑ n ∈ Finset.range N, 2 / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1)) := by
  set m := massL l
  set LHS := physL l (fun s => Real.log |x - s|) + m * Real.log 4 with hLHS
  have hz : 2 * x - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have step : ∀ r : ℝ, 0 < r → r < 1 → LHS ≤ m * Real.log (1 / r) + T -
      ∑ n ∈ Finset.range N, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1)) := by
    intro r h0 h1
    set Sg := ∑ n ∈ Finset.range N, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1)) with hSg
    have ht : Tendsto (fun M : ℕ => m * (Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r))) + T - Sg)
        atTop (𝓝 (m * (Real.log (1 / r) + 2 * (0 / (1 - r))) + T - Sg)) := by
      have p := (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)
      exact ((((p.div_const (1 - r)).const_mul 2).const_add _).const_mul m |>.add_const T).sub_const Sg
    have ht' : m * (Real.log (1 / r) + 2 * (0 / (1 - r))) + T - Sg = m * Real.log (1 / r) + T - Sg := by
      simp
    rw [ht'] at ht
    refine ge_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    have a1 := physL_log_le h2 hx0 hx1 h0 h1 M
    have a2 := Finset.sum_range_add_sum_Ico (fun n : ℕ => 2 * r ^ (n + 1) / ((n : ℝ) + 1) *
      basis (n + 1) (2 * x - 1) * physL l (TF (n + 1))) hM
    have a3 := tail_cs hN M (fun n => physL l (TF (n + 1)))
      (fun n => r ^ (n + 1) * basis (n + 1) (2 * x - 1)) (fun n => by
        rw [abs_mul, abs_of_nonneg (pow_nonneg h0.le _)]
        have q1 := abs_basis_le_one (n + 1) hz
        have q2 : r ^ (n + 1) ≤ 1 := pow_le_one₀ h0.le h1.le
        have q3 := abs_nonneg (basis (n + 1) (2 * x - 1))
        have q4 : 0 ≤ r ^ (n + 1) := pow_nonneg h0.le _
        nlinarith) (hB M) hT hBT
    have e : ∑ n ∈ Finset.Ico N M, 2 / ((n : ℝ) + 1) * (r ^ (n + 1) * basis (n + 1) (2 * x - 1)) *
          physL l (TF (n + 1)) =
        ∑ n ∈ Finset.Ico N M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
          physL l (TF (n + 1)) := Finset.sum_congr rfl fun n _ => by ring
    rw [e] at a3
    have a4 := (abs_le.mp a3).1
    simp only [← hSg] at a2
    simp only [hLHS]
    linarith
  set Q := ∑ n ∈ Finset.range N, 2 / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
      physL l (TF (n + 1)) with hQ
  have hc : ContinuousAt (fun r : ℝ => m * Real.log (1 / r) + T -
      ∑ n ∈ Finset.range N, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1))) 1 := by
    have h1 : ContinuousAt (fun r : ℝ => Real.log (1 / r)) 1 :=
      ContinuousAt.log (continuousAt_const.div continuousAt_id (by norm_num)) (by norm_num)
    refine ((h1.const_mul m).add continuousAt_const).sub ?_
    refine tendsto_finsetSum _ fun n _ => ?_
    have : ContinuousAt (fun r : ℝ => 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
      physL l (TF (n + 1))) 1 := by fun_prop
    exact this
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  have ev : (m * Real.log (1 / (1 : ℝ)) + T -
      ∑ n ∈ Finset.range N, 2 * (1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1))) = T - Q := by
    simp [hQ]
  rw [ev] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
  exact step r hr.1 hr.2

/-! ### Orthogonality of cosines on `[0,π]` -/

theorem int_cos_int {k : ℤ} (hk : k ≠ 0) : ∫ θ in (0 : ℝ)..π, Real.cos ((k : ℝ) * θ) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hk', integral_cos]
  simp [Real.sin_int_mul_pi]

theorem cos_mul_cos (m n : ℕ) (θ : ℝ) : Real.cos ((m : ℝ) * θ) * Real.cos ((n : ℝ) * θ) =
    (Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * θ) + Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * θ)) / 2 := by
  push_cast
  rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
  ring

theorem cos_int_continuous (k : ℤ) : Continuous fun θ : ℝ => Real.cos ((k : ℝ) * θ) := by fun_prop

theorem int_cos_cos {m n : ℕ} (h : m ≠ n) :
    ∫ θ in (0 : ℝ)..π, Real.cos ((m : ℝ) * θ) * Real.cos ((n : ℝ) * θ) = 0 := by
  simp only [cos_mul_cos]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((cos_int_continuous _).intervalIntegrable _ _) ((cos_int_continuous _).intervalIntegrable _ _),
    int_cos_int (by omega), int_cos_int (by omega)]
  simp

theorem int_cos_sq {n : ℕ} (h : n ≠ 0) :
    ∫ θ in (0 : ℝ)..π, Real.cos ((n : ℝ) * θ) * Real.cos ((n : ℝ) * θ) = π / 2 := by
  simp only [cos_mul_cos]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((cos_int_continuous _).intervalIntegrable _ _) ((cos_int_continuous _).intervalIntegrable _ _),
    int_cos_int (k := (n : ℤ) + n) (by omega)]
  simp

/-- The cosine polynomial. -/
def cosS (b : ℕ → ℝ) (M : ℕ) (θ : ℝ) : ℝ := ∑ n ∈ Finset.range M, b n * Real.cos ((n : ℝ) * θ)

theorem cosS_continuous (b : ℕ → ℝ) (M : ℕ) : Continuous (cosS b M) := by
  unfold cosS; fun_prop

theorem int_cosS_mul (b : ℕ → ℝ) {M k : ℕ} (hk : M ≤ k) :
    ∫ θ in (0 : ℝ)..π, cosS b M θ * Real.cos ((k : ℝ) * θ) = 0 := by
  unfold cosS
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun n _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  refine Finset.sum_eq_zero fun n hn => ?_
  simp only [mul_assoc]
  rw [intervalIntegral.integral_const_mul, int_cos_cos (by have := Finset.mem_range.mp hn; omega)]
  simp

theorem int_cosS_sq (b : ℕ → ℝ) (M : ℕ) :
    ∫ θ in (0 : ℝ)..π, (cosS b (M + 1) θ) ^ 2 =
      π * (b 0) ^ 2 + (π / 2) * ∑ n ∈ Finset.range M, (b (n + 1)) ^ 2 := by
  induction M with
  | zero => simp [cosS]
  | succ M ih =>
    have e : ∀ θ, (cosS b (M + 1 + 1) θ) ^ 2 = (cosS b (M + 1) θ) ^ 2 +
        2 * b (M + 1) * (cosS b (M + 1) θ * Real.cos (((M + 1 : ℕ) : ℝ) * θ)) +
        (b (M + 1)) ^ 2 * (Real.cos (((M + 1 : ℕ) : ℝ) * θ) * Real.cos (((M + 1 : ℕ) : ℝ) * θ)) := by
      intro θ
      have : cosS b (M + 1 + 1) θ = cosS b (M + 1) θ + b (M + 1) * Real.cos (((M + 1 : ℕ) : ℝ) * θ) := by
        unfold cosS; rw [Finset.sum_range_succ _ (M + 1)]
      rw [this]; ring
    simp only [e]
    have c1 := cosS_continuous b (M + 1)
    rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ih,
      int_cosS_mul b le_rfl, int_cos_sq (by omega), Finset.sum_range_succ]
    ring

/-! ### Bessel on the disjoint cells -/

/-- Density of a cell. -/
def gc (c : YCell) : ℝ := c.w / (c.hi - c.lo)

/-- `∫ h² dθ` of the physical density `h = g_c bet`. -/
def G2 (l : List YCell) : ℝ :=
  (l.map fun c => gc c ^ 2 * ∫ θ in Th c.lo..Th c.hi, bet θ ^ 2).sum

/-- Sorted disjoint cells above `a`. -/
def Sep : ℝ → List YCell → Prop
  | _, [] => True
  | a, c :: l => a ≤ c.lo ∧ Sep c.hi l

theorem bet_continuousOn {a b : ℝ} (h0 : 0 ≤ a) (h1 : b < π) : ContinuousOn bet (Icc a b) := by
  unfold bet
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    (by fun_prop))
  intro θ hθ
  have := cos_half_pos (h0.trans hθ.1) (lt_of_le_of_lt hθ.2 h1)
  positivity

theorem cross {c : YCell} (h2 : 2 ≤ c.lo) (b : ℕ → ℝ) (M : ℕ) :
    ∫ θ in Th c.lo..Th c.hi, bet θ * cosS b M θ =
      ∑ n ∈ Finset.range M, b n * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1) := by
  have hlt := c.lo_lt
  have hs := subst_Y h2 hlt (fun y => ∑ n ∈ Finset.range M, b n * basis n (2 * YCell.physX y - 1))
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hab := Th_lt h2 hlt
  have hc : ∫ θ in Th c.lo..Th c.hi, bet θ * cosS b M θ = ∫ θ in Th c.lo..Th c.hi, bet θ *
      ∑ n ∈ Finset.range M, b n * basis n (2 * YCell.physX (Yth θ) - 1) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hab.le] at hθ
    have h0 : 0 ≤ θ := ml.1.trans hθ.1
    have h1 : θ < π := lt_of_le_of_lt hθ.2 mh.2
    simp only [cosS]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [physX_Yth h0 h1, two_sth_sub, basis_cos]
  rw [hc, ← hs, intervalIntegral.integral_finsetSum
    (fun n _ => (basisX_int h2 hlt n).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

theorem cell_bessel {c : YCell} (h2 : 2 ≤ c.lo) (b : ℕ → ℝ) (M : ℕ) :
    2 * ∑ n ∈ Finset.range M, b n * c.phys (TF n) ≤
      gc c ^ 2 * (∫ θ in Th c.lo..Th c.hi, bet θ ^ 2) +
        ∫ θ in Th c.lo..Th c.hi, (cosS b M θ) ^ 2 := by
  have hlt := c.lo_lt
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hab := Th_lt h2 hlt
  have hbc : ContinuousOn bet (uIcc (Th c.lo) (Th c.hi)) := by
    rw [uIcc_of_le hab.le]; exact bet_continuousOn ml.1 mh.2
  have hSc := cosS_continuous b M
  have i1 : IntervalIntegrable (fun θ => gc c ^ 2 * bet θ ^ 2) volume (Th c.lo) (Th c.hi) :=
    (continuousOn_const.mul (hbc.pow 2)).intervalIntegrable
  have i1' : IntervalIntegrable (fun θ => bet θ ^ 2) volume (Th c.lo) (Th c.hi) :=
    (hbc.pow 2).intervalIntegrable
  have i2 : IntervalIntegrable (fun θ => 2 * gc c * (bet θ * cosS b M θ)) volume (Th c.lo) (Th c.hi) :=
    (continuousOn_const.mul (hbc.mul hSc.continuousOn)).intervalIntegrable
  have i2' : IntervalIntegrable (fun θ => bet θ * cosS b M θ) volume (Th c.lo) (Th c.hi) :=
    (hbc.mul hSc.continuousOn).intervalIntegrable
  have i3 : IntervalIntegrable (fun θ => (cosS b M θ) ^ 2) volume (Th c.lo) (Th c.hi) :=
    (hSc.pow 2).intervalIntegrable _ _
  have hnn : 0 ≤ ∫ θ in Th c.lo..Th c.hi, (gc c * bet θ - cosS b M θ) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun θ _ => sq_nonneg _
  have e : ∫ θ in Th c.lo..Th c.hi, (gc c * bet θ - cosS b M θ) ^ 2 =
      gc c ^ 2 * (∫ θ in Th c.lo..Th c.hi, bet θ ^ 2) -
        2 * gc c * (∫ θ in Th c.lo..Th c.hi, bet θ * cosS b M θ) +
        ∫ θ in Th c.lo..Th c.hi, (cosS b M θ) ^ 2 := by
    have : ∀ θ, (gc c * bet θ - cosS b M θ) ^ 2 = gc c ^ 2 * bet θ ^ 2 -
        2 * gc c * (bet θ * cosS b M θ) + (cosS b M θ) ^ 2 := fun θ => by ring
    simp only [this]
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [e, cross h2] at hnn
  have e2 : gc c * ∑ n ∈ Finset.range M, b n * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1) =
      ∑ n ∈ Finset.range M, b n * c.phys (TF n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    show _ = b n * (gc c * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1))
    ring
  have e3 : 2 * gc c * ∑ n ∈ Finset.range M, b n * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1) =
      2 * ∑ n ∈ Finset.range M, b n * c.phys (TF n) := by rw [← e2]; ring
  rw [e3] at hnn
  linarith

theorem Th_le {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) : Th a ≤ Th b := by
  rcases hab.lt_or_eq with h | rfl
  · exact (Th_lt h2 h).le
  · exact le_rfl

theorem bessel_list {l : List YCell} {a : ℝ} (ha : 2 ≤ a) (hs : Sep a l) (b : ℕ → ℝ) (M : ℕ) :
    2 * ∑ n ∈ Finset.range M, b n * physL l (TF n) ≤
      G2 l + ∫ θ in Th a..π, (cosS b M θ) ^ 2 := by
  have hSc := (cosS_continuous b M).pow 2
  induction l generalizing a with
  | nil =>
    simp only [physL, G2, List.map_nil, List.sum_nil, mul_zero, Finset.sum_const_zero, zero_add]
    exact intervalIntegral.integral_nonneg (Th_mem ha).2.le fun θ _ => sq_nonneg _
  | cons c l ih =>
    obtain ⟨h1, h3⟩ := hs
    have hc2 : 2 ≤ c.lo := ha.trans h1
    have hh2 : 2 ≤ c.hi := hc2.trans c.lo_lt.le
    have A := cell_bessel hc2 b M
    have Bq := ih hh2 h3
    have e1 : ∀ n, physL (c :: l) (TF n) = c.phys (TF n) + physL l (TF n) := fun n => by
      simp [physL]
    have e2 : G2 (c :: l) = gc c ^ 2 * (∫ θ in Th c.lo..Th c.hi, bet θ ^ 2) + G2 l := by
      simp [G2]
    have i := fun u v => hSc.intervalIntegrable (μ := volume) u v
    have s1 := intervalIntegral.integral_add_adjacent_intervals (i (Th c.lo) (Th c.hi)) (i (Th c.hi) π)
    have s2 := intervalIntegral.integral_add_adjacent_intervals (i (Th a) (Th c.lo)) (i (Th c.lo) π)
    have s3 : 0 ≤ ∫ θ in Th a..Th c.lo, (cosS b M θ) ^ 2 :=
      intervalIntegral.integral_nonneg (Th_le ha h1) fun θ _ => sq_nonneg _
    simp only [e1, mul_add, Finset.sum_add_distrib, e2]
    simp only [Pi.pow_apply] at s1 s2
    linarith

/-- **Bessel inequality** for the physical density on sorted disjoint cells. -/
theorem bessel {l : List YCell} {a : ℝ} (ha : 2 ≤ a) (hs : Sep a l) (M : ℕ) :
    (physL l (TF 0)) ^ 2 / 2 + ∑ n ∈ Finset.range M, (physL l (TF (n + 1))) ^ 2 ≤ π / 2 * G2 l := by
  set b : ℕ → ℝ := fun n => if n = 0 then physL l (TF 0) / π else 2 * physL l (TF n) / π with hb
  have hp := Real.pi_pos
  have A := bessel_list ha hs b (M + 1)
  have hSc := (cosS_continuous b (M + 1)).pow 2
  have i := fun u v => hSc.intervalIntegrable (μ := volume) u v
  have s1 := intervalIntegral.integral_add_adjacent_intervals (i 0 (Th a)) (i (Th a) π)
  have s3 : 0 ≤ ∫ θ in (0 : ℝ)..Th a, (cosS b (M + 1) θ) ^ 2 :=
    intervalIntegral.integral_nonneg (Th_mem ha).1 fun θ _ => sq_nonneg _
  simp only [Pi.pow_apply] at s1
  rw [int_cosS_sq] at s1
  have e0 : b 0 = physL l (TF 0) / π := by simp [hb]
  have e1 : ∀ n, b (n + 1) = 2 * physL l (TF (n + 1)) / π := fun n => by simp [hb]
  rw [Finset.sum_range_succ'] at A
  simp only [e0, e1] at A s1
  have q1 : ∑ n ∈ Finset.range M, (2 * physL l (TF (n + 1)) / π) * physL l (TF (n + 1)) =
      2 / π * ∑ n ∈ Finset.range M, (physL l (TF (n + 1))) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  have q2 : ∑ n ∈ Finset.range M, (2 * physL l (TF (n + 1)) / π) ^ 2 =
      4 / π ^ 2 * ∑ n ∈ Finset.range M, (physL l (TF (n + 1))) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  rw [q1] at A
  rw [q2] at s1
  set Q := ∑ n ∈ Finset.range M, (physL l (TF (n + 1))) ^ 2
  set m0 := physL l (TF 0)
  have key : 2 * (2 / π * Q + m0 / π * m0) ≤ G2 l + (π * (m0 / π) ^ 2 + π / 2 * (4 / π ^ 2 * Q)) := by
    linarith
  have r1 : π * (m0 / π) ^ 2 = m0 ^ 2 / π := by field_simp
  have r2 : π / 2 * (4 / π ^ 2 * Q) = 2 / π * Q := by field_simp; ring
  rw [r1, r2] at key
  have r3 : m0 ^ 2 / π + 2 / π * Q ≤ G2 l := by
    have : 2 * (2 / π * Q + m0 / π * m0) = 2 * (2 / π * Q) + 2 * (m0 ^ 2 / π) := by ring
    linarith
  have r4 := mul_le_mul_of_nonneg_left r3 (by positivity : (0 : ℝ) ≤ π / 2)
  have r5 : π / 2 * (m0 ^ 2 / π + 2 / π * Q) = m0 ^ 2 / 2 + Q := by field_simp
  linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### The `L²` norm of the density on one cell, without roots -/

/-- `W²`, the square of `bet` in the `Y` coordinate. -/
def Wsq (y : ℝ) : ℝ := (y ^ 2 - 4) * (1 / YCell.physX y - 1)

theorem Th_Yth {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) : Th (Yth θ) = θ := by
  unfold Th
  rw [physX_Yth h0 h1, two_sth_sub, Real.arccos_cos h0 h1.le]

theorem bet_Th_sq {y : ℝ} (h2 : 2 ≤ y) : bet (Th y) ^ 2 = Wsq y := by
  obtain ⟨p0, p1⟩ := physX_mem h2
  obtain ⟨t0, t1⟩ := Th_mem h2
  rw [bet_eq_bb t0 t1, sth_Th h2]
  unfold Wsq
  have hy := physX_add_inv h2
  set x := YCell.physX y
  have hq : 0 ≤ (1 - x) / x := div_nonneg (by linarith) p0.le
  have hs := Real.sq_sqrt hq
  unfold bb
  rw [mul_pow, mul_pow, hs, ← hy]
  field_simp
  ring

theorem Wsq_eq {y : ℝ} (h2 : 2 ≤ y) :
    Wsq y = (y ^ 2 - 4) * (y - 2) / 2 + (y ^ 2 - 4) ^ (3 / 2 : ℝ) / 2 := by
  have ht : 0 ≤ y ^ 2 - 4 := by nlinarith
  have hx : 1 / YCell.physX y = (y + √(y ^ 2 - 4)) / 2 := by
    unfold YCell.physX
    rw [_root_.if_pos (by linarith)]
    have : 0 < y + √(y ^ 2 - 4) := by have := Real.sqrt_nonneg (y ^ 2 - 4); linarith
    field_simp
  have hr : (y ^ 2 - 4) ^ (3 / 2 : ℝ) = (y ^ 2 - 4) * √(y ^ 2 - 4) := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' ht (by norm_num), Real.rpow_one]
  unfold Wsq
  rw [hx, hr]
  ring

theorem Wsq_convex : ConvexOn ℝ (Ici 2) Wsq := by
  have c1 : ConvexOn ℝ (Ici (2 : ℝ)) fun y : ℝ => (y ^ 2 - 4) * (y - 2) / 2 := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 2)
      (f' := fun y => (3 * y ^ 2 - 4 * y - 4) / 2) (f'' := fun y => 3 * y - 2) (by fun_prop) ?_ ?_ ?_
    · intro y _
      have : HasDerivAt (fun y : ℝ => (y ^ 2 - 4) * (y - 2) / 2) ((3 * y ^ 2 - 4 * y - 4) / 2) y := by
        have h := (((hasDerivAt_pow 2 y).sub_const 4).mul ((hasDerivAt_id y).sub_const 2)).div_const 2
        refine h.congr_deriv ?_
        try simp only [id]
        push_cast; ring
      exact this.hasDerivWithinAt
    · intro y _
      have : HasDerivAt (fun y : ℝ => (3 * y ^ 2 - 4 * y - 4) / 2) (3 * y - 2) y := by
        have h := ((((hasDerivAt_pow 2 y).const_mul 3).sub ((hasDerivAt_id y).const_mul 4)).sub_const 4).div_const 2
        refine h.congr_deriv ?_
        try simp only [id]
        push_cast; ring
      exact this.hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have : (2 : ℝ) < y := hy
      show 0 ≤ 3 * y - 2
      linarith
  have c2 : ConvexOn ℝ (Ici (2 : ℝ)) fun y : ℝ => y ^ 2 - 4 := by
    have h := (convexOn_pow (𝕜 := ℝ) 2).subset
      (show Ici (2 : ℝ) ⊆ Ici 0 from fun y (hy : (2 : ℝ) ≤ y) => show (0 : ℝ) ≤ y by linarith) (convex_Ici 2)
    exact (h.add_const (-4)).congr (fun y _ => by show y ^ 2 + (-4) = y ^ 2 - 4; ring)
  have c3 : ConvexOn ℝ (Ici (2 : ℝ)) fun y : ℝ => (y ^ 2 - 4) ^ (3 / 2 : ℝ) := by
    have himg : (fun y : ℝ => y ^ 2 - 4) '' Ici 2 ⊆ Ici 0 := by
      rintro _ ⟨y, hy, rfl⟩
      have : (2 : ℝ) ≤ y := hy
      show 0 ≤ y ^ 2 - 4
      nlinarith
    have hconv : Convex ℝ ((fun y : ℝ => y ^ 2 - 4) '' Ici 2) := by
      have : (fun y : ℝ => y ^ 2 - 4) '' Ici 2 = Ici 0 := by
        refine Subset.antisymm himg ?_
        intro t ht
        have ht' : (0 : ℝ) ≤ t := ht
        refine ⟨√(t + 4), ?_, ?_⟩
        · show (2 : ℝ) ≤ √(t + 4)
          apply Real.le_sqrt_of_sq_le
          linarith
        · show √(t + 4) ^ 2 - 4 = t
          rw [Real.sq_sqrt (by linarith)]; ring
      rw [this]; exact convex_Ici 0
    have g := ((convexOn_rpow (p := 3 / 2) (by norm_num)).subset himg hconv)
    refine g.comp c2 ?_
    intro a ha b hb hab
    exact Real.rpow_le_rpow (himg ha) hab (by norm_num)
  have c4 := (c1.add (c3.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)))
  refine c4.congr ?_
  intro y hy
  have : (2 : ℝ) ≤ y := hy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Wsq_eq this]
  ring

theorem Th_continuousOn {lo hi : ℝ} (h2 : 2 ≤ lo) : ContinuousOn Th (Icc lo hi) := by
  have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
  unfold Th
  exact Real.continuous_arccos.comp_continuousOn ((continuousOn_const.mul hc).sub continuousOn_const)

theorem int_bet_sq {lo hi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) :
    ∫ θ in Th lo..Th hi, bet θ ^ 2 = ∫ y in lo..hi, bet (Th y) := by
  rw [subst_Y h2 hlt (fun y => bet (Th y))]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  rw [uIcc_of_le (Th_lt h2 hlt).le] at hθ
  simp only
  rw [Th_Yth (ml.1.trans hθ.1) (lt_of_le_of_lt hθ.2 mh.2)]
  ring

/-- The cell `L²` integral by AM-GM against any `lam > 0` and the chord of the convex `W²`. -/
theorem cell_bet_sq {lo hi lam Vlo Vhi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (hl : 0 < lam)
    (h1 : Wsq lo ≤ Vlo) (h3 : Wsq hi ≤ Vhi) :
    ∫ θ in Th lo..Th hi, bet θ ^ 2 ≤ (hi - lo) * (lam / 2 + (Vlo + Vhi) / (4 * lam)) := by
  rw [int_bet_sq h2 hlt]
  have hd : 0 < hi - lo := by linarith
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hW : ContinuousOn (fun y => bet (Th y)) (Icc lo hi) := by
    refine (bet_continuousOn ml.1 mh.2).comp (Th_continuousOn h2) ?_
    intro y hy
    exact ⟨Th_le h2 hy.1, Th_le (h2.trans hy.1) hy.2⟩
  set A : ℝ → ℝ := fun y => lam / 2 + (Vlo * (hi - y) + Vhi * (y - lo)) / (hi - lo) / (2 * lam) with hA
  have hAc : Continuous A := by simp only [hA]; fun_prop
  have hle : ∫ y in lo..hi, bet (Th y) ≤ ∫ y in lo..hi, A y := by
    apply intervalIntegral.integral_mono_on hlt.le (hW.intervalIntegrable_of_Icc hlt.le)
      (hAc.intervalIntegrable _ _)
    intro y hy
    have hy2 : 2 ≤ y := h2.trans hy.1
    have hsq := bet_Th_sq hy2
    have hch : Wsq y ≤ (Vlo * (hi - y) + Vhi * (y - lo)) / (hi - lo) := by
      have a0 : 0 ≤ (hi - y) / (hi - lo) := div_nonneg (by linarith [hy.2]) hd.le
      have b0 : 0 ≤ (y - lo) / (hi - lo) := div_nonneg (by linarith [hy.1]) hd.le
      have ab : (hi - y) / (hi - lo) + (y - lo) / (hi - lo) = 1 := by field_simp; ring
      have := Wsq_convex.2 (show lo ∈ Ici (2 : ℝ) from h2) (show hi ∈ Ici (2 : ℝ) from h2.trans hlt.le)
        a0 b0 ab
      have e : ((hi - y) / (hi - lo)) • lo + ((y - lo) / (hi - lo)) • hi = y := by
        simp only [smul_eq_mul]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd.ne']
        ring
      rw [e] at this
      simp only [smul_eq_mul] at this
      have q1 := mul_le_mul_of_nonneg_left h1 a0
      have q2 := mul_le_mul_of_nonneg_left h3 b0
      calc Wsq y ≤ _ := this
        _ ≤ (hi - y) / (hi - lo) * Vlo + (y - lo) / (hi - lo) * Vhi := by linarith
        _ = _ := by field_simp
    have amgm : bet (Th y) ≤ lam / 2 + Wsq y / (2 * lam) := by
      rw [← hsq]
      have : lam / 2 + bet (Th y) ^ 2 / (2 * lam) - bet (Th y) = (bet (Th y) - lam) ^ 2 / (2 * lam) := by
        field_simp; ring
      have h4 : 0 ≤ (bet (Th y) - lam) ^ 2 / (2 * lam) := by positivity
      linarith
    have : Wsq y / (2 * lam) ≤ (Vlo * (hi - y) + Vhi * (y - lo)) / (hi - lo) / (2 * lam) := by
      gcongr
    simp only [hA]
    linarith
  refine hle.trans (le_of_eq ?_)
  have hpr : ∀ y ∈ uIcc lo hi, HasDerivAt
      (fun y => lam / 2 * y + (Vlo * (hi * y - y ^ 2 / 2) + Vhi * (y ^ 2 / 2 - lo * y)) / (hi - lo) / (2 * lam))
      (A y) y := by
    intro y _
    have d2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
      have := (hasDerivAt_pow 2 y).div_const 2
      refine this.congr_deriv ?_
      push_cast; ring
    have d1 := hasDerivAt_id y
    have h := ((d1.const_mul (lam / 2)).add
      (((((d1.const_mul hi).sub d2).const_mul Vlo).add
        ((d2.sub (d1.const_mul lo)).const_mul Vhi)).div_const (hi - lo) |>.div_const (2 * lam)))
    refine h.congr_deriv ?_
    simp only [hA, id]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hpr (hAc.intervalIntegrable _ _)]
  field_simp
  ring

/-- Bessel gives the moment tail. -/
theorem tail_of_bessel {l : List YCell} {a : ℝ} (ha : 2 ≤ a) (hs : Sep a l) {N : ℕ} {Bq : ℝ}
    (hBq : π / 2 * G2 l - ((physL l (TF 0)) ^ 2 / 2 + ∑ n ∈ Finset.range N, (physL l (TF (n + 1))) ^ 2) ≤ Bq)
    (M : ℕ) : ∑ n ∈ Finset.Ico N M, (physL l (TF (n + 1))) ^ 2 ≤ Bq := by
  rcases Nat.lt_or_ge M N with h | h
  · rw [Finset.Ico_eq_empty (by omega)]
    have := bessel ha hs N
    simp only [Finset.sum_empty]
    linarith
  · have := bessel ha hs M
    have e := Finset.sum_range_add_sum_Ico (fun n => (physL l (TF (n + 1))) ^ 2) h
    linarith

/-! ### From the field to the physical kernels -/

theorem avg_rowK {c : YCell} (h2 : 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    c.avg (rowK x) = c.phys (fun s => Real.log |x - s|) + c.phys (fun s => Real.log |1 - s * x|) := by
  unfold YCell.phys YCell.avg
  have i1 := rowlog2_int h2 c.lo_lt hx0 hx1
  have i2 := rowlog_int h2 c.lo_lt hx0 hx1
  rw [← mul_add, ← intervalIntegral.integral_add i1 i2]
  congr 2
  funext y
  unfold rowK
  rw [mul_comm x]

theorem row_cell {c : YCell} (h2 : 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    c.pot (x + 1 / x) + c.phys (fun u => Real.log |u|) + c.w * Real.log |x| =
      c.phys (fun s => Real.log |x - s|) + c.phys (fun s => Real.log |1 - s * x|) := by
  have := cell_row (Or.inl h2) hx0.ne'
  rw [avg_rowK h2 hx0 hx1] at this
  linarith

theorem row_list {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    potL l (x + 1 / x) + physL l (fun u => Real.log |u|) + massL l * Real.log |x| =
      physL l (fun s => Real.log |x - s|) + physL l (fun s => Real.log |1 - s * x|) := by
  induction l with
  | nil => simp [potL, physL, massL]
  | cons c l ih =>
    have a1 := row_cell (h2 c (by simp)) hx0 hx1
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    have e2 : massL (c :: l) = c.w + massL l := by simp [massL]
    have e3 : potL (c :: l) (x + 1 / x) = c.pot (x + 1 / x) + potL l (x + 1 / x) := by simp [potL]
    simp only [e1, e2, e3, add_mul]
    linarith

theorem row_cell_neg {c : YCell} (h : c.hi ≤ -2) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    c.pot (-u + 1 / (-u)) + c.phys (fun v => Real.log |v|) + c.w * Real.log |-u| =
      c.reflect.phys (fun s => Real.log |u - s|) + c.reflect.phys (fun s => Real.log |1 - s * u|) := by
  have h1 := cell_row (Or.inr h) (x := -u) (neg_ne_zero.mpr hu0.ne')
  have hr2 : 2 ≤ c.reflect.lo := by show 2 ≤ -c.hi; linarith
  have h3 := avg_rowK hr2 hu0 hu1
  have e : c.avg (rowK (-u)) = c.reflect.avg (rowK u) := by
    unfold YCell.avg YCell.reflect
    have ed : -c.lo - -c.hi = c.hi - c.lo := by ring
    simp only [ed]
    congr 1
    have := intervalIntegral.integral_comp_neg (a := c.lo) (b := c.hi) (rowK u)
    rw [← this]
    apply intervalIntegral.integral_congr
    intro Y hY
    rw [uIcc_of_le c.lo_lt.le] at hY
    have hb : 0 < -Y := by linarith [hY.2, c.lo_lt]
    have := rowK_neg_neg u hb
    simp only [neg_neg] at this
    exact this
  rw [e, h3] at h1
  linarith

theorem row_list_neg {l : List YCell} (h : ∀ c ∈ l, c.hi ≤ -2) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    potL l (-u + 1 / (-u)) + physL l (fun v => Real.log |v|) + massL l * Real.log |-u| =
      physL (MomentSource.reflectL l) (fun s => Real.log |u - s|) +
        physL (MomentSource.reflectL l) (fun s => Real.log |1 - s * u|) := by
  induction l with
  | nil => simp [potL, physL, massL, MomentSource.reflectL]
  | cons c l ih =>
    have a1 := row_cell_neg (h c (by simp)) hu0 hu1
    have a2 := ih fun d hd => h d (by simp [hd])
    have e1 : ∀ (m : List YCell) (c : YCell) f, physL (c :: m) f = c.phys f + physL m f :=
      fun m c f => by simp [physL]
    have e2 : massL (c :: l) = c.w + massL l := by simp [massL]
    have e3 : potL (c :: l) (-u + 1 / (-u)) = c.pot (-u + 1 / (-u)) + potL l (-u + 1 / (-u)) := by
      simp [potL]
    have e4 : MomentSource.reflectL (c :: l) = c.reflect :: MomentSource.reflectL l := rfl
    simp only [e4, e1, e2, e3, add_mul]
    linarith

/-! ### Reflection by sign -/

theorem log_one_sub_le_sum {z : ℝ} (h0 : 0 ≤ z) (h1 : z < 1) (K : ℕ) :
    Real.log (1 - z) ≤ -∑ k ∈ Finset.range K, z ^ (k + 1) / ((k : ℝ) + 1) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := z) (by rw [abs_of_nonneg h0]; exact h1)
  have := sum_le_hasSum (Finset.range K) (fun i _ => by positivity) hs
  linarith

theorem phys_pow_int {c : YCell} (h2 : 2 ≤ c.lo) (k : ℕ) :
    IntervalIntegrable (fun y => YCell.physX y ^ k) volume c.lo c.hi :=
  ((physX_continuousOn (lo := c.lo) (hi := c.hi) (Or.inl h2)).pow k).intervalIntegrable_of_Icc
    c.lo_lt.le

theorem phys_refl_le {c : YCell} (h2 : 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (K : ℕ) :
    c.phys (fun s => Real.log |1 - s * x|) ≤
      -∑ k ∈ Finset.range K, x ^ (k + 1) / ((k : ℝ) + 1) * c.phys (fun s => s ^ (k + 1)) := by
  have hlt := c.lo_lt
  have hd : 0 < c.hi - c.lo := by linarith
  have hg0 : 0 ≤ c.w / (c.hi - c.lo) := div_nonneg c.w_nonneg hd.le
  set a : ℕ → ℝ := fun k => x ^ (k + 1) / ((k : ℝ) + 1) with ha
  have hi1 := rowlog_int h2 hlt hx0 hx1
  have hi2 : ∀ k ∈ Finset.range K, IntervalIntegrable
      (fun y => a k * YCell.physX y ^ (k + 1)) volume c.lo c.hi :=
    fun k _ => (phys_pow_int h2 (k + 1)).const_mul _
  have hi3 : IntervalIntegrable
      (fun y => ∑ k ∈ Finset.range K, a k * YCell.physX y ^ (k + 1)) volume c.lo c.hi :=
    (IntervalIntegrable.sum (Finset.range K) hi2).congr (by
      intro y _
      simp [Finset.sum_apply])
  have hle : ∫ y in c.lo..c.hi, Real.log |1 - YCell.physX y * x| ≤
      ∫ y in c.lo..c.hi, -∑ k ∈ Finset.range K, a k * YCell.physX y ^ (k + 1) := by
    apply intervalIntegral.integral_mono_ae_restrict hlt.le hi1 hi3.neg
    have hae : ∀ᵐ Y ∂(volume : Measure ℝ), Y ∉ ({2} : Set ℝ) :=
      (Set.countable_singleton _).ae_notMem volume
    have hm := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Icc (a := c.lo) (b := c.hi))
    filter_upwards [ae_restrict_of_ae (s := Icc c.lo c.hi) hae, hm] with Y hY hYm
    have hY2 : 2 ≤ Y := h2.trans hYm.1
    have hYlt : 2 < Y := lt_of_le_of_ne hY2 fun h => hY (Set.mem_singleton_iff.mpr h.symm)
    obtain ⟨p0, _⟩ := physX_mem hY2
    have p1 := physX_lt_one hYlt
    have hz1 : YCell.physX Y * x < 1 := by nlinarith
    have hz0 : 0 ≤ YCell.physX Y * x := by positivity
    have := log_one_sub_le_sum hz0 hz1 K
    rw [abs_of_pos (by linarith)]
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ha]
    rw [mul_pow]; ring
  have hev : ∫ y in c.lo..c.hi, -∑ k ∈ Finset.range K, a k * YCell.physX y ^ (k + 1) =
      -∑ k ∈ Finset.range K, a k * ∫ y in c.lo..c.hi, YCell.physX y ^ (k + 1) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_finsetSum hi2]
    simp only [intervalIntegral.integral_const_mul]
  rw [hev] at hle
  have := mul_le_mul_of_nonneg_left hle hg0
  have e2 : ∑ k ∈ Finset.range K, a k * c.phys (fun s => s ^ (k + 1)) =
      c.w / (c.hi - c.lo) * ∑ k ∈ Finset.range K, a k * ∫ y in c.lo..c.hi, YCell.physX y ^ (k + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ * (c.w / (c.hi - c.lo) * _) = _
    ring
  rw [e2]
  show c.w / (c.hi - c.lo) * ∫ y in c.lo..c.hi, Real.log |1 - YCell.physX y * x| ≤ _
  linarith

theorem physL_refl_le {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (K : ℕ) :
    physL l (fun s => Real.log |1 - s * x|) ≤
      -∑ k ∈ Finset.range K, x ^ (k + 1) / ((k : ℝ) + 1) * physL l (fun s => s ^ (k + 1)) := by
  induction l with
  | nil => simp [physL]
  | cons c l ih =>
    have a1 := phys_refl_le (h2 c (by simp)) hx0 hx1 K
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    simp only [e1, mul_add, Finset.sum_add_distrib]
    linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_pos vY_le_one physX_pos phys_pos)

/-! ### Exact moments of a cell -/

section moments

noncomputable section

def Er (l : List YCell) (j : ℕ) : ℝ := (l.map fun c => gc c * (vY c.lo ^ j - vY c.hi ^ j)).sum

def Lr (l : List YCell) : ℝ :=
  (l.map fun c => gc c * (Real.log (vY c.lo) - Real.log (vY c.hi))).sum

theorem cell_mom2 {c : YCell} (h2 : 2 ≤ c.lo) (k : ℕ) :
    c.phys (fun s => s ^ (k + 2)) = gc c * (vY c.lo ^ (k + 1) - vY c.hi ^ (k + 1)) / ((k : ℝ) + 1) -
      gc c * (vY c.lo ^ (k + 3) - vY c.hi ^ (k + 3)) / ((k : ℝ) + 3) := by
  rw [phys_pos h2, CompactHf.integral_vY_pow k h2 c.lo_lt.le]
  unfold CompactHf.momK gc
  simp only [show k + 2 ≠ 1 by omega, _root_.if_false, show k + 2 - 1 = k + 1 by omega]
  push_cast
  have e1 : (k : ℝ) + 2 - 1 = (k : ℝ) + 1 := by ring
  have e2 : (k : ℝ) + 2 + 1 = (k : ℝ) + 3 := by ring
  rw [e1, e2, show k + 2 + 1 = k + 3 by omega]
  ring

theorem cell_mom1 {c : YCell} (h2 : 2 ≤ c.lo) :
    c.phys (fun s => s ^ 1) = gc c * (Real.log (vY c.lo) - Real.log (vY c.hi)) -
      gc c * (vY c.lo ^ 2 - vY c.hi ^ 2) / 2 := by
  have := CompactHf.integral_vY_pow' (k := 1) le_rfl h2 c.lo_lt.le
  rw [phys_pos h2, this]
  unfold CompactHf.momK gc MomentSource.H1
  simp only [_root_.if_true]
  ring

theorem mom2 {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) (k : ℕ) :
    physL l (fun s => s ^ (k + 2)) = Er l (k + 1) / ((k : ℝ) + 1) - Er l (k + 3) / ((k : ℝ) + 3) := by
  induction l with
  | nil => simp [physL, Er]
  | cons c l ih =>
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    have e2 : ∀ j, Er (c :: l) j = gc c * (vY c.lo ^ j - vY c.hi ^ j) + Er l j := fun j => by simp [Er]
    rw [e1, a2, cell_mom2 (h2 c (by simp)), e2, e2]
    ring

theorem mom1 {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) :
    physL l (fun s => s ^ 1) = Lr l - Er l 2 / 2 := by
  induction l with
  | nil => simp [physL, Er, Lr]
  | cons c l ih =>
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    have e2 : ∀ j, Er (c :: l) j = gc c * (vY c.lo ^ j - vY c.hi ^ j) + Er l j := fun j => by simp [Er]
    have e3 : Lr (c :: l) = gc c * (Real.log (vY c.lo) - Real.log (vY c.hi)) + Lr l := by simp [Lr]
    rw [e1, a2, cell_mom1 (h2 c (by simp)), e2, e3]
    ring

theorem stream_close {P a : ℕ} {x : ℝ} (ha : a ≤ 2 ^ P) (h1 : (a : ℝ) / 2 ^ P ≤ x)
    (h2 : x ≤ ((a : ℝ) + 1) / 2 ^ P) (hx1 : x ≤ 1) (j : ℕ) :
    |x ^ j - (MomentInputs.stream P a (2 ^ P) j : ℝ) / 2 ^ P| ≤ 2 * j / 2 ^ P := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have ht0 : (0 : ℝ) ≤ (a : ℝ) / 2 ^ P := by positivity
  have ht1 : (a : ℝ) / 2 ^ P ≤ 1 := by rw [div_le_one hd]; exact_mod_cast ha
  have u := MomentInputs.stream_upper P a (2 ^ P) j
  have l := MomentInputs.stream_lower P a (2 ^ P) ha j
  have e1 : (((2 ^ P : ℕ) : ℝ)) / 2 ^ P = 1 := by push_cast; field_simp
  rw [e1, one_mul] at u l
  have p := MomentInputs.abs_pow_sub_pow_le_unit (ht0.trans h1) hx1 ht0 ht1 j
  have q : |x - (a : ℝ) / 2 ^ P| ≤ 1 / 2 ^ P := by
    rw [abs_of_nonneg (by linarith)]
    have : ((a : ℝ) + 1) / 2 ^ P = (a : ℝ) / 2 ^ P + 1 / 2 ^ P := by ring
    linarith
  have r : |x ^ j - ((a : ℝ) / 2 ^ P) ^ j| ≤ j / 2 ^ P := by
    refine p.trans ?_
    calc (j : ℝ) * |x - (a : ℝ) / 2 ^ P| ≤ j * (1 / 2 ^ P) := by gcongr
      _ = j / 2 ^ P := by ring
  have r' := abs_le.mp r
  rw [abs_le]
  have e2 : 2 * (j : ℝ) / 2 ^ P = j / 2 ^ P + j / 2 ^ P := by ring
  rw [e2]
  constructor <;> linarith [r'.1, r'.2]

end

/-! ### Kernel records -/

/-- One gas cell of the certificate: `[a,b]/10^12`, integer mass `p`, endpoint enclosures
`al/2^P ≤ X(lo) ≤ (al+1)/2^P`, `ah/2^P ≤ X(hi) ≤ (ah+1)/2^P`, and the AM-GM parameter `lam/2^32`. -/
structure GD where
  a : ℕ
  b : ℕ
  p : ℕ
  al : ℕ
  ah : ℕ
  lam : ℕ

/-- `t + 1/t ≥ Y` at `t = A/2^P`. -/
def lowOK (P Yn A : ℕ) : Bool := decide (Yn * A * 2 ^ P ≤ (A * A + 4 ^ P) * 10 ^ 12)
/-- `t + 1/t ≤ Y` at `t = (A+1)/2^P`, or `t ≥ 1`. -/
def upOK (P Yn A : ℕ) : Bool :=
  decide (2 ^ P ≤ A + 1) || decide (((A + 1) * (A + 1) + 4 ^ P) * 10 ^ 12 ≤ Yn * (A + 1) * 2 ^ P)

def GD.ok (P : ℕ) (d : GD) : Bool :=
  decide (2 * 10 ^ 12 ≤ d.a) && decide (d.a < d.b) && decide (0 < d.ah) && decide (d.ah ≤ d.al) &&
    decide (d.al ≤ 2 ^ P) && decide (0 < d.lam) && lowOK P d.a d.al && upOK P d.a d.al &&
    lowOK P d.b d.ah && upOK P d.b d.ah

/-- `⌊gc · 2^P⌋`. -/
def GD.g (P T : ℕ) (d : GD) : ℕ := d.p * 10 ^ 12 * 2 ^ P / (T * (d.b - d.a))

/-- Stream state of a cell. -/
structure St where
  g : ℕ
  al : ℕ
  ah : ℕ
  u : ℕ
  v : ℕ

def St.step (P : ℕ) (s : St) : St := ⟨s.g, s.al, s.ah, s.u * s.al / 2 ^ P, s.v * s.ah / 2 ^ P⟩

def stAt (P T : ℕ) (j : ℕ) (d : GD) : St :=
  ⟨d.g P T, d.al, d.ah, MomentInputs.stream P d.al (2 ^ P) j, MomentInputs.stream P d.ah (2 ^ P) j⟩

theorem stAt_step (P T j : ℕ) (d : GD) : (stAt P T j d).step P = stAt P T (j + 1) d := rfl

def eVal (S : List St) : ℤ := (S.map fun s => (s.g : ℤ) * ((s.u : ℤ) - s.v)).sum

/-- The rows `E_j`, `j = j0, ..., j0+n-1`, one pass per `j`. -/
def rows (P : ℕ) : ℕ → List St → List ℤ
  | 0, _ => []
  | n + 1, S => eVal S :: rows P n (S.map (St.step P))

/-- Sequential closeness to a real sequence, with lists of values and errors. -/
def CloseL (m : ℕ → ℝ) : ℕ → List ℚ → List ℚ → Prop
  | _, [], _ => True
  | _, _ :: _, [] => False
  | k, a :: as, d :: ds => |m k - (a : ℝ)| ≤ (d : ℝ) ∧ CloseL m (k + 1) as ds

section spec

variable {P T : ℕ}

/-- A real cell and its record. -/
structure Rel (P T : ℕ) (c : YCell) (d : GD) : Prop where
  lo : c.lo = (d.a : ℝ) / 10 ^ 12
  hi : c.hi = (d.b : ℝ) / 10 ^ 12
  w : c.w = (d.p : ℝ) / (T : ℝ)
  ok : d.ok P = true

theorem enc_low {t Y : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hY : 2 ≤ Y) (h : Y ≤ t + 1 / t) :
    t ≤ vY Y := by
  have := physX_anti hY h
  rw [physX_inv h0 h1, physX_pos hY] at this
  exact this

theorem enc_up {t Y : ℝ} (h0 : 0 < t) (hY : 2 ≤ Y) (h : t + 1 / t ≤ Y ∨ 1 ≤ t) : vY Y ≤ t := by
  rcases h with h | h
  · rcases le_or_gt t 1 with h1 | h1
    · have h3 : 2 ≤ t + 1 / t := by
        have e : t + 1 / t - 2 = (t - 1) ^ 2 / t := by field_simp; ring
        have : 0 ≤ (t - 1) ^ 2 / t := by positivity
        linarith
      have := physX_anti h3 h
      rw [physX_inv h0 h1, physX_pos hY] at this
      exact this
    · exact (vY_le_one hY).trans h1.le
  · exact (vY_le_one hY).trans h

theorem t_add_inv {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    A / D + 1 / (A / D) = (A * A + D * D) / (A * D) := by
  field_simp

theorem low_real {P Yn A : ℕ} (hA : 0 < A) (hA1 : A ≤ 2 ^ P) (hY : 2 ≤ (Yn : ℝ) / 10 ^ 12)
    (h : lowOK P Yn A = true) : (A : ℝ) / 2 ^ P ≤ vY ((Yn : ℝ) / 10 ^ 12) := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have h' : Yn * A * 2 ^ P ≤ (A * A + 4 ^ P) * 10 ^ 12 := of_decide_eq_true h
  have h'' : (Yn : ℝ) * A * 2 ^ P ≤ ((A : ℝ) * A + 4 ^ P) * 10 ^ 12 := by exact_mod_cast h'
  refine enc_low (by positivity) ?_ hY ?_
  · rw [div_le_one hd]; exact_mod_cast hA1
  · have e4 : (4 : ℝ) ^ P = 2 ^ P * 2 ^ P := by rw [← mul_pow]; norm_num
    rw [e4] at h''
    rw [t_add_inv hA0 hd, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem up_real {P Yn A : ℕ} (hY : 2 ≤ (Yn : ℝ) / 10 ^ 12)
    (h : upOK P Yn A = true) : vY ((Yn : ℝ) / 10 ^ 12) ≤ ((A : ℝ) + 1) / 2 ^ P := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have hA0 : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  refine enc_up (by positivity) hY ?_
  unfold upOK at h
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · right
    have h' : 2 ^ P ≤ A + 1 := of_decide_eq_true h
    have h'' : (2 : ℝ) ^ P ≤ (A : ℝ) + 1 := by exact_mod_cast h'
    rw [le_div_iff₀ hd]; linarith
  · left
    have h' : ((A + 1) * (A + 1) + 4 ^ P) * 10 ^ 12 ≤ Yn * (A + 1) * 2 ^ P := of_decide_eq_true h
    have h'' : (((A : ℝ) + 1) * ((A : ℝ) + 1) + 4 ^ P) * 10 ^ 12 ≤ (Yn : ℝ) * ((A : ℝ) + 1) * 2 ^ P := by
      exact_mod_cast h'
    have e4 : (4 : ℝ) ^ P = 2 ^ P * 2 ^ P := by rw [← mul_pow]; norm_num
    rw [e4] at h''
    rw [t_add_inv hA0 hd, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- Facts extracted from one record. -/
structure Facts (P : ℕ) (c : YCell) (d : GD) : Prop where
  two : 2 ≤ c.lo
  al1 : d.al ≤ 2 ^ P
  ah0 : 0 < d.ah
  ahl : d.ah ≤ d.al
  lam0 : 0 < d.lam
  ll : (d.al : ℝ) / 2 ^ P ≤ vY c.lo
  lu : vY c.lo ≤ ((d.al : ℝ) + 1) / 2 ^ P
  hl : (d.ah : ℝ) / 2 ^ P ≤ vY c.hi
  hu : vY c.hi ≤ ((d.ah : ℝ) + 1) / 2 ^ P
  dab : d.a < d.b

theorem Rel.facts {c : YCell} {d : GD} (h : Rel P T c d) : Facts P c d := by
  have hk := h.ok
  simp only [GD.ok, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩ := hk
  have h2 : 2 ≤ (d.a : ℝ) / 10 ^ 12 := by
    rw [le_div_iff₀ (by norm_num)]
    have : ((2 * 10 ^ 12 : ℕ) : ℝ) ≤ d.a := by exact_mod_cast k1
    push_cast at this
    linarith
  have h3 : 2 ≤ (d.b : ℝ) / 10 ^ 12 := by
    have : (d.a : ℝ) ≤ d.b := by exact_mod_cast k2.le
    refine h2.trans ?_
    gcongr
  have hah2 : d.ah ≤ 2 ^ P := k4.trans k5
  rw [← h.lo] at h2
  refine ⟨h2, k5, k3, k4, k6, ?_, ?_, ?_, ?_, k2⟩
  · rw [h.lo]; refine low_real (lt_of_lt_of_le k3 k4) k5 (h.lo ▸ h2) k7
  · rw [h.lo]; exact up_real (h.lo ▸ h2) k8
  · rw [h.hi]; exact low_real k3 hah2 h3 k9
  · rw [h.hi]; exact up_real h3 k10

end spec

end moments

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_pos vY_le_one physX_pos phys_pos)

/-! ### Rounding -/

def fl (q : ℚ) : ℤ := q.num / (q.den : ℤ)
def ce (q : ℚ) : ℤ := -fl (-q)

theorem fl_eq (q : ℚ) : fl q = ⌊q⌋ := Rat.floor_def'.symm

theorem fl_le (q : ℚ) : ((fl q : ℤ) : ℚ) ≤ q := by rw [fl_eq]; exact Int.floor_le q
theorem lt_fl (q : ℚ) : q < (fl q : ℚ) + 1 := by rw [fl_eq]; exact Int.lt_floor_add_one q
theorem le_ce (q : ℚ) : q ≤ (ce q : ℚ) := by
  have := fl_le (-q); unfold ce; push_cast; linarith
theorem ce_lt (q : ℚ) : (ce q : ℚ) < q + 1 := by
  have := lt_fl (-q); unfold ce; push_cast; linarith

theorem fl_real (q : ℚ) (Q : ℕ) : ((fl (q * 2 ^ Q) : ℤ) : ℝ) ≤ (q : ℝ) * 2 ^ Q ∧
    (q : ℝ) * 2 ^ Q < ((fl (q * 2 ^ Q) : ℤ) : ℝ) + 1 := by
  have h1 := fl_le (q * 2 ^ Q)
  have h2 := lt_fl (q * 2 ^ Q)
  have h1' : (((fl (q * 2 ^ Q) : ℤ) : ℚ) : ℝ) ≤ ((q * 2 ^ Q : ℚ) : ℝ) := Rat.cast_le.mpr h1
  have h2' : ((q * 2 ^ Q : ℚ) : ℝ) < ((((fl (q * 2 ^ Q) : ℤ) : ℚ) + 1 : ℚ) : ℝ) := Rat.cast_lt.mpr h2
  push_cast at h1' h2'
  exact ⟨h1', h2'⟩

theorem ce_real (q : ℚ) (Q : ℕ) : (q : ℝ) * 2 ^ Q ≤ ((ce (q * 2 ^ Q) : ℤ) : ℝ) := by
  have h1 := le_ce (q * 2 ^ Q)
  have h1' : ((q * 2 ^ Q : ℚ) : ℝ) ≤ (((ce (q * 2 ^ Q) : ℤ) : ℚ) : ℝ) := Rat.cast_le.mpr h1
  push_cast at h1'
  exact h1'

section spec

variable {P T Q : ℕ}

noncomputable section

theorem Rel.gc_close {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) :
    (d.g P T : ℝ) / 2 ^ P ≤ gc c ∧ gc c ≤ ((d.g P T : ℝ) + 1) / 2 ^ P := by
  have f := h.facts
  have hdab : (0 : ℝ) < (d.b : ℝ) - d.a := by
    have : (d.a : ℝ) < d.b := by exact_mod_cast f.dab
    linarith
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hM : 0 < T * (d.b - d.a) := Nat.mul_pos hT (by have := f.dab; omega)
  have hcast : ((T * (d.b - d.a) : ℕ) : ℝ) = (T : ℝ) * ((d.b : ℝ) - d.a) := by
    rw [Nat.cast_mul, Nat.cast_sub f.dab.le]
  have hg : gc c = (d.p : ℝ) * 10 ^ 12 / ((T : ℝ) * ((d.b : ℝ) - d.a)) := by
    unfold gc
    rw [h.w, h.lo, h.hi]
    field_simp
  have h1 : d.g P T * (T * (d.b - d.a)) ≤ d.p * 10 ^ 12 * 2 ^ P := Nat.div_mul_le_self _ _
  have h2 : d.p * 10 ^ 12 * 2 ^ P < (d.g P T + 1) * (T * (d.b - d.a)) := by
    have := Nat.lt_succ_iff.mpr (le_refl (d.g P T))
    exact (Nat.div_lt_iff_lt_mul hM).mp this
  have h1' : (d.g P T : ℝ) * ((T : ℝ) * ((d.b : ℝ) - d.a)) ≤ (d.p : ℝ) * 10 ^ 12 * 2 ^ P := by
    rw [← hcast]; exact_mod_cast h1
  have h2' : (d.p : ℝ) * 10 ^ 12 * 2 ^ P < ((d.g P T : ℝ) + 1) * ((T : ℝ) * ((d.b : ℝ) - d.a)) := by
    rw [← hcast]; exact_mod_cast h2
  have hM' : (0 : ℝ) < (T : ℝ) * ((d.b : ℝ) - d.a) := by positivity
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  rw [hg]
  constructor
  · rw [div_le_div_iff₀ hd hM']; linarith
  · rw [div_le_div_iff₀ hM' hd]; linarith

theorem cell_E {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) (j : ℕ) :
    |gc c * (vY c.lo ^ j - vY c.hi ^ j) -
        ((d.g P T : ℝ) * ((MomentInputs.stream P d.al (2 ^ P) j : ℝ) -
          (MomentInputs.stream P d.ah (2 ^ P) j : ℝ))) / 4 ^ P| ≤
      (1 + 4 * j * ((d.g P T : ℝ) / 2 ^ P)) / 2 ^ P := by
  have f := h.facts
  obtain ⟨g1, g2⟩ := h.gc_close hT
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have h2' : 2 ≤ c.hi := f.two.trans c.lo_lt.le
  have hx1 := vY_le_one f.two
  have hy1 := vY_le_one h2'
  have hx0 := (vY_pos f.two).le
  have hy0 := (vY_pos h2').le
  have s1 := stream_close f.al1 f.ll f.lu hx1 j
  have s2 := stream_close (f.ahl.trans f.al1) f.hl f.hu hy1 j
  set G := (d.g P T : ℝ) / 2 ^ P with hG
  have hG0 : 0 ≤ G := by positivity
  set u := (MomentInputs.stream P d.al (2 ^ P) j : ℝ) / 2 ^ P
  set v := (MomentInputs.stream P d.ah (2 ^ P) j : ℝ) / 2 ^ P
  set D := vY c.lo ^ j - vY c.hi ^ j with hD
  have e4 : (4 : ℝ) ^ P = 2 ^ P * 2 ^ P := by rw [← mul_pow]; norm_num
  have e : ((d.g P T : ℝ) * ((MomentInputs.stream P d.al (2 ^ P) j : ℝ) -
      (MomentInputs.stream P d.ah (2 ^ P) j : ℝ))) / 4 ^ P = G * (u - v) := by
    simp only [hG, u, v]; rw [e4]; field_simp
  rw [e]
  have hD1 : |D| ≤ 1 := by
    have a1 : vY c.lo ^ j ≤ 1 := pow_le_one₀ hx0 hx1
    have a2 : vY c.hi ^ j ≤ 1 := pow_le_one₀ hy0 hy1
    have a3 : 0 ≤ vY c.lo ^ j := pow_nonneg hx0 j
    have a4 : 0 ≤ vY c.hi ^ j := pow_nonneg hy0 j
    rw [abs_le]; constructor <;> linarith
  have hDd : |D - (u - v)| ≤ 4 * j / 2 ^ P := by
    have q1 := abs_le.mp s1
    have q2 := abs_le.mp s2
    have e2 : 4 * (j : ℝ) / 2 ^ P = 2 * j / 2 ^ P + 2 * j / 2 ^ P := by ring
    rw [abs_le, e2]
    constructor <;> linarith [q1.1, q1.2, q2.1, q2.2]
  have hgg : |gc c - G| ≤ 1 / 2 ^ P := by
    rw [abs_of_nonneg (by linarith)]
    have : ((d.g P T : ℝ) + 1) / 2 ^ P = G + 1 / 2 ^ P := by simp only [hG]; ring
    linarith
  have split : gc c * D - G * (u - v) = (gc c - G) * D + G * (D - (u - v)) := by ring
  rw [split]
  calc |(gc c - G) * D + G * (D - (u - v))| ≤ |gc c - G| * |D| + G * |D - (u - v)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hG0]
    _ ≤ 1 / 2 ^ P * 1 + G * (4 * j / 2 ^ P) := by
        gcongr
    _ = _ := by ring

def eV (P T : ℕ) (L : List GD) (j : ℕ) : ℤ := eVal (L.map (stAt P T j))
def SG (P T : ℕ) (L : List GD) : ℕ := (L.map (GD.g P T)).sum

theorem Er_close {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T) (j : ℕ) :
    |Er l j - (eV P T L j : ℝ) / 4 ^ P| ≤
      ((L.length : ℝ) + 4 * j * ((SG P T L : ℝ) / 2 ^ P)) / 2 ^ P := by
  induction h with
  | nil => simp [Er, eV, eVal, SG]
  | @cons c d l L hr hl ih =>
    have a := cell_E hr hT j
    have e1 : Er (c :: l) j = gc c * (vY c.lo ^ j - vY c.hi ^ j) + Er l j := by simp [Er]
    have e2 : ((eV P T (d :: L) j : ℤ) : ℝ) = (d.g P T : ℝ) * ((MomentInputs.stream P d.al (2 ^ P) j : ℝ) -
          (MomentInputs.stream P d.ah (2 ^ P) j : ℝ)) + (eV P T L j : ℝ) := by
      simp [eV, eVal, stAt]
    have e3 : ((SG P T (d :: L) : ℕ) : ℝ) = (d.g P T : ℝ) + (SG P T L : ℝ) := by simp [SG]
    rw [e1, e2, e3, List.length_cons]
    have q1 := abs_le.mp a
    have q2 := abs_le.mp ih
    push_cast
    have e4 : ∀ A B : ℝ, (A + B) / 4 ^ P = A / 4 ^ P + B / 4 ^ P := fun A B => add_div _ _ _
    rw [e4]
    have e5 : (((L.length : ℝ) + 1 + 4 * j * (((d.g P T : ℝ) + (SG P T L : ℝ)) / 2 ^ P)) / 2 ^ P) =
        (1 + 4 * j * ((d.g P T : ℝ) / 2 ^ P)) / 2 ^ P +
          ((L.length : ℝ) + 4 * j * ((SG P T L : ℝ) / 2 ^ P)) / 2 ^ P := by ring
    rw [e5, abs_le]
    constructor <;> linarith [q1.1, q1.2, q2.1, q2.2]

/-- Sequential closeness of an integer row list. -/
def CloseZ (m : ℕ → ℝ) (S : ℝ) (err : ℕ → ℝ) : ℕ → List ℤ → Prop
  | _, [] => True
  | k, e :: es => |m k - (e : ℝ) / S| ≤ err k ∧ CloseZ m S err (k + 1) es

theorem rows_close {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T)
    (n j : ℕ) :
    CloseZ (Er l) (4 ^ P) (fun j => ((L.length : ℝ) + 4 * j * ((SG P T L : ℝ) / 2 ^ P)) / 2 ^ P) j
      (rows P n (L.map (stAt P T j))) := by
  induction n generalizing j with
  | zero => trivial
  | succ n ih =>
    refine ⟨Er_close h hT j, ?_⟩
    have : (L.map (stAt P T j)).map (St.step P) = L.map (stAt P T (j + 1)) := by
      rw [List.map_map]; rfl
    rw [this]
    exact ih (j + 1)

end

/-- Moments from the row list: entry `i` is the moment `k+2+i`; the row list starts at `E_(k+1)`. -/
def mB (S : ℚ) : ℕ → List ℤ → List ℚ
  | k, e :: e2 :: e3 :: r =>
    ((e : ℚ) / S / ((k : ℚ) + 1) - (e3 : ℚ) / S / ((k : ℚ) + 3)) :: mB S (k + 1) (e2 :: e3 :: r)
  | _, _ => []

def dB (err : ℕ → ℚ) : ℕ → List ℤ → List ℚ
  | k, _ :: e2 :: e3 :: r =>
    (err (k + 1) / ((k : ℚ) + 1) + err (k + 3) / ((k : ℚ) + 3)) :: dB err (k + 1) (e2 :: e3 :: r)
  | _, _ => []

theorem mB_close {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {S : ℚ} {err : ℕ → ℚ}
    (R : List ℤ) (k : ℕ) (h : CloseZ (Er l) (S : ℝ) (fun j => (err j : ℝ)) (k + 1) R) :
    CloseL (fun i => physL l (fun s => s ^ i)) (k + 2) (mB S k R) (dB err k R) := by
  induction R generalizing k with
  | nil => simp [mB, CloseL]
  | cons e R ih =>
    cases R with
    | nil => simp [mB, CloseL]
    | cons e2 R =>
      cases R with
      | nil => simp [mB, CloseL]
      | cons e3 R =>
        obtain ⟨c1, c2, c3, c4⟩ := h
        simp only [mB, dB, CloseL]
        refine ⟨?_, ?_⟩
        · rw [mom2 h2 k]
          have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
          push_cast
          have split : Er l (k + 1) / ((k : ℝ) + 1) - Er l (k + 3) / ((k : ℝ) + 3) -
              ((e : ℝ) / (S : ℝ) / ((k : ℝ) + 1) - (e3 : ℝ) / (S : ℝ) / ((k : ℝ) + 3)) =
              (Er l (k + 1) - (e : ℝ) / (S : ℝ)) / ((k : ℝ) + 1) -
                (Er l (k + 3) - (e3 : ℝ) / (S : ℝ)) / ((k : ℝ) + 3) := by ring
          rw [split]
          refine (abs_sub _ _).trans ?_
          rw [abs_div, abs_div, abs_of_pos hk1, abs_of_pos hk3]
          gcongr
        · exact ih (k + 1) ⟨c2, c3, c4⟩

/-! ### The first logarithmic moment -/

def GD.t (d : GD) : ℚ := ((d.al : ℚ) - d.ah) / ((d.al : ℚ) + d.ah)
def serQ (t : ℚ) : ℚ := 2 * t * (1 + t ^ 2 / 3 + t ^ 4 / 5 + t ^ 6 / 7)
def GD.le (d : GD) : ℚ := 2 * d.t ^ 9 / (1 - d.t ^ 2) + 1 / (d.ah : ℚ)
def GD.ghat (P T : ℕ) (d : GD) : ℚ := (d.g P T : ℚ) / 2 ^ P
def GD.lV (P T : ℕ) (d : GD) : ℚ := d.ghat P T * serQ d.t
def GD.lE (P T : ℕ) (d : GD) : ℚ := d.ghat P T * d.le + (serQ d.t + d.le) / 2 ^ P
def GD.lI (P T Q : ℕ) (d : GD) : ℤ := fl (d.lV P T * 2 ^ Q)
def GD.lEI (P T Q : ℕ) (d : GD) : ℤ := ce (d.lE P T * 2 ^ Q)

noncomputable section

theorem log_enc {x a δ : ℝ} (ha : 0 < a) (h1 : a ≤ x) (h2 : x ≤ a + δ) :
    0 ≤ Real.log x - Real.log a ∧ Real.log x - Real.log a ≤ δ / a := by
  have hx : 0 < x := lt_of_lt_of_le ha h1
  constructor
  · have := Real.log_le_log ha h1; linarith
  · rw [← Real.log_div hx.ne' ha.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hx ha)
    refine this.trans ?_
    rw [div_sub_one ha.ne']
    gcongr
    linarith

theorem cell_L {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) :
    |gc c * (Real.log (vY c.lo) - Real.log (vY c.hi)) - ((d.lV P T : ℚ) : ℝ)| ≤ ((d.lE P T : ℚ) : ℝ) := by
  have f := h.facts
  obtain ⟨g1, g2⟩ := h.gc_close hT
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have hah : (0 : ℝ) < d.ah := by exact_mod_cast f.ah0
  have hal : (0 : ℝ) < d.al := lt_of_lt_of_le hah (by exact_mod_cast f.ahl)
  have hle : (d.ah : ℝ) ≤ d.al := by exact_mod_cast f.ahl
  set tq : ℝ := ((d.al : ℝ) - d.ah) / ((d.al : ℝ) + d.ah) with ht
  have htq : ((d.t : ℚ) : ℝ) = tq := by simp [GD.t, ht]
  have t0 : 0 ≤ tq := div_nonneg (by linarith) (by positivity)
  have t1 : tq < 1 := by rw [ht, div_lt_one (by positivity)]; linarith
  have at' := CatalanMeasure.WLog.atanh_tail t0 t1 4
  have elog : (1 + tq) / (1 - tq) = (d.al : ℝ) / d.ah := by
    have hs : (d.al : ℝ) + d.ah ≠ 0 := by positivity
    have a1 : 1 + tq = 2 * (d.al : ℝ) / ((d.al : ℝ) + d.ah) := by rw [ht]; field_simp; ring
    have a2 : 1 - tq = 2 * (d.ah : ℝ) / ((d.al : ℝ) + d.ah) := by rw [ht]; field_simp; ring
    rw [a1, a2, div_div_div_cancel_right₀ hs]
    field_simp
  rw [elog] at at'
  have ser : 2 * tq * ∑ i ∈ Finset.range 4, (tq ^ 2) ^ i / ((1 + 2 * i : ℕ) : ℝ) = ((serQ d.t : ℚ) : ℝ) := by
    simp only [serQ, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    rw [htq]
    ring
  rw [ser] at at'
  have l1 := log_enc (a := (d.al : ℝ) / 2 ^ P) (x := vY c.lo) (δ := 1 / 2 ^ P) (by positivity) f.ll
    (by have := f.lu; rw [add_div] at this; exact this)
  have l2 := log_enc (a := (d.ah : ℝ) / 2 ^ P) (x := vY c.hi) (δ := 1 / 2 ^ P) (by positivity) f.hl
    (by have := f.hu; rw [add_div] at this; exact this)
  have r1 : (1 / 2 ^ P) / ((d.al : ℝ) / 2 ^ P) = 1 / (d.al : ℝ) := by field_simp
  have r2 : (1 / 2 ^ P) / ((d.ah : ℝ) / 2 ^ P) = 1 / (d.ah : ℝ) := by field_simp
  rw [r1] at l1
  rw [r2] at l2
  have r3 : 1 / (d.al : ℝ) ≤ 1 / (d.ah : ℝ) := by gcongr
  have elg : Real.log ((d.al : ℝ) / d.ah) =
      Real.log ((d.al : ℝ) / 2 ^ P) - Real.log ((d.ah : ℝ) / 2 ^ P) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  set ℓ := Real.log (vY c.lo) - Real.log (vY c.hi) with hℓ
  set Sg : ℝ := ((serQ d.t : ℚ) : ℝ) with hSg
  set ee : ℝ := ((d.le : ℚ) : ℝ) with hee
  have eex : ee = 2 * tq ^ 9 / (1 - tq ^ 2) + 1 / (d.ah : ℝ) := by
    simp only [hee, GD.le]; push_cast; rw [htq]
  have hclose : |ℓ - Sg| ≤ ee := by
    have q := abs_le.mp at'
    have : 2 * tq ^ (2 * 4 + 1) / (1 - tq ^ 2) = 2 * tq ^ 9 / (1 - tq ^ 2) := by norm_num
    rw [this] at q
    rw [eex, abs_le]
    rw [elg] at q
    constructor <;> linarith [q.1, q.2, l1.1, l1.2, l2.1, l2.2]
  have hS0 : 0 ≤ Sg := by
    simp only [hSg, serQ]
    push_cast
    rw [htq]
    positivity
  have hee0 : 0 ≤ ee := (abs_nonneg _).trans hclose
  set G : ℝ := (d.g P T : ℝ) / 2 ^ P with hG
  have hG0 : 0 ≤ G := by positivity
  have eV : ((d.lV P T : ℚ) : ℝ) = G * Sg := by simp [GD.lV, GD.ghat, hG, hSg]
  have eE : ((d.lE P T : ℚ) : ℝ) = G * ee + (Sg + ee) / 2 ^ P := by
    simp [GD.lE, GD.ghat, hG, hSg, hee]
  rw [eV, eE]
  have hgg : |gc c - G| ≤ 1 / 2 ^ P := by
    rw [abs_of_nonneg (by linarith)]
    have : ((d.g P T : ℝ) + 1) / 2 ^ P = G + 1 / 2 ^ P := by simp only [hG]; ring
    linarith
  have hl : |ℓ| ≤ Sg + ee := by
    have q := abs_le.mp hclose
    rw [abs_le]; constructor <;> linarith [q.1, q.2]
  have split : gc c * ℓ - G * Sg = (gc c - G) * ℓ + G * (ℓ - Sg) := by ring
  rw [split]
  calc |(gc c - G) * ℓ + G * (ℓ - Sg)| ≤ |gc c - G| * |ℓ| + G * |ℓ - Sg| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hG0]
    _ ≤ 1 / 2 ^ P * (Sg + ee) + G * ee := by gcongr
    _ = _ := by ring

end

end spec

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_pos vY_le_one physX_pos phys_pos)

section spec

variable {P T Q : ℕ}

noncomputable section

def LI (P T Q : ℕ) (L : List GD) : ℤ := (L.map (GD.lI P T Q)).sum
def LEI (P T Q : ℕ) (L : List GD) : ℤ := (L.map (GD.lEI P T Q)).sum

theorem cast_sum_cons {β : Type*} (f : β → ℤ) (d : β) (L : List β) :
    ((((d :: L).map f).sum : ℤ) : ℝ) = (f d : ℝ) + ((L.map f).sum : ℤ) := by
  simp

theorem Lr_close {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T) :
    |Lr l - (LI P T Q L : ℝ) / 2 ^ Q| ≤ ((LEI P T Q L : ℝ) + L.length) / 2 ^ Q := by
  have hq : (0 : ℝ) < 2 ^ Q := by positivity
  induction h with
  | nil => simp [Lr, LI, LEI]
  | @cons c d l L hr hl ih =>
    have a := abs_le.mp (cell_L hr hT)
    have e1 : Lr (c :: l) = gc c * (Real.log (vY c.lo) - Real.log (vY c.hi)) + Lr l := by simp [Lr]
    have e2 : ((LI P T Q (d :: L) : ℤ) : ℝ) = (d.lI P T Q : ℝ) + (LI P T Q L : ℝ) :=
      cast_sum_cons (GD.lI P T Q) d L
    have e3 : ((LEI P T Q (d :: L) : ℤ) : ℝ) = (d.lEI P T Q : ℝ) + (LEI P T Q L : ℝ) :=
      cast_sum_cons (GD.lEI P T Q) d L
    obtain ⟨f1, f2⟩ : ((d.lI P T Q : ℤ) : ℝ) ≤ ((d.lV P T : ℚ) : ℝ) * 2 ^ Q ∧
        ((d.lV P T : ℚ) : ℝ) * 2 ^ Q < (d.lI P T Q : ℝ) + 1 := fl_real _ Q
    have f3 : ((d.lE P T : ℚ) : ℝ) * 2 ^ Q ≤ (d.lEI P T Q : ℝ) := ce_real _ Q
    have g1 : ((d.lV P T : ℚ) : ℝ) ≤ ((d.lI P T Q : ℝ) + 1) / 2 ^ Q := by
      rw [le_div_iff₀ hq]; linarith
    have g2 : (d.lI P T Q : ℝ) / 2 ^ Q ≤ ((d.lV P T : ℚ) : ℝ) := by
      rw [div_le_iff₀ hq]; linarith
    have g3 : ((d.lE P T : ℚ) : ℝ) ≤ (d.lEI P T Q : ℝ) / 2 ^ Q := by
      rw [le_div_iff₀ hq]; linarith
    rw [e1, e2, e3, List.length_cons]
    have q2 := abs_le.mp ih
    push_cast
    have s1 : ((d.lI P T Q : ℝ) + (LI P T Q L : ℝ)) / 2 ^ Q =
        (d.lI P T Q : ℝ) / 2 ^ Q + (LI P T Q L : ℝ) / 2 ^ Q := add_div _ _ _
    have s2 : ((d.lEI P T Q : ℝ) + (LEI P T Q L : ℝ) + ((L.length : ℝ) + 1)) / 2 ^ Q =
        (d.lEI P T Q : ℝ) / 2 ^ Q + 1 / 2 ^ Q + ((LEI P T Q L : ℝ) + (L.length : ℝ)) / 2 ^ Q := by ring
    have s3 : ((d.lI P T Q : ℝ) + 1) / 2 ^ Q = (d.lI P T Q : ℝ) / 2 ^ Q + 1 / 2 ^ Q := add_div _ _ _
    rw [s1, s2, abs_le]
    constructor <;> linarith [a.1, a.2, q2.1, q2.2]

/-! ### The density norm -/

end

def vQ (P : ℕ) (Yn A : ℕ) : ℚ :=
  ((Yn : ℚ) ^ 2 / 10 ^ 24 - 4) * ((Yn : ℚ) / 10 ^ 12 - (A : ℚ) / 2 ^ P - 1)

def GD.cg (P T : ℕ) (d : GD) : ℚ :=
  ((d.p : ℚ) / (T : ℚ)) ^ 2 * (10 ^ 12 / ((d.b : ℚ) - d.a)) *
    ((d.lam : ℚ) / 2 ^ 32 / 2 + (vQ P d.a d.al + vQ P d.b d.ah) / (4 * ((d.lam : ℚ) / 2 ^ 32)))

def GD.cgI (P T Q : ℕ) (d : GD) : ℤ := ce (d.cg P T * 2 ^ Q)

def G2I (P T Q : ℕ) (L : List GD) : ℤ := (L.map (GD.cgI P T Q)).sum

noncomputable section

theorem Wsq_le {y t : ℝ} (hy : 2 ≤ y) (ht : t ≤ vY y) : Wsq y ≤ (y ^ 2 - 4) * (y - t - 1) := by
  have h := MomentSource.vY_add_inv hy
  have hx := vY_pos hy
  unfold Wsq
  rw [physX_pos hy, one_div]
  have : (vY y)⁻¹ = y - vY y := by linarith
  rw [this]
  have : 0 ≤ y ^ 2 - 4 := by nlinarith
  apply mul_le_mul_of_nonneg_left _ this
  linarith

theorem cell_G2 {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) :
    gc c ^ 2 * ∫ θ in Th c.lo..Th c.hi, bet θ ^ 2 ≤ ((d.cg P T : ℚ) : ℝ) := by
  have f := h.facts
  have hlt := c.lo_lt
  have hh2 : 2 ≤ c.hi := f.two.trans hlt.le
  have hlam : (0 : ℝ) < (d.lam : ℝ) / 2 ^ 32 := by
    have : (0 : ℝ) < d.lam := by exact_mod_cast f.lam0
    positivity
  set vlo : ℝ := ((vQ P d.a d.al : ℚ) : ℝ) with hvlo
  set vhi : ℝ := ((vQ P d.b d.ah : ℚ) : ℝ) with hvhi
  have e1 : Wsq c.lo ≤ vlo := by
    refine (Wsq_le f.two f.ll).trans (le_of_eq ?_)
    simp only [hvlo, vQ, h.lo]
    push_cast
    ring
  have e2 : Wsq c.hi ≤ vhi := by
    refine (Wsq_le hh2 f.hl).trans (le_of_eq ?_)
    simp only [hvhi, vQ, h.hi]
    push_cast
    ring
  have := cell_bet_sq f.two hlt hlam e1 e2
  have hdab : (0 : ℝ) < (d.b : ℝ) - d.a := by
    have : (d.a : ℝ) < d.b := by exact_mod_cast f.dab
    linarith
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hgg : gc c ^ 2 * (c.hi - c.lo) = ((d.p : ℝ) / T) ^ 2 * (10 ^ 12 / ((d.b : ℝ) - d.a)) := by
    unfold gc
    rw [h.w, h.lo, h.hi]
    field_simp
  calc _ ≤ gc c ^ 2 * ((c.hi - c.lo) * ((d.lam : ℝ) / 2 ^ 32 / 2 + (vlo + vhi) / (4 * ((d.lam : ℝ) / 2 ^ 32)))) :=
        mul_le_mul_of_nonneg_left this (sq_nonneg _)
    _ = _ := by
        rw [← mul_assoc, hgg]
        simp only [GD.cg, hvlo, hvhi]
        push_cast
        ring

theorem G2_le {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T) :
    G2 l ≤ (G2I P T Q L : ℝ) / 2 ^ Q := by
  have hq : (0 : ℝ) < 2 ^ Q := by positivity
  induction h with
  | nil => simp [G2, G2I]
  | @cons c d l L hr hl ih =>
    have a := cell_G2 hr hT
    have e1 : G2 (c :: l) = gc c ^ 2 * (∫ θ in Th c.lo..Th c.hi, bet θ ^ 2) + G2 l := by simp [G2]
    have e2 : ((G2I P T Q (d :: L) : ℤ) : ℝ) = (d.cgI P T Q : ℝ) + (G2I P T Q L : ℝ) :=
      cast_sum_cons (GD.cgI P T Q) d L
    have f3 : ((d.cg P T : ℚ) : ℝ) * 2 ^ Q ≤ (d.cgI P T Q : ℝ) := ce_real _ Q
    have g3 : ((d.cg P T : ℚ) : ℝ) ≤ (d.cgI P T Q : ℝ) / 2 ^ Q := by
      rw [le_div_iff₀ hq]; linarith
    rw [e1, e2, add_div]
    linarith

end

end spec

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz xmulZ rawSum_xmulZ)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

/-! ### Shifted Chebyshev polynomials in the monomial basis -/

theorem Pz_addZ (a b : List ℤ) (x : ℝ) : Pz (addZ a b) x = Pz a x + Pz b x := by
  induction a generalizing b with
  | nil => simp [addZ, Pz]
  | cons a t ih =>
    cases b with
    | nil => simp [addZ, Pz]
    | cons b r => simp only [addZ, Pz, ih]; push_cast; ring

theorem Pz_smulZ (a : ℤ) (b : List ℤ) (x : ℝ) : Pz (smulZ a b) x = (a : ℝ) * Pz b x := by
  induction b with
  | nil => simp [smulZ, Pz]
  | cons b t ih =>
    have : smulZ a (b :: t) = (a * b) :: smulZ a t := rfl
    rw [this]
    simp only [Pz, ih]; push_cast; ring

theorem Pz_continuous (L : List ℤ) : Continuous (Pz L) := by
  induction L with
  | nil => exact continuous_const
  | cons a t ih =>
    have : Pz (a :: t) = fun x => (a : ℝ) + x * Pz t x := rfl
    rw [this]; fun_prop

theorem len_addZ (a b : List ℤ) : (addZ a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => simp [addZ]
  | cons a t ih =>
    cases b with
    | nil => simp [addZ]
    | cons b r => simp [addZ, ih]

theorem len_smulZ (a : ℤ) (b : List ℤ) : (smulZ a b).length = b.length := by simp [smulZ]

/-- `T_(n+2)(2x-1) = (4x-2) T_(n+1)(2x-1) - T_n(2x-1)` on coefficient lists. -/
def tNext (a b : List ℤ) : List ℤ :=
  addZ (addZ (0 :: smulZ 4 b) (smulZ (-2) b)) (smulZ (-1) a)

theorem Pz_tNext {a b : List ℤ} {k : ℕ} (ha : ∀ s, Pz a s = basis k (2 * s - 1))
    (hb : ∀ s, Pz b s = basis (k + 1) (2 * s - 1)) (s : ℝ) :
    Pz (tNext a b) s = basis (k + 2) (2 * s - 1) := by
  simp only [tNext, Pz_addZ, Pz_smulZ, Pz, ha, hb]
  rw [basis_add_two]
  push_cast
  ring

theorem len_tNext {a b : List ℤ} {k : ℕ} (ha : a.length ≤ k + 1) (hb : b.length ≤ k + 2) :
    (tNext a b).length ≤ k + 3 := by
  simp only [tNext, len_addZ, len_smulZ, List.length_cons]
  omega

theorem Pz_t0 (s : ℝ) : Pz [1] s = basis 0 (2 * s - 1) := by simp [Pz, basis_zero]
theorem Pz_t1 (s : ℝ) : Pz [-1, 2] s = basis 1 (2 * s - 1) := by
  simp only [Pz, basis_one']; push_cast; ring

noncomputable section

/-- Linear functional on a coefficient list. -/
def Mev (m : ℕ → ℝ) : List ℤ → ℕ → ℝ
  | [], _ => 0
  | a :: t, k => (a : ℝ) * m k + Mev m t (k + 1)

theorem Mev_add (m1 m2 : ℕ → ℝ) (L : List ℤ) (k : ℕ) :
    Mev (fun i => m1 i + m2 i) L k = Mev m1 L k + Mev m2 L k := by
  induction L generalizing k with
  | nil => simp [Mev]
  | cons a t ih => simp only [Mev, ih]; ring

theorem Mev_zero (L : List ℤ) (k : ℕ) : Mev (fun _ => 0) L k = 0 := by
  induction L generalizing k with
  | nil => simp [Mev]
  | cons a t ih => simp [Mev, ih]

theorem phys_cont_int {c : YCell} (h2 : 2 ≤ c.lo) {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun y => f (YCell.physX y)) volume c.lo c.hi :=
  (hf.comp_continuousOn (physX_continuousOn (lo := c.lo) (hi := c.hi) (Or.inl h2))).intervalIntegrable_of_Icc
    c.lo_lt.le

theorem phys_add {c : YCell} (h2 : 2 ≤ c.lo) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    c.phys (fun s => f s + g s) = c.phys f + c.phys g := by
  unfold YCell.phys YCell.avg
  rw [intervalIntegral.integral_add (phys_cont_int h2 hf) (phys_cont_int h2 hg)]
  ring

theorem phys_Pz {c : YCell} (h2 : 2 ≤ c.lo) (L : List ℤ) (k : ℕ) :
    c.phys (fun s => s ^ k * Pz L s) = Mev (fun i => c.phys fun s => s ^ i) L k := by
  induction L generalizing k with
  | nil =>
    have : (fun s : ℝ => s ^ k * Pz [] s) = fun s => (0 : ℝ) * s := by funext s; simp [Pz]
    rw [this, MomentSource.phys_const_mul]
    simp [Mev]
  | cons a t ih =>
    have e : (fun s : ℝ => s ^ k * Pz (a :: t) s) = fun s => (a : ℝ) * s ^ k + s ^ (k + 1) * Pz t s := by
      funext s; simp only [Pz]; ring
    have hc := Pz_continuous t
    rw [e, phys_add h2 (by fun_prop) (by fun_prop), MomentSource.phys_const_mul, ih]
    rfl

theorem physL_Pz {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) (L : List ℤ) (k : ℕ) :
    physL l (fun s => s ^ k * Pz L s) = Mev (fun i => physL l fun s => s ^ i) L k := by
  induction l with
  | nil =>
    simp only [physL, List.map_nil, List.sum_nil]
    exact (Mev_zero L k).symm
  | cons c l ih =>
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    simp only [e1]
    rw [Mev_add, phys_Pz (h2 c (by simp)), ih fun d hd => h2 d (by simp [hd])]

theorem physL_TF {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {L : List ℤ} {n : ℕ}
    (h : ∀ s, Pz L s = basis n (2 * s - 1)) :
    physL l (TF n) = Mev (fun i => physL l fun s => s ^ i) L 0 := by
  rw [← physL_Pz h2 L 0]
  congr 1
  funext s
  simp [TF, h]

end

/-- Exact pairing with a value list. -/
def dotQ : List ℤ → List ℚ → ℚ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: t, m :: ms => (a : ℚ) * m + dotQ t ms

/-- The error of the pairing. -/
def dotA : List ℤ → List ℚ → ℚ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: t, d :: ds => |(a : ℚ)| * d + dotA t ds

theorem dot_close {m : ℕ → ℝ} : ∀ (L : List ℤ) (k : ℕ) (mL dL : List ℚ), CloseL m k mL dL →
    L.length ≤ mL.length → |Mev m L k - (dotQ L mL : ℝ)| ≤ (dotA L dL : ℝ)
  | [], k, mL, dL, _, _ => by simp [Mev, dotQ, dotA]
  | _ :: _, _, [], _, _, h => by simp at h
  | _ :: _, _, _ :: _, [], hc, _ => by simp [CloseL] at hc
  | a :: t, k, v :: vs, d :: ds, hc, h => by
    obtain ⟨h1, h2⟩ := hc
    have ih := dot_close t (k + 1) vs ds h2 (by simpa using h)
    simp only [Mev, dotQ, dotA]
    push_cast
    have e : (a : ℝ) * m k + Mev m t (k + 1) - ((a : ℝ) * (v : ℝ) + (dotQ t vs : ℝ)) =
        (a : ℝ) * (m k - v) + (Mev m t (k + 1) - dotQ t vs) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    gcongr

def muV (mL : List ℚ) : ℕ → List ℤ → List ℤ → List ℚ
  | 0, _, _ => []
  | n + 1, a, b => dotQ a mL :: muV mL n b (tNext a b)

def muE (dL : List ℚ) : ℕ → List ℤ → List ℤ → List ℚ
  | 0, _, _ => []
  | n + 1, a, b => dotA a dL :: muE dL n b (tNext a b)

theorem mu_close {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {mL dL : List ℚ}
    (hm : CloseL (fun i => physL l fun s => s ^ i) 0 mL dL) (n k : ℕ) (a b : List ℤ)
    (ha : ∀ s, Pz a s = basis k (2 * s - 1)) (hb : ∀ s, Pz b s = basis (k + 1) (2 * s - 1))
    (la : a.length ≤ k + 1) (lb : b.length ≤ k + 2) (hlen : k + n ≤ mL.length) :
    CloseL (fun i => physL l (TF i)) k (muV mL n a b) (muE dL n a b) := by
  induction n generalizing k a b with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · show |physL l (TF k) - _| ≤ _
      rw [physL_TF h2 ha]
      exact dot_close a 0 mL dL hm (by omega)
    · exact ih (k + 1) b (tNext a b) hb (fun s => Pz_tNext ha hb s) lb (len_tNext la lb) (by omega)

/-- Replace values and errors by shorter ones. -/
def relax : List ℚ → List ℚ → List ℚ → List ℚ → Bool
  | [], _, _, _ => true
  | _ :: _, [], _, _ => false
  | _ :: _, _ :: _, [], _ => false
  | _ :: _, _ :: _, _ :: _, [] => false
  | v :: vs, e :: es, w :: ws, f :: fs => decide (|v - w| + e ≤ f) && relax vs es ws fs

theorem relax_close {m : ℕ → ℝ} : ∀ (k : ℕ) (v e w f : List ℚ), CloseL m k v e → relax v e w f = true →
    v.length = w.length → CloseL m k w f
  | _, [], _, [], _, _, _, _ => by simp [CloseL]
  | _, [], _, _ :: _, _, _, _, hl => by simp at hl
  | _, _ :: _, [], _, _, _, h, _ => by simp [relax] at h
  | _, _ :: _, _ :: _, [], _, _, h, _ => by simp [relax] at h
  | _, _ :: _, _ :: _, _ :: _, [], _, h, _ => by simp [relax] at h
  | k, v :: vs, e :: es, w :: ws, f :: fs, hc, h, hl => by
    obtain ⟨h1, h2⟩ := hc
    simp only [relax, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨?_, relax_close (k + 1) vs es ws fs h2 h.2 (by simpa using hl)⟩
    have q : ((|v - w| + e : ℚ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast h.1
    push_cast at q
    calc |m k - (w : ℝ)| = |(m k - v) + ((v : ℝ) - w)| := by ring_nf
      _ ≤ |m k - v| + |(v : ℝ) - w| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- Lower bound of a sum of squares. -/
def sqLow : List ℚ → List ℚ → ℚ
  | [], _ => 0
  | _ :: _, [] => 0
  | v :: vs, e :: es => (v ^ 2 - 2 * |v| * e) + sqLow vs es

theorem sq_ge {a v e : ℝ} (h : |a - v| ≤ e) : v ^ 2 - 2 * |v| * e ≤ a ^ 2 := by
  have h1 : a ^ 2 - v ^ 2 = (a - v) ^ 2 + 2 * v * (a - v) := by ring
  have h2 : -(2 * |v| * e) ≤ 2 * v * (a - v) := by
    have : |2 * v * (a - v)| ≤ 2 * |v| * e := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
    exact (abs_le.mp this).1
  nlinarith [sq_nonneg (a - v)]

theorem sqLow_le {m : ℕ → ℝ} : ∀ (k : ℕ) (v e : List ℚ), CloseL m k v e →
    (sqLow v e : ℝ) ≤ ∑ i ∈ Finset.range v.length, (m (k + i)) ^ 2
  | _, [], _, _ => by simp [sqLow]
  | _, _ :: _, [], hc => by simp [CloseL] at hc
  | k, v :: vs, e :: es, hc => by
    obtain ⟨h1, h2⟩ := hc
    have ih := sqLow_le (k + 1) vs es h2
    simp only [sqLow, List.length_cons]
    rw [Finset.sum_range_succ']
    have h3 := sq_ge h1
    push_cast
    have e2 : ∑ i ∈ Finset.range vs.length, (m (k + (i + 1))) ^ 2 =
        ∑ i ∈ Finset.range vs.length, (m (k + 1 + i)) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by congr 2; omega
    rw [e2]
    simp only [add_zero]
    linarith

/-- Sum of a list. -/
def sumQ : List ℚ → ℚ
  | [] => 0
  | a :: t => a + sumQ t

theorem close_cheb {A : ℕ → ℝ} {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : ∀ (k : ℕ) (c e : List ℚ),
    CloseL A k c e → c.length = e.length →
    |∑ i ∈ Finset.range c.length, A (k + i) * basis (k + i) z - rawQ c k z| ≤ (sumQ e : ℝ)
  | k, [], [], _, _ => by simp [rawQ, sumQ]
  | _, [], _ :: _, _, h => by simp at h
  | _, _ :: _, [], _, h => by simp at h
  | k, c :: cs, e :: es, hc, h => by
    obtain ⟨h1, h2⟩ := hc
    have ih := close_cheb hz (k + 1) cs es h2 (by simpa using h)
    have hb := abs_basis_le_one k hz
    rw [List.length_cons, Finset.sum_range_succ']
    have e1 : ∑ i ∈ Finset.range cs.length, A (k + (i + 1)) * basis (k + (i + 1)) z =
        ∑ i ∈ Finset.range cs.length, A (k + 1 + i) * basis (k + 1 + i) z :=
      Finset.sum_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by ring]
    rw [e1]
    simp only [rawQ, sumQ, add_zero]
    have e2 : ∑ i ∈ Finset.range cs.length, A (k + 1 + i) * basis (k + 1 + i) z + A k * basis k z -
        ((c : ℝ) * basis k z + rawQ cs (k + 1) z) =
        (∑ i ∈ Finset.range cs.length, A (k + 1 + i) * basis (k + 1 + i) z - rawQ cs (k + 1) z) +
        (A k - c) * basis k z := by ring
    rw [e2]
    push_cast
    refine (abs_add_le _ _).trans ?_
    have h3 : |(A k - c) * basis k z| ≤ (e : ℝ) := by
      rw [abs_mul]
      have := abs_nonneg (A k - c)
      calc |A k - c| * |basis k z| ≤ |A k - c| * 1 := by gcongr
        _ ≤ _ := by linarith
    linarith

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail (hasDeriv_basis abs_U_le)
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

noncomputable section

/-! ### Chord errors -/

/-- `f` lies below its chord on `[b,a]` up to `e`. -/
def CE (f : ℝ → ℝ) (b a e : ℝ) : Prop :=
  ∀ x ∈ Icc b a, f x ≤ ((a - x) * f b + (x - b) * f a) / (a - b) + e

theorem CE.add {f g : ℝ → ℝ} {b a e1 e2 : ℝ} (hab : b < a) (h1 : CE f b a e1) (h2 : CE g b a e2) :
    CE (fun x => f x + g x) b a (e1 + e2) := by
  intro x hx
  have q1 := h1 x hx
  have q2 := h2 x hx
  have e : ((a - x) * (f b + g b) + (x - b) * (f a + g a)) / (a - b) =
      ((a - x) * f b + (x - b) * f a) / (a - b) + ((a - x) * g b + (x - b) * g a) / (a - b) := by
    rw [← add_div]; ring_nf
  simp only [e]
  linarith

theorem CE.congr {f g : ℝ → ℝ} {b a e : ℝ} (h : CE f b a e) (hb : b ≤ a) (hfg : ∀ x ∈ Icc b a, g x = f x) :
    CE g b a e := by
  intro x hx
  rw [hfg x hx, hfg b ⟨le_rfl, hb⟩, hfg a ⟨hb, le_rfl⟩]
  exact h x hx

theorem CE.mono {f : ℝ → ℝ} {b a e e' : ℝ} (h : CE f b a e) (he : e ≤ e') : CE f b a e' :=
  fun x hx => (h x hx).trans (by linarith)

theorem CE_const {b a : ℝ} (hab : b < a) (c : ℝ) : CE (fun _ => c) b a 0 := by
  intro x _
  have : a - b ≠ 0 := by linarith
  have e : ((a - x) * c + (x - b) * c) / (a - b) = c := by field_simp; ring
  simp only [e]
  linarith

theorem CE.const_mul {f : ℝ → ℝ} {b a e c : ℝ} (hab : b < a) (hc : 0 ≤ c) (h : CE f b a e) :
    CE (fun x => c * f x) b a (c * e) := by
  intro x hx
  have q := mul_le_mul_of_nonneg_left (h x hx) hc
  refine q.trans (le_of_eq ?_)
  have : a - b ≠ 0 := by linarith
  field_simp

theorem CE_of_deriv2 {f f' f'' : ℝ → ℝ} {b a M : ℝ} (hab : b < a) (hM0 : 0 ≤ M)
    (hf : ∀ x ∈ Icc b a, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc b a, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc b a, -M ≤ f'' x) : CE f b a (M * (a - b) ^ 2 / 8) := by
  set g : ℝ → ℝ := fun x => f x + M / 2 * ((x - b) * (x - a)) with hg
  have hconv : ConvexOn ℝ (Icc b a) g := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc b a)
      (f' := fun x => f' x + M / 2 * (2 * x - b - a)) (f'' := fun x => f'' x + M) ?_ ?_ ?_ ?_
    · intro x hx
      have := (hf x hx).continuousAt.continuousWithinAt (s := Icc b a)
      exact this.add (by fun_prop)
    · intro x hx
      have hx' := interior_subset hx
      have h2 : HasDerivAt (fun x : ℝ => M / 2 * ((x - b) * (x - a))) (M / 2 * (2 * x - b - a)) x := by
        have h := (((hasDerivAt_id x).sub_const b).mul ((hasDerivAt_id x).sub_const a)).const_mul (M / 2)
        refine h.congr_deriv ?_
        simp only [id]; ring
      exact ((hf x hx').add h2).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      have h2 : HasDerivAt (fun x : ℝ => M / 2 * (2 * x - b - a)) M x := by
        have h := ((((hasDerivAt_id x).const_mul 2).sub_const b).sub_const a).const_mul (M / 2)
        refine h.congr_deriv ?_
        ring
      exact ((hf' x hx').add h2).hasDerivWithinAt
    · intro x hx
      have := hM x (interior_subset hx)
      show 0 ≤ f'' x + M
      linarith
  intro x hx
  have hd : 0 < a - b := by linarith
  have a0 : 0 ≤ (a - x) / (a - b) := div_nonneg (by linarith [hx.2]) hd.le
  have b0 : 0 ≤ (x - b) / (a - b) := div_nonneg (by linarith [hx.1]) hd.le
  have ab : (a - x) / (a - b) + (x - b) / (a - b) = 1 := by field_simp; ring
  have := hconv.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) a0 b0 ab
  have e : ((a - x) / (a - b)) • b + ((x - b) / (a - b)) • a = x := by
    simp only [smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd.ne']
    ring
  rw [e] at this
  simp only [smul_eq_mul, hg] at this
  have e2 : (a - x) / (a - b) * (f b + M / 2 * ((b - b) * (b - a))) +
      (x - b) / (a - b) * (f a + M / 2 * ((a - b) * (a - a))) =
      ((a - x) * f b + (x - b) * f a) / (a - b) := by
    field_simp; ring
  rw [e2] at this
  have h3 : M / 2 * ((x - b) * (a - x)) ≤ M * (a - b) ^ 2 / 8 := by
    have : (x - b) * (a - x) ≤ (a - b) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
    nlinarith
  nlinarith

/-! ### Base terms -/

/-- `c (x/ρ)^n` with `(x/ρ)^n ≤ 1`: only a negative `c` costs anything. -/
theorem CE_zpow {c ρ b a : ℝ} {n : ℤ} (hb : 0 < b) (hab : b < a) (hρ : 0 < ρ)
    (hy : ∀ x ∈ Icc b a, (x / ρ) ^ n ≤ 1) :
    CE (fun x => c * (x / ρ) ^ n) b a
      (max (-c) 0 * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) * (a - b) ^ 2 / 8) := by
  have hnn : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    have : 0 ≤ n * (n - 1) := by
      rcases le_or_gt n 0 with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
      · exact mul_nonneg h.le (by omega)
    exact_mod_cast this
  have hpos : ∀ x ∈ Icc b a, 0 < x := fun x hx => lt_of_lt_of_le hb hx.1
  set C := c * (ρ ^ n)⁻¹ with hC
  have hform : ∀ x, x ≠ 0 → c * (x / ρ) ^ n = C * x ^ n := by
    intro x _
    rw [div_zpow, hC]; ring
  have hmain : CE (fun x => C * x ^ n) b a
      (max (-c) 0 * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) * (a - b) ^ 2 / 8) := by
    refine CE_of_deriv2 (f' := fun x => C * ((n : ℝ) * x ^ (n - 1)))
      (f'' := fun x => C * ((n : ℝ) * (((n - 1 : ℤ) : ℝ) * x ^ (n - 1 - 1)))) hab (by positivity) ?_ ?_ ?_
    · intro x hx
      exact (hasDerivAt_zpow n x (Or.inl (hpos x hx).ne')).const_mul C
    · intro x hx
      exact ((hasDerivAt_zpow (n - 1) x (Or.inl (hpos x hx).ne')).const_mul (n : ℝ)).const_mul C
    · intro x hx
      have hx0 := hpos x hx
      have hyy := hy x hx
      have hy0 : 0 ≤ (x / ρ) ^ n := by positivity
      have e : C * ((n : ℝ) * (((n - 1 : ℤ) : ℝ) * x ^ (n - 1 - 1))) =
          c * ((n : ℝ) * ((n : ℝ) - 1)) * ((x / ρ) ^ n / x ^ 2) := by
        have : x ^ (n - 1 - 1) = x ^ n / x ^ 2 := by
          rw [show n - 1 - 1 = n - 2 by ring, zpow_sub₀ hx0.ne']
          norm_cast
        rw [this, div_zpow, hC]
        push_cast
        field_simp
      rw [e]
      have h1 : (x / ρ) ^ n / x ^ 2 ≤ 1 / b ^ 2 := by
        apply div_le_div₀ zero_le_one hyy (by positivity)
        have := hx.1
        gcongr
      have h0 : 0 ≤ (x / ρ) ^ n / x ^ 2 := by positivity
      rcases le_or_gt 0 c with hc | hc
      · have : 0 ≤ c * ((n : ℝ) * ((n : ℝ) - 1)) * ((x / ρ) ^ n / x ^ 2) := by positivity
        rw [max_eq_right (by linarith)]
        simp only [zero_mul, neg_zero]
        exact this
      · rw [max_eq_left (by linarith)]
        have h3 : ((n : ℝ) * ((n : ℝ) - 1)) * ((x / ρ) ^ n / x ^ 2) ≤
            ((n : ℝ) * ((n : ℝ) - 1)) * (1 / b ^ 2) := by gcongr
        have h4 : -c * (((n : ℝ) * ((n : ℝ) - 1)) * ((x / ρ) ^ n / x ^ 2)) ≤
            -c * (((n : ℝ) * ((n : ℝ) - 1)) * (1 / b ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
        have e5 : -c * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) =
            -c * (((n : ℝ) * ((n : ℝ) - 1)) * (1 / b ^ 2)) := by ring
        rw [e5]
        nlinarith
  exact hmain.congr hab.le fun x hx => hform x (hpos x hx).ne'

theorem CE_log {m b a : ℝ} (hm : 0 ≤ m) (hb : 0 < b) (hab : b < a) :
    CE (fun x => m * Real.log x) b a ((m / b ^ 2) * (a - b) ^ 2 / 8) := by
  have hpos : ∀ x ∈ Icc b a, 0 < x := fun x hx => lt_of_lt_of_le hb hx.1
  refine CE_of_deriv2 (f' := fun x => m * x⁻¹) (f'' := fun x => m * (-(x ^ 2)⁻¹)) hab (by positivity) ?_ ?_ ?_
  · intro x hx
    exact (Real.hasDerivAt_log (hpos x hx).ne').const_mul m
  · intro x hx
    have := (hasDerivAt_inv (hpos x hx).ne').const_mul m
    exact this
  · intro x hx
    have hx0 := hpos x hx
    have h1 : (x ^ 2)⁻¹ ≤ 1 / b ^ 2 := by
      rw [one_div]
      have := hx.1
      gcongr
    have : m * (x ^ 2)⁻¹ ≤ m * (1 / b ^ 2) := mul_le_mul_of_nonneg_left h1 hm
    have e : m / b ^ 2 = m * (1 / b ^ 2) := by ring
    rw [e]
    linarith

theorem CE_log1 {s b a : ℝ} (hs : 0 ≤ s) (hab : b < a) :
    CE (fun x => -s * Real.log (1 + x ^ 2)) b a ((2 * s) * (a - b) ^ 2 / 8) := by
  have hp : ∀ x : ℝ, 0 < 1 + x ^ 2 := fun x => by positivity
  refine CE_of_deriv2 (f' := fun x => -s * (2 * x / (1 + x ^ 2)))
    (f'' := fun x => -s * ((2 * (1 + x ^ 2) - 2 * x * (2 * x)) / (1 + x ^ 2) ^ 2)) hab (by positivity) ?_ ?_ ?_
  · intro x _
    have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
      have := ((hasDerivAt_pow 2 x).const_add 1)
      refine this.congr_deriv ?_
      push_cast; ring
    exact (h1.log (hp x).ne').const_mul (-s)
  · intro x _
    have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
      have := ((hasDerivAt_pow 2 x).const_add 1)
      refine this.congr_deriv ?_
      push_cast; ring
    have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
      have := (hasDerivAt_id x).const_mul 2
      refine this.congr_deriv ?_
      ring
    exact (h2.div h1 (hp x).ne').const_mul (-s)
  · intro x _
    have h3 : (2 * (1 + x ^ 2) - 2 * x * (2 * x)) / (1 + x ^ 2) ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
    nlinarith

/-- Derivative of `U_n`. -/
def dU (n : ℕ) (z : ℝ) : ℝ :=
  (Polynomial.derivative (Polynomial.Chebyshev.U ℝ (n : ℤ))).eval z

theorem hasDeriv_U (n : ℕ) (z : ℝ) :
    HasDerivAt (fun z => (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval z) (dU n z) z :=
  (Polynomial.Chebyshev.U ℝ (n : ℤ)).hasDerivAt z

theorem dU_add_two (n : ℕ) (z : ℝ) :
    dU (n + 2) z = 2 * (((n : ℝ) + 2) * (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval z) + dU n z := by
  unfold dU
  have h := Polynomial.Chebyshev.U_eq_two_mul_T_add_U ℝ (n : ℤ)
  have hd := Polynomial.Chebyshev.T_derivative_eq_U (R := ℝ) ((n : ℤ) + 2)
  push_cast
  rw [h, Polynomial.derivative_add, Polynomial.derivative_mul, hd]
  simp only [Polynomial.derivative_ofNat, zero_mul, zero_add, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_intCast]
  have e : (n : ℤ) + 2 - 1 = (n : ℤ) + 1 := by ring
  rw [e]
  simp

theorem abs_dU_le {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (n : ℕ) :
    |dU n z| ≤ ((n : ℝ) + 1) ^ 3 ∧ |dU (n + 1) z| ≤ ((n : ℝ) + 2) ^ 3 := by
  induction n with
  | zero =>
    constructor
    · simp [dU]
    · have : dU 1 z = 2 := by simp [dU, Polynomial.Chebyshev.U_one]
      rw [this]; norm_num
  | succ n ih =>
    refine ⟨by push_cast; convert ih.2 using 2; ring, ?_⟩
    rw [show n + 1 + 1 = n + 2 by ring, dU_add_two]
    have hU := abs_U_le hz (n + 1)
    have hn : (0 : ℝ) ≤ n := by positivity
    calc |2 * (((n : ℝ) + 2) * (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval z) + dU n z|
        ≤ 2 * (((n : ℝ) + 2) * ((n : ℝ) + 2)) + ((n : ℝ) + 1) ^ 3 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
          have h1 : |(Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval z| ≤ (n : ℝ) + 2 := by
            refine hU.trans (le_of_eq ?_); push_cast; ring
          have := ih.1
          gcongr
      _ ≤ _ := by push_cast; nlinarith [hn, mul_nonneg hn hn, mul_nonneg (mul_nonneg hn hn) hn]

/-- The affine pullback of one Chebyshev term. -/
theorem CE_basis {c α β b a : ℝ} (n : ℕ) (hab : b < a) (hz : ∀ x ∈ Icc b a, α * x + β ∈ Icc (-1 : ℝ) 1) :
    CE (fun x => c * basis n (α * x + β)) b a ((|c| * (n : ℝ) ^ 4 * α ^ 2) * (a - b) ^ 2 / 8) := by
  rcases n with _ | n
  · have := CE_const hab c
    refine (this.congr hab.le fun x _ => by simp [basis_zero]).mono ?_
    simp
  have hin : ∀ x : ℝ, HasDerivAt (fun x => α * x + β) α x := fun x => by
    have := ((hasDerivAt_id x).const_mul α).add_const β
    refine this.congr_deriv ?_
    ring
  refine CE_of_deriv2 (f' := fun x => c * ((((n : ℝ) + 1) *
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (α * x + β)) * α))
    (f'' := fun x => c * ((((n : ℝ) + 1) * (dU n (α * x + β) * α)) * α)) hab (by positivity) ?_ ?_ ?_
  · intro x _
    exact ((hasDeriv_basis n (α * x + β)).comp x (hin x)).const_mul c
  · intro x _
    have h1 := (hasDeriv_U n (α * x + β)).comp x (hin x)
    exact (((h1.const_mul ((n : ℝ) + 1))).mul_const α).const_mul c
  · intro x hx
    have hU := (abs_dU_le (hz x hx) n).1
    have hb : |c * ((((n : ℝ) + 1) * (dU n (α * x + β) * α)) * α)| ≤
        |c| * (((n + 1 : ℕ) : ℝ)) ^ 4 * α ^ 2 := by
      have e : c * ((((n : ℝ) + 1) * (dU n (α * x + β) * α)) * α) =
          c * (((n : ℝ) + 1) * dU n (α * x + β)) * α ^ 2 := by ring
      rw [e, abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1),
        abs_of_nonneg (sq_nonneg α)]
      have : ((n : ℝ) + 1) * |dU n (α * x + β)| ≤ (((n + 1 : ℕ) : ℝ)) ^ 4 := by
        push_cast
        calc ((n : ℝ) + 1) * |dU n (α * x + β)| ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ 3 := by gcongr
          _ = _ := by ring
      gcongr
    exact (abs_le.mp hb).1

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail (basis_add_two basis_one')
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

/-! ### Radial blocks -/

/-- One radial block: `M log max(x,ρ) + 2^-W Σ_j D_j ψ^(j+1)`. -/
structure Blk where
  rho : ℚ
  sg : ℚ
  M : ℚ
  D : List ℤ

/-- `Σ_j d_j y^(k+j+1)`. -/
noncomputable def polK : List ℤ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | d :: t, k, y => (d : ℝ) * y ^ (k + 1) + polK t (k + 1) y

theorem polK_eq (y : ℝ) : ∀ (D : List ℤ) (k : ℕ), polK D k y = y ^ (k + 1) * Pz D y
  | [], _ => by simp [polK, Pz]
  | d :: t, k => by
    simp only [polK, Pz, polK_eq y t (k + 1)]
    ring

noncomputable def psiR (ρ x : ℝ) : ℝ := if ρ < x then ρ / x else x / ρ

noncomputable def blkF (W : ℕ) (B : Blk) (x : ℝ) : ℝ :=
  (B.M : ℝ) * Real.log (max x B.rho) + polK B.D 0 (psiR B.rho x) / 2 ^ W

/-- The negative part of the second-derivative weight of a block. -/
def S2 : List ℤ → ℕ → ℤ
  | [], _ => 0
  | d :: t, k => max (-d) 0 * (((k : ℤ) + 1) * ((k : ℤ) + 2)) + S2 t (k + 1)

theorem S2_nonneg : ∀ (D : List ℤ) (k : ℕ), 0 ≤ S2 D k
  | [], _ => le_rfl
  | d :: t, k => by
    have := S2_nonneg t (k + 1)
    have h1 : 0 ≤ max (-d) 0 := le_max_right _ _
    have : 0 ≤ max (-d) 0 * (((k : ℤ) + 1) * ((k : ℤ) + 2)) := by positivity
    simp only [S2]
    omega

noncomputable section

theorem CE_polK {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {ρ b a : ℝ} (hb : 0 < b) (hab : b < a) (hρ : 0 < ρ)
    (hy : ∀ x ∈ Icc b a, (x / ρ) ^ ε ≤ 1) : ∀ (D : List ℤ) (k : ℕ),
    CE (fun x => polK D k ((x / ρ) ^ ε)) b a (((S2 D k : ℤ) : ℝ) / b ^ 2 * (a - b) ^ 2 / 8)
  | [], k => by
    have := CE_const hab 0
    simpa [polK, S2] using this
  | d :: t, k => by
    have ih := CE_polK hε hb hab hρ hy t (k + 1)
    set n : ℤ := ε * ((k : ℤ) + 1) with hn
    have hpw : ∀ x ∈ Icc b a, ((x / ρ) ^ ε) ^ (k + 1) = (x / ρ) ^ n := by
      intro x _
      rw [hn, zpow_mul]
      norm_cast
    have h1 : ∀ x ∈ Icc b a, (x / ρ) ^ n ≤ 1 := by
      intro x hx
      rw [← hpw x hx]
      have h0 : 0 ≤ (x / ρ) ^ ε := by
        have : 0 < x := lt_of_lt_of_le hb hx.1
        positivity
      exact pow_le_one₀ h0 (hy x hx)
    have hz := CE_zpow (c := (d : ℝ)) hb hab hρ h1
    have hz' : CE (fun x => (d : ℝ) * ((x / ρ) ^ ε) ^ (k + 1)) b a
        (max (-(d : ℝ)) 0 * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) * (a - b) ^ 2 / 8) :=
      hz.congr hab.le fun x hx => by rw [hpw x hx]
    have hsum := hz'.add hab ih
    refine (hsum.congr hab.le fun x _ => by simp only [polK]).mono ?_
    have hnn : (n : ℝ) * ((n : ℝ) - 1) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      have hk : (0 : ℝ) ≤ k := by positivity
      rcases hε with rfl | rfl
      · simp only [hn]; push_cast; nlinarith
      · simp only [hn]; push_cast; nlinarith
    have hS : ((S2 (d :: t) k : ℤ) : ℝ) =
        max (-(d : ℝ)) 0 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) + ((S2 t (k + 1) : ℤ) : ℝ) := by
      simp only [S2]
      push_cast
      ring
    rw [hS]
    have hm : 0 ≤ max (-(d : ℝ)) 0 := le_max_right _ _
    have hb2 : 0 < b ^ 2 := by positivity
    have hd2 : 0 ≤ (a - b) ^ 2 / 8 := by positivity
    have e1 : max (-(d : ℝ)) 0 * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) * (a - b) ^ 2 / 8 =
        (max (-(d : ℝ)) 0 * ((n : ℝ) * ((n : ℝ) - 1))) / b ^ 2 * ((a - b) ^ 2 / 8) := by ring
    have e2 : ((max (-(d : ℝ)) 0 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) + ((S2 t (k + 1) : ℤ) : ℝ))) / b ^ 2 *
        (a - b) ^ 2 / 8 = (max (-(d : ℝ)) 0 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) / b ^ 2 * ((a - b) ^ 2 / 8) +
        ((S2 t (k + 1) : ℤ) : ℝ) / b ^ 2 * (a - b) ^ 2 / 8 := by ring
    rw [e1, e2]
    have : (max (-(d : ℝ)) 0 * ((n : ℝ) * ((n : ℝ) - 1))) / b ^ 2 * ((a - b) ^ 2 / 8) ≤
        (max (-(d : ℝ)) 0 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) / b ^ 2 * ((a - b) ^ 2 / 8) := by
      gcongr
    linarith

/-- Weight of one block on a cell. -/
def blkE (W : ℕ) (B : Blk) : ℝ := (B.M : ℝ) + ((S2 B.D 0 : ℤ) : ℝ) / 2 ^ W

theorem CE_blk (W : ℕ) (B : Blk) {b a : ℝ} (hb : 0 < b) (hab : b < a) (hρ : (0 : ℝ) < B.rho)
    (hM : (0 : ℝ) ≤ B.M) (hsep : (B.rho : ℝ) ≤ b ∨ a ≤ B.rho) :
    CE (blkF W B) b a (blkE W B / b ^ 2 * (a - b) ^ 2 / 8) := by
  have hq : (0 : ℝ) ≤ 1 / 2 ^ W := by positivity
  have hb2 : 0 < b ^ 2 := by positivity
  rcases hsep with h | h
  · have hpsi : ∀ x ∈ Icc b a, psiR B.rho x = (x / B.rho) ^ (-1 : ℤ) := by
      intro x hx
      have hxr : (B.rho : ℝ) ≤ x := h.trans hx.1
      have hx0 : 0 < x := lt_of_lt_of_le hb hx.1
      unfold psiR
      split_ifs with hl
      · rw [zpow_neg_one, inv_div]
      · have : x = B.rho := le_antisymm (not_lt.mp hl) hxr
        rw [this, div_self hρ.ne']; simp
    have h1 := CE_log hM hb hab
    have hy : ∀ x ∈ Icc b a, (x / (B.rho : ℝ)) ^ (-1 : ℤ) ≤ 1 := by
      intro x hx
      have hxr : (B.rho : ℝ) ≤ x := h.trans hx.1
      have hx0 : 0 < x := lt_of_lt_of_le hb hx.1
      rw [zpow_neg_one, inv_div, div_le_one hx0]
      exact hxr
    have h2 := (CE_polK (Or.inr rfl) hb hab hρ hy B.D 0).const_mul hab hq
    refine ((h1.add hab h2).congr hab.le ?_).mono (le_of_eq ?_)
    · intro x hx
      have hxr : (B.rho : ℝ) ≤ x := h.trans hx.1
      simp only [blkF, max_eq_left hxr, hpsi x hx]
      ring
    · unfold blkE
      ring
  · have hpsi : ∀ x ∈ Icc b a, psiR B.rho x = (x / B.rho) ^ (1 : ℤ) := by
      intro x hx
      have hxr : x ≤ B.rho := hx.2.trans h
      unfold psiR
      rw [if_neg (not_lt.mpr hxr), zpow_one]
    have h1 := CE_const hab ((B.M : ℝ) * Real.log B.rho)
    have hy : ∀ x ∈ Icc b a, (x / (B.rho : ℝ)) ^ (1 : ℤ) ≤ 1 := by
      intro x hx
      rw [zpow_one, div_le_one hρ]
      exact hx.2.trans h
    have h2 := (CE_polK (Or.inl rfl) hb hab hρ hy B.D 0).const_mul hab hq
    refine (((h1.add hab h2).congr hab.le ?_).mono ?_)
    · intro x hx
      have hxr : x ≤ B.rho := hx.2.trans h
      simp only [blkF, max_eq_right hxr, hpsi x hx]
      ring
    · unfold blkE
      have hd : 0 ≤ (B.M : ℝ) / b ^ 2 * (a - b) ^ 2 / 8 := by positivity
      have e : ((B.M : ℝ) + ((S2 B.D 0 : ℤ) : ℝ) / 2 ^ W) / b ^ 2 * (a - b) ^ 2 / 8 =
          (B.M : ℝ) / b ^ 2 * (a - b) ^ 2 / 8 +
            1 / 2 ^ W * (((S2 B.D 0 : ℤ) : ℝ) / b ^ 2 * (a - b) ^ 2 / 8) := by ring
      rw [e]
      linarith

def sumF (W : ℕ) (Bs : List Blk) (x : ℝ) : ℝ := (Bs.map fun B => blkF W B x).sum

def sumE (W : ℕ) (Bs : List Blk) : ℝ := (Bs.map fun B => blkE W B).sum

theorem CE_sum (W : ℕ) {b a : ℝ} (hb : 0 < b) (hab : b < a) : ∀ (Bs : List Blk),
    (∀ B ∈ Bs, (0 : ℝ) < B.rho ∧ (0 : ℝ) ≤ B.M ∧ ((B.rho : ℝ) ≤ b ∨ a ≤ B.rho)) →
    CE (sumF W Bs) b a (sumE W Bs / b ^ 2 * (a - b) ^ 2 / 8)
  | [], _ => by
    have := CE_const hab 0
    exact (this.congr hab.le fun x _ => by simp [sumF]).mono (by simp [sumE])
  | B :: t, h => by
    have h1 := h B (by simp)
    have ih := CE_sum W hb hab t fun B hB => h B (List.mem_cons_of_mem _ hB)
    have := (CE_blk W B hb hab h1.1 h1.2.1 h1.2.2).add hab ih
    refine (this.congr hab.le fun x _ => by simp [sumF]).mono (le_of_eq ?_)
    simp only [sumE, List.map_cons, List.sum_cons]
    ring

/-- Fourth-power weight of a Chebyshev list. -/
def mc4 : List ℚ → ℕ → ℚ
  | [], _ => 0
  | c :: t, k => |c| * (k : ℚ) ^ 4 + mc4 t (k + 1)

theorem CE_rawQ {α β b a : ℝ} (hab : b < a) (hz : ∀ x ∈ Icc b a, α * x + β ∈ Icc (-1 : ℝ) 1) :
    ∀ (l : List ℚ) (k : ℕ),
    CE (fun x => -rawQ l k (α * x + β)) b a (((mc4 l k : ℚ) : ℝ) * α ^ 2 * (a - b) ^ 2 / 8)
  | [], k => by
    have := CE_const hab 0
    simpa [rawQ, mc4] using this
  | c :: t, k => by
    have ih := CE_rawQ hab hz t (k + 1)
    have h1 := CE_basis (c := -(c : ℝ)) k hab hz
    refine ((h1.add hab ih).congr hab.le fun x _ => ?_).mono (le_of_eq ?_)
    · simp only [rawQ]; ring
    · simp only [mc4]
      push_cast
      rw [abs_neg]
      ring

/-- The cover function. -/
structure Cov where
  W : ℕ
  Bs : List Blk
  s : ℚ
  Cl : List ℚ
  α : ℚ
  β : ℚ

def Cov.Phi (C : Cov) (x : ℝ) : ℝ :=
  sumF C.W C.Bs x + (-(C.s : ℝ) * Real.log (1 + x ^ 2)) + -rawQ C.Cl 0 ((C.α : ℝ) * x + C.β)

theorem Cov.CE (C : Cov) {b a : ℝ} (hb : 0 < b) (hab : b < a) (hs : (0 : ℝ) ≤ C.s)
    (hz : ∀ x ∈ Icc b a, (C.α : ℝ) * x + C.β ∈ Icc (-1 : ℝ) 1)
    (h : ∀ B ∈ C.Bs, (0 : ℝ) < B.rho ∧ (0 : ℝ) ≤ B.M ∧ ((B.rho : ℝ) ≤ b ∨ a ≤ B.rho)) :
    OrdHf.CE C.Phi b a ((a - b) ^ 2 / 8 * (sumE C.W C.Bs / b ^ 2 + (2 * (C.s : ℝ) +
      ((mc4 C.Cl 0 : ℚ) : ℝ) * (C.α : ℝ) ^ 2))) := by
  have h1 := CE_sum C.W hb hab C.Bs h
  have h2 := CE_log1 hs hab
  have h3 := CE_rawQ hab hz C.Cl 0
  refine (((h1.add hab h2).add hab h3).congr hab.le fun x _ => rfl).mono (le_of_eq ?_)
  ring

theorem CE.le_max {f : ℝ → ℝ} {b a e vb va : ℝ} (hab : b < a) (h : OrdHf.CE f b a e)
    (hb : f b ≤ vb) (ha : f a ≤ va) : ∀ x ∈ Icc b a, f x ≤ max va vb + e := by
  intro x hx
  have q := h x hx
  have hd : 0 < a - b := by linarith
  have h1 : (a - x) * f b ≤ (a - x) * max va vb :=
    mul_le_mul_of_nonneg_left (hb.trans (le_max_right _ _)) (by linarith [hx.2])
  have h2 : (x - b) * f a ≤ (x - b) * max va vb :=
    mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (by linarith [hx.1])
  have h3 : ((a - x) * f b + (x - b) * f a) / (a - b) ≤ max va vb := by
    rw [div_le_iff₀ hd]
    nlinarith
  linarith

end

/-! ### Node values -/

/-- `⌈p t / q⌉` Horner with rounding up. -/
def hU (p q : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: t => d + -((-(p * hU p q t)) / q)

theorem hU_spec {p q : ℤ} (hp : 0 ≤ p) (hq : 0 < q) : ∀ D : List ℤ,
    Pz D ((p : ℝ) / q) ≤ (hU p q D : ℝ)
  | [] => by simp [Pz, hU]
  | d :: t => by
    have ih := hU_spec hp hq t
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hp' : (0 : ℝ) ≤ p := by exact_mod_cast hp
    have h1 : (-(p * hU p q t)) / q * q ≤ -(p * hU p q t) := by
      have := Int.mul_ediv_add_emod (-(p * hU p q t)) q
      have h2 := Int.emod_nonneg (-(p * hU p q t)) hq.ne'
      nlinarith
    have h1' : (((-(p * hU p q t)) / q : ℤ) : ℝ) * q ≤ -((p : ℝ) * (hU p q t : ℝ)) := by
      exact_mod_cast h1
    simp only [Pz, hU]
    push_cast
    have h3 : (p : ℝ) / q * Pz t ((p : ℝ) / q) ≤ -(((-(p * hU p q t)) / q : ℤ) : ℝ) := by
      calc (p : ℝ) / q * Pz t ((p : ℝ) / q) ≤ (p : ℝ) / q * (hU p q t : ℝ) := by gcongr
        _ ≤ _ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hq']
          linarith
    push_cast at h3
    linarith

/-- Rational forward Chebyshev evaluation. -/
def evT (z : ℚ) : ℚ → ℚ → List ℚ → ℚ
  | _, _, [] => 0
  | t0, t1, c :: l => c * t0 + evT z t1 (2 * z * t1 - t0) l

theorem evT_spec (z : ℚ) : ∀ (l : List ℚ) (k : ℕ) (t0 t1 : ℚ),
    (t0 : ℝ) = basis k z → (t1 : ℝ) = basis (k + 1) z →
    ((evT z t0 t1 l : ℚ) : ℝ) = rawQ l k z
  | [], _, _, _, _, _ => by simp [evT, rawQ]
  | c :: l, k, t0, t1, h0, h1 => by
    have := evT_spec z l (k + 1) t1 (2 * z * t1 - t0) h1 (by
      rw [show k + 1 + 1 = k + 2 by ring, basis_add_two]
      push_cast
      rw [h0, h1])
    simp only [evT, rawQ]
    push_cast
    rw [this, h0]

/-- `log x` enclosure from `Cert.WLog`; a failed call has negative error. -/
def logE (x : ℚ) : ℚ × ℚ :=
  match CatalanMeasure.WLog.expPQ x.num.toNat x.den with
  | some (m, P, Q) =>
    match CatalanMeasure.WLog.lnQP 6 m P Q with
    | some r => r
    | none => (0, -1)
  | none => (0, -1)

theorem logE_spec {x : ℚ} (hx : 0 < x) (he : 0 ≤ (logE x).2) :
    |Real.log x - ((logE x).1 : ℝ)| ≤ ((logE x).2 : ℝ) := by
  unfold logE at he ⊢
  split at he
  · rename_i m P Q h1
    split at he
    · rename_i r h2
      first | rw [h2] | skip
      obtain ⟨hQ, h3, h4, h5⟩ := CatalanMeasure.WLog.expPQ_spec h1
      have := CatalanMeasure.WLog.lnQP_spec (v := r.1) (e := r.2) hQ h3 h4 (by simpa using h2)
      rw [← h5] at this
      have hn : ((x.num.toNat : ℕ) : ℝ) = (x.num : ℝ) := by
        have : ((x.num.toNat : ℕ) : ℤ) = x.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx.le)
        exact_mod_cast this
      have hxr : (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) := by
        have := Rat.num_div_den x
        conv_lhs => rw [← this]
        push_cast
        rfl
      rw [hn, ← hxr] at this
      simpa using this
    · simp at he; norm_num at he
  · simp at he; norm_num at he

def logHi (x : ℚ) : ℚ := (logE x).1 + (logE x).2
def logLo (x : ℚ) : ℚ := (logE x).1 - (logE x).2

/-- Node value of a block, given an upper bound `Lx` for `log x`. -/
def blkV (W : ℕ) (x Lx : ℚ) (B : Blk) : ℚ :=
  if B.rho < x then
    let y := B.rho / x
    B.M * Lx + y * (hU y.num (y.den : ℤ) B.D : ℚ) / 2 ^ W
  else
    let y := x / B.rho
    B.M * B.sg + y * (hU y.num (y.den : ℤ) B.D : ℚ) / 2 ^ W

def sumV (W : ℕ) (x Lx : ℚ) : List Blk → ℚ
  | [] => 0
  | B :: t => blkV W x Lx B + sumV W x Lx t

def Cov.evC (C : Cov) (x : ℚ) : ℚ := evT (C.α * x + C.β) 1 (C.α * x + C.β) C.Cl

def Cov.V (C : Cov) (x : ℚ) : ℚ :=
  sumV C.W x (logHi x) C.Bs + -C.s * logLo (1 + x ^ 2) +
    -C.evC x

/-- A node is valid when both logarithm calls succeeded and the value is below `v`. -/
def Cov.nodeOK (C : Cov) (n : ℚ × ℚ) : Bool :=
  decide (0 ≤ (logE n.1).2) && decide (0 ≤ (logE (1 + n.1 ^ 2)).2) && decide (C.V n.1 ≤ n.2)

noncomputable section

theorem blkV_spec (W : ℕ) {x Lx : ℚ} (B : Blk) (hx : 0 < x) (hL : Real.log x ≤ Lx) (hρ : 0 < B.rho)
    (hM : 0 ≤ B.M) (hsg : Real.log B.rho ≤ B.sg) : blkF W B x ≤ ((blkV W x Lx B : ℚ) : ℝ) := by
  have hq : (0 : ℝ) < 2 ^ W := by positivity
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have hρr : (0 : ℝ) < B.rho := by exact_mod_cast hρ
  have hMr : (0 : ℝ) ≤ B.M := by exact_mod_cast hM
  have key : ∀ y : ℚ, 0 ≤ y → (y : ℝ) ≤ 1 → polK B.D 0 (y : ℝ) / 2 ^ W ≤
      (((y * (hU y.num (y.den : ℤ) B.D : ℚ) / 2 ^ W : ℚ)) : ℝ) := by
    intro y hy _
    have hyr : (0 : ℝ) ≤ y := by exact_mod_cast hy
    have h1 := hU_spec (p := y.num) (q := (y.den : ℤ)) (Rat.num_nonneg.mpr hy)
      (by exact_mod_cast y.den_pos) B.D
    have hyy : ((y.num : ℤ) : ℝ) / (((y.den : ℤ)) : ℝ) = y := by
      have := Rat.num_div_den y
      conv_rhs => rw [← this]
      push_cast
      rfl
    rw [hyy] at h1
    rw [polK_eq]
    have h2 := mul_le_mul_of_nonneg_left h1 hyr
    simp only [zero_add, pow_one]
    push_cast
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr h2
  unfold blkF blkV
  by_cases h : B.rho < x
  · have hr : (B.rho : ℝ) < x := by exact_mod_cast h
    have hps : psiR B.rho x = ((B.rho / x : ℚ) : ℝ) := by
      unfold psiR
      rw [if_pos hr]
      push_cast
      rfl
    rw [if_pos h, max_eq_left hr.le, hps]
    have := key (B.rho / x) (by positivity) (by push_cast; rw [div_le_one hxr]; exact hr.le)
    have h2 := mul_le_mul_of_nonneg_left hL hMr
    simp only
    push_cast at this ⊢
    linarith
  · have hr : (x : ℝ) ≤ B.rho := by exact_mod_cast not_lt.mp h
    have hps : psiR B.rho x = ((x / B.rho : ℚ) : ℝ) := by
      unfold psiR
      rw [if_neg (not_lt.mpr hr)]
      push_cast
      rfl
    rw [if_neg h, max_eq_right hr, hps]
    have := key (x / B.rho) (by positivity) (by push_cast; rw [div_le_one hρr]; exact hr)
    have h2 := mul_le_mul_of_nonneg_left hsg hMr
    simp only
    push_cast at this ⊢
    linarith

theorem sumV_spec (W : ℕ) {x Lx : ℚ} (hx : 0 < x) (hL : Real.log x ≤ Lx) : ∀ (Bs : List Blk),
    (∀ B ∈ Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg) →
    sumF W Bs x ≤ ((sumV W x Lx Bs : ℚ) : ℝ)
  | [], _ => by simp [sumF, sumV]
  | B :: t, h => by
    have h1 := h B (by simp)
    have ih := sumV_spec W hx hL t fun B hB => h B (List.mem_cons_of_mem _ hB)
    have := blkV_spec W B hx hL h1.1 h1.2.1 h1.2.2
    simp only [sumF, sumV, List.map_cons, List.sum_cons] at ih ⊢
    push_cast
    linarith

theorem Cov.node_le (C : Cov) {n : ℚ × ℚ} (hx : 0 < n.1) (h : C.nodeOK n = true) (hs : 0 ≤ C.s)
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg) :
    C.Phi n.1 ≤ n.2 := by
  simp only [Cov.nodeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have l1 := abs_le.mp (logE_spec hx h1)
  have hy : 0 < 1 + n.1 ^ 2 := by positivity
  have l2 := abs_le.mp (logE_spec hy h2)
  have hL : Real.log n.1 ≤ logHi n.1 := by
    unfold logHi; push_cast; linarith [l1.2]
  have hS : ((logLo (1 + n.1 ^ 2) : ℚ) : ℝ) ≤ Real.log (1 + (n.1 : ℝ) ^ 2) := by
    unfold logLo
    have := l2.1
    push_cast at this ⊢
    linarith
  have h4 := sumV_spec C.W hx hL C.Bs hB
  have hsr : (0 : ℝ) ≤ C.s := by exact_mod_cast hs
  have h5 := mul_le_mul_of_nonneg_left hS hsr
  have hz : ((C.evC n.1 : ℚ) : ℝ) = rawQ C.Cl 0 ((C.α : ℝ) * n.1 + C.β) := by
    have := evT_spec (C.α * n.1 + C.β) C.Cl 0 1 (C.α * n.1 + C.β)
      (by simp [basis_zero]) (by push_cast; rw [basis_one'])
    push_cast at this
    exact this
  have h3' : ((C.V n.1 : ℚ) : ℝ) ≤ n.2 := by exact_mod_cast h3
  unfold Cov.V at h3'
  unfold Cov.Phi
  push_cast at h3' hz
  rw [← hz]

  linarith

/-- The bottom node. -/
def bot : ℚ × ℚ → List (ℚ × ℚ) → ℚ
  | n, [] => n.1
  | _, m :: t => bot m t

/-- Consecutive nodes: separation from every radius, range of the Chebyshev variable, and the
chord bound. -/
def Cov.chain (C : Cov) (E K Bud : ℚ) : ℚ × ℚ → List (ℚ × ℚ) → Bool
  | n, [] => decide (n.2 ≤ Bud)
  | a, b :: t =>
    decide (0 < b.1) && decide (b.1 < a.1) && decide (-1 ≤ C.α * b.1 + C.β) &&
    decide (C.α * a.1 + C.β ≤ 1) &&
    C.Bs.all (fun B => decide (B.rho ≤ b.1) || decide (a.1 ≤ B.rho)) &&
    decide (max a.2 b.2 + (a.1 - b.1) ^ 2 / 8 * (E / b.1 ^ 2 + K) ≤ Bud) &&
    Cov.chain C E K Bud b t

theorem Cov.cover (C : Cov) {E K Bud : ℚ} (hs : 0 ≤ C.s) (hα : 0 ≤ C.α)
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hE : sumE C.W C.Bs ≤ E) (hK : 2 * C.s + mc4 C.Cl 0 * C.α ^ 2 ≤ K) :
    ∀ (t : List (ℚ × ℚ)) (n : ℚ × ℚ), 0 < n.1 → C.chain E K Bud n t = true →
      (∀ m ∈ n :: t, C.nodeOK m = true) →
      ∀ x ∈ Icc ((bot n t : ℚ) : ℝ) n.1, C.Phi x ≤ Bud
  | [], n, h0, hc, hn => by
    intro x hx
    have hxe : x = n.1 := le_antisymm hx.2 hx.1
    have h1 := C.node_le h0 (hn n (by simp)) hs hB
    have h2 : (n.2 : ℝ) ≤ Bud := by
      have : n.2 ≤ Bud := by simpa [Cov.chain] using hc
      exact_mod_cast this
    rw [hxe]
    linarith
  | b :: t, a, h0, hc, hn => by
    simp only [Cov.chain, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.or_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨hb0, hba⟩, hz1⟩, hz2⟩, hsep⟩, hmax⟩, hrest⟩ := hc
    have ih := Cov.cover C hs hα hB hE hK t b hb0 hrest fun m hm => hn m (List.mem_cons_of_mem _ hm)
    intro x hx
    rcases le_or_gt (b.1 : ℝ) x with hxb | hxb
    · have hb0' : (0 : ℝ) < b.1 := by exact_mod_cast hb0
      have hba' : (b.1 : ℝ) < a.1 := by exact_mod_cast hba
      have hαr : (0 : ℝ) ≤ C.α := by exact_mod_cast hα
      have hz : ∀ y ∈ Icc (b.1 : ℝ) a.1, (C.α : ℝ) * y + C.β ∈ Icc (-1 : ℝ) 1 := by
        intro y hy
        have g1 : (-1 : ℝ) ≤ C.α * b.1 + C.β := by exact_mod_cast hz1
        have g2 : (C.α : ℝ) * a.1 + C.β ≤ 1 := by exact_mod_cast hz2
        have g3 := mul_le_mul_of_nonneg_left hy.1 hαr
        have g4 := mul_le_mul_of_nonneg_left hy.2 hαr
        constructor <;> linarith
      have hsr : (0 : ℝ) ≤ C.s := by exact_mod_cast hs
      have hce := C.CE hb0' hba' hsr hz fun B hBm => by
        obtain ⟨p1, p2, _⟩ := hB B hBm
        refine ⟨by exact_mod_cast p1, by exact_mod_cast p2, ?_⟩
        rcases hsep B hBm with q | q
        · left; exact_mod_cast q
        · right; exact_mod_cast q
      have hva := C.node_le h0 (hn a (by simp)) hs hB
      have hvb := C.node_le hb0 (hn b (by simp)) hs hB
      have hfin := CE.le_max hba' hce hvb hva x ⟨hxb, hx.2⟩
      have hmax' : (max (a.2 : ℝ) b.2) + ((a.1 : ℝ) - b.1) ^ 2 / 8 * ((E : ℝ) / (b.1 : ℝ) ^ 2 + K) ≤ Bud := by
        exact_mod_cast hmax
      have hE' : sumE C.W C.Bs ≤ (E : ℝ) := hE
      have hK' : 2 * (C.s : ℝ) + ((mc4 C.Cl 0 : ℚ) : ℝ) * (C.α : ℝ) ^ 2 ≤ K := by exact_mod_cast hK
      have : ((a.1 : ℝ) - b.1) ^ 2 / 8 * (sumE C.W C.Bs / (b.1 : ℝ) ^ 2 + (2 * (C.s : ℝ) +
          ((mc4 C.Cl 0 : ℚ) : ℝ) * (C.α : ℝ) ^ 2)) ≤
          ((a.1 : ℝ) - b.1) ^ 2 / 8 * ((E : ℝ) / (b.1 : ℝ) ^ 2 + K) := by
        gcongr
      linarith
    · exact ih x ⟨hx.1, hxb.le⟩

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.MomentInputs (abs_pow_sub_pow_le_unit)

noncomputable section

/-! ### Grouping the auxiliary list by radius -/

/-- The cosine moment of radius class `i`. -/
def aC (l : List AuxEntry) (i k : ℕ) : ℝ :=
  (l.map fun e => if e.rad = i then e.w * Real.cos ((k : ℝ) * e.phase) else 0).sum

theorem aC_cons (e : AuxEntry) (t : List AuxEntry) (i k : ℕ) :
    aC (e :: t) i k = (if e.rad = i then e.w * Real.cos ((k : ℝ) * e.phase) else 0) + aC t i k := by
  simp [aC]

theorem group_sum (n K : ℕ) (L : ℕ → ℝ) (f : ℕ → ℕ → ℝ) : ∀ l : List AuxEntry, (∀ e ∈ l, e.rad < n) →
    (l.map fun e => e.w * (L e.rad +
        ∑ k ∈ Finset.range K, f e.rad (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase))).sum =
      ∑ i ∈ Finset.range n, (aC l i 0 * L i + ∑ k ∈ Finset.range K, f i (k + 1) * aC l i (k + 1))
  | [], _ => by simp [aC]
  | e :: t, h => by
    have ih := group_sum n K L f t fun e he => h e (List.mem_cons_of_mem _ he)
    have hlt : e.rad < n := h e (by simp)
    have key : ∀ i, aC (e :: t) i 0 * L i +
        ∑ k ∈ Finset.range K, f i (k + 1) * aC (e :: t) i (k + 1) =
        (if e.rad = i then e.w * (L e.rad + ∑ k ∈ Finset.range K,
            f e.rad (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase)) else 0) +
        (aC t i 0 * L i + ∑ k ∈ Finset.range K, f i (k + 1) * aC t i (k + 1)) := by
      intro i
      simp only [aC_cons]
      split_ifs with hi
      · subst hi
        simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, mul_add, add_mul,
          Finset.sum_add_distrib, Finset.mul_sum]
        have : ∑ k ∈ Finset.range K, f e.rad (k + 1) * (e.w * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase)) =
            ∑ k ∈ Finset.range K, e.w * (f e.rad (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase)) :=
          Finset.sum_congr rfl fun k _ => by ring
        rw [this]
        ring
      · simp
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.sum_congr rfl fun i _ => key i]
    generalize e.w * (L e.rad + ∑ k ∈ Finset.range K,
      f e.rad (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase)) = X
    have h2 : ∑ i ∈ Finset.range n, (if e.rad = i then X else 0) = X := by
      rw [Finset.sum_ite_eq (Finset.range n) e.rad, if_pos (Finset.mem_range.mpr hlt)]
    conv_rhs => rw [Finset.sum_add_distrib, h2]

theorem psi_pos (r : ℝ) {x : ℝ} (hx : 0 < x) : psi r x = psiR r x := by
  unfold psi psiR
  rw [abs_of_pos hx]

theorem psi_neg (r : ℝ) {u : ℝ} (hu : 0 < u) : psi r (-u) = -psiR r u := by
  unfold psi psiR
  rw [abs_neg, abs_of_pos hu]
  split_ifs <;> ring

theorem radialA_pos (S : CapSource) (K n : ℕ) {x : ℝ} (hx : 0 < x)
    (hl : ∀ e ∈ S.aux Sign.pos, e.rad < n) :
    S.radialA (Trunc.finite K) Sign.pos x = ∑ i ∈ Finset.range n,
      (aC (S.aux Sign.pos) i 0 * Real.log (max x (S.rad i)) +
        ∑ k ∈ Finset.range K, S.coef (k + 1) * psiR (S.rad i) x ^ (k + 1) * aC (S.aux Sign.pos) i (k + 1)) := by
  rw [← group_sum n K (fun i => Real.log (max x (S.rad i)))
    (fun i k => S.coef k * psiR (S.rad i) x ^ k) _ hl]
  unfold radialA
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp [Trunc.sum, abs_of_pos hx, psi_pos _ hx]

theorem radialA_neg (S : CapSource) (K n : ℕ) {u : ℝ} (hu : 0 < u)
    (hl : ∀ e ∈ S.aux Sign.neg, e.rad < n) :
    S.radialA (Trunc.finite K) Sign.neg (-u) = ∑ i ∈ Finset.range n,
      (aC (S.aux Sign.neg) i 0 * Real.log (max u (S.rad i)) +
        ∑ k ∈ Finset.range K, ((-1) ^ (k + 1) * S.coef (k + 1)) *
          (psiR (S.rad i) u ^ (k + 1) + (S.rad i * u) ^ (k + 1)) * aC (S.aux Sign.neg) i (k + 1)) := by
  rw [← group_sum n K (fun i => Real.log (max u (S.rad i)))
    (fun i k => ((-1) ^ k * S.coef k) * (psiR (S.rad i) u ^ k + (S.rad i * u) ^ k)) _ hl]
  unfold radialA
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Trunc.sum, abs_neg, abs_of_pos hu, if_true]
  have key : ∀ k : ℕ, S.coef (k + 1) * psi (S.rad e.rad) (-u) ^ (k + 1) *
        Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) +
      S.coef (k + 1) * (S.rad e.rad * -u) ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) =
      (-1) ^ (k + 1) * S.coef (k + 1) * (psiR (S.rad e.rad) u ^ (k + 1) + (S.rad e.rad * u) ^ (k + 1)) *
        Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) := by
    intro k
    rw [psi_neg _ hu, neg_pow, mul_neg, neg_pow (S.rad e.rad * u)]
    ring
  rw [add_assoc, ← Finset.sum_add_distrib (s := Finset.range K)]
  exact congrArg (fun z => e.w * (Real.log (max u (S.rad e.rad)) + z))
    (Finset.sum_congr rfl fun k _ => key k)

/-! ### One radial series against one block list -/

/-- `Σ_{j<m} t(k+j+1) y^(k+j+1)`. -/
def serR (t : ℕ → ℝ) (y : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | k, m + 1 => t (k + 1) * y ^ (k + 1) + serR t y (k + 1) m

theorem serR_eq (t : ℕ → ℝ) (y : ℝ) (m : ℕ) :
    serR t y 0 m = ∑ k ∈ Finset.range m, t (k + 1) * y ^ (k + 1) := by
  have : ∀ (m k : ℕ), serR t y k m = ∑ j ∈ Finset.range m, t (k + j + 1) * y ^ (k + j + 1) := by
    intro m
    induction m with
    | zero => intro k; rfl
    | succ m ih =>
      intro k
      rw [serR, ih, Finset.sum_range_succ']
      simp only [add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show k + 1 + j + 1 = k + (j + 1) + 1 by ring]
  simpa using this m 0

/-- Closeness of an integer list to a sequence. -/
def CLz (t : ℕ → ℝ) (sc e : ℝ) : ℕ → List ℤ → Prop
  | _, [] => True
  | k, d :: D => |t (k + 1) - (d : ℝ) / sc| ≤ e ∧ CLz t sc e (k + 1) D

/-- `ℓ¹` norm of an integer list. -/
def abs1 : List ℤ → ℤ
  | [] => 0
  | d :: t => |d| + abs1 t

theorem abs1_nonneg : ∀ l : List ℤ, 0 ≤ abs1 l
  | [] => le_rfl
  | d :: t => by
    have := abs1_nonneg t
    have := abs_nonneg d
    simp only [abs1]
    omega

/-- The first `n` entries, shortened by `sh` bits. -/
def truncD (sh n : ℕ) (F : List ℤ) : List ℤ := (F.take n).map (· / 2 ^ sh)

theorem floor_close (d : ℤ) (W sh : ℕ) :
    |(d : ℝ) / 2 ^ (W + sh) - ((d / 2 ^ sh : ℤ) : ℝ) / 2 ^ W| ≤ 1 / 2 ^ W := by
  have hs : (0 : ℤ) < 2 ^ sh := by positivity
  have h1 : d / 2 ^ sh * 2 ^ sh ≤ d := Int.ediv_mul_le d hs.ne'
  have h2 : d < (d / 2 ^ sh + 1) * 2 ^ sh := by
    have := Int.lt_ediv_add_one_mul_self d hs
    exact this
  have hs' : (0 : ℝ) < 2 ^ sh := by positivity
  have hw : (0 : ℝ) < 2 ^ W := by positivity
  have h1' : ((d / 2 ^ sh : ℤ) : ℝ) * 2 ^ sh ≤ d := by exact_mod_cast h1
  have h2' : (d : ℝ) < (((d / 2 ^ sh : ℤ) : ℝ) + 1) * 2 ^ sh := by exact_mod_cast h2
  have e : (d : ℝ) / 2 ^ (W + sh) = (d : ℝ) / 2 ^ sh / 2 ^ W := by
    rw [pow_add]; field_simp
  rw [e, ← sub_div, abs_div, abs_of_pos hw]
  apply div_le_div_of_nonneg_right _ hw.le
  rw [abs_le]
  constructor
  · have : ((d / 2 ^ sh : ℤ) : ℝ) ≤ (d : ℝ) / 2 ^ sh := by rw [le_div_iff₀ hs']; exact h1'
    linarith
  · have : (d : ℝ) / 2 ^ sh < ((d / 2 ^ sh : ℤ) : ℝ) + 1 := by rw [div_lt_iff₀ hs']; exact h2'
    linarith

theorem ser_le {t : ℕ → ℝ} {y yh η e : ℝ} (W sh K : ℕ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hh0 : 0 ≤ yh) (hh1 : yh ≤ 1) (hη : |y - yh| ≤ η) (he : 0 ≤ e) :
    ∀ (F : List ℤ) (n k : ℕ), CLz t (2 ^ (W + sh)) e k F → k + F.length ≤ K →
    serR t y k F.length ≤ polK (truncD sh n F) k yh / 2 ^ W +
      (((abs1 (F.drop n) : ℤ) : ℝ) / 2 ^ (W + sh) + (F.length : ℝ) * (e + 1 / 2 ^ W) +
        ((abs1 (truncD sh n F) : ℤ) : ℝ) / 2 ^ W * ((K : ℝ) * η))
  | [], n, k, _, _ => by
    simp [serR, truncD, polK, abs1]
  | d :: F, 0, k, hc, hk => by
    obtain ⟨h1, h2⟩ := hc
    have ih := ser_le W sh K hy0 hy1 hh0 hh1 hη he F 0 (k + 1) h2 (by simp at hk; omega)
    simp only [truncD, List.take_zero, List.map_nil, polK, zero_div, zero_add, abs1, Int.cast_zero,
      zero_mul, add_zero, List.drop_zero] at ih ⊢
    rw [List.length_cons, serR]
    have hsc : (0 : ℝ) < 2 ^ (W + sh) := by positivity
    have hw : (0 : ℝ) ≤ 1 / 2 ^ W := by positivity
    have hp0 : 0 ≤ y ^ (k + 1) := by positivity
    have hp1 : y ^ (k + 1) ≤ 1 := pow_le_one₀ hy0 hy1
    have ht : |t (k + 1)| ≤ |(d : ℝ)| / 2 ^ (W + sh) + e := by
      have q := abs_le.mp h1
      have : |(d : ℝ) / 2 ^ (W + sh)| = |(d : ℝ)| / 2 ^ (W + sh) := by rw [abs_div, abs_of_pos hsc]
      rw [← this]
      have r := abs_sub_abs_le_abs_sub (t (k + 1)) ((d : ℝ) / 2 ^ (W + sh))
      linarith
    have h3 : t (k + 1) * y ^ (k + 1) ≤ |(d : ℝ)| / 2 ^ (W + sh) + e := by
      calc t (k + 1) * y ^ (k + 1) ≤ |t (k + 1)| * y ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hp0
        _ ≤ |t (k + 1)| * 1 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
        _ ≤ _ := by linarith
    push_cast
    have e1 : (|(d : ℝ)| + ((abs1 F : ℤ) : ℝ)) / 2 ^ (W + sh) =
        |(d : ℝ)| / 2 ^ (W + sh) + ((abs1 F : ℤ) : ℝ) / 2 ^ (W + sh) := add_div _ _ _
    rw [e1]
    nlinarith
  | d :: F, n + 1, k, hc, hk => by
    obtain ⟨h1, h2⟩ := hc
    have ih := ser_le W sh K hy0 hy1 hh0 hh1 hη he F n (k + 1) h2 (by simp at hk; omega)
    have hD : truncD sh (n + 1) (d :: F) = (d / 2 ^ sh) :: truncD sh n F := by simp [truncD]
    rw [hD, List.drop_succ_cons, List.length_cons, serR]
    simp only [polK, abs1]
    set d' := d / 2 ^ sh with hd'
    set D := truncD sh n F
    have hw : (0 : ℝ) < 2 ^ W := by positivity
    have hη0 : 0 ≤ η := (abs_nonneg _).trans hη
    have hf := floor_close d W sh
    have hp0 : 0 ≤ y ^ (k + 1) := by positivity
    have hp1 : y ^ (k + 1) ≤ 1 := pow_le_one₀ hy0 hy1
    have hpw := abs_pow_sub_pow_le_unit hy0 hy1 hh0 hh1 (k + 1)
    have hkK : ((k + 1 : ℕ) : ℝ) ≤ K := by
      have : k + 1 ≤ K := by simp at hk; omega
      exact_mod_cast this
    have hpw2 : |y ^ (k + 1) - yh ^ (k + 1)| ≤ (K : ℝ) * η := by
      refine hpw.trans ?_
      have := abs_nonneg (y - yh)
      calc ((k + 1 : ℕ) : ℝ) * |y - yh| ≤ (K : ℝ) * |y - yh| := by gcongr
        _ ≤ _ := by gcongr
    have hc1 : |t (k + 1) - (d' : ℝ) / 2 ^ W| ≤ e + 1 / 2 ^ W := by
      have := abs_sub_le (t (k + 1)) ((d : ℝ) / 2 ^ (W + sh)) ((d' : ℝ) / 2 ^ W)
      linarith
    have h4 : t (k + 1) * y ^ (k + 1) - (d' : ℝ) / 2 ^ W * yh ^ (k + 1) ≤
        (e + 1 / 2 ^ W) + |(d' : ℝ)| / 2 ^ W * ((K : ℝ) * η) := by
      have ex : t (k + 1) * y ^ (k + 1) - (d' : ℝ) / 2 ^ W * yh ^ (k + 1) =
          (t (k + 1) - (d' : ℝ) / 2 ^ W) * y ^ (k + 1) +
            (d' : ℝ) / 2 ^ W * (y ^ (k + 1) - yh ^ (k + 1)) := by ring
      rw [ex]
      have g1 : (t (k + 1) - (d' : ℝ) / 2 ^ W) * y ^ (k + 1) ≤ e + 1 / 2 ^ W := by
        calc _ ≤ |t (k + 1) - (d' : ℝ) / 2 ^ W| * y ^ (k + 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hp0
          _ ≤ |t (k + 1) - (d' : ℝ) / 2 ^ W| * 1 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
          _ ≤ _ := by linarith
      have g2 : (d' : ℝ) / 2 ^ W * (y ^ (k + 1) - yh ^ (k + 1)) ≤
          |(d' : ℝ)| / 2 ^ W * ((K : ℝ) * η) := by
        calc _ ≤ |(d' : ℝ) / 2 ^ W * (y ^ (k + 1) - yh ^ (k + 1))| := le_abs_self _
          _ = |(d' : ℝ)| / 2 ^ W * |y ^ (k + 1) - yh ^ (k + 1)| := by
              rw [abs_mul, abs_div, abs_of_pos hw]
          _ ≤ _ := by gcongr
      linarith
    have e2 : ((d' : ℝ) * yh ^ (k + 1) + polK D (k + 1) yh) / 2 ^ W =
        (d' : ℝ) / 2 ^ W * yh ^ (k + 1) + polK D (k + 1) yh / 2 ^ W := by ring
    rw [e2]
    push_cast
    have e3 : (|(d' : ℝ)| + ((abs1 D : ℤ) : ℝ)) / 2 ^ W * ((K : ℝ) * η) =
        |(d' : ℝ)| / 2 ^ W * ((K : ℝ) * η) + ((abs1 D : ℤ) : ℝ) / 2 ^ W * ((K : ℝ) * η) := by ring
    rw [e3]
    linarith

/-! ### Comparing radii -/

theorem psiR_close {r ρ x : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hx : 0 < x) :
    |psiR r x - psiR ρ x| ≤ (ρ - r) / r := by
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
  have hd : 0 ≤ (ρ - r) / r := div_nonneg (by linarith) hr.le
  unfold psiR
  split_ifs with h1 h2 h2
  · -- r < x, ρ < x
    rw [← sub_div, abs_div, abs_of_pos hx, abs_sub_comm, abs_of_nonneg (by linarith)]
    gcongr
  · -- r < x ≤ ρ : both in [r/ρ, 1]
    have hx2 : x ≤ ρ := not_lt.mp h2
    have a1 : r / x ≤ 1 := by rw [div_le_one hx]; exact h1.le
    have a2 : x / ρ ≤ 1 := by rw [div_le_one hρ]; exact hx2
    have a3 : r / ρ ≤ r / x := by gcongr
    have a4 : r / ρ ≤ x / ρ := by gcongr
    have a5 : 1 - r / ρ ≤ (ρ - r) / r := by
      have : 1 - r / ρ = (ρ - r) / ρ := by field_simp
      rw [this]
      apply div_le_div_of_nonneg_left (by linarith) hr hrρ
    rw [abs_le]
    constructor <;> linarith
  · -- x ≤ r, ρ < x : impossible
    exfalso
    have := not_lt.mp h1
    linarith
  · -- x ≤ r ≤ ρ
    have hx1 : x ≤ r := not_lt.mp h1
    have e : x / r - x / ρ = x / r * ((ρ - r) / ρ) := by field_simp
    have a1 : x / r ≤ 1 := by rw [div_le_one hr]; exact hx1
    have a2 : (ρ - r) / ρ ≤ (ρ - r) / r :=
      div_le_div_of_nonneg_left (by linarith) hr hrρ
    have a3 : 0 ≤ (ρ - r) / ρ := div_nonneg (by linarith) hρ.le
    rw [e, abs_of_nonneg (by positivity)]
    calc x / r * ((ρ - r) / ρ) ≤ 1 * ((ρ - r) / ρ) := by gcongr
      _ ≤ _ := by linarith

theorem psiR_mem {r x : ℝ} (hr : 0 < r) (hx : 0 < x) : 0 ≤ psiR r x ∧ psiR r x ≤ 1 := by
  unfold psiR
  split_ifs with h
  · exact ⟨by positivity, by rw [div_le_one hx]; exact h.le⟩
  · exact ⟨by positivity, by rw [div_le_one hr]; exact not_lt.mp h⟩

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

/-! ### Exponential enclosures -/

def expS (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => expS y n + y ^ n / (n.factorial : ℚ)

def expE (y : ℚ) (n : ℕ) : ℚ := expS y n + y ^ n * ((n : ℚ) + 1) / ((n.factorial : ℚ) * n)

theorem expS_cast (y : ℚ) (n : ℕ) :
    ((expS y n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (y : ℝ) ^ m / (m.factorial : ℝ) := by
  induction n with
  | zero => simp [expS]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; simp [expS]

theorem exp_lo {y : ℚ} (h : 0 ≤ y) (n : ℕ) : ((expS y n : ℚ) : ℝ) ≤ Real.exp y := by
  rw [expS_cast]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast h) n

theorem exp_hi {y : ℚ} (h : 0 ≤ y) (h1 : y ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp y ≤ ((expE y n : ℚ) : ℝ) := by
  have := Real.exp_bound' (x := (y : ℝ)) (by exact_mod_cast h) (by exact_mod_cast h1) hn
  unfold expE
  push_cast
  rw [expS_cast]
  exact this

theorem expNeg_enc {a : ℚ} (h0 : 0 ≤ a) (h4 : a ≤ 4) {n : ℕ} (hn : 0 < n)
    (hp : 0 < expS (a / 4) n) :
    ((1 / expE (a / 4) n ^ 4 : ℚ) : ℝ) ≤ Real.exp (-(a : ℝ)) ∧
      Real.exp (-(a : ℝ)) ≤ ((1 / expS (a / 4) n ^ 4 : ℚ) : ℝ) := by
  have hy0 : 0 ≤ a / 4 := by positivity
  have hy1 : a / 4 ≤ 1 := by linarith
  have l := exp_lo hy0 n
  have u := exp_hi hy0 hy1 hn
  have hp' : (0 : ℝ) < expS (a / 4) n := by exact_mod_cast hp
  have e : Real.exp (-(a : ℝ)) = 1 / Real.exp ((a / 4 : ℚ) : ℝ) ^ 4 := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    push_cast
    ring_nf
  have hE : 0 < Real.exp ((a / 4 : ℚ) : ℝ) := Real.exp_pos _
  rw [e]
  push_cast at l u hp' ⊢
  constructor
  · gcongr
  · gcongr

/-! ### Cosines of multiples of `π/NA` (GD5: the angle denominator `NA` is a parameter; the design has `NA = 93`) -/

def cT (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => cT x n + (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℚ)

theorem cT_cast (x : ℚ) (n : ℕ) : ((cT x n : ℚ) : ℝ) =
    ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  induction n with
  | zero => simp [cT]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; simp [cT]

theorem cos_taylor_re (x : ℝ) : ∀ N : ℕ,
    (∑ m ∈ Finset.range (2 * N), ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re =
      ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Complex.add_re, Complex.add_re, ih, Finset.sum_range_succ]
    have e1 : ((x : ℂ) * Complex.I) ^ (2 * N) / ((2 * N).factorial : ℂ) =
        (((-1 : ℝ) ^ N * x ^ (2 * N) / ((2 * N).factorial : ℝ) : ℝ) : ℂ) := by
      rw [mul_pow, pow_mul Complex.I, Complex.I_sq]
      push_cast
      ring
    have e2 : (((x : ℂ) * Complex.I) ^ (2 * N + 1) / ((2 * N + 1).factorial : ℂ)).re = 0 := by
      have : ((x : ℂ) * Complex.I) ^ (2 * N + 1) / ((2 * N + 1).factorial : ℂ) =
          (((-1 : ℝ) ^ N * x ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) : ℝ) : ℂ) * Complex.I := by
        rw [mul_pow, pow_succ Complex.I, pow_succ (x : ℂ), pow_mul Complex.I, Complex.I_sq]
        push_cast
        ring
      rw [this]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [e2, e1, Complex.ofReal_re]
    ring

theorem cos_taylor (x : ℝ) (hx : |x| ≤ 1) (N : ℕ) (hN : 0 < N) :
    |Real.cos x - ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)| ≤
      |x| ^ (2 * N) * (((2 * N).succ : ℝ) / (((2 * N).factorial : ℝ) * ((2 * N : ℕ) : ℝ))) := by
  have hxc : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by simpa using hx
  have hb := Complex.exp_bound hxc (n := 2 * N) (by omega)
  have hre : (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := Complex.exp_ofReal_mul_I_re x
  have h1 := Complex.abs_re_le_norm (Complex.exp ((x : ℂ) * Complex.I) -
    ∑ m ∈ Finset.range (2 * N), ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))
  rw [Complex.sub_re, hre, cos_taylor_re] at h1
  refine h1.trans ?_
  refine hb.trans (le_of_eq ?_)
  have hn : ‖(x : ℂ) * Complex.I‖ = |x| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  rw [hn]
  push_cast
  ring

/-- `|cos(2x) - (2c²-1)| ≤ 5 e` from `|cos x - c| ≤ e ≤ 1/2`. -/
theorem cos_double {x c e : ℝ} (h : |Real.cos x - c| ≤ e) (he : e ≤ 1 / 2) :
    |Real.cos (2 * x) - (2 * c ^ 2 - 1)| ≤ 5 * e := by
  have e0 : 0 ≤ e := (abs_nonneg _).trans h
  have hc := Real.cos_le_one x
  have hc' := Real.neg_one_le_cos x
  have hb := abs_le.mp h
  have ex : Real.cos (2 * x) - (2 * c ^ 2 - 1) = 2 * (Real.cos x - c) * (Real.cos x + c) := by
    rw [Real.cos_two_mul]; ring
  rw [ex, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h2 : |Real.cos x + c| ≤ 5 / 2 := by
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  calc 2 * |Real.cos x - c| * |Real.cos x + c| ≤ 2 * e * (5 / 2) := by gcongr
    _ = 5 * e := by ring

/-- Rational approximation of `π`, `|π - PIQ| ≤ 10^-20`. -/
def PIQ : ℚ := 314159265358979323846 / 10 ^ 20

theorem pi_close : |Real.pi - (PIQ : ℝ)| ≤ 1 / 10 ^ 20 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  rw [abs_le]
  unfold PIQ
  push_cast
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- `cos(m π/NA)` from Taylor at `m π/(4A)` and two doublings (GD5: the angle denominator `NA` is a
parameter; the design has `NA = 93`, 94 angles `m = 0, ..., 93`). -/
def cosA (NA m : ℕ) : ℚ :=
  let c0 := cT ((m : ℚ) * PIQ / (4 * (NA : ℚ))) 12
  let c1 := 2 * c0 ^ 2 - 1
  2 * c1 ^ 2 - 1

theorem cosA_close {NA m : ℕ} (hA : 0 < NA) (hm : m ≤ NA) :
    |Real.cos ((m : ℝ) * (Real.pi / NA)) - ((cosA NA m : ℚ) : ℝ)| ≤ 1 / 10 ^ 17 := by
  have hAr : (0 : ℝ) < NA := by exact_mod_cast hA
  set xh : ℚ := (m : ℚ) * PIQ / (4 * (NA : ℚ)) with hxh
  set x : ℝ := (m : ℝ) * Real.pi / (4 * (NA : ℝ)) with hx
  have hmr : (m : ℝ) ≤ NA := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hxe : |x - (xh : ℝ)| ≤ 1 / 10 ^ 20 := by
    have e : x - (xh : ℝ) = (m : ℝ) / (4 * (NA : ℝ)) * (Real.pi - PIQ) := by
      rw [hx, hxh]; push_cast; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : (m : ℝ) / (4 * (NA : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc (m : ℝ) / (4 * (NA : ℝ)) * |Real.pi - PIQ| ≤ 1 * (1 / 10 ^ 20) := by
          have := pi_close
          gcongr
      _ = _ := one_mul _
  have hxq : |(xh : ℝ)| ≤ 1 := by
    have h0 : (0 : ℝ) ≤ xh := by
      rw [hxh]; unfold PIQ; push_cast; positivity
    rw [abs_of_nonneg h0, hxh]
    unfold PIQ
    push_cast
    rw [div_le_one (by positivity)]
    nlinarith
  have ht := cos_taylor (xh : ℝ) hxq 12 (by norm_num)
  rw [← cT_cast] at ht
  have hrem : |(xh : ℝ)| ^ (2 * 12) * (((2 * 12).succ : ℝ) / (((2 * 12).factorial : ℝ) * ((2 * 12 : ℕ) : ℝ)))
      ≤ 1 / 10 ^ 23 := by
    have h1 : |(xh : ℝ)| ^ (2 * 12) ≤ 1 := pow_le_one₀ (abs_nonneg _) hxq
    have h2 : (((2 * 12).succ : ℝ) / (((2 * 12).factorial : ℝ) * ((2 * 12 : ℕ) : ℝ))) ≤ 1 / 10 ^ 23 := by
      norm_num [Nat.factorial]
    have h3 : (0 : ℝ) ≤ (((2 * 12).succ : ℝ) / (((2 * 12).factorial : ℝ) * ((2 * 12 : ℕ) : ℝ))) := by
      positivity
    exact (mul_le_mul h1 h2 h3 zero_le_one).trans (le_of_eq (one_mul _))
  have h0 : |Real.cos x - ((cT xh 12 : ℚ) : ℝ)| ≤ 2 / 10 ^ 20 := by
    have a := Real.abs_cos_sub_cos_le x xh
    have b := abs_sub_le (Real.cos x) (Real.cos xh) ((cT xh 12 : ℚ) : ℝ)
    have c := ht.trans hrem
    norm_num at c hxe a ⊢
    linarith
  have h1 := cos_double h0 (by norm_num)
  have h2 := cos_double h1 (by norm_num)
  have e4 : 2 * (2 * x) = (m : ℝ) * (Real.pi / NA) := by rw [hx]; field_simp; ring
  rw [e4] at h2
  unfold cosA
  simp only
  push_cast
  rw [← hxh]
  refine h2.trans ?_
  norm_num

/-- The period-`2A` even fold of an index. -/
def foldA (NA n : ℕ) : ℕ := if n % (2 * NA) ≤ NA then n % (2 * NA) else 2 * NA - n % (2 * NA)

theorem foldA_le {NA : ℕ} (hA : 0 < NA) (n : ℕ) : foldA NA n ≤ NA := by
  unfold foldA
  have : n % (2 * NA) < 2 * NA := Nat.mod_lt _ (by omega)
  split_ifs <;> omega

theorem cos_fold {NA : ℕ} (hA : 0 < NA) (k j : ℕ) :
    Real.cos ((k : ℝ) * (Real.pi * (j : ℝ) / NA)) =
      Real.cos ((foldA NA k : ℝ) * (Real.pi * (j : ℝ) / NA)) := by
  have hAr : (NA : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  have hk : (k : ℝ) = (2 * (NA : ℝ)) * ((k / (2 * NA) : ℕ) : ℝ) + ((k % (2 * NA) : ℕ) : ℝ) := by
    have := Nat.div_add_mod k (2 * NA)
    have h' : (k : ℝ) = ((2 * NA * (k / (2 * NA)) + k % (2 * NA) : ℕ) : ℝ) := by rw [this]
    rw [h']
    push_cast
    ring
  have e1 : Real.cos ((k : ℝ) * (Real.pi * (j : ℝ) / NA)) =
      Real.cos (((k % (2 * NA) : ℕ) : ℝ) * (Real.pi * (j : ℝ) / NA)) := by
    have : (k : ℝ) * (Real.pi * (j : ℝ) / NA) =
        ((k % (2 * NA) : ℕ) : ℝ) * (Real.pi * (j : ℝ) / NA) + (((k / (2 * NA)) * j : ℕ) : ℝ) * (2 * Real.pi) := by
      rw [hk]; push_cast; field_simp; ring
    rw [this, Real.cos_add_nat_mul_two_pi]
  rw [e1]
  unfold foldA
  split_ifs with h
  · rfl
  · have hlt : k % (2 * NA) < 2 * NA := Nat.mod_lt _ (by omega)
    have hc : ((2 * NA - k % (2 * NA) : ℕ) : ℝ) = 2 * (NA : ℝ) - ((k % (2 * NA) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hlt.le]; push_cast; ring
    have : ((2 * NA - k % (2 * NA) : ℕ) : ℝ) * (Real.pi * (j : ℝ) / NA) =
        (j : ℝ) * (2 * Real.pi) - ((k % (2 * NA) : ℕ) : ℝ) * (Real.pi * (j : ℝ) / NA) := by
      rw [hc]; field_simp
    rw [this, Real.cos_nat_mul_two_pi_sub]

/-- Packed cosine table: slot `m` holds `(cos(mπ/NA)+1) 2^80`. -/
def cosI (CT : ℕ) (m : ℕ) : ℤ := (((CT >>> (96 * m)) % 2 ^ 96 : ℕ) : ℤ) - 2 ^ 80

def cosChk (NA CT m : ℕ) : Bool :=
  decide (|cosA NA m - (cosI CT m : ℚ) / 2 ^ 80| ≤ 1 / 10 ^ 17)

/-- The table error. -/
def Ecos : ℚ := 2 / 10 ^ 17

theorem cosI_close {NA : ℕ} (hA : 0 < NA) {CT : ℕ} (h : ∀ m ≤ NA, cosChk NA CT m = true) (k j : ℕ) :
    |Real.cos ((k : ℝ) * (Real.pi * (j : ℝ) / NA)) -
      ((cosI CT (foldA NA (k * j)) : ℤ) : ℝ) / 2 ^ 80| ≤ (Ecos : ℝ) := by
  have e1 : (k : ℝ) * (Real.pi * (j : ℝ) / NA) = ((k * j : ℕ) : ℝ) * (Real.pi * ((1 : ℕ) : ℝ) / NA) := by
    push_cast; ring
  rw [e1, cos_fold hA]
  set m := foldA NA (k * j) with hm
  have hle : m ≤ NA := foldA_le hA _
  have h1 := cosA_close hA hle
  have h2 := h m hle
  simp only [cosChk, decide_eq_true_eq] at h2
  have h3 : |((cosA NA m : ℚ) : ℝ) - ((cosI CT m : ℤ) : ℝ) / 2 ^ 80| ≤ 1 / 10 ^ 17 := by
    have := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at this
    exact this
  have e2 : (m : ℝ) * (Real.pi * ((1 : ℕ) : ℝ) / NA) = (m : ℝ) * (Real.pi / NA) := by
    push_cast; ring
  rw [e2]
  have := abs_sub_le (Real.cos ((m : ℝ) * (Real.pi / NA))) ((cosA NA m : ℚ) : ℝ)
    (((cosI CT m : ℤ) : ℝ) / 2 ^ 80)
  unfold Ecos
  push_cast
  linarith

/-! ### Radius classes of a `Tr` list -/

theorem mkAux_eq {g : ℝ} {M : ℤ} {t : Tr} (hp : 0 ≤ t.2.2) (hM : 0 ≤ M) (hg : 0 ≤ g) :
    (mkAux g M t).rad = t.1.toNat ∧ (mkAux g M t).phase = Real.pi * (t.2.1 : ℝ) / 93 ∧
      (mkAux g M t).w = g * (t.2.2 : ℝ) / (M : ℝ) := by
  have h : 0 ≤ t.2.2 ∧ 0 ≤ M ∧ 0 ≤ g := ⟨hp, hM, hg⟩
  unfold mkAux
  rw [dif_pos h]
  exact ⟨rfl, rfl, rfl⟩

/-- Entries `(j, p)` of radius class `i`. -/
def grp (T : List Tr) (i : ℕ) : List (ℕ × ℕ) :=
  (T.filter fun t => t.1.toNat == i).map fun t => (t.2.1.toNat, t.2.2.toNat)

noncomputable def cS (NA : ℕ) (G : List (ℕ × ℕ)) (m : ℕ) : ℝ :=
  (G.map fun e => (e.2 : ℝ) * Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / NA))).sum

def pS (G : List (ℕ × ℕ)) : ℕ := (G.map fun e => e.2).sum

theorem aC_map {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g) (i m : ℕ) : ∀ T : List Tr,
    (∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2) →
    aC (T.map (mkAux g M)) i m = g / M * cS 93 (grp T i) m
  | [], _ => by simp [aC, cS, grp]
  | t :: T, h => by
    have ih := aC_map hM hg i m T fun t ht => h t (List.mem_cons_of_mem _ ht)
    obtain ⟨h1, h2⟩ := h t (by simp)
    obtain ⟨e1, e2, e3⟩ := mkAux_eq (t := t) h2 hM hg
    have hj : ((t.2.1.toNat : ℕ) : ℝ) = (t.2.1 : ℝ) := by
      have : ((t.2.1.toNat : ℕ) : ℤ) = t.2.1 := Int.toNat_of_nonneg h1
      exact_mod_cast this
    have hp : ((t.2.2.toNat : ℕ) : ℝ) = (t.2.2 : ℝ) := by
      have : ((t.2.2.toNat : ℕ) : ℤ) = t.2.2 := Int.toNat_of_nonneg h2
      exact_mod_cast this
    rw [List.map_cons, aC_cons, ih, e1, e2, e3]
    by_cases hi : t.1.toNat = i
    · have : grp (t :: T) i = (t.2.1.toNat, t.2.2.toNat) :: grp T i := by
        simp [grp, hi]
      rw [this, if_pos hi]
      simp only [cS, List.map_cons, List.sum_cons, Nat.cast_ofNat]
      rw [hj, hp]
      ring
    · have : grp (t :: T) i = grp T i := by
        simp [grp, hi]
      rw [this, if_neg hi, zero_add]

theorem cS_fold {NA : ℕ} (hA : 0 < NA) (G : List (ℕ × ℕ)) (k : ℕ) :
    cS NA G k = cS NA G (foldA NA k) := by
  unfold cS
  congr 1
  refine List.map_congr_left fun e _ => ?_
  rw [cos_fold hA]

theorem abs_cS_le (NA : ℕ) (G : List (ℕ × ℕ)) (m : ℕ) : |cS NA G m| ≤ (pS G : ℝ) := by
  induction G with
  | nil => simp [cS, pS]
  | cons e G ih =>
    simp only [cS, pS, List.map_cons, List.sum_cons] at ih ⊢
    rw [Nat.cast_add]
    refine (abs_add_le _ _).trans ?_
    have : |(e.2 : ℝ) * Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / NA))| ≤ (e.2 : ℝ) := by
      rw [abs_mul, Nat.abs_cast]
      have := Real.abs_cos_le_one ((m : ℝ) * (Real.pi * (e.1 : ℝ) / NA))
      have h0 : (0 : ℝ) ≤ e.2 := by positivity
      nlinarith
    linarith

theorem cS_zero (NA : ℕ) (G : List (ℕ × ℕ)) : cS NA G 0 = (pS G : ℝ) := by
  induction G with
  | nil => simp [cS, pS]
  | cons e G ih =>
    simp only [cS, pS, List.map_cons, List.sum_cons] at ih ⊢
    rw [Nat.cast_add, ← ih]
    simp

/-- Integer cosine sum over a class, scale `2^80`. -/
def rI (NA CT : ℕ) (G : List (ℕ × ℕ)) (m : ℕ) : ℤ :=
  (G.map fun e => (e.2 : ℤ) * cosI CT (foldA NA (m * e.1))).sum

theorem cS_close {NA : ℕ} (hA : 0 < NA) {CT : ℕ} (h : ∀ m ≤ NA, cosChk NA CT m = true) (G : List (ℕ × ℕ)) (m : ℕ) :
    |cS NA G m - ((rI NA CT G m : ℤ) : ℝ) / 2 ^ 80| ≤ (pS G : ℝ) * (Ecos : ℝ) := by
  induction G with
  | nil => simp [cS, pS, rI]
  | cons e G ih =>
    simp only [cS, pS, rI, List.map_cons, List.sum_cons] at ih ⊢
    have h1 := cosI_close hA h m e.1
    set c := Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / NA))
    set ci := cosI CT (foldA NA (m * e.1))
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add]
    have ex : (e.2 : ℝ) * c + (G.map fun e => (e.2 : ℝ) * Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / NA))).sum -
        ((e.2 : ℝ) * (ci : ℝ) + (((G.map fun e => (e.2 : ℤ) * cosI CT (foldA NA (m * e.1))).sum : ℤ) : ℝ)) / 2 ^ 80 =
        (e.2 : ℝ) * (c - (ci : ℝ) / 2 ^ 80) +
        ((G.map fun e => (e.2 : ℝ) * Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / NA))).sum -
          (((G.map fun e => (e.2 : ℤ) * cosI CT (foldA NA (m * e.1))).sum : ℤ) : ℝ) / 2 ^ 80) := by
      ring
    rw [ex]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, Nat.abs_cast, add_mul]
    have : (e.2 : ℝ) * |c - (ci : ℝ) / 2 ^ 80| ≤ (e.2 : ℝ) * (Ecos : ℝ) := by gcongr
    linarith

/-- The table of a class: `A_m ≈ h · Σ p cos`, scale `2^80`. -/
def rowA (NA CT : ℕ) (hq : ℚ) (G : List (ℕ × ℕ)) : List ℤ :=
  (List.range (NA + 1)).map fun m => fl (hq * (rI NA CT G m : ℚ))

theorem rowA_close {NA : ℕ} (hA : 0 < NA) {CT : ℕ} (h : ∀ m ≤ NA, cosChk NA CT m = true) {hq : ℚ} (hq0 : 0 ≤ hq)
    (G : List (ℕ × ℕ)) (k : ℕ) :
    |(hq : ℝ) * cS NA G k - (((rowA NA CT hq G).getD (foldA NA k) 0 : ℤ) : ℝ) / 2 ^ 80| ≤
      (hq : ℝ) * ((pS G : ℝ) * (Ecos : ℝ)) + 1 / 2 ^ 80 := by
  rw [cS_fold hA]
  set m := foldA NA k with hm
  have hle : m < NA + 1 := Nat.lt_succ_of_le (foldA_le hA k)
  have hg : (rowA NA CT hq G).getD m 0 = fl (hq * (rI NA CT G m : ℚ)) := by
    unfold rowA
    simp [List.getD, hle]
  rw [hg]
  have h1 := cS_close hA h G m
  have hq0' : (0 : ℝ) ≤ hq := by exact_mod_cast hq0
  have hf1 := fl_le (hq * (rI NA CT G m : ℚ))
  have hf2 := lt_fl (hq * (rI NA CT G m : ℚ))
  set v := fl (hq * (rI NA CT G m : ℚ))
  have g1 : (v : ℝ) ≤ (hq : ℝ) * ((rI NA CT G m : ℤ) : ℝ) := by exact_mod_cast hf1
  have g2 : (hq : ℝ) * ((rI NA CT G m : ℤ) : ℝ) < (v : ℝ) + 1 := by exact_mod_cast hf2
  have ex : (hq : ℝ) * cS NA G m - (v : ℝ) / 2 ^ 80 = (hq : ℝ) * (cS NA G m - ((rI NA CT G m : ℤ) : ℝ) / 2 ^ 80) +
      ((hq : ℝ) * ((rI NA CT G m : ℤ) : ℝ) - (v : ℝ)) / 2 ^ 80 := by ring
  rw [ex]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hq0', abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 80)]
  have h2 : |(hq : ℝ) * ((rI NA CT G m : ℤ) : ℝ) - (v : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have h3 : (hq : ℝ) * |cS NA G m - ((rI NA CT G m : ℤ) : ℝ) / 2 ^ 80| ≤ (hq : ℝ) * ((pS G : ℝ) * (Ecos : ℝ)) := by
    gcongr
  have h4 : |(hq : ℝ) * ((rI NA CT G m : ℤ) : ℝ) - (v : ℝ)| / 2 ^ 80 ≤ 1 / 2 ^ 80 := by gcongr
  linarith

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

/-! ### Kernel coefficients -/

/-- Closed forms of strength and curvature in `r = q²`. -/
def Afun (r : ℚ) : ℚ := 3 * (1 - r ^ 2) / (2 * (1 + 4 * r + r ^ 2))
def Bfun (r : ℚ) : ℚ := (1 - r) ^ 2 / (2 * (1 + 4 * r + r ^ 2))

structure CoefEnc where
  ql : ℚ
  qh : ℚ
  Al : ℚ
  Ah : ℚ
  Bl : ℚ
  Bh : ℚ

def CoefEnc.cLo (E : CoefEnc) (k : ℕ) : ℚ := -(E.qh ^ k * (1 + E.Ah * k + E.Bh * (k : ℚ) ^ 2) / k)
def CoefEnc.cHi (E : CoefEnc) (k : ℕ) : ℚ := -(E.ql ^ k * (1 + E.Al * k + E.Bl * (k : ℚ) ^ 2) / k)

/-- `E` encloses the three constants of `S`. -/
structure CoefEnc.Valid (E : CoefEnc) (S : CapSource) : Prop where
  ql0 : 0 ≤ E.ql
  Al0 : 0 ≤ E.Al
  Bl0 : 0 ≤ E.Bl
  ql : (E.ql : ℝ) ≤ S.q
  qh : S.q ≤ E.qh
  Al : (E.Al : ℝ) ≤ S.strength
  Ah : S.strength ≤ E.Ah
  Bl : (E.Bl : ℝ) ≤ S.curvature
  Bh : S.curvature ≤ E.Bh

theorem CoefEnc.coef_mem {E : CoefEnc} {S : CapSource} (h : E.Valid S) {k : ℕ} (hk : 0 < k) :
    ((E.cLo k : ℚ) : ℝ) ≤ S.coef k ∧ S.coef k ≤ ((E.cHi k : ℚ) : ℝ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have q0 : (0 : ℝ) ≤ E.ql := by exact_mod_cast h.ql0
  have A0 : (0 : ℝ) ≤ E.Al := by exact_mod_cast h.Al0
  have B0 : (0 : ℝ) ≤ E.Bl := by exact_mod_cast h.Bl0
  have s0 : 0 ≤ S.q := q0.trans h.ql
  have a1 : (0 : ℝ) ≤ S.strength := A0.trans h.Al
  have b1 : (0 : ℝ) ≤ S.curvature := B0.trans h.Bl
  have h1 : (E.ql : ℝ) ^ k ≤ S.q ^ k := pow_le_pow_left₀ q0 h.ql k
  have h2 : S.q ^ k ≤ (E.qh : ℝ) ^ k := pow_le_pow_left₀ s0 h.qh k
  have p1 : 1 + (E.Al : ℝ) * k + E.Bl * (k : ℝ) ^ 2 ≤ 1 + S.strength * k + S.curvature * (k : ℝ) ^ 2 := by
    have := h.Al; have := h.Bl; gcongr
  have p2 : 1 + S.strength * k + S.curvature * (k : ℝ) ^ 2 ≤ 1 + (E.Ah : ℝ) * k + E.Bh * (k : ℝ) ^ 2 := by
    have := h.Ah; have := h.Bh; gcongr
  have p0 : 0 ≤ 1 + (E.Al : ℝ) * k + E.Bl * (k : ℝ) ^ 2 := by positivity
  unfold CapSource.coef CoefEnc.cLo CoefEnc.cHi
  push_cast
  constructor
  · apply neg_le_neg
    apply div_le_div_of_nonneg_right _ hkr.le
    exact mul_le_mul h2 p2 (p0.trans p1) (pow_nonneg (s0.trans h.qh) k)
  · apply neg_le_neg
    apply div_le_div_of_nonneg_right _ hkr.le
    exact mul_le_mul h1 p1 p0 (pow_nonneg s0 k)

def coefChk (E : CoefEnc) (δ : ℚ) : List ℤ → ℕ → Bool
  | [], _ => true
  | d :: t, k => decide (|E.cLo (k + 1) - (d : ℚ) / 2 ^ 80| ≤ δ) &&
      decide (|E.cHi (k + 1) - (d : ℚ) / 2 ^ 80| ≤ δ) && coefChk E δ t (k + 1)

theorem coef_close {E : CoefEnc} {S : CapSource} (h : E.Valid S) {δ : ℚ} :
    ∀ (Cq : List ℤ) (k : ℕ), coefChk E δ Cq k = true →
    CLz S.coef (2 ^ 80) (δ : ℝ) k Cq
  | [], _, _ => trivial
  | d :: t, k, hc => by
    simp only [coefChk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    refine ⟨?_, coef_close h t (k + 1) h3⟩
    obtain ⟨m1, m2⟩ := CoefEnc.coef_mem h (Nat.succ_pos k)
    have g1 : |((E.cLo (k + 1) : ℚ) : ℝ) - (d : ℝ) / 2 ^ 80| ≤ (δ : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this
      exact this
    have g2 : |((E.cHi (k + 1) : ℚ) : ℝ) - (d : ℝ) / 2 ^ 80| ≤ (δ : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h2
      push_cast at this
      exact this
    have g1' := abs_le.mp g1
    have g2' := abs_le.mp g2
    rw [abs_le]
    constructor <;> linarith [g1'.1, g2'.2]

/-! ### A full coefficient row -/

/-- `s^k c_k A[fold k]`, scale `2^160`. -/
def tRow (NA : ℕ) (s : ℤ) (A : List ℤ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, c :: cs => (s ^ (k + 1) * c * A.getD (foldA NA (k + 1)) 0) :: tRow NA s A (k + 1) cs

theorem tRow_len (NA : ℕ) (s : ℤ) (A : List ℤ) : ∀ (Cq : List ℤ) (k : ℕ), (tRow NA s A k Cq).length = Cq.length
  | [], _ => rfl
  | _ :: t, k => by simp [tRow, tRow_len NA s A t (k + 1)]

theorem tRow_close {NA : ℕ} {c a : ℕ → ℝ} {s : ℤ} (hs : |(s : ℝ)| = 1) {A : List ℤ} {δc δa Ab : ℝ}
    (hA : ∀ k, |a k - ((A.getD (foldA NA k) 0 : ℤ) : ℝ) / 2 ^ 80| ≤ δa)
    (hAb : ∀ k, |a k| ≤ Ab) :
    ∀ (Cq : List ℤ) (k : ℕ), CLz c (2 ^ 80) δc k Cq → (∀ d ∈ Cq, |(d : ℝ)| ≤ 2 ^ 81) →
    CLz (fun k => (s : ℝ) ^ k * c k * a k) (2 ^ 160) (δc * Ab + 2 * δa) k (tRow NA s A k Cq)
  | [], _, _, _ => trivial
  | d :: t, k, hc, hb => by
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, tRow_close hs hA hAb t (k + 1) h2 fun d hd => hb d (List.mem_cons_of_mem _ hd)⟩
    have hd := hb d (by simp)
    set al := ((A.getD (foldA NA (k + 1)) 0 : ℤ) : ℝ) with hal
    have e1 := hA (k + 1)
    have e2 := hAb (k + 1)
    have ex : (s : ℝ) ^ (k + 1) * c (k + 1) * a (k + 1) -
        (((s ^ (k + 1) * d * A.getD (foldA NA (k + 1)) 0 : ℤ)) : ℝ) / 2 ^ 160 =
        (s : ℝ) ^ (k + 1) * ((c (k + 1) - (d : ℝ) / 2 ^ 80) * a (k + 1) +
          (d : ℝ) / 2 ^ 80 * (a (k + 1) - al / 2 ^ 80)) := by
      push_cast
      rw [← hal]
      ring
    rw [ex, abs_mul, abs_pow, hs, one_pow, one_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have g1 : |(d : ℝ) / 2 ^ 80| ≤ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 80), div_le_iff₀ (by positivity)]
      refine hd.trans (le_of_eq ?_)
      norm_num
    have δ0 : 0 ≤ δa := (abs_nonneg _).trans e1
    have h3 : |c (k + 1) - (d : ℝ) / 2 ^ 80| * |a (k + 1)| ≤ δc * Ab :=
      mul_le_mul h1 e2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    have h4 : |(d : ℝ) / 2 ^ 80| * |a (k + 1) - al / 2 ^ 80| ≤ 2 * δa :=
      mul_le_mul g1 e1 (abs_nonneg _) (by norm_num)
    linarith

/-! ### One radius class against one block -/

noncomputable section

theorem block_le {t : ℕ → ℝ} {r e a0 : ℝ} {B : Blk} (W sh n K : ℕ) {F : List ℤ}
    (hr : 0 < r) (hrρ : r ≤ B.rho) (hM : (B.M : ℝ) = a0) (ha0 : 0 ≤ a0)
    (hD : B.D = truncD sh n F) (hF : CLz t (2 ^ (W + sh)) e 0 F) (hK : F.length = K)
    (he : 0 ≤ e) {x : ℝ} (hx : 0 < x) :
    a0 * Real.log (max x r) + ∑ k ∈ Finset.range K, t (k + 1) * psiR r x ^ (k + 1) ≤
      blkF W B x + (((abs1 (F.drop n) : ℤ) : ℝ) / 2 ^ (W + sh) + (K : ℝ) * (e + 1 / 2 ^ W) +
        ((abs1 B.D : ℤ) : ℝ) / 2 ^ W * ((K : ℝ) * (((B.rho : ℝ) - r) / r))) := by
  have hρ : (0 : ℝ) < B.rho := lt_of_lt_of_le hr hrρ
  obtain ⟨y0, y1⟩ := psiR_mem hr hx
  obtain ⟨z0, z1⟩ := psiR_mem hρ hx
  have hs := ser_le W sh K y0 y1 z0 z1 (psiR_close hr hrρ hx) he F n 0 hF (by omega)
  rw [hK, serR_eq, ← hD] at hs
  have hl : Real.log (max x r) ≤ Real.log (max x (B.rho : ℝ)) :=
    Real.log_le_log (lt_max_of_lt_left hx) (max_le_max le_rfl hrρ)
  have := mul_le_mul_of_nonneg_left hl ha0
  unfold blkF
  rw [hM]
  linarith

theorem sum_getD {α : Type*} (d : α) (f : α → ℝ) : ∀ l : List α,
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum
  | [] => by simp
  | a :: t => by
    have := sum_getD d f t
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← this, add_comm]
    simp

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz xmulZ rawSum_xmulZ)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

/-! ### From the literal moment list to the Chebyshev moments -/

variable {P T Q : ℕ}

/-- Row error, as a rational function of the index. -/
def rowErr (P Ln Sg : ℕ) (j : ℕ) : ℚ :=
  ((Ln : ℚ) + 4 * j * ((Sg : ℚ) / 2 ^ P)) / 2 ^ P

/-- Exact gas mass. -/
def massQ (T : ℕ) (L : List GD) : ℚ := ((L.map GD.p).sum : ℚ) / T

theorem massL_rel {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) :
    massL l = ((massQ T L : ℚ) : ℝ) := by
  induction h with
  | nil => simp [massL, massQ]
  | @cons c d l L hr _ ih =>
    have e : massL (c :: l) = c.w + massL l := by simp [massL]
    rw [e, ih, hr.w]
    simp only [massQ, List.map_cons, List.sum_cons]
    push_cast
    ring

theorem physL_one (l : List YCell) : physL l (fun s => s ^ 0) = massL l := by
  induction l with
  | nil => simp [physL, massL]
  | cons c l ih =>
    have e1 : physL (c :: l) (fun s => s ^ 0) = c.phys (fun _ => 1) + physL l (fun s => s ^ 0) := by
      simp [physL]
    have e2 : massL (c :: l) = c.w + massL l := by simp [massL]
    rw [e1, e2, ih, MomentSource.phys_one]

theorem moments_close {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T)
    (h2 : ∀ c ∈ l, 2 ≤ c.lo) {R r : List ℤ} {n : ℕ} {e1 e2 : ℤ}
    (hR : rows P n (L.map (stAt P T 1)) = R) (hR' : R = e1 :: e2 :: r) {Ln Sg : ℕ} {LIv LEIv : ℤ}
    (hLn : L.length = Ln) (hSg : SG P T L = Sg) (hLI : LI P T Q L = LIv)
    (hLEI : LEI P T Q L = LEIv) :
    CloseL (fun i => physL l (fun s => s ^ i)) 0
      (massQ T L :: ((LIv : ℚ) / 2 ^ Q - (e2 : ℚ) / 4 ^ P / 2) ::
        mB (4 ^ P) 0 R)
      (0 :: (((LEIv : ℚ) + Ln) / 2 ^ Q + rowErr P Ln Sg 2 / 2) ::
        dB (rowErr P Ln Sg) 0 R) := by
  subst hLI hLEI hLn hSg
  have hc := rows_close h hT n 1
  rw [hR] at hc
  have hc' : CloseZ (Er l) (((4 ^ P : ℚ)) : ℝ) (fun j => ((rowErr P L.length (SG P T L) j : ℚ) : ℝ)) (0 + 1) R := by
    have e : (fun j : ℕ => ((rowErr P L.length (SG P T L) j : ℚ) : ℝ)) =
        fun j : ℕ => ((L.length : ℝ) + 4 * j * ((SG P T L : ℝ) / 2 ^ P)) / 2 ^ P := by
      funext j
      unfold rowErr
      push_cast
      rfl
    rw [e]
    push_cast
    exact hc
  have hm := mB_close h2 (S := 4 ^ P) (err := rowErr P L.length (SG P T L)) R 0 hc'
  have hE : |Er l 2 - (e2 : ℝ) / 4 ^ P| ≤ ((rowErr P L.length (SG P T L) 2 : ℚ) : ℝ) := by
    rw [hR'] at hc'
    have := hc'.2.1
    simpa using this
  refine ⟨?_, ?_, hm⟩
  · show |physL l (fun s => s ^ 0) - _| ≤ _
    rw [physL_one, massL_rel h]
    simp
  · show |physL l (fun s => s ^ 1) - _| ≤ _
    rw [mom1 h2]
    have hL := Lr_close (Q := Q) h hT
    have ex : Lr l - Er l 2 / 2 - (((LI P T Q L : ℚ) / 2 ^ Q - (e2 : ℚ) / 4 ^ P / 2 : ℚ) : ℝ) =
        (Lr l - (LI P T Q L : ℝ) / 2 ^ Q) - (Er l 2 - (e2 : ℝ) / 4 ^ P) / 2 := by
      push_cast
      ring
    rw [ex]
    refine (abs_sub _ _).trans ?_
    have g : |(Er l 2 - (e2 : ℝ) / 4 ^ P) / 2| ≤ ((rowErr P L.length (SG P T L) 2 : ℚ) : ℝ) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
    push_cast at g ⊢
    linarith

/-! ### Gas bound -/

/-- Scale `-2/n · μ_n` and shorten. -/
def chkC (W : ℕ) : ℕ → List ℚ → List ℚ → List ℤ → List ℚ → Bool
  | _, [], _, _, _ => true
  | _, _ :: _, [], _, _ => false
  | _, _ :: _, _ :: _, [], _ => false
  | _, _ :: _, _ :: _, _ :: _, [] => false
  | k, v :: vs, e :: es, c :: cs, f :: fs =>
    decide (|(-2 / (k : ℚ)) * v - (c : ℚ) / 2 ^ W| + 2 / (k : ℚ) * e ≤ f) && chkC W (k + 1) vs es cs fs

noncomputable section

theorem chkC_spec {μ : ℕ → ℝ} (W : ℕ) : ∀ (k : ℕ) (v e : List ℚ) (c : List ℤ) (f : List ℚ), 0 < k →
    CloseL μ k v e → chkC W k v e c f = true → v.length = c.length →
    CloseL (fun n => -2 / (n : ℝ) * μ n) k (c.map fun d : ℤ => (d : ℚ) / 2 ^ W) f
  | _, [], _, [], _, _, _, _, _ => trivial
  | _, [], _, _ :: _, _, _, _, _, h => by simp at h
  | _, _ :: _, [], _, _, _, hc, _, _ => by simp [CloseL] at hc
  | _, _ :: _, _ :: _, [], _, _, _, h, _ => by simp [chkC] at h
  | _, _ :: _, _ :: _, _ :: _, [], _, _, h, _ => by simp [chkC] at h
  | k, v :: vs, e :: es, c :: cs, f :: fs, hk, hc, h, hl => by
    simp only [chkC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨g1, g2⟩ := hc
    refine ⟨?_, chkC_spec W (k + 1) vs es cs fs (Nat.succ_pos k) g2 h2 (by simpa using hl)⟩
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have h1' : |(-2 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W| + 2 / (k : ℝ) * (e : ℝ) ≤ (f : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this
      exact this
    have ex : -2 / (k : ℝ) * μ k - (((c : ℚ) / 2 ^ W : ℚ) : ℝ) =
        (-2 / (k : ℝ)) * (μ k - v) + ((-2 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W) := by
      push_cast
      ring
    rw [ex]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_div, abs_of_pos hkr]
    have g : (|(-2 : ℝ)| / (k : ℝ)) * |μ k - (v : ℝ)| ≤ 2 / (k : ℝ) * (e : ℝ) := by
      have : |(-2 : ℝ)| = 2 := by norm_num
      rw [this]
      gcongr
    linarith

theorem rawQ_map (W : ℕ) (z : ℝ) : ∀ (c : List ℤ) (k : ℕ),
    rawQ (c.map fun d : ℤ => (d : ℚ) / 2 ^ W) k z = rawSum c k z / 2 ^ W
  | [], _ => by simp [rawQ]
  | d :: t, k => by
    simp only [List.map_cons, rawQ, rawSum_cons, rawQ_map W z t (k + 1)]
    push_cast
    ring

/-- Chebyshev rows folded into a monomial list. -/
def comb : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ
  | [], _, _, acc => acc
  | c :: cs, a, b, acc => comb cs b (tNext a b) (addZ acc (smulZ c a))

theorem comb_spec (x : ℝ) : ∀ (cs a b acc : List ℤ) (k : ℕ),
    (∀ s, Pz a s = basis k (2 * s - 1)) → (∀ s, Pz b s = basis (k + 1) (2 * s - 1)) →
    Pz (comb cs a b acc) x = Pz acc x + rawSum cs k (2 * x - 1)
  | [], _, _, acc, _, _, _ => by simp [comb]
  | c :: cs, a, b, acc, k, ha, hb => by
    have := comb_spec x cs b (tNext a b) (addZ acc (smulZ c a)) (k + 1) hb (fun s => Pz_tNext ha hb s)
    simp only [comb, this, Pz_addZ, Pz_smulZ, ha, rawSum_cons]
    ring

/-- The whole gas bound: Poisson, Bessel and the moment list. -/
theorem gas_main {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) (hS : Sep 2 l) {W N : ℕ} (hN : 1 ≤ N)
    {v0 e0 : ℚ} {vs es : List ℚ} (hμ : CloseL (fun n => physL l (TF n)) 0 (v0 :: vs) (e0 :: es))
    (hlen : vs.length = N) {Gb Bq Tb : ℚ} (hG : G2 l ≤ Gb)
    (hBq : 31415926536 / 10 ^ 10 / 2 * Gb - ((v0 ^ 2 - 2 * |v0| * e0) / 2 + sqLow vs es) ≤ Bq)
    (hGb : 0 ≤ Gb) (hT0 : 0 ≤ Tb) (hBT : 4 * Bq ≤ (N : ℚ) * Tb ^ 2)
    {cN : List ℤ} {f : List ℚ} (hc : chkC W 1 vs es cN f = true) (hcl : cN.length = N)
    (hfl : f.length = N) (acc : List ℤ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    physL l (fun s => Real.log |x - s|) + massL l * Real.log 4 + Pz acc x / 2 ^ W ≤
      (Tb : ℝ) + Pz (comb cN [-1, 2] (tNext [1] [-1, 2]) acc) x / 2 ^ W + (sumQ f : ℝ) := by
  obtain ⟨c0, c1⟩ := hμ
  have hB : ∀ M, ∑ n ∈ Finset.Ico N M, (physL l (TF (n + 1))) ^ 2 ≤ (Bq : ℝ) := by
    refine tail_of_bessel (le_refl 2) hS ?_
    have hs := sqLow_le 1 vs es c1
    rw [hlen] at hs
    have e : ∑ i ∈ Finset.range N, (physL l (TF (1 + i))) ^ 2 =
        ∑ n ∈ Finset.range N, (physL l (TF (n + 1))) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    rw [e] at hs
    have h0 := sq_ge c0
    have hpi : Real.pi ≤ 31415926536 / 10 ^ 10 := by
      have := Real.pi_lt_d20
      norm_num at this ⊢
      linarith
    have hBq' : (31415926536 / 10 ^ 10 / 2 : ℝ) * (Gb : ℝ) -
        (((v0 : ℝ) ^ 2 - 2 * |(v0 : ℝ)| * e0) / 2 + (sqLow vs es : ℝ)) ≤ Bq := by
      have := (Rat.cast_le (K := ℝ)).mpr hBq
      push_cast at this
      exact this
    have hGb' : (0 : ℝ) ≤ Gb := by exact_mod_cast hGb
    have g1 : Real.pi / 2 * G2 l ≤ (31415926536 / 10 ^ 10 / 2 : ℝ) * (Gb : ℝ) := by
      have h3 : Real.pi / 2 ≤ (31415926536 / 10 ^ 10 / 2 : ℝ) := by linarith
      have h4 : 0 ≤ Real.pi / 2 := by positivity
      calc Real.pi / 2 * G2 l ≤ Real.pi / 2 * (Gb : ℝ) := mul_le_mul_of_nonneg_left hG h4
        _ ≤ _ := mul_le_mul_of_nonneg_right h3 hGb'
    linarith
  have hT0' : (0 : ℝ) ≤ Tb := by exact_mod_cast hT0
  have hBT' : 4 * (Bq : ℝ) ≤ (N : ℝ) * (Tb : ℝ) ^ 2 := by exact_mod_cast hBT
  have hg := gas_upper h2 hx0 hx1 hN hB hT0' hBT'
  have hz : 2 * x - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcl' := chkC_spec (μ := fun n => physL l (TF n)) W 1 vs es cN f one_pos c1 hc (by omega)
  have hcc := close_cheb hz 1 _ f hcl' (by simp [hcl, hfl])
  rw [rawQ_map, List.length_map, hcl] at hcc
  have hs : ∑ i ∈ Finset.range N, -2 / ((1 + i : ℕ) : ℝ) * physL l (TF (1 + i)) * basis (1 + i) (2 * x - 1) =
      -∑ n ∈ Finset.range N, 2 / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) * physL l (TF (n + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm 1 i]
    push_cast
    ring
  rw [hs] at hcc
  have hb := (abs_le.mp hcc).2
  have hcomb := comb_spec x cN [-1, 2] (tNext [1] [-1, 2]) acc 1 Pz_t1
    (fun s => Pz_tNext (k := 0) Pz_t0 Pz_t1 s)
  rw [hcomb, add_div]
  linarith [(abs_le.mp hcc).1]

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

/-- Integer list as dyadic rationals. -/
def dyL (W : ℕ) (c : List ℤ) : List ℚ := c.map fun d : ℤ => (d : ℚ) / 2 ^ W

/-- The literal gas record: every stage of the gas computation, stored once. -/
structure GasLit where
  P : ℕ
  T : ℕ
  Q : ℕ
  Qm : ℕ
  Qv : ℕ
  W : ℕ
  N : ℕ
  Ln : ℕ
  Sg : ℕ
  LIv : ℤ
  LEIv : ℤ
  L : List GD
  R : List ℤ
  Mi : List ℤ
  Me : List ℤ
  v0 : ℤ
  e0 : ℤ
  Vi : List ℤ
  Ve : List ℤ
  G2v : ℤ
  Bq : ℚ
  Tb : ℚ
  cN : List ℤ
  f : List ℤ

/-- Moments from the rows. -/
def GasLit.mL (g : GasLit) : List ℚ :=
  massQ g.T g.L :: ((g.LIv : ℚ) / 2 ^ g.Q - (g.R.getD 1 0 : ℚ) / 4 ^ g.P / 2) :: mB (4 ^ g.P) 0 g.R

def GasLit.dL (g : GasLit) : List ℚ :=
  0 :: (((g.LEIv : ℚ) + g.Ln) / 2 ^ g.Q + rowErr g.P g.Ln g.Sg 2 / 2) ::
    dB (rowErr g.P g.Ln g.Sg) 0 g.R

def GasLit.chkM (g : GasLit) : Bool :=
  relax g.mL g.dL (dyL g.Qm g.Mi) (dyL g.Qm g.Me) && (g.mL.length == g.Mi.length)

/-- Chebyshev moments from the shortened moments. -/
def GasLit.chkV (g : GasLit) : Bool :=
  relax (muV (dyL g.Qm g.Mi) (g.N + 1) [1] [-1, 2]) (muE (dyL g.Qm g.Me) (g.N + 1) [1] [-1, 2])
    (dyL g.Qv (g.v0 :: g.Vi)) (dyL g.Qv (g.e0 :: g.Ve)) && decide (g.N + 1 ≤ g.Mi.length)

/-- Scalar checks. -/
def GasLit.chkS (g : GasLit) : Bool :=
  decide (31415926536 / 10 ^ 10 / 2 * ((g.G2v : ℚ) / 2 ^ g.Q) -
      (((((g.v0 : ℚ) / 2 ^ g.Qv)) ^ 2 - 2 * |(g.v0 : ℚ) / 2 ^ g.Qv| * ((g.e0 : ℚ) / 2 ^ g.Qv)) / 2 +
        sqLow (dyL g.Qv g.Vi) (dyL g.Qv g.Ve)) ≤ g.Bq) &&
  decide (0 ≤ g.G2v) && decide (0 ≤ g.Tb) && decide (4 * g.Bq ≤ (g.N : ℚ) * g.Tb ^ 2) &&
  decide (1 ≤ g.N) && decide (g.Vi.length = g.N) && decide (g.cN.length = g.N) &&
  decide (g.f.length = g.N)

def GasLit.chkC (g : GasLit) : Bool :=
  OrdHf.chkC g.W 1 (dyL g.Qv g.Vi) (dyL g.Qv g.Ve) g.cN (dyL 40 g.f)

/-- The monomial list of a gas record with an extra list `acc`. -/
def GasLit.G (g : GasLit) (acc : List ℤ) : List ℤ := comb g.cN [-1, 2] (tNext [1] [-1, 2]) acc

/-- Separation check on the record. -/
def sepL : ℕ → List GD → Bool
  | _, [] => true
  | a, d :: t => decide (a ≤ d.a) && sepL d.b t

noncomputable section

theorem sep_of {P T : ℕ} : ∀ {l : List YCell} {L : List GD} (a : ℕ), List.Forall₂ (Rel P T) l L →
    sepL a L = true → Sep ((a : ℝ) / 10 ^ 12) l
  | _, _, _, .nil, _ => trivial
  | c :: l, d :: L, a, .cons hr hl, h => by
    simp only [sepL, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨?_, ?_⟩
    · rw [hr.lo]
      have : (a : ℝ) ≤ d.a := by exact_mod_cast h.1
      gcongr
    · rw [hr.hi]
      exact sep_of d.b hl h.2

theorem len_dyL (W : ℕ) (c : List ℤ) : (dyL W c).length = c.length := by simp [dyL]

/-- All gas checks together give the gas bound. -/
theorem gas_of_lit (g : GasLit) {l : List YCell} (h : List.Forall₂ (Rel g.P g.T) l g.L)
    (hT : 0 < g.T) (h2 : ∀ c ∈ l, 2 ≤ c.lo) (hS : sepL (2 * 10 ^ 12) g.L = true)
    {nR : ℕ} (c1 : rows g.P nR (g.L.map (stAt g.P g.T 1)) = g.R) {e1 e2 : ℤ} {r : List ℤ}
    (c1' : g.R = e1 :: e2 :: r) (cLn : g.L.length = g.Ln) (cSg : SG g.P g.T g.L = g.Sg)
    (cLI : LI g.P g.T g.Q g.L = g.LIv) (cLEI : LEI g.P g.T g.Q g.L = g.LEIv)
    (cM : g.chkM = true) (cV : g.chkV = true) (cG : G2I g.P g.T g.Q g.L = g.G2v)
    (cS : g.chkS = true) (cC : g.chkC = true) (acc : List ℤ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    physL l (fun s => Real.log |x - s|) + massL l * Real.log 4 + Pz acc x / 2 ^ g.W ≤
      (g.Tb : ℝ) + Pz (g.G acc) x / 2 ^ g.W + (sumQ (dyL 40 g.f) : ℝ) := by
  simp only [GasLit.chkS, Bool.and_eq_true, decide_eq_true_eq] at cS
  obtain ⟨⟨⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩ := cS
  simp only [GasLit.chkM, Bool.and_eq_true, beq_iff_eq] at cM
  simp only [GasLit.chkV, Bool.and_eq_true, decide_eq_true_eq] at cV
  have hm0 := moments_close (Q := g.Q) h hT h2 c1 c1' cLn cSg cLI cLEI
  have hR1 : g.R.getD 1 0 = e2 := by rw [c1']; rfl
  have hm1 : CloseL (fun i => physL l (fun s => s ^ i)) 0 g.mL g.dL := by
    unfold GasLit.mL GasLit.dL
    rw [hR1]
    exact hm0
  have hm2 := relax_close 0 _ _ _ _ hm1 cM.1 (by rw [len_dyL]; exact cM.2)
  have hmu := mu_close h2 hm2 (g.N + 1) 0 [1] [-1, 2] Pz_t0 Pz_t1 (by simp) (by simp)
    (by rw [len_dyL]; omega)
  have hmu2 := relax_close 0 _ _ _ _ hmu cV.1 (by
    have : ∀ (n : ℕ) (a b : List ℤ) (mL : List ℚ), (muV mL n a b).length = n := by
      intro n
      induction n with
      | zero => intro a b mL; rfl
      | succ n ih => intro a b mL; simp [muV, ih]
    rw [this, len_dyL]
    simp [s6])
  simp only [dyL, List.map_cons] at hmu2
  have hG : G2 l ≤ (((g.G2v : ℚ) / 2 ^ g.Q : ℚ) : ℝ) := by
    have := G2_le (Q := g.Q) h hT
    rw [cG] at this
    push_cast
    exact this
  have hS' : Sep 2 l := by
    have := sep_of (2 * 10 ^ 12) h hS
    have e : (((2 * 10 ^ 12 : ℕ) : ℝ) / 10 ^ 12) = 2 := by norm_num
    rw [e] at this
    exact this
  have hGb : (0 : ℚ) ≤ (g.G2v : ℚ) / 2 ^ g.Q := by
    have : (0 : ℚ) ≤ g.G2v := by exact_mod_cast s2
    positivity
  exact gas_main h2 hS' s5 hmu2 (by simp [s6]) hG s1 hGb s3 s4 cC s7 (by simp [dyL, s8]) acc hx0 hx1

/-- Mirror moments for the negative species. -/
def chkMir (W : ℕ) : ℕ → List ℚ → List ℚ → List ℤ → List ℚ → Bool
  | _, [], _, _, _ => true
  | _, _ :: _, [], _, _ => false
  | _, _ :: _, _ :: _, [], _ => false
  | _, _ :: _, _ :: _, _ :: _, [] => false
  | k, v :: vs, e :: es, c :: cs, f :: fs =>
    decide (|(-1 / (k : ℚ)) * v - (c : ℚ) / 2 ^ W| + 1 / (k : ℚ) * e ≤ f) && chkMir W (k + 1) vs es cs fs

/-- `Σ_{i<len} B(k+i) u^(k+i)` against `u^k Pz c u`. -/
theorem mir_close {μ : ℕ → ℝ} {u : ℝ} (W : ℕ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∀ (k : ℕ) (v e : List ℚ) (c : List ℤ) (f : List ℚ), 0 < k → CloseL μ k v e →
    chkMir W k v e c f = true → v.length = c.length → v.length = f.length →
    ∑ i ∈ Finset.range v.length, (-1 / ((k + i : ℕ) : ℝ)) * μ (k + i) * u ^ (k + i) ≤
      u ^ k * Pz c u / 2 ^ W + (sumQ f : ℝ)
  | _, [], _, [], [], _, _, _, _, _ => by simp [Pz, sumQ]
  | _, [], _, [], _ :: _, _, _, _, _, h => by simp at h
  | _, [], _, _ :: _, _, _, _, _, h, _ => by simp at h
  | _, _ :: _, [], _, _, _, hc, _, _, _ => by simp [CloseL] at hc
  | _, _ :: _, _ :: _, [], _, _, _, h, _, _ => by simp [chkMir] at h
  | _, _ :: _, _ :: _, _ :: _, [], _, _, h, _, _ => by simp [chkMir] at h
  | k, v :: vs, e :: es, c :: cs, f :: fs, hk, hc, h, hl, hf => by
    simp only [chkMir, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨g1, g2⟩ := hc
    have ih := mir_close W hu0 hu1 (k + 1) vs es cs fs (Nat.succ_pos k) g2 h2 (by simpa using hl)
      (by simpa using hf)
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have h1' : |(-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W| + 1 / (k : ℝ) * (e : ℝ) ≤ (f : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this
      exact this
    rw [List.length_cons, Finset.sum_range_succ']
    have e1 : ∑ i ∈ Finset.range vs.length, (-1 / ((k + (i + 1) : ℕ) : ℝ)) * μ (k + (i + 1)) * u ^ (k + (i + 1)) =
        ∑ i ∈ Finset.range vs.length, (-1 / ((k + 1 + i : ℕ) : ℝ)) * μ (k + 1 + i) * u ^ (k + 1 + i) :=
      Finset.sum_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by ring]
    rw [e1]
    simp only [add_zero]
    have hp0 : 0 ≤ u ^ k := by positivity
    have hp1 : u ^ k ≤ 1 := pow_le_one₀ hu0 hu1
    have ex : (-1 / (k : ℝ)) * μ k * u ^ k - (c : ℝ) / 2 ^ W * u ^ k =
        ((-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)) * u ^ k := by ring
    have hb : (-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W) ≤ (f : ℝ) := by
      have a1 : (-1 / (k : ℝ)) * (μ k - v) ≤ 1 / (k : ℝ) * e := by
        have q := (abs_le.mp g1).1
        have : (-1 / (k : ℝ)) * (μ k - v) = 1 / (k : ℝ) * (-(μ k - v)) := by ring
        rw [this]
        have hk1 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) hk1
      have a2 := le_abs_self ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)
      linarith
    have hf0 : (0 : ℝ) ≤ f := by
      have h3 := abs_nonneg ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)
      have h4 : (0 : ℝ) ≤ e := (abs_nonneg _).trans g1
      have h5 : (0 : ℝ) ≤ 1 / (k : ℝ) * e := by positivity
      linarith
    have hb2 : ((-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)) * u ^ k ≤ (f : ℝ) := by
      rcases le_or_gt 0 ((-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)) with q | q
      · calc _ ≤ ((-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)) * 1 :=
              mul_le_mul_of_nonneg_left hp1 q
          _ ≤ _ := by linarith
      · have := mul_nonpos_of_nonpos_of_nonneg q.le hp0
        linarith
    have eP : u ^ k * Pz (c :: cs) u / 2 ^ W = (c : ℝ) / 2 ^ W * u ^ k + u ^ (k + 1) * Pz cs u / 2 ^ W := by
      simp only [Pz]
      ring
    rw [eP]
    simp only [sumQ, Rat.cast_add]
    rw [← ex] at hb2
    linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

/-- The literal radial record of one species. -/
structure RadLit where
  NA : ℕ
  CT : ℕ
  hq : ℚ
  Cq : List ℤ
  δc : ℚ
  s : ℤ
  W : ℕ
  sh : ℕ
  Gs : List (List (ℕ × ℕ))
  As : List (List ℤ)
  Bs : List Blk
  ns : List ℕ
  Tls : List ℤ
  etas : List ℚ

def dBlk : Blk := ⟨1, 0, 0, []⟩

def RadLit.G (R : RadLit) (i : ℕ) : List (ℕ × ℕ) := R.Gs.getD i []
def RadLit.A (R : RadLit) (i : ℕ) : List ℤ := R.As.getD i []
def RadLit.B (R : RadLit) (i : ℕ) : Blk := R.Bs.getD i dBlk
def RadLit.n (R : RadLit) (i : ℕ) : ℕ := R.ns.getD i 0
def RadLit.Tl (R : RadLit) (i : ℕ) : ℤ := R.Tls.getD i 0
def RadLit.eta (R : RadLit) (i : ℕ) : ℚ := R.etas.getD i 0

/-- The full coefficient row of class `i`, scale `2^160`. -/
def RadLit.F (R : RadLit) (i : ℕ) : List ℤ := tRow R.NA R.s (R.A i) 0 R.Cq

/-- The tolerance on `a_i(k)`, its bound, and the row tolerance. -/
def RadLit.Ab (R : RadLit) (i : ℕ) : ℚ := R.hq * (pS (R.G i) : ℚ)
def RadLit.da (R : RadLit) (i : ℕ) : ℚ := R.hq * ((pS (R.G i) : ℚ) * Ecos) + 1 / 2 ^ 80
def RadLit.e (R : RadLit) (i : ℕ) : ℚ := R.δc * R.Ab i + 2 * R.da i

/-- The error of class `i`. -/
def RadLit.err (R : RadLit) (i : ℕ) : ℚ :=
  (R.Tl i : ℚ) / 2 ^ (R.W + R.sh) + 384 * (R.e i + 1 / 2 ^ R.W) +
    ((abs1 (R.B i).D : ℤ) : ℚ) / 2 ^ R.W * (384 * R.eta i)

/-- The angle table of a record: denominator `NA` (93 for `mkAux`) and the checked cosines. -/
def RadLit.AngOK (R : RadLit) : Prop := R.NA = 93 ∧ ∀ m ≤ R.NA, cosChk R.NA R.CT m = true

/-- Checks of class `i` against the `Tr` list. -/
def RadLit.chk (R : RadLit) (T : List Tr) (i : ℕ) : Bool :=
  decide (grp T i = R.G i) && decide (rowA R.NA R.CT R.hq (R.G i) = R.A i) &&
  decide ((R.B i).D = truncD R.sh (R.n i) (R.F i)) &&
  decide (abs1 ((R.F i).drop (R.n i)) ≤ R.Tl i) && decide ((R.B i).M = R.hq * (pS (R.G i) : ℚ))

/-- Radius enclosure. -/
def radA (i : ℕ) : ℚ := (sigN.getD (min i 15) 0 : ℚ) / 10 ^ 17
def radLo (i : ℕ) : ℚ := 1 / expE (radA i / 4) 24 ^ 4
def radHi (i : ℕ) : ℚ := 1 / expS (radA i / 4) 24 ^ 4

def radChk (rho sg eta : ℚ) (i : ℕ) : Bool :=
  decide (0 ≤ radA i) && decide (radA i ≤ 4) && decide (0 < expS (radA i / 4) 24) &&
  decide (0 < radLo i) && decide (radHi i ≤ rho) && decide ((rho - radLo i) / radLo i ≤ eta) &&
  decide (-radA i + eta ≤ sg)

noncomputable section

theorem rad_cap (i : ℕ) : capSource.rad i = Real.exp (-((radA i : ℚ) : ℝ)) := by
  show Real.exp (-sigmaF i) = _
  unfold sigmaF radA
  push_cast
  rfl

theorem rad_facts {rho sg eta : ℚ} {i : ℕ} (h : radChk rho sg eta i = true) :
    0 < capSource.rad i ∧ capSource.rad i ≤ rho ∧ ((rho : ℝ) - capSource.rad i) / capSource.rad i ≤ eta ∧
      Real.log rho ≤ sg ∧ 0 < rho := by
  simp only [radChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  obtain ⟨l, u⟩ := expNeg_enc h1 h2 (n := 24) (by norm_num) h3
  rw [← rad_cap] at l u
  have hr := Real.exp_pos (-((radA i : ℚ) : ℝ))
  rw [← rad_cap] at hr
  set r := capSource.rad i with hrdef
  have lo' : ((radLo i : ℚ) : ℝ) ≤ r := l
  have hi' : r ≤ ((radHi i : ℚ) : ℝ) := u
  have h5' : ((radHi i : ℚ) : ℝ) ≤ rho := by exact_mod_cast h5
  have h4' : (0 : ℝ) < radLo i := by exact_mod_cast h4
  have h6' : ((rho : ℝ) - radLo i) / radLo i ≤ eta := by exact_mod_cast h6
  have hrr : r ≤ rho := hi'.trans h5'
  have hρ : 0 < (rho : ℝ) := lt_of_lt_of_le hr hrr
  have he : ((rho : ℝ) - r) / r ≤ eta := by
    refine le_trans ?_ h6'
    rw [div_le_div_iff₀ hr h4']
    nlinarith
  refine ⟨hr, hrr, he, ?_, by exact_mod_cast hρ⟩
  have h7' : -((radA i : ℚ) : ℝ) + eta ≤ sg := by exact_mod_cast h7
  have hl : Real.log r = -((radA i : ℚ) : ℝ) := by rw [hrdef, rad_cap, Real.log_exp]
  have : Real.log ((rho : ℝ) / r) ≤ (rho : ℝ) / r - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hρ.ne' hr.ne', hl] at this
  have e : (rho : ℝ) / r - 1 = ((rho : ℝ) - r) / r := by field_simp
  rw [e] at this
  linarith

/-- The cosine moments of a class, through the literal row. -/
theorem class_facts (R : RadLit) {T : List Tr} {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hgq : (R.hq : ℝ) = g / M) (hq0 : 0 ≤ R.hq) (hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2)
    (hcos : R.AngOK) {i : ℕ} (hc : R.chk T i = true) :
    (∀ k, |aC (T.map (mkAux g M)) i k - (((R.A i).getD (foldA R.NA k) 0 : ℤ) : ℝ) / 2 ^ 80| ≤ (R.da i : ℝ)) ∧
      (∀ k, |aC (T.map (mkAux g M)) i k| ≤ (R.Ab i : ℝ)) ∧
      aC (T.map (mkAux g M)) i 0 = ((R.B i).M : ℝ) := by
  simp only [RadLit.chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, _⟩, _⟩, c5⟩ := hc
  have hq0' : (0 : ℝ) ≤ R.hq := by exact_mod_cast hq0
  have hA0 : 0 < R.NA := by rw [hcos.1]; norm_num
  have ha : ∀ k, aC (T.map (mkAux g M)) i k = (R.hq : ℝ) * cS R.NA (R.G i) k := by
    intro k
    rw [aC_map hM hg i k T hT, c1, hgq, hcos.1]
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · rw [ha, ← c2]
    have := rowA_close hA0 hcos.2 hq0 (R.G i) k
    unfold RadLit.da
    push_cast
    exact this
  · rw [ha, abs_mul, abs_of_nonneg hq0']
    unfold RadLit.Ab
    push_cast
    exact mul_le_mul_of_nonneg_left (abs_cS_le _ _ _) hq0'
  · rw [ha, cS_zero, c5]
    push_cast
    rfl

/-- One class, in the shape of the radial sums. -/
theorem class_le (R : RadLit) {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hgq : (R.hq : ℝ) = g / M) (hq0 : 0 ≤ R.hq) (hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2)
    (hcos : R.AngOK) (hs : |(R.s : ℝ)| = 1)
    (hδ : CLz S.coef (2 ^ 80) (R.δc : ℝ) 0 R.Cq) (hCb : ∀ d ∈ R.Cq, |(d : ℝ)| ≤ 2 ^ 81)
    (hlen : R.Cq.length = 384) (hW : R.W + R.sh = 160) (hδ0 : 0 ≤ R.δc)
    {i : ℕ} (hc : R.chk T i = true) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ (R.B i).rho)
    (hη : ((((R.B i).rho : ℚ) : ℝ) - r) / r ≤ (R.eta i : ℝ)) {x : ℝ} (hx : 0 < x) :
    aC (T.map (mkAux g M)) i 0 * Real.log (max x r) +
      ∑ k ∈ Finset.range 384, ((R.s : ℝ) ^ (k + 1) * S.coef (k + 1) *
        aC (T.map (mkAux g M)) i (k + 1)) * psiR r x ^ (k + 1) ≤
      blkF R.W (R.B i) x + (R.err i : ℝ) := by
  obtain ⟨f1, f2, f3⟩ := class_facts R hM hg hgq hq0 hT hcos hc
  have hclz := tRow_close (a := aC (T.map (mkAux g M)) i) hs f1 f2 R.Cq 0 hδ hCb
  have hc' := hc
  simp only [RadLit.chk, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, _⟩ := hc'
  have hsc : (2 : ℝ) ^ 160 = 2 ^ (R.W + R.sh) := by rw [hW]
  rw [hsc] at hclz
  have hFl : (R.F i).length = 384 := by
    unfold RadLit.F
    rw [tRow_len, hlen]
  have hAb0 : (0 : ℝ) ≤ R.Ab i := (abs_nonneg _).trans (f2 0)
  have hda0 : (0 : ℝ) ≤ R.da i := (abs_nonneg _).trans (f1 0)
  have hδ0' : (0 : ℝ) ≤ R.δc := by exact_mod_cast hδ0
  have he0 : 0 ≤ (R.δc : ℝ) * R.Ab i + 2 * R.da i := by positivity
  have ha0 : 0 ≤ aC (T.map (mkAux g M)) i 0 := by
    rw [f3]
    have : ((R.B i).M : ℝ) = (R.hq : ℝ) * ((pS (R.G i) : ℕ) : ℝ) := by
      have h5 := hc
      simp only [RadLit.chk, Bool.and_eq_true, decide_eq_true_eq] at h5
      rw [h5.2]
      push_cast
      rfl
    rw [this]
    have : (0 : ℝ) ≤ R.hq := by exact_mod_cast hq0
    positivity
  have hb := block_le (B := R.B i) (t := fun k => (R.s : ℝ) ^ k * S.coef k * aC (T.map (mkAux g M)) i k)
    R.W R.sh (R.n i) 384 hr hrρ f3.symm ha0 c3 hclz hFl he0 hx
  refine hb.trans ?_
  have hTl : ((abs1 ((R.F i).drop (R.n i)) : ℤ) : ℝ) ≤ (R.Tl i : ℝ) := by exact_mod_cast c4
  have hL0 : (0 : ℝ) ≤ ((abs1 (R.B i).D : ℤ) : ℝ) / 2 ^ R.W := by
    have : (0 : ℝ) ≤ ((abs1 (R.B i).D : ℤ) : ℝ) := by exact_mod_cast abs1_nonneg _
    positivity
  have h1 : ((abs1 (R.B i).D : ℤ) : ℝ) / 2 ^ R.W * (((384 : ℕ) : ℝ) * ((((R.B i).rho : ℝ) - r) / r)) ≤
      ((abs1 (R.B i).D : ℤ) : ℝ) / 2 ^ R.W * (384 * (R.eta i : ℝ)) := by
    push_cast
    gcongr
  have h2 : ((abs1 ((R.F i).drop (R.n i)) : ℤ) : ℝ) / 2 ^ (R.W + R.sh) ≤
      (R.Tl i : ℝ) / 2 ^ (R.W + R.sh) := by gcongr
  unfold RadLit.err RadLit.e
  push_cast
  push_cast at h1
  linarith

/-- All classes together, for a positive `x`, with species sign `s`. -/
theorem classes_le (R : RadLit) {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hgq : (R.hq : ℝ) = g / M) (hq0 : 0 ≤ R.hq) (hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2)
    (hcos : R.AngOK) (hs : |(R.s : ℝ)| = 1)
    (hδ : CLz S.coef (2 ^ 80) (R.δc : ℝ) 0 R.Cq) (hCb : ∀ d ∈ R.Cq, |(d : ℝ)| ≤ 2 ^ 81)
    (hlen : R.Cq.length = 384) (hW : R.W + R.sh = 160) (hδ0 : 0 ≤ R.δc)
    (n : ℕ) (hB : R.Bs.length = n) (hc : ∀ i < n, R.chk T i = true)
    (hrad : ∀ i < n, 0 < S.rad i ∧ S.rad i ≤ (R.B i).rho ∧
      ((((R.B i).rho : ℚ) : ℝ) - S.rad i) / S.rad i ≤ (R.eta i : ℝ)) {x : ℝ} (hx : 0 < x) :
    ∑ i ∈ Finset.range n, (aC (T.map (mkAux g M)) i 0 * Real.log (max x (S.rad i)) +
      ∑ k ∈ Finset.range 384, ((R.s : ℝ) ^ (k + 1) * S.coef (k + 1) *
        aC (T.map (mkAux g M)) i (k + 1)) * psiR (S.rad i) x ^ (k + 1)) ≤
      sumF R.W R.Bs x + ∑ i ∈ Finset.range n, (R.err i : ℝ) := by
  have e : sumF R.W R.Bs x = ∑ i ∈ Finset.range n, blkF R.W (R.B i) x := by
    subst hB
    unfold sumF
    rw [← sum_getD dBlk (fun B => blkF R.W B x)]
    rfl
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  obtain ⟨r1, r2, r3⟩ := hrad i hi'
  exact class_le R hM hg hgq hq0 hT hcos hs hδ hCb hlen hW hδ0 (hc i hi') r1 r2 r3 hx

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz xmulZ rawSum_xmulZ)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)
open CatalanMeasure.GenD.Signed.RouteI.MomentInputs (abs_pow_sub_pow_le_unit)

/-! ### Cell lists -/

def relP (P : ℕ) : List Tr → List GD → Bool
  | [], [] => true
  | t :: ts, d :: ds => decide ((d.a : ℤ) = t.1 ∧ (d.b : ℤ) = t.2.1 ∧ (d.p : ℤ) = t.2.2) && d.ok P &&
      relP P ts ds
  | _, _ => false

def relN (P : ℕ) : List Tr → List GD → Bool
  | [], [] => true
  | t :: ts, d :: ds => decide ((d.a : ℤ) = -t.2.1 ∧ (d.b : ℤ) = -t.1 ∧ (d.p : ℤ) = t.2.2) && d.ok P &&
      relN P ts ds
  | _, _ => false

noncomputable section

theorem ok_lt {P : ℕ} {d : GD} (h : d.ok P = true) : d.a < d.b := by
  simp only [GD.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem relP_spec {P T : ℕ} {Tz : ℤ} (hT : (T : ℤ) = Tz) : ∀ (ts : List Tr) (L : List GD),
    relP P ts L = true → List.Forall₂ (Rel P T) (ts.map (mkCell 1 Tz)) L
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [relP] at h
  | _ :: _, [], h => by simp [relP] at h
  | t :: ts, d :: ds, h => by
    simp only [relP, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2, h3⟩, hok⟩, hr⟩ := h
    have hlt := ok_lt hok
    have hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2 := by omega
    obtain ⟨e1, e2, e3⟩ := mkCell_eq (m := 1) (T := Tz) hv (by omega) zero_le_one
    refine .cons ⟨?_, ?_, ?_, hok⟩ (relP_spec hT ts ds hr)
    · rw [e1, ← h1]; simp
    · rw [e2, ← h2]; simp
    · rw [e3, ← h3, ← hT]; simp

theorem relN_spec {P T : ℕ} {Tz : ℤ} (hT : (T : ℤ) = Tz) : ∀ (ts : List Tr) (L : List GD),
    relN P ts L = true →
    List.Forall₂ (Rel P T) (ts.map fun t => (mkCell 1 Tz t).reflect) L
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [relN] at h
  | _ :: _, [], h => by simp [relN] at h
  | t :: ts, d :: ds, h => by
    simp only [relN, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2, h3⟩, hok⟩, hr⟩ := h
    have hlt := ok_lt hok
    have hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2 := by omega
    obtain ⟨e1, e2, e3⟩ := mkCell_eq (m := 1) (T := Tz) hv (by omega) zero_le_one
    have r1 : (mkCell 1 Tz t).reflect.lo = -(mkCell 1 Tz t).hi := rfl
    have r2 : (mkCell 1 Tz t).reflect.hi = -(mkCell 1 Tz t).lo := rfl
    have r3 : (mkCell 1 Tz t).reflect.w = (mkCell 1 Tz t).w := rfl
    have c1 : (d.a : ℝ) = -(t.2.1 : ℝ) := by exact_mod_cast h1
    have c2 : (d.b : ℝ) = -(t.1 : ℝ) := by exact_mod_cast h2
    refine .cons ⟨?_, ?_, ?_, hok⟩ (relN_spec hT ts ds hr)
    · rw [r1, e2, c1]; ring
    · rw [r2, e1, c2]; ring
    · rw [r3, e3, ← h3, ← hT]; simp

/-! ### The coefficient enclosure of `capSource` -/

theorem cap_q : capSource.q = Real.exp (-(((27 / 500 : ℚ)) : ℝ)) := by
  show Real.exp (-(27 / 250 : ℝ) / 2) = _
  congr 1
  push_cast
  ring

theorem q_enc : ((1 / expE (27 / 500 / 4) 24 ^ 4 : ℚ) : ℝ) ≤ capSource.q ∧
    capSource.q ≤ ((1 / expS (27 / 500 / 4) 24 ^ 4 : ℚ) : ℝ) := by
  rw [cap_q]
  exact expNeg_enc (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

theorem strength_eq (S : CapSource) (h1 : S.q ^ 2 < 1) (h0 : 0 ≤ S.q ^ 2) :
    S.strength = 3 * (1 - (S.q ^ 2) ^ 2) / (2 * (1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2)) := by
  unfold CapSource.strength CapSource.normalizer
  set r := S.q ^ 2
  have a : 1 - r ≠ 0 := by linarith
  have b : 1 + 4 * r + r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem curvature_eq (S : CapSource) (h1 : S.q ^ 2 < 1) (h0 : 0 ≤ S.q ^ 2) :
    S.curvature = (1 - S.q ^ 2) ^ 2 / (2 * (1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2)) := by
  unfold CapSource.curvature CapSource.normalizer
  set r := S.q ^ 2
  have a : 1 - r ≠ 0 := by linarith
  have b : 1 + 4 * r + r ^ 2 ≠ 0 := by positivity
  field_simp

/-- The enclosure check of a literal `CoefEnc`. -/
def CoefEnc.chk (E : CoefEnc) : Bool :=
  decide (0 ≤ E.ql) && decide (E.ql ≤ 1 / expE (27 / 500 / 4) 24 ^ 4) &&
  decide (1 / expS (27 / 500 / 4) 24 ^ 4 ≤ E.qh) && decide (E.qh < 1) &&
  decide (0 ≤ E.Al) && decide (0 ≤ E.Bl) &&
  decide (E.Al ≤ Afun (E.qh ^ 2)) && decide (Afun (E.ql ^ 2) ≤ E.Ah) &&
  decide (E.Bl ≤ Bfun (E.qh ^ 2)) && decide (Bfun (E.ql ^ 2) ≤ E.Bh)

theorem CoefEnc.valid {E : CoefEnc} (h : E.chk = true) : E.Valid capSource := by
  simp only [CoefEnc.chk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  obtain ⟨q1, q2⟩ := q_enc
  have l : (E.ql : ℝ) ≤ capSource.q := by
    refine le_trans ?_ q1
    exact_mod_cast h2
  have u : capSource.q ≤ E.qh := by
    refine q2.trans ?_
    exact_mod_cast h3
  have ql0 : (0 : ℝ) ≤ E.ql := by exact_mod_cast h1
  have qh1 : (E.qh : ℝ) < 1 := by exact_mod_cast h4
  set q := capSource.q with hq
  have q0 : 0 ≤ q := ql0.trans l
  have rl : (E.ql : ℝ) ^ 2 ≤ q ^ 2 := by gcongr
  have ru : q ^ 2 ≤ (E.qh : ℝ) ^ 2 := by gcongr
  have rl0 : (0 : ℝ) ≤ (E.ql : ℝ) ^ 2 := by positivity
  have r1 : q ^ 2 < 1 := by nlinarith
  have rh1 : (E.qh : ℝ) ^ 2 < 1 := by nlinarith [q0.trans u]
  have r0 : 0 ≤ q ^ 2 := by positivity
  have se := strength_eq capSource r1 r0
  have ce := curvature_eq capSource r1 r0
  rw [← hq] at se ce
  have A1 : ((Afun (E.qh ^ 2) : ℚ) : ℝ) ≤ capSource.strength := by
    rw [se]
    unfold Afun
    push_cast
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  have A2 : capSource.strength ≤ ((Afun (E.ql ^ 2) : ℚ) : ℝ) := by
    rw [se]
    unfold Afun
    push_cast
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  have B1 : ((Bfun (E.qh ^ 2) : ℚ) : ℝ) ≤ capSource.curvature := by
    rw [ce]
    unfold Bfun
    push_cast
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  have B2 : capSource.curvature ≤ ((Bfun (E.ql ^ 2) : ℚ) : ℝ) := by
    rw [ce]
    unfold Bfun
    push_cast
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  exact ⟨h1, h5, h6, l, u, le_trans (by exact_mod_cast h7) A1, A2.trans (by exact_mod_cast h8),
    le_trans (by exact_mod_cast h9) B1, B2.trans (by exact_mod_cast h10)⟩

/-- Rational upper bound of `auxTail` at degree 384. -/
def CoefEnc.tail (E : CoefEnc) (m : ℚ) (c : ℚ) : ℚ :=
  E.qh ^ 385 * ((1 / 385 + E.Ah) * (1 / (1 - E.qh)) +
    E.Bh * (385 * (1 / (1 - E.qh)) + E.qh * (1 / (1 - E.qh)) ^ 2)) * m * c

theorem auxTail_le {E : CoefEnc} {S : CapSource} (h : E.Valid S) (hq1 : E.qh < 1) (σ : Sign) {m : ℚ}
    (hm : S.auxMass σ ≤ m) (hm0 : 0 ≤ S.auxMass σ) {c : ℚ} (hc : (if σ = Sign.neg then (2 : ℝ) else 1) ≤ c) :
    S.auxTail (Trunc.finite 384) σ ≤ ((E.tail m c : ℚ) : ℝ) := by
  have q0 : 0 ≤ S.q := (by exact_mod_cast h.ql0 : (0 : ℝ) ≤ E.ql).trans h.ql
  have hq1' : (E.qh : ℝ) < 1 := by exact_mod_cast hq1
  have qh0 : (0 : ℝ) ≤ E.qh := q0.trans h.qh
  have a0 : 0 ≤ S.strength := (by exact_mod_cast h.Al0 : (0 : ℝ) ≤ E.Al).trans h.Al
  have b0 : 0 ≤ S.curvature := (by exact_mod_cast h.Bl0 : (0 : ℝ) ≤ E.Bl).trans h.Bl
  have g1 : 0 < 1 - (E.qh : ℝ) := by linarith
  have g2 : 0 < 1 - S.q := by linarith [h.qh]
  have g3 : 1 / (1 - S.q) ≤ 1 / (1 - (E.qh : ℝ)) := by
    apply one_div_le_one_div_of_le g1
    linarith [h.qh]
  have g0 : 0 ≤ 1 / (1 - S.q) := by positivity
  have hAh := h.Ah
  have hBh := h.Bh
  have hqh := h.qh
  have s0 : (0 : ℝ) ≤ (if σ = Sign.neg then (2 : ℝ) else 1) := by split_ifs <;> norm_num
  unfold CapSource.auxTail CoefEnc.tail
  push_cast
  have B0 : (0 : ℝ) ≤ E.Bh := b0.trans hBh
  have A0 : (0 : ℝ) ≤ E.Ah := a0.trans hAh
  have m0 : (0 : ℝ) ≤ m := hm0.trans hm
  have e1 : ((384 : ℝ) + 1) = 385 := by norm_num
  rw [e1]
  gcongr

/-! ### Mirror block of the negative species -/

/-- `d ρ^k`, rounded down, with `ρ = rn/2^rb`. -/
def wt (rn rb : ℕ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, d :: t => (d * (rn : ℤ) ^ (k + 1) / 2 ^ (rb * (k + 1))) :: wt rn rb (k + 1) t

theorem wt_len (rn rb : ℕ) : ∀ (F : List ℤ) (k : ℕ), (wt rn rb k F).length = F.length
  | [], _ => rfl
  | _ :: t, k => by simp [wt, wt_len rn rb t (k + 1)]

theorem wt_close {t : ℕ → ℝ} {sc e Fb η r : ℝ} {rn rb K : ℕ} (hsc : 0 < sc) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hρ1 : (rn : ℝ) / 2 ^ rb ≤ 1) (hη : |r - (rn : ℝ) / 2 ^ rb| ≤ η) (he : 0 ≤ e) (hFb : 0 ≤ Fb) :
    ∀ (F : List ℤ) (k : ℕ), CLz t sc e k F → (∀ d ∈ F, |(d : ℝ)| / sc ≤ Fb) → k + F.length ≤ K →
    CLz (fun k => t k * r ^ k) sc (e + Fb * ((K : ℝ) * η) + 1 / sc) k (wt rn rb k F)
  | [], _, _, _, _ => trivial
  | d :: F, k, hc, hb, hk => by
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, wt_close hsc hr0 hr1 hρ1 hη he hFb F (k + 1) h2
      (fun d hd => hb d (List.mem_cons_of_mem _ hd)) (by simp at hk; omega)⟩
    set ρ : ℝ := (rn : ℝ) / 2 ^ rb with hρd
    have hρ0 : 0 ≤ ρ := by positivity
    have hd := hb d (by simp)
    have hrp0 : 0 ≤ r ^ (k + 1) := by positivity
    have hrp1 : r ^ (k + 1) ≤ 1 := pow_le_one₀ hr0 hr1
    have hη0 : 0 ≤ η := (abs_nonneg _).trans hη
    have hpw := abs_pow_sub_pow_le_unit hr0 hr1 hρ0 hρ1 (k + 1)
    have hkK : ((k + 1 : ℕ) : ℝ) ≤ K := by
      have : k + 1 ≤ K := by simp at hk; omega
      exact_mod_cast this
    have hpw2 : |r ^ (k + 1) - ρ ^ (k + 1)| ≤ (K : ℝ) * η := by
      refine hpw.trans ?_
      have := abs_nonneg (r - ρ)
      calc ((k + 1 : ℕ) : ℝ) * |r - ρ| ≤ (K : ℝ) * |r - ρ| := by gcongr
        _ ≤ _ := by gcongr
    -- floor
    set N : ℤ := d * (rn : ℤ) ^ (k + 1) with hN
    set Dn : ℤ := 2 ^ (rb * (k + 1)) with hDn
    have hD0 : 0 < Dn := by positivity
    have f1 : N / Dn * Dn ≤ N := Int.ediv_mul_le N hD0.ne'
    have f2 : N < (N / Dn + 1) * Dn := Int.lt_ediv_add_one_mul_self N hD0
    have hD0' : (0 : ℝ) < (Dn : ℝ) := by exact_mod_cast hD0
    have f1' : ((N / Dn : ℤ) : ℝ) * Dn ≤ N := by exact_mod_cast f1
    have f2' : (N : ℝ) < (((N / Dn : ℤ) : ℝ) + 1) * Dn := by exact_mod_cast f2
    have eN : (N : ℝ) / Dn = (d : ℝ) * ρ ^ (k + 1) := by
      rw [hN, hDn, hρd]
      push_cast
      rw [div_pow, pow_mul, ← pow_mul (2 : ℝ)]
      ring_nf
    have g1 : ((N / Dn : ℤ) : ℝ) ≤ (d : ℝ) * ρ ^ (k + 1) := by
      rw [← eN, le_div_iff₀ hD0']; exact f1'
    have g2 : (d : ℝ) * ρ ^ (k + 1) < ((N / Dn : ℤ) : ℝ) + 1 := by
      rw [← eN, div_lt_iff₀ hD0']; exact f2'
    have ex : t (k + 1) * r ^ (k + 1) - ((N / Dn : ℤ) : ℝ) / sc =
        (t (k + 1) - (d : ℝ) / sc) * r ^ (k + 1) + (d : ℝ) / sc * (r ^ (k + 1) - ρ ^ (k + 1)) +
          ((d : ℝ) * ρ ^ (k + 1) - ((N / Dn : ℤ) : ℝ)) / sc := by ring
    show |t (k + 1) * r ^ (k + 1) - ((N / Dn : ℤ) : ℝ) / sc| ≤ _
    rw [ex]
    refine (abs_add_le _ _).trans ?_
    have t1 := abs_add_le ((t (k + 1) - (d : ℝ) / sc) * r ^ (k + 1))
      ((d : ℝ) / sc * (r ^ (k + 1) - ρ ^ (k + 1)))
    have t2 : |(t (k + 1) - (d : ℝ) / sc) * r ^ (k + 1)| ≤ e := by
      rw [abs_mul, abs_of_nonneg hrp0]
      calc _ ≤ |t (k + 1) - (d : ℝ) / sc| * 1 := by gcongr
        _ ≤ e := by linarith
    have t3 : |(d : ℝ) / sc * (r ^ (k + 1) - ρ ^ (k + 1))| ≤ Fb * ((K : ℝ) * η) := by
      rw [abs_mul, abs_div, abs_of_pos hsc]
      exact mul_le_mul hd hpw2 (abs_nonneg _) hFb
    have t4 : |((d : ℝ) * ρ ^ (k + 1) - ((N / Dn : ℤ) : ℝ)) / sc| ≤ 1 / sc := by
      rw [abs_div, abs_of_pos hsc]
      have : |(d : ℝ) * ρ ^ (k + 1) - ((N / Dn : ℤ) : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      gcongr
    linarith

theorem CLz_add {t1 t2 : ℕ → ℝ} {sc e1 e2 : ℝ} : ∀ (F1 F2 : List ℤ) (k : ℕ),
    CLz t1 sc e1 k F1 → CLz t2 sc e2 k F2 → F1.length = F2.length →
    CLz (fun k => t1 k + t2 k) sc (e1 + e2) k (addZ F1 F2)
  | [], [], _, _, _, _ => by simp [addZ, CLz]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | a :: F1, b :: F2, k, h1, h2, h => by
    refine ⟨?_, CLz_add F1 F2 (k + 1) h1.2 h2.2 (by simpa using h)⟩
    have ex : t1 (k + 1) + t2 (k + 1) - (((a + b : ℤ)) : ℝ) / sc =
        (t1 (k + 1) - (a : ℝ) / sc) + (t2 (k + 1) - (b : ℝ) / sc) := by
      push_cast
      ring
    rw [ex]
    exact (abs_add_le _ _).trans (add_le_add h1.1 h2.1)

/-! ### Change of variable to the Chebyshev list in `w` -/

/-- With `x = (A + B w)/D'` and `E = 2 D'`: `E rawSum (Rc l) 0 w = E^len Pz l x`. -/
def RcS (A B E a : ℤ) (n : ℕ) (r : List ℤ) : List ℤ :=
  addZ [a * E ^ n] (addZ (smulZ (2 * A) r) (smulZ B (xmulZ r)))

def Rc (A B E : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: t => RcS A B E a t.length (Rc A B E t)

theorem Rc_eval (A B E : ℤ) {w x : ℝ} (hx : (E : ℝ) * x = 2 * ((A : ℝ) + B * w)) : ∀ l : List ℤ,
    (E : ℝ) * rawSum (Rc A B E l) 0 w = (E : ℝ) ^ l.length * Pz l x
  | [] => by simp [Rc, Pz]
  | a :: t => by
    have ih := Rc_eval A B E hx t
    simp only [Rc, RcS, rawSum_addZ, rawSum_smulZ, rawSum_xmulZ, List.length_cons, Pz, rawSum_cons,
      rawSum_nil, basis_zero, mul_one, add_zero]
    push_cast
    have e : (E : ℝ) ^ (t.length + 1) * ((a : ℝ) + x * Pz t x) =
        (E : ℝ) * ((a : ℝ) * (E : ℝ) ^ t.length) + ((E : ℝ) * x) * ((E : ℝ) ^ t.length * Pz t x) := by
      ring
    rw [e, ← ih, hx]
    ring

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz xmulZ rawSum_xmulZ)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ addQ rawQ_addQ diffSum abs_rawQ_sub_le)
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_pos vY_le_one physX_pos reflectL)

/-- The fold of the classes of the mirror series. -/
def mirF (R : RadLit) (rns : List ℕ) (rb : ℕ) : ℕ → List ℤ
  | 0 => List.replicate 384 0
  | i + 1 => addZ (mirF R rns rb i) (wt (rns.getD i 0) rb 0 (R.F i))

/-- Its error. -/
def mirE (R : RadLit) (Fb : ℚ) : ℕ → ℚ
  | 0 => 0
  | i + 1 => mirE R Fb i + (R.e i + Fb * (384 * R.eta i) + 1 / 2 ^ 160)

noncomputable section

theorem CLz_zero {sc : ℝ} : ∀ (n k : ℕ), CLz (fun _ => 0) sc 0 k (List.replicate n 0)
  | 0, _ => trivial
  | n + 1, k => ⟨by simp, CLz_zero n (k + 1)⟩

/-- The closeness of one class row. -/
theorem class_close (R : RadLit) {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hgq : (R.hq : ℝ) = g / M) (hq0 : 0 ≤ R.hq) (hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2)
    (hcos : R.AngOK) (hs : |(R.s : ℝ)| = 1)
    (hδ : CLz S.coef (2 ^ 80) (R.δc : ℝ) 0 R.Cq) (hCb : ∀ d ∈ R.Cq, |(d : ℝ)| ≤ 2 ^ 81)
    (hδ0 : 0 ≤ R.δc) {i : ℕ} (hc : R.chk T i = true) :
    CLz (fun k => (R.s : ℝ) ^ k * S.coef k * aC (T.map (mkAux g M)) i k) (2 ^ 160) ((R.e i : ℚ) : ℝ) 0
      (R.F i) ∧ (0 : ℝ) ≤ ((R.e i : ℚ) : ℝ) := by
  obtain ⟨f1, f2, _⟩ := class_facts R hM hg hgq hq0 hT hcos hc
  have hclz := tRow_close (a := aC (T.map (mkAux g M)) i) hs f1 f2 R.Cq 0 hδ hCb
  have hAb0 : (0 : ℝ) ≤ R.Ab i := (abs_nonneg _).trans (f2 0)
  have hda0 : (0 : ℝ) ≤ R.da i := (abs_nonneg _).trans (f1 0)
  have hδ0' : (0 : ℝ) ≤ R.δc := by exact_mod_cast hδ0
  have e : ((R.e i : ℚ) : ℝ) = (R.δc : ℝ) * R.Ab i + 2 * R.da i := by
    unfold RadLit.e
    push_cast
    ring
  rw [e]
  exact ⟨hclz, by positivity⟩

theorem mirF_close (R : RadLit) (rns : List ℕ) (rb : ℕ) {t : ℕ → ℕ → ℝ} {r : ℕ → ℝ} {Fb : ℚ}
    (hFb0 : 0 ≤ Fb) (n : ℕ)
    (hc : ∀ i < n, CLz (t i) (2 ^ 160) ((R.e i : ℚ) : ℝ) 0 (R.F i) ∧ (0 : ℝ) ≤ ((R.e i : ℚ) : ℝ))
    (hr : ∀ i < n, 0 ≤ r i ∧ r i ≤ 1 ∧ ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb ≤ 1 ∧
      |r i - ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb| ≤ (R.eta i : ℝ))
    (hl : ∀ i < n, (R.F i).length = 384)
    (hb : ∀ i < n, ∀ d ∈ R.F i, |(d : ℝ)| / 2 ^ 160 ≤ Fb) :
    CLz (fun k => ∑ i ∈ Finset.range n, t i k * r i ^ k) (2 ^ 160) ((mirE R Fb n : ℚ) : ℝ) 0
      (mirF R rns rb n) ∧ (mirF R rns rb n).length = 384 ∧ (0 : ℝ) ≤ ((mirE R Fb n : ℚ) : ℝ) := by
  induction n with
  | zero =>
    refine ⟨?_, by simp only [mirF, List.length_replicate], by simp [mirE]⟩
    simp only [Finset.range_zero, Finset.sum_empty, mirF, mirE, Rat.cast_zero]
    exact CLz_zero 384 0
  | succ n ih =>
    obtain ⟨a1, a2, a3⟩ := ih (fun i hi => hc i (by omega)) (fun i hi => hr i (by omega))
      (fun i hi => hl i (by omega)) (fun i hi => hb i (by omega))
    obtain ⟨c1, c2⟩ := hc n (by omega)
    obtain ⟨r0, r1, r2, r3⟩ := hr n (by omega)
    have hFb0' : (0 : ℝ) ≤ Fb := by exact_mod_cast hFb0
    have hw := wt_close (t := t n) (sc := 2 ^ 160) (e := ((R.e n : ℚ) : ℝ)) (Fb := (Fb : ℝ))
      (η := (R.eta n : ℝ)) (r := r n) (rn := rns.getD n 0) (rb := rb) (K := 384) (by positivity) r0 r1 r2
      r3 c2 hFb0' (R.F n) 0 c1 (hb n (by omega)) (by rw [hl n (by omega)])
    have hwl : (wt (rns.getD n 0) rb 0 (R.F n)).length = 384 := by
      rw [wt_len, hl n (by omega)]
    have hadd := CLz_add _ _ 0 a1 hw (by rw [a2, hwl])
    have eE : ((mirE R Fb (n + 1) : ℚ) : ℝ) = ((mirE R Fb n : ℚ) : ℝ) +
        (((R.e n : ℚ) : ℝ) + (Fb : ℝ) * (((384 : ℕ) : ℝ) * (R.eta n : ℝ)) + 1 / 2 ^ 160) := by
      simp only [mirE]
      push_cast
      ring
    have eT : (fun k => ∑ i ∈ Finset.range (n + 1), t i k * r i ^ k) =
        fun k => ∑ i ∈ Finset.range n, t i k * r i ^ k + t n k * r n ^ k := by
      funext k
      rw [Finset.sum_range_succ]
    have hη0 : (0 : ℝ) ≤ R.eta n := (abs_nonneg _).trans r3
    refine ⟨?_, ?_, ?_⟩
    · rw [eT, eE]
      exact hadd
    · simp only [mirF]
      rw [len_addZ, a2, hwl]
      rfl
    · rw [eE]
      positivity

theorem CLz_congr {t1 t2 : ℕ → ℝ} {sc e : ℝ} (h : ∀ k, t1 k = t2 k) :
    ∀ (F : List ℤ) (k : ℕ), CLz t1 sc e k F → CLz t2 sc e k F
  | [], _, _ => trivial
  | _ :: F, k, hc => ⟨by rw [← h]; exact hc.1, CLz_congr h F (k + 1) hc.2⟩

/-- The mirror series of all classes. -/
theorem mirror_series (R : RadLit) (rns : List ℕ) (rb nm : ℕ) {t : ℕ → ℕ → ℝ} {r : ℕ → ℝ} {Fb : ℚ}
    (hFb0 : 0 ≤ Fb) (n : ℕ) (hW : R.W + R.sh = 160)
    (hc : ∀ i < n, CLz (t i) (2 ^ 160) ((R.e i : ℚ) : ℝ) 0 (R.F i) ∧ (0 : ℝ) ≤ ((R.e i : ℚ) : ℝ))
    (hr : ∀ i < n, 0 ≤ r i ∧ r i ≤ 1 ∧ ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb ≤ 1 ∧
      |r i - ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb| ≤ (R.eta i : ℝ))
    (hl : ∀ i < n, (R.F i).length = 384)
    (hb : ∀ i < n, ∀ d ∈ R.F i, |(d : ℝ)| / 2 ^ 160 ≤ Fb) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range 384, t i (k + 1) * (r i * u) ^ (k + 1) ≤
      polK (truncD R.sh nm (mirF R rns rb n)) 0 u / 2 ^ R.W +
        (((abs1 ((mirF R rns rb n).drop nm) : ℤ) : ℝ) / 2 ^ 160 +
          384 * (((mirE R Fb n : ℚ) : ℝ) + 1 / 2 ^ R.W)) := by
  obtain ⟨a1, a2, a3⟩ := mirF_close R rns rb hFb0 n hc hr hl hb
  have hsc : (2 : ℝ) ^ 160 = 2 ^ (R.W + R.sh) := by rw [hW]
  rw [hsc] at a1
  have h := ser_le (t := fun k => ∑ i ∈ Finset.range n, t i k * r i ^ k) (y := u) (yh := u) (η := 0)
    R.W R.sh 384 hu0 hu1 hu0 hu1 (by simp) a3 (mirF R rns rb n) nm 0 a1 (by rw [a2])
  rw [a2, serR_eq] at h
  simp only [mul_zero, add_zero] at h
  have e : ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range 384, t i (k + 1) * (r i * u) ^ (k + 1) =
      ∑ k ∈ Finset.range 384, (∑ i ∈ Finset.range n, t i (k + 1) * r i ^ (k + 1)) * u ^ (k + 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]
    ring
  rw [e, hsc]
  push_cast at h
  linarith

/-! ### Reflection and field shape -/

theorem reflTail_eq (S : CapSource) (hr : S.reflDeg = 899) :
    S.reflTail = ((S.gas Sign.pos).map fun c =>
      let prim : ℝ → ℝ := fun x => x ^ 900 / 900 + x ^ 901 / 901
      c.w / (c.hi - c.lo) * (prim (YCell.physX c.lo) - prim (YCell.physX c.hi)) / 901).sum := by
  unfold CapSource.reflTail
  rw [hr]
  norm_num

theorem reflPoly_eq (S : CapSource) (hr : S.reflDeg = 899) (u : ℝ) :
    S.reflPoly u = ∑ k ∈ Finset.range 900, u ^ (k + 1) / ((k : ℝ) + 1) *
      physL (S.gas Sign.pos) (fun s => s ^ (k + 1)) := by
  unfold CapSource.reflPoly CapSource.reflMoment
  rw [hr]
  refine Finset.sum_congr (by norm_num) fun k _ => ?_
  ring

theorem field_eq (S : CapSource) (K : ℕ) (σ : Sign) (x : ℝ) :
    S.ordField (Trunc.finite K) σ x =
      (physL (S.gas σ) (fun u => Real.log |u|) + potL (S.gas σ) (x + 1 / x) +
        massL (S.gas σ) * Real.log |x|) - kappa σ - 53 / 58 * Real.log (1 + x ^ 2) +
      (if σ = Sign.pos then S.reflPoly x + S.reflTail else 0) + S.radialA (Trunc.finite K) σ x +
      S.auxTail (Trunc.finite K) σ := by
  simp only [CapSource.ordField, CapSource.rowField, CapSource.refR, CapSource.refC, Flavor.marked,
    physL, potL, List.map_nil, List.sum_nil]
  ring

theorem field_pos (S : CapSource) (K : ℕ) (h2 : ∀ c ∈ S.gas Sign.pos, 2 ≤ c.lo)
    (hr : S.reflDeg = 899) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ 1) :
    S.ordField (Trunc.finite K) Sign.pos u ≤
      physL (S.gas Sign.pos) (fun s => Real.log |u - s|) - kappa Sign.pos -
        53 / 58 * Real.log (1 + u ^ 2) + S.reflTail + S.radialA (Trunc.finite K) Sign.pos u +
        S.auxTail (Trunc.finite K) Sign.pos := by
  rw [field_eq]
  have a := row_list h2 hu0 hu1
  have b := physL_refl_le h2 hu0 hu1 900
  have c : S.reflPoly u = ∑ k ∈ Finset.range 900, u ^ (k + 1) / ((k : ℝ) + 1) *
      physL (S.gas Sign.pos) (fun s => s ^ (k + 1)) := reflPoly_eq S hr u
  rw [if_pos rfl]
  rw [← c] at b
  linarith

theorem field_neg (S : CapSource) (K : ℕ) (h : ∀ c ∈ S.gas Sign.neg, c.hi ≤ -2) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ 1) :
    S.ordField (Trunc.finite K) Sign.neg (-u) =
      physL (reflectL (S.gas Sign.neg)) (fun s => Real.log |u - s|) +
        physL (reflectL (S.gas Sign.neg)) (fun s => Real.log |1 - s * u|) - kappa Sign.neg -
        53 / 58 * Real.log (1 + u ^ 2) + S.radialA (Trunc.finite K) Sign.neg (-u) +
        S.auxTail (Trunc.finite K) Sign.neg := by
  rw [field_eq]
  have a := row_list_neg h hu0 hu1
  have e : (if Sign.neg = Sign.pos then S.reflPoly (-u) + S.reflTail else 0) = 0 := if_neg (by decide)
  rw [e, neg_sq]
  linarith

/-! ### The tail `Eref900` -/

def eInt (n P Q T : ℕ) (d : GD) : ℕ :=
  d.p * 10 ^ 12 * ((d.al + 1) ^ n / 2 ^ (n * P - Q) + 1) / (T * (d.b - d.a)) + 1

def erefTerm (c : YCell) : ℝ :=
  let prim : ℝ → ℝ := fun x => x ^ 900 / 900 + x ^ 901 / 901
  c.w / (c.hi - c.lo) * (prim (YCell.physX c.lo) - prim (YCell.physX c.hi)) / 901

theorem nat_lt_div (n d : ℕ) (hd : 0 < d) : n < (n / d + 1) * d := by
  rw [mul_comm]
  exact Nat.lt_mul_div_succ n hd

theorem xpow_le {P Q n a : ℕ} (hQ : Q ≤ n * P) {x : ℝ} (x0 : 0 ≤ x)
    (hxa : x ≤ ((a : ℝ) + 1) / 2 ^ P) :
    x ^ n ≤ (((a + 1) ^ n / 2 ^ (n * P - Q) + 1 : ℕ) : ℝ) / 2 ^ Q := by
  set X : ℕ := (a + 1) ^ n / 2 ^ (n * P - Q) + 1 with hX
  have s1 : x ^ n ≤ (((a : ℝ) + 1) / 2 ^ P) ^ n := by gcongr
  refine s1.trans ?_
  have hdv : 0 < 2 ^ (n * P - Q) := by positivity
  have s2 : (a + 1) ^ n < X * 2 ^ (n * P - Q) := nat_lt_div _ _ hdv
  have s3 : (((a : ℝ) + 1)) ^ n ≤ (X : ℝ) * 2 ^ (n * P - Q) := by
    exact_mod_cast s2.le
  have s4 : ((2 : ℝ) ^ P) ^ n = 2 ^ (n * P - Q) * 2 ^ Q := by
    rw [← pow_add, Nat.sub_add_cancel hQ, ← pow_mul, mul_comm]
  rw [div_pow, s4, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (0 : ℝ) < 2 ^ Q := by positivity
  calc ((a : ℝ) + 1) ^ n * 2 ^ Q ≤ ((X : ℝ) * 2 ^ (n * P - Q)) * 2 ^ Q := by gcongr
    _ = _ := by ring

theorem cell_erefG {P Q T n m : ℕ} {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hnm : n ≤ m)
    (hQ : Q ≤ n * P) {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) :
    c.w / (c.hi - c.lo) * ((YCell.physX c.lo ^ n / A + YCell.physX c.lo ^ m / B) -
      (YCell.physX c.hi ^ n / A + YCell.physX c.hi ^ m / B)) / B ≤
      (1 / A + 1 / B) / B * ((eInt n P Q T d : ℝ) / 2 ^ Q) := by
  have f := h.facts
  have hdab : (0 : ℝ) < (d.b : ℝ) - d.a := by
    have : (d.a : ℝ) < d.b := by exact_mod_cast f.dab
    linarith
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h2h : 2 ≤ c.hi := f.two.trans c.lo_lt.le
  have x0 := (vY_pos f.two).le
  have x1 := vY_le_one f.two
  have y0 := (vY_pos h2h).le
  rw [physX_pos f.two, physX_pos h2h]
  set x := vY c.lo with hx
  set y := vY c.hi with hy
  have hgc : c.w / (c.hi - c.lo) = (d.p : ℝ) * 10 ^ 12 / ((T : ℝ) * ((d.b : ℝ) - d.a)) := by
    rw [h.w, h.lo, h.hi]
    field_simp
  have hg0 : 0 ≤ c.w / (c.hi - c.lo) := by rw [hgc]; positivity
  set X : ℕ := (d.al + 1) ^ n / 2 ^ (n * P - Q) + 1 with hX
  have hp1 : x ^ n ≤ (X : ℝ) / 2 ^ Q := xpow_le hQ x0 f.lu
  have hp2 : x ^ m ≤ x ^ n := pow_le_pow_of_le_one x0 x1 hnm
  have hA' : 0 ≤ 1 / A := by positivity
  have hB' : 0 ≤ 1 / B := by positivity
  have hprim : x ^ n / A + x ^ m / B ≤ (1 / A + 1 / B) * ((X : ℝ) / 2 ^ Q) := by
    have a1 : x ^ n / A ≤ 1 / A * ((X : ℝ) / 2 ^ Q) := by
      rw [div_eq_mul_inv, one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hp1 (by positivity)
    have a2 : x ^ m / B ≤ 1 / B * ((X : ℝ) / 2 ^ Q) := by
      rw [div_eq_mul_inv, one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left (hp2.trans hp1) (by positivity)
    linarith
  have hyy : 0 ≤ y ^ n / A + y ^ m / B := by positivity
  have hE : (d.p : ℝ) * 10 ^ 12 * (X : ℝ) / ((T : ℝ) * ((d.b : ℝ) - d.a)) ≤ (eInt n P Q T d : ℝ) := by
    have hM : 0 < T * (d.b - d.a) := Nat.mul_pos hT (by have := f.dab; omega)
    have hcast : ((T * (d.b - d.a) : ℕ) : ℝ) = (T : ℝ) * ((d.b : ℝ) - d.a) := by
      rw [Nat.cast_mul, Nat.cast_sub f.dab.le]
    have n1 : d.p * 10 ^ 12 * X ≤ eInt n P Q T d * (T * (d.b - d.a)) :=
      (nat_lt_div _ _ hM).le
    have n2 : ((d.p * 10 ^ 12 * X : ℕ) : ℝ) ≤ (eInt n P Q T d : ℝ) * ((T * (d.b - d.a) : ℕ) : ℝ) := by
      exact_mod_cast n1
    rw [hcast] at n2
    push_cast at n2
    rw [div_le_iff₀ (by positivity)]
    have e10 : (10 : ℝ) ^ 12 = 1000000000000 := by norm_num
    rw [e10]
    exact n2
  have main : c.w / (c.hi - c.lo) * (x ^ n / A + x ^ m / B - (y ^ n / A + y ^ m / B)) ≤
      (1 / A + 1 / B) * ((eInt n P Q T d : ℝ) / 2 ^ Q) := by
    calc _ ≤ c.w / (c.hi - c.lo) * ((1 / A + 1 / B) * ((X : ℝ) / 2 ^ Q)) := by
          apply mul_le_mul_of_nonneg_left _ hg0
          linarith
      _ = (1 / A + 1 / B) * (((d.p : ℝ) * 10 ^ 12 * (X : ℝ) / ((T : ℝ) * ((d.b : ℝ) - d.a))) / 2 ^ Q) := by
          rw [hgc]; ring
      _ ≤ _ := by gcongr
  have e : (1 / A + 1 / B) / B * ((eInt n P Q T d : ℝ) / 2 ^ Q) =
      ((1 / A + 1 / B) * ((eInt n P Q T d : ℝ) / 2 ^ Q)) / B := by ring
  rw [e]
  gcongr

theorem eref_le {P Q T : ℕ} (hQ : Q ≤ 900 * P) (hT : 0 < T) {l : List YCell} {L : List GD}
    (h : List.Forall₂ (Rel P T) l L) :
    (l.map erefTerm).sum ≤ (1 / 900 + 1 / 901) / 901 * (((L.map (eInt 900 P Q T)).sum : ℕ) / 2 ^ Q) := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    have : erefTerm _ ≤ _ := cell_erefG (n := 900) (m := 901) (A := 900) (B := 901) (by norm_num)
      (by norm_num) (by norm_num) hQ hr hT
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.cast_add]
    have e : ∀ a b : ℝ, (1 / 900 + 1 / 901) / 901 * ((a + b) / 2 ^ Q) =
        (1 / 900 + 1 / 901) / 901 * (a / 2 ^ Q) + (1 / 900 + 1 / 901) / 901 * (b / 2 ^ Q) :=
      fun a b => by ring
    rw [e]
    linarith

/-! ### The conversion to the Chebyshev variable -/

theorem rawQ_mapD (c : ℚ) (z : ℝ) : ∀ (l : List ℤ) (k : ℕ),
    rawQ (l.map fun d : ℤ => (d : ℚ) / c) k z = rawSum l k z / (c : ℝ)
  | [], _ => by simp [rawQ]
  | d :: t, k => by
    simp only [List.map_cons, rawQ, rawSum_cons, rawQ_mapD c z t (k + 1)]
    push_cast
    ring

/-- Monomial list in the variable `x` as a Chebyshev list in `w`. -/
def Zq (A B E : ℤ) (W : ℕ) (l : List ℤ) : List ℚ :=
  (Rc A B E l).map fun d : ℤ => (d : ℚ) / (((E : ℚ) ^ (l.length - 1)) * 2 ^ W)

theorem Pz_rawQ {A B E : ℤ} (hE : 0 < E) (W : ℕ) {w x : ℝ} (hx : (E : ℝ) * x = 2 * ((A : ℝ) + B * w))
    {l : List ℤ} (hl : 0 < l.length) : Pz l x / 2 ^ W = rawQ (Zq A B E W l) 0 w := by
  unfold Zq
  rw [rawQ_mapD]
  have h := Rc_eval A B E hx l
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 := ⟨l.length - 1, by omega⟩
  rw [hn] at h ⊢
  simp only [Nat.add_sub_cancel]
  push_cast
  have h' : rawSum (Rc A B E l) 0 w = (E : ℝ) ^ n * Pz l x := by
    have : (E : ℝ) * rawSum (Rc A B E l) 0 w = (E : ℝ) * ((E : ℝ) ^ n * Pz l x) := by
      rw [h]; ring
    exact mul_left_cancel₀ hE'.ne' this
  rw [h']
  field_simp

/-- The last step of both species. -/
theorem to_cheb (C : Cov) {Bud : ℚ} {A B E : ℤ} (hE : 0 < E) (W : ℕ) {w u : ℝ}
    (hw : w = (C.α : ℝ) * u + C.β) (hw1 : w ∈ Icc (-1 : ℝ) 1)
    (hx : (E : ℝ) * u = 2 * ((A : ℝ) + B * w)) {l : List ℤ} (hl : 0 < l.length)
    (hP : C.Phi u ≤ Bud) (p : List ℤ) (D : ℕ) :
    Pz l u / 2 ^ W + sumF C.W C.Bs u - (C.s : ℝ) * Real.log (1 + u ^ 2) ≤
      (Bud : ℝ) + (diffSum (D : ℚ) (addQ (Zq A B E W l) C.Cl) p : ℝ) + chebSum p D w := by
  have h1 := Pz_rawQ hE W hx hl
  have h2 := abs_rawQ_sub_le D (addQ (Zq A B E W l) C.Cl) p 0 w hw1
  rw [rawQ_addQ] at h2
  have h3 := (abs_le.mp h2).2
  unfold Cov.Phi at hP
  rw [← hw] at hP
  unfold chebSum
  rw [h1]
  linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompactInstance
open CatalanMeasure.GenD.Signed.RouteI.CompactCap (affine)
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ addQ diffSum)
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (reflectL physL_perm)

/-- Sum of the class errors. -/
def errS (R : RadLit) : ℕ → ℚ
  | 0 => 0
  | i + 1 => errS R i + R.err i

/-- Rational form of `sumE`. -/
def sumEQ (W : ℕ) : List Blk → ℚ
  | [] => 0
  | B :: t => (B.M + (S2 B.D 0 : ℚ) / 2 ^ W) + sumEQ W t

noncomputable section

theorem errS_cast (R : RadLit) (n : ℕ) : ∑ i ∈ Finset.range n, (R.err i : ℝ) = ((errS R n : ℚ) : ℝ) := by
  induction n with
  | zero => simp [errS]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp [errS]

theorem sumEQ_cast (W : ℕ) : ∀ Bs : List Blk, sumE W Bs = ((sumEQ W Bs : ℚ) : ℝ)
  | [] => by simp [sumE, sumEQ]
  | B :: t => by
    have := sumEQ_cast W t
    unfold sumE at this ⊢
    simp only [List.map_cons, List.sum_cons, sumEQ, this]
    unfold blkE
    push_cast
    ring

theorem moments_of_lit (g : GasLit) {l : List YCell} (h : List.Forall₂ (Rel g.P g.T) l g.L)
    (hT : 0 < g.T) (h2 : ∀ c ∈ l, 2 ≤ c.lo)
    {nR : ℕ} (c1 : rows g.P nR (g.L.map (stAt g.P g.T 1)) = g.R) {e1 e2 : ℤ} {r : List ℤ}
    (c1' : g.R = e1 :: e2 :: r) (cLn : g.L.length = g.Ln) (cSg : SG g.P g.T g.L = g.Sg)
    (cLI : LI g.P g.T g.Q g.L = g.LIv) (cLEI : LEI g.P g.T g.Q g.L = g.LEIv)
    (cM : g.chkM = true) :
    CloseL (fun i => physL l (fun s => s ^ i)) 0 (dyL g.Qm g.Mi) (dyL g.Qm g.Me) := by
  simp only [GasLit.chkM, Bool.and_eq_true, beq_iff_eq] at cM
  have hm0 := moments_close (Q := g.Q) h hT h2 c1 c1' cLn cSg cLI cLEI
  have hR1 : g.R.getD 1 0 = e2 := by rw [c1']; rfl
  have hm1 : CloseL (fun i => physL l (fun s => s ^ i)) 0 g.mL g.dL := by
    unfold GasLit.mL GasLit.dL
    rw [hR1]
    exact hm0
  exact relax_close 0 _ _ _ _ hm1 cM.1 (by rw [len_dyL]; exact cM.2)

theorem CloseL_tail {m : ℕ → ℝ} {k : ℕ} {a d : ℚ} {as ds : List ℚ}
    (h : CloseL m k (a :: as) (d :: ds)) : CloseL m (k + 1) as ds := h.2

theorem mirror_le {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {W Qm : ℕ} {m0 e0 : ℤ} {mt et : List ℤ}
    (hc : CloseL (fun i => physL l (fun s => s ^ i)) 0 (dyL Qm (m0 :: mt)) (dyL Qm (e0 :: et)))
    {mi : List ℤ} {me : List ℚ} (ck : chkMir W 1 (dyL Qm mt) (dyL Qm et) mi me = true)
    (l1 : mt.length = mi.length) (l2 : mt.length = me.length) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    physL l (fun s => Real.log |1 - s * u|) ≤ Pz (0 :: mi) u / 2 ^ W + (sumQ me : ℝ) := by
  have a := physL_refl_le h2 hu0 hu1 mt.length
  have hc' : CloseL (fun i => physL l (fun s => s ^ i)) 1 (dyL Qm mt) (dyL Qm et) := CloseL_tail hc
  have b := mir_close (μ := fun i => physL l (fun s => s ^ i)) W hu0.le hu1 1 (dyL Qm mt) (dyL Qm et) mi me
    one_pos hc' ck (by rw [len_dyL]; exact l1) (by rw [len_dyL]; exact l2)
  rw [len_dyL] at b
  have e : ∑ i ∈ Finset.range mt.length, (-1 / ((1 + i : ℕ) : ℝ)) *
      (fun i => physL l (fun s => s ^ i)) (1 + i) * u ^ (1 + i) =
      -∑ k ∈ Finset.range mt.length, u ^ (k + 1) / ((k : ℝ) + 1) * physL l (fun s => s ^ (k + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm 1 i]
    push_cast
    ring
  rw [e] at b
  have ep : Pz (0 :: mi) u = u * Pz mi u := by simp [Pz]
  rw [ep]
  simp only [pow_one] at b
  linarith

/-- Everything a radial record must satisfy. -/
structure RadOK (R : RadLit) (S : CapSource) (T : List Tr) (g : ℝ) (M : ℤ) (n : ℕ) : Prop where
  hM : 0 ≤ M
  hg : 0 ≤ g
  hgq : (R.hq : ℝ) = g / M
  hq0 : 0 ≤ R.hq
  hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2
  hcos : R.AngOK
  hδ : CLz S.coef (2 ^ 80) (R.δc : ℝ) 0 R.Cq
  hCb : ∀ d ∈ R.Cq, |(d : ℝ)| ≤ 2 ^ 81
  hlen : R.Cq.length = 384
  hW : R.W + R.sh = 160
  hδ0 : 0 ≤ R.δc
  hB : R.Bs.length = n
  hc : ∀ i < n, R.chk T i = true
  hrad : ∀ i < n, 0 < S.rad i ∧ S.rad i ≤ (R.B i).rho ∧
    ((((R.B i).rho : ℚ) : ℝ) - S.rad i) / S.rad i ≤ (R.eta i : ℝ)

theorem radial_pos {R : RadLit} {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} {n : ℕ}
    (h : RadOK R S T g M n) (hs : R.s = 1) (haux : S.aux Sign.pos = T.map (mkAux g M))
    (hl : ∀ e ∈ S.aux Sign.pos, e.rad < n) {u : ℝ} (hu : 0 < u) :
    S.radialA (Trunc.finite 384) Sign.pos u ≤ sumF R.W R.Bs u + ((errS R n : ℚ) : ℝ) := by
  have c := classes_le R h.hM h.hg h.hgq h.hq0 h.hT h.hcos (by rw [hs]; simp) h.hδ h.hCb h.hlen h.hW h.hδ0
    n h.hB h.hc h.hrad hu
  rw [errS_cast] at c
  refine le_trans (le_of_eq ?_) c
  rw [radialA_pos S 384 n hu hl, haux]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hs]
  push_cast
  ring

theorem radial_neg {R : RadLit} {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} {n : ℕ}
    (h : RadOK R S T g M n) (hs : R.s = -1) (haux : S.aux Sign.neg = T.map (mkAux g M))
    (hl : ∀ e ∈ S.aux Sign.neg, e.rad < n) (rns : List ℕ) (rb nm : ℕ) {Fb : ℚ} (hFb0 : 0 ≤ Fb)
    (hrn : ∀ i < n, ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb = (R.B i).rho ∧ (R.B i).rho ≤ 1)
    (hr1 : ∀ i < n, S.rad i ≤ 1)
    (hb : ∀ i < n, ∀ d ∈ R.F i, |(d : ℝ)| / 2 ^ 160 ≤ Fb) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    S.radialA (Trunc.finite 384) Sign.neg (-u) ≤ sumF R.W R.Bs u + ((errS R n : ℚ) : ℝ) +
      (polK (truncD R.sh nm (mirF R rns rb n)) 0 u / 2 ^ R.W +
        (((abs1 ((mirF R rns rb n).drop nm) : ℤ) : ℝ) / 2 ^ 160 +
          384 * (((mirE R Fb n : ℚ) : ℝ) + 1 / 2 ^ R.W))) := by
  have hs' : |(R.s : ℝ)| = 1 := by rw [hs]; simp
  have c := classes_le R h.hM h.hg h.hgq h.hq0 h.hT h.hcos hs' h.hδ h.hCb h.hlen h.hW h.hδ0
    n h.hB h.hc h.hrad hu
  rw [errS_cast] at c
  have hF : ∀ i < n, (R.F i).length = 384 := fun i _ => by
    unfold RadLit.F
    rw [tRow_len, h.hlen]
  have m := mirror_series (t := fun i k => (R.s : ℝ) ^ k * S.coef k * aC (T.map (mkAux g M)) i k)
    (r := S.rad) R rns rb nm hFb0 n h.hW
    (fun i hi => class_close R h.hM h.hg h.hgq h.hq0 h.hT h.hcos hs' h.hδ h.hCb h.hδ0 (h.hc i hi))
    (fun i hi => by
      obtain ⟨r1, r2, r3⟩ := h.hrad i hi
      obtain ⟨n1, n2⟩ := hrn i hi
      have n2' : (((R.B i).rho : ℚ) : ℝ) ≤ 1 := by exact_mod_cast n2
      refine ⟨r1.le, hr1 i hi, by rw [n1]; exact n2', ?_⟩
      rw [n1, abs_sub_comm, abs_of_nonneg (by linarith)]
      refine le_trans ?_ r3
      rw [le_div_iff₀ r1]
      have : (0 : ℝ) ≤ (((R.B i).rho : ℚ) : ℝ) - S.rad i := by linarith
      nlinarith [hr1 i hi])
    hF hb hu.le hu1
  rw [radialA_neg S 384 n hu hl, haux]
  have e : ∑ i ∈ Finset.range n, (aC (T.map (mkAux g M)) i 0 * Real.log (max u (S.rad i)) +
      ∑ k ∈ Finset.range 384, ((-1) ^ (k + 1) * S.coef (k + 1)) *
        (psiR (S.rad i) u ^ (k + 1) + (S.rad i * u) ^ (k + 1)) * aC (T.map (mkAux g M)) i (k + 1)) =
      ∑ i ∈ Finset.range n, (aC (T.map (mkAux g M)) i 0 * Real.log (max u (S.rad i)) +
        ∑ k ∈ Finset.range 384, ((R.s : ℝ) ^ (k + 1) * S.coef (k + 1) *
          aC (T.map (mkAux g M)) i (k + 1)) * psiR (S.rad i) u ^ (k + 1)) +
      ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range 384,
        (R.s : ℝ) ^ (k + 1) * S.coef (k + 1) * aC (T.map (mkAux g M)) i (k + 1) *
          (S.rad i * u) ^ (k + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hs]
    push_cast
    ring
  rw [e]
  linarith

theorem sumF_snoc (W : ℕ) (Bs : List Blk) (B : Blk) (x : ℝ) :
    sumF W (Bs ++ [B]) x = sumF W Bs x + blkF W B x := by
  simp [sumF]

theorem addZ_len_pos : ∀ {a b : List ℤ}, 0 < a.length → 0 < (addZ a b).length
  | _ :: _, [], _ => by simp [addZ]
  | _ :: _, _ :: _, _ => by simp [addZ]

/-- The mirror block. -/
def mBlk (D : List ℤ) : Blk := ⟨1, 0, 0, D⟩

theorem blkF_mBlk (W : ℕ) (D : List ℤ) {u : ℝ} (hu1 : u ≤ 1) :
    blkF W (mBlk D) u = polK D 0 u / 2 ^ W := by
  unfold blkF mBlk psiR
  simp [not_lt.mpr hu1]

theorem log4 : (2 * (6931471803 / 10 ^ 10 : ℝ)) ≤ Real.log 4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  rw [h]
  norm_num at this ⊢
  linarith

theorem capAux (σ : Sign) : capSource.aux σ = (auxT σ).map (mkAux (tgt σ) (sumP (auxT σ))) := rfl

/-- Positive species. -/
theorem pos_core (g : GasLit) (R : RadLit) (C : Cov) (En : CoefEnc) {Bud : ℚ}
    (hrel : relP g.P gasPosT g.L = true) (hTg : (g.T : ℤ) = sumP row0) (hT : 0 < g.T)
    (hS : sepL (2 * 10 ^ 12) g.L = true) {nR : ℕ}
    (c1 : rows g.P nR (g.L.map (stAt g.P g.T 1)) = g.R) {e1 e2 : ℤ} {r : List ℤ}
    (c1' : g.R = e1 :: e2 :: r) (cLn : g.L.length = g.Ln) (cSg : SG g.P g.T g.L = g.Sg)
    (cLI : LI g.P g.T g.Q g.L = g.LIv) (cLEI : LEI g.P g.T g.Q g.L = g.LEIv)
    (cM : g.chkM = true) (cV : g.chkV = true) (cG : G2I g.P g.T g.Q g.L = g.G2v)
    (cS : g.chkS = true) (cC : g.chkC = true) {Ev : ℕ}
    (cE : (g.L.map (eInt 900 g.P 64 g.T)).sum = Ev) (hP : 64 ≤ 900 * g.P)
    (hR : RadOK R capSource (auxT Sign.pos) (tgt Sign.pos) (sumP (auxT Sign.pos)) 16)
    (hs : R.s = 1) (hEn : En.Valid capSource) (hq1 : En.qh < 1)
    (hCW : C.W = R.W) (hCB : C.Bs = R.Bs) (hCs : C.s = 53 / 58)
    (hCα : C.α = 2000000 / 901251) (hCβ : C.β = -(1098749 / 901251))
    (hPhi : ∀ x ∈ Icc (98749 / 1000000 : ℝ) 1, C.Phi x ≤ Bud)
    (hGl : 0 < (g.G []).length) (hmq : 0 ≤ massQ g.T g.L)
    (hfin : g.Tb + sumQ (dyL 40 g.f) - 2 * massQ g.T g.L * (6931471803 / 10 ^ 10) - 14762657 / 100000000 +
      (1 / 900 + 1 / 901) / 901 * ((Ev : ℚ) / 2 ^ 64) + errS R 16 +
      En.tail (1 - massQ g.T g.L) 1 + Bud +
      diffSum (D : ℚ) (addQ (Zq 1098749 901251 4000000 g.W (g.G [])) C.Cl) posP ≤ posEps) :
    PosHf capSource (Trunc.finite 384) := by
  intro u hu
  have hu0 : 0 < u := by have := hu.1; linarith
  have hu1 := hu.2
  have hF : List.Forall₂ (Rel g.P g.T) (capSource.gas Sign.pos) g.L := relP_spec hTg gasPosT g.L hrel
  have h2 : ∀ c ∈ capSource.gas Sign.pos, 2 ≤ c.lo := gas_pos_lo
  have fld := field_pos capSource 384 h2 rfl hu0 hu1
  have gs := gas_of_lit g hF hT h2 hS c1 c1' cLn cSg cLI cLEI cM cV cG cS cC [] hu0 hu1
  have hm : massL (capSource.gas Sign.pos) = ((massQ g.T g.L : ℚ) : ℝ) := massL_rel hF
  have er : capSource.reflTail ≤ (1 / 900 + 1 / 901) / 901 * ((Ev : ℝ) / 2 ^ 64) := by
    have := eref_le hP hT hF
    rw [cE] at this
    rw [reflTail_eq capSource rfl]
    exact this
  have rd := radial_pos hR hs (capAux Sign.pos) (fun e he => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (show e ∈ (auxT Sign.pos).map _ from he)
    exact mkAux_rad_lt _ _ t (pa_ok t ht).2) hu0
  have tgtq : tgt Sign.pos = ((1 - massQ g.T g.L : ℚ) : ℝ) := by
    show 1 - massL (capSource.gas Sign.pos) = _
    rw [hm]
    push_cast
    ring
  have tl := auxTail_le hEn hq1 Sign.pos (m := 1 - massQ g.T g.L) (c := 1)
    (by rw [auxMass_eq, tgtq]) (by rw [auxMass_eq]; exact tgt_nonneg _) (by simp)
  set w := affine (98749 / 1000000) u with hwd
  have hw : w = (C.α : ℝ) * u + C.β := by
    rw [hwd, hCα, hCβ]
    unfold affine
    push_cast
    ring
  have hx : (((4000000 : ℤ)) : ℝ) * u = 2 * (((1098749 : ℤ) : ℝ) + ((901251 : ℤ) : ℝ) * w) := by
    rw [hwd]
    unfold affine
    push_cast
    ring
  have hw1 : w ∈ Icc (-1 : ℝ) 1 := by
    have a := hu.1
    rw [hw, hCα, hCβ]
    push_cast
    constructor <;> linarith
  have ch := to_cheb C (A := 1098749) (B := 901251) (E := 4000000) (by norm_num) g.W hw hw1 hx hGl
    (hPhi u hu) posP D
  have fq := (Rat.cast_le (K := ℝ)).mpr hfin
  have l4 := log4
  have m0 : (0 : ℝ) ≤ ((massQ g.T g.L : ℚ) : ℝ) := by exact_mod_cast hmq
  have ml := mul_le_mul_of_nonneg_left l4 m0
  rw [hCW, hCB, hCs] at ch
  have hk : kappa Sign.pos = 14762657 / 100000000 := rfl
  have hz : Pz ([] : List ℤ) u = 0 := by simp [Pz]
  rw [hz, hm, zero_div] at gs
  rw [hk] at fld
  push_cast at fq ch
  linarith [fld, gs, er, rd, tl, ch, fq, ml]

theorem massL_perm {a b : List YCell} (h : a.Perm b) : massL a = massL b := by
  unfold massL
  exact (h.map _).sum_eq

theorem massL_reflect (l : List YCell) : massL (reflectL l) = massL l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have e : ∀ (d : YCell) (m : List YCell), massL (d :: m) = d.w + massL m := fun d m => by
      simp [massL]
    show massL (c.reflect :: reflectL l) = _
    rw [e, e, ih]
    rfl

/-- Negative species. -/
theorem neg_core (g : GasLit) (R : RadLit) (C : Cov) (En : CoefEnc) {Bud : ℚ}
    (hrel : relN g.P gasNegT.reverse g.L = true) (hTg : (g.T : ℤ) = sumP row0) (hT : 0 < g.T)
    (hS : sepL (2 * 10 ^ 12) g.L = true) {nR : ℕ}
    (c1 : rows g.P nR (g.L.map (stAt g.P g.T 1)) = g.R) {e1 e2 : ℤ} {r : List ℤ}
    (c1' : g.R = e1 :: e2 :: r) (cLn : g.L.length = g.Ln) (cSg : SG g.P g.T g.L = g.Sg)
    (cLI : LI g.P g.T g.Q g.L = g.LIv) (cLEI : LEI g.P g.T g.Q g.L = g.LEIv)
    (cM : g.chkM = true) (cV : g.chkV = true) (cG : G2I g.P g.T g.Q g.L = g.G2v)
    (cS : g.chkS = true) (cC : g.chkC = true)
    {m0' e0' : ℤ} {mt et : List ℤ} (hMi : g.Mi = m0' :: mt) (hMe : g.Me = e0' :: et)
    {mi : List ℤ} {me : List ℚ} (ck : chkMir g.W 1 (dyL g.Qm mt) (dyL g.Qm et) mi me = true)
    (l1 : mt.length = mi.length) (l2 : mt.length = me.length)
    (hR : RadOK R capSource (auxT Sign.neg) (tgt Sign.neg) (sumP (auxT Sign.neg)) 16)
    (hs : R.s = -1) (rns : List ℕ) (rb nm : ℕ)
    (hrn : ∀ i < 16, ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb = (R.B i).rho ∧ (R.B i).rho ≤ 1)
    (hb : ∀ i < 16, ∀ d ∈ R.F i, |(d : ℝ)| / 2 ^ 160 ≤ ((1 : ℚ) : ℝ))
    {Dm : List ℤ} (hDm : Dm = truncD R.sh nm (mirF R rns rb 16)) {Tm : ℤ}
    (hTm : abs1 ((mirF R rns rb 16).drop nm) = Tm)
    (hEn : En.Valid capSource) (hq1 : En.qh < 1)
    (hCW : C.W = R.W) (hCB : C.Bs = R.Bs ++ [mBlk Dm]) (hCs : C.s = 53 / 58)
    (hCα : C.α = 200000 / 80499) (hCβ : C.β = -(119501 / 80499))
    (hPhi : ∀ x ∈ Icc (19501 / 100000 : ℝ) 1, C.Phi x ≤ Bud)
    (hmq : 0 ≤ massQ g.T g.L)
    (hfin : g.Tb + sumQ (dyL 40 g.f) + sumQ me - 2 * massQ g.T g.L * (6931471803 / 10 ^ 10) -
      5463909 / 100000000 + errS R 16 + ((Tm : ℚ) / 2 ^ 160 + 384 * (mirE R 1 16 + 1 / 2 ^ R.W)) +
      En.tail (53 / 58 - massQ g.T g.L) 2 + Bud +
      diffSum (D : ℚ) (addQ (Zq 119501 80499 400000 g.W (g.G (0 :: mi))) C.Cl) negP ≤ negEps) :
    NegHf capSource (Trunc.finite 384) := by
  intro u hu
  have hu0 : 0 < u := by have := hu.1; linarith
  have hu1 := hu.2
  set l : List YCell := gasNegT.reverse.map fun t => (mkCell 1 (sumP row0) t).reflect with hl
  have hF : List.Forall₂ (Rel g.P g.T) l g.L := relN_spec hTg gasNegT.reverse g.L hrel
  have hp : l.Perm (reflectL (capSource.gas Sign.neg)) := by
    have e : l = (reflectL (capSource.gas Sign.neg)).reverse := by
      rw [hl]
      show _ = (((gasNegT.map (mkCell 1 (sumP row0))).map YCell.reflect)).reverse
      rw [List.map_map, List.map_reverse]
      rfl
    rw [e]
    exact List.reverse_perm _
  have h2 : ∀ c ∈ l, 2 ≤ c.lo := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (hp.mem_iff.1 hc)
    have := gas_neg_hi d hd
    show 2 ≤ -d.hi
    linarith
  have fld := field_neg capSource 384 gas_neg_hi hu0 hu1
  rw [← physL_perm hp, ← physL_perm hp] at fld
  have gs := gas_of_lit g hF hT h2 hS c1 c1' cLn cSg cLI cLEI cM cV cG cS cC (0 :: mi) hu0 hu1
  have mo := moments_of_lit g hF hT h2 c1 c1' cLn cSg cLI cLEI cM
  rw [hMi, hMe] at mo
  have mr := mirror_le h2 mo ck l1 l2 hu0 hu1
  have hm : massL l = ((massQ g.T g.L : ℚ) : ℝ) := massL_rel hF
  have hm' : massL (capSource.gas Sign.neg) = ((massQ g.T g.L : ℚ) : ℝ) := by
    rw [← massL_reflect, ← massL_perm hp, hm]
  have rd := radial_neg hR hs (capAux Sign.neg) (fun e he => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (show e ∈ (auxT Sign.neg).map _ from he)
    exact mkAux_rad_lt _ _ t (na_ok t ht).2) rns rb nm (Fb := 1) zero_le_one hrn
    (fun i hi => (hR.hrad i hi).2.1.trans (by exact_mod_cast (hrn i hi).2)) hb hu0 hu1
  rw [← hDm, hTm] at rd
  have tgtq : tgt Sign.neg = ((53 / 58 - massQ g.T g.L : ℚ) : ℝ) := by
    show 53 / 58 - massL (capSource.gas Sign.neg) = _
    rw [hm']
    push_cast
    ring
  have tl := auxTail_le hEn hq1 Sign.neg (m := 53 / 58 - massQ g.T g.L) (c := 2)
    (by rw [auxMass_eq, tgtq]) (by rw [auxMass_eq]; exact tgt_nonneg _) (by simp)
  set w := affine (19501 / 100000) u with hwd
  have hw : w = (C.α : ℝ) * u + C.β := by
    rw [hwd, hCα, hCβ]
    unfold affine
    push_cast
    ring
  have hx : (((400000 : ℤ)) : ℝ) * u = 2 * (((119501 : ℤ) : ℝ) + ((80499 : ℤ) : ℝ) * w) := by
    rw [hwd]
    unfold affine
    push_cast
    ring
  have hw1 : w ∈ Icc (-1 : ℝ) 1 := by
    have a := hu.1
    rw [hw, hCα, hCβ]
    push_cast
    constructor <;> linarith
  have hGl : 0 < (g.G (0 :: mi)).length := by
    have : ∀ (c a b acc : List ℤ), 0 < acc.length → 0 < (comb c a b acc).length := by
      intro c
      induction c with
      | nil => intro a b acc h; exact h
      | cons d t ih =>
        intro a b acc h
        simp only [comb]
        exact ih _ _ _ (by
          exact addZ_len_pos h)
    exact this _ _ _ _ (by simp)
  have ch := to_cheb C (A := 119501) (B := 80499) (E := 400000) (by norm_num) g.W hw hw1 hx hGl
    (hPhi u hu) negP D
  have fq := (Rat.cast_le (K := ℝ)).mpr hfin
  have l4 := log4
  have m0 : (0 : ℝ) ≤ ((massQ g.T g.L : ℚ) : ℝ) := by exact_mod_cast hmq
  have ml := mul_le_mul_of_nonneg_left l4 m0
  rw [hCW, hCB, hCs, sumF_snoc, blkF_mBlk _ _ hu1] at ch
  have hk : kappa Sign.neg = 5463909 / 100000000 := rfl
  rw [hm] at gs
  rw [hk] at fld
  push_cast at fq ch
  linarith [fld, gs, mr, rd, tl, ch, fq, ml]

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

/-- Decoder of the flat cell list. -/
def gdOf : List ℤ → List GD
  | a :: b :: p :: al :: ah :: lam :: t =>
    ⟨a.toNat, b.toNat, p.toNat, al.toNat, ah.toNat, lam.toNat⟩ :: gdOf t
  | _ => []

/-- Decoder of the flat node list. -/
def ndOf : List ℤ → List (ℚ × ℚ)
  | x :: d :: v :: t => ((x : ℚ) / d, (v : ℚ) / 2 ^ 80) :: ndOf t
  | _ => []

/-- Class checks and radius checks together. -/
def RadLit.allChk (R : RadLit) (T : List Tr) : Bool :=
  (List.range 16).all fun i => R.chk T i && radChk (R.B i).rho (R.B i).sg (R.eta i) i

def auxOK (T : List Tr) : Bool := T.all fun t => decide (0 ≤ t.2.1) && decide (0 ≤ t.2.2)

def cqOK (Cq : List ℤ) : Bool := Cq.all fun d => decide (|d| ≤ 2 ^ 81)

def rnOK (R : RadLit) (rns : List ℕ) (rb : ℕ) : Bool :=
  (List.range 16).all fun i => decide (((rns.getD i 0 : ℕ) : ℚ) / 2 ^ rb = (R.B i).rho) &&
    decide ((R.B i).rho ≤ 1)

def fbOK (R : RadLit) : Bool :=
  (List.range 16).all fun i => (R.F i).all fun d => decide (|d| ≤ 2 ^ 160)

noncomputable section

theorem RadLit.allChk_spec {R : RadLit} {T : List Tr} (h : R.allChk T = true) {i : ℕ} (hi : i < 16) :
    R.chk T i = true ∧ radChk (R.B i).rho (R.B i).sg (R.eta i) i = true := by
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simpa using this

theorem radOK_of (R : RadLit) (σ : Sign) {En : CoefEnc} (hEn : En.Valid capSource) {mq : ℚ}
    (hmq : tgt σ = mq) (h1 : R.hq = mq / (sumP (auxT σ) : ℚ)) (h2 : 0 ≤ R.hq)
    (hTa : auxOK (auxT σ) = true) (hNA : R.NA = 93)
    (hcos : (List.range (R.NA + 1)).all (cosChk R.NA R.CT) = true)
    (hco : coefChk En R.δc R.Cq 0 = true) (hCb : cqOK R.Cq = true) (hlen : R.Cq.length = 384)
    (hW : R.W + R.sh = 160) (hδ0 : 0 ≤ R.δc) (hB : R.Bs.length = 16)
    (hall : R.allChk (auxT σ) = true) (hM : 0 ≤ sumP (auxT σ)) :
    RadOK R capSource (auxT σ) (tgt σ) (sumP (auxT σ)) 16 where
  hM := hM
  hg := tgt_nonneg σ
  hgq := by rw [h1, hmq]; push_cast; rfl
  hq0 := h2
  hT := fun t ht => by
    have := List.all_eq_true.1 hTa t ht
    simpa using this
  hcos := ⟨hNA, fun m hm => List.all_eq_true.1 hcos m (List.mem_range.2 (by omega))⟩
  hδ := coef_close hEn R.Cq 0 hco
  hCb := fun d hd => by
    have := List.all_eq_true.1 hCb d hd
    simp only [decide_eq_true_eq] at this
    have h : ((|d| : ℤ) : ℝ) ≤ ((2 ^ 81 : ℤ) : ℝ) := by exact_mod_cast this
    rw [Int.cast_abs, Int.cast_pow, Int.cast_ofNat] at h
    exact h
  hlen := hlen
  hW := hW
  hδ0 := hδ0
  hB := hB
  hc := fun i hi => (R.allChk_spec hall hi).1
  hrad := fun i hi => by
    obtain ⟨a, b, c, _, _⟩ := rad_facts (R.allChk_spec hall hi).2
    exact ⟨a, b, c⟩

theorem blks_ok (R : RadLit) {T : List Tr} (hB : R.Bs.length = 16) (hq0 : 0 ≤ R.hq)
    (hall : R.allChk T = true) : ∀ B ∈ R.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg := by
  intro B hBm
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hBm
  have hi' : i < 16 := by omega
  obtain ⟨c, r⟩ := R.allChk_spec hall hi'
  have e : R.B i = R.Bs[i] := List.getD_eq_getElem _ _ hi
  obtain ⟨_, _, _, a, b⟩ := rad_facts r
  rw [e] at a b
  refine ⟨b, ?_, a⟩
  simp only [RadLit.chk, Bool.and_eq_true, decide_eq_true_eq] at c
  rw [← e, c.2]
  positivity

theorem Phi_of (C : Cov) {E K Bud lo : ℚ} (n : ℚ × ℚ) (t : List (ℚ × ℚ)) (hs : 0 ≤ C.s) (hα : 0 ≤ C.α)
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hE : sumEQ C.W C.Bs ≤ E) (hK : 2 * C.s + mc4 C.Cl 0 * C.α ^ 2 ≤ K) (h0 : 0 < n.1)
    (hc : C.chain E K Bud n t = true) (hn : (n :: t).all C.nodeOK = true) (hlo : bot n t = lo)
    (h1 : n.1 = 1) {x : ℝ} (hx : x ∈ Icc (lo : ℝ) 1) : C.Phi x ≤ Bud := by
  refine C.cover hs hα hB (by rw [sumEQ_cast]; exact_mod_cast hE) hK t n h0 hc
    (fun m hm => List.all_eq_true.1 hn m hm) x ?_
  rw [hlo, h1]
  simpa using hx

theorem hrn_of {R : RadLit} {rns : List ℕ} {rb : ℕ} (h : rnOK R rns rb = true) {i : ℕ} (hi : i < 16) :
    ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb = (R.B i).rho ∧ (R.B i).rho ≤ 1 := by
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  rw [← this.1]
  push_cast
  rfl

theorem hb_of {R : RadLit} (h : fbOK R = true) {i : ℕ} (hi : i < 16) {d : ℤ} (hd : d ∈ R.F i) :
    |(d : ℝ)| / 2 ^ 160 ≤ ((1 : ℚ) : ℝ) := by
  have := List.all_eq_true.1 (List.all_eq_true.1 h i (List.mem_range.2 hi)) d hd
  simp only [decide_eq_true_eq] at this
  have h1 : ((|d| : ℤ) : ℝ) ≤ ((2 ^ 160 : ℤ) : ℝ) := by exact_mod_cast this
  rw [Int.cast_abs, Int.cast_pow, Int.cast_ofNat] at h1
  rw [Rat.cast_one, div_le_one (by positivity)]
  exact h1

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf
open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompactInstance
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (diffSum addQ)
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (reflectL)

def CTl : ℕ := 3432289493168574315307147760865130825474106292166924779170433513824196210417976913383338703551059324455566675134143829985313882632853974031432453092075303558452237396205582081627130169788205630708567009536263687035494658485063820281032815309135506764251649650001775125298312326893277362136346083476612080559403214766756854467921458681203503548857688352790435098749118491981922746054340054693791549024756659733298618902756895556207340227569415585540071448379110765362736123371139308930722709944588641739583976913362053074947174014815101781487501172563584887772329224430732407961729123729288387187482558880760144047668163479017850790306649607989655104753921029071745931422350735054141231443933206758231786587867987104494845978396329009705540237637473560124620006797501126318706269778156491694036860751134624928384798511277612612767609846013338674639143763754472045390048727260327746667174279245369949731525549451402148820335506211337341630972705470355551049728570503018640151761203991179936668563238515489984394293720441825267608612145748397032384570184865833811786929667456036674032411962373449942999713958931257749536457133914550343741466047548523659779933260111705831053156591097787450059080804340124797366766254628030527549348304758385247747664442547165486235274814885099085229989877880060538663643447963497940381244660440963784580311954965903373427664395883711314980951991513156144989793065440520027484909458895827612071340662866327119285922573537807030142266050057745552816993103996247581762607566719884023456582722503928266514996996159676078379216885259579668331081905755382116539870669710456921130925366677622036563095062623066937426309527693137110123370236450096955626269500821855960974051709254987484275258508591785547264778997013505647888889796293866476169334765200572051782696410821517222560989642325873222005276036207181275417136335113063298619303115508553519636851256610808149592432021800556878732114501044959450455160752442589963445348275564833393223582488561747444978376942617760892593836131248155719673136502837752948512849764488791988244424947691498988471162091551998897740407267779632880162951650756724567152196782079273081860670855556476931673967540977276008008279845407431573045617411793227288950954436928609047824008861621169354162762158346328158825636275981758752062483200558618543791949224942346237290831874083602575719380870432466534348040883367576842374831495408743106813200565075912367739936834156755901853186104353474372564979896426478765482707300030466235719157193869076290325478465981035048207507956671716038572991768840290014676069084130617762879380578378922530072495806415151261722724357410799216675947062991970079817655961040446680010434475735384064
def Cql : List ℤ := raw_ints% [-1208337569457489154579320, -603288975639820611874650, -401220318635059555424516, -299902041005742789206114, -238889520682016818390759, -198035453570295095276931, -168705923277331329388406, -146584430592503193941793, -129273246433301312742272, -115333961060135550427022, -103851376744274829357273, -94215459663480714335017, -86003934055423734381752, -78915197104643940277440, -72728071214716363532278, -67276652017172413564403, -62434035972752070871076, -58101474170987762084536, -54200953011896531707843, -50670002195102030565568, -47457987435786967286513, -44523415367867071153608, -41831942466697220440209, -39354882555307875468832, -37068073205771063460581, -34951004335505846719279, -32986140956599763668734, -31158391482420431687896, -29454686406530017828987, -27863641556045105750137, -26375286783071588071456, -24980845745476881284042, -23672555909897152839330, -22443520469652492948948, -21287585771564977677866, -20199239271463564624963, -19173524116953118113697, -18205967279150729551421, -17292518788118867124163, -16429500117187691152199, -15613560144039719772375, -14841637417000359489750, -14110927692541307485506, -13418855898887663171127, -12763051831648200410095, -12141329008797155524433, -11551666210432686170333, -10992191308383564187998, -10461167055701622943694, -9956978559303207518359, -9478122202814126451159, -9023195822847096767490, -8590889971938614992841, -8179980126340176020160, -7789319717713869674759, -7417833885261352273854, -7064513859512405829544, -6728411901396261519341, -6408636730707161197362, -6104349386974923007020, -5814759473323462147623, -5539121740360617593324, -5276732972668876072651, -5026929145205671142026, -4789082820995911947200, -4562600765009890920525, -4346921752151605590486, -4141514549906887739687, -3945876058477255055412, -3759529593204345463527, -3582023295813587526879, -3412928662510301653005, -3251839178277167338708, -3098369047874819791748, -2952152015059313837790, -2812840262420150395649, -2680103385026619379651, -2553627431762193362342, -2433114008838482658518, -2318279440522055665293, -2208853982588052846530, -2104581084441594062111, -2005216696228087962649, -1910528617592413003316, -1820295885049514457781, -1734308195199566845608, -1652365361263246707635, -1574276800630127700858, -1499861051308615713399, -1428945315341695345138, -1361365027411259789769, -1296963446996873969013, -1235591272584171999930, -1177106276535207565751, -1121372959339275056593, -1068262222059161274507, -1017651055875497675775, -969422247711768861137, -923464100995397970761, -879670170676886505696, -837939011689867713048, -798173940090701620759, -760282806167396817812, -724177778854635348024, -689775140834900698859, -656995093745520380574, -625761572948151955694, -596002071351149241678, -567647471806598895777, -540631887632845628077, -514892510840232531378, -490369467662756424502, -467005681021543215770, -444746739567635226876, -423540772971686652236, -403338333146907269041, -384092281109088877077, -365757679193893998784, -348291688366873010470, -331653470375986613780, -315804094509820370115, -300706448737255123324, -286325155016163659439, -272626488569796555287, -259578300939950578555, -247149946635828502232, -235312213206743055036, -224037254575529588830, -213298527477748266827, -203070730859510555985, -193329748094087245405, -184052591884374370744, -175217351724835345976, -166803143802726316480, -158790063224269444853, -151159138456986045874, -143892287884657198414, -136972278376361287301, -130382685775762203616, -124107857221303830461, -118132875212220070818, -112443523339308165637, -107026253603248638495, -101868155246899298717, -96956925031453991214, -92280838889649153738, -87828724892332043314, -83589937467682441951, -79554332815212917973, -75712245459368966652, -72054465890116776291, -68572219240349722094, -65257144952271335202, -62101277387128408139, -59097027334778712171, -56237164381588823749, -53514800097073791086, -50923372001516541094, -48456628278545491165, -46108613198308003897, -43873653218459089949, -41746343731692893968, -39721536429982558389, -37794327257065428369, -35960044922018439176, -34214239948015949531, -32552674231552128263, -30971311088544997768, -29466305764821977611, -28033996389519716095, -26670895350916484427, -25373681075155658360, -24139190189215937562, -22964410050339960992, -21846471624949777129, -20782642700857037665, -19770321417319531544, -18807030098205408882, -17890409374203728481, -17018212580666291054, -16188300418282514493, -15398635864377722159, -14647279323186941120, -13932384003992374600, -13252191516524294544, -12605027673513314139, -11989298490747912434, -11403486375435710774, -10846146494091313054, -10315903311578444076, -9811447293320534769, -9331531763062651754, -8874969908919554926, -8440631930780457029, -8027442322461485045, -7634377282302602917, -7260462246197514839, -6904769537323464368, -6566416127103483786, -6244561502187110309, -5938405632477423933, -5647187035463004306, -5370180932333555116, -5106697491567985700, -4856080155884130397, -4617704048630465541, -4390974455882570964, -4175325380681077439, -3970218166013825769, -3775140183303301855, -3589603583311453461, -3413144106518070904, -3245319950166343252, -3085710689300286855, -2933916249243773677, -2789555927090139421, -2652267459885089659, -2521706137294098147, -2397543956648945813, -2279468818366711289, -2167183759828613549, -2060406225895833788, -1958867374325006900, -1862311414427663718, -1770494977395705865, -1683186516789179410, -1600165737753347885, -1521223053599507817, -1446159068448292433, -1374784084695515831, -1306917634119058752, -1242388031501019674, -1181031949692477061, -1122694015098849994, -1067226422612119782, -1014488569062193558, -964346704303556749, -916673599095174080, -871348228971453475, -828255473340074475, -787285829078689116, -748335137937011101, -711304327083697406, -676099162168770255, -642630012302198473, -610811626377723939, -580562920198146583, -551806773884132310, -524469839073241884, -498482355439351835, -473777976085004965, -450293601380539598, -427969220844152614, -406747762676398473, -386574950581059567, -367399167521885275, -349171326081428503, -331844745104148401, -315375032321133248, -299719972668263633, -284839422023416699, -270695206101439561, -257251024258124686, -244472357966331275, -232326383738742427, -220781890282554649, -209809199681689488, -199380092411920810, -189467736003648726, -180046617175944113, -171092477273957340, -162582250849850841, -154494007235096943, -146806894959297711, -139501088877650055, -132557739875813310, -125958927027253730, -119687612084155814, -113727596188718372, -108063478697107401, -102680618013531101, -97565094336847129, -92703674226820247, -88083776901631086, -83693442182504531, -79521300005389506, -75556541423490261, -71788891028132135, -68208580718950775, -64806324757731558, -61573296043403339, -58501103548715417, -55581770862005887, -52807715780210477, -50171730901869917, -47666965171377359, -45286906328071247, -43025364216029025, -40876454912558712, -38834585635423724, -36894440390776437, -35050966325622467, -33299360750395057, -31635058798891522, -30053721694415505, -28551225592483676, -27123650971897231, -25767272547350509, -24478549678054701, -23254117248097117, -22090776995438817, -20985489267578521, -19935365182981365, -18937659178389783, -17989761923103259, -17089193582236002, -16233597411839346, -15420733669610718, -14648473825705607, -13914795058924961, -13217775024269733, -12555586878538651, -11926494551296381, -11328848249158710, -10761080181930732, -10221700499694653, -9709293430477281, -9222513608634674, -8760082584574166, -8320785506893236, -7903467968451533, -7507033008307955, -7130438261850016, -6772693251818751, -6432856813290177, -6110034646014523, -5803376987838162, -5512076403241004, -5235365681314946, -4972515837787510, -4722834215959729, -4485662681679300, -4260375907709700, -4046379743083907, -3843109663248150, -3650029297007315, -3466629026479741, -3292424656455622, -3126956149730631, -2969786425155048, -2820500215299113, -2678702980787876, -2544019878503917, -2416094780994262, -2294589344549066, -2179182123544363, -2069567728759872, -1965456027495660, -1866571383418757, -1772651934172854, -1683448904881199, -1598725955765105, -1518258562188139, -1441833425519525, -1369247913289560, -1300309527185268, -1234835397506205, -1172651802768509, -1113593713210105, -1057504357011594, -1004234808105954, -953643594505897, -905596326130686, -859965341164562, -816629370026828, -775473216079144, -736387452238842, -699268132708249, -664016519069076, -630538820028135, -598745944136000, -568553264833804, -539880397215328, -512650985921925]
def dcL : ℚ := (137056426003 / 332306998946228968225951765070086144 : ℚ)
def Enc : CoefEnc := ⟨(161197219848661288509620604195940589287 / 170141183460469231731687303715884105728 : ℚ), (322394439697322577019241208391881178575 / 340282366920938463463374607431768211456 : ℚ), (18375233944490641139105470806103934607 / 340282366920938463463374607431768211456 : ℚ), (18375233944490641139105470806103934609 / 340282366920938463463374607431768211456 : ℚ), (20652068278450630479526165946105097 / 21267647932558653966460912964485513216 : ℚ), (330433092455210087672418655137681553 / 340282366920938463463374607431768211456 : ℚ)⟩
def gdP : List ℤ := raw_ints% [2000033231527, 2000039851323, 6686, 115126506182925728565962108219083771479052611125894842417479424160288629343369, 115063421637341750954831431586478552896497309656506793059967265927116199453972, 4049562, 2000039851323, 2000046079500, 339827331, 115063421637341750954831431586478552896497309656506793059967265927116199453972, 115008734028686139352127222438899187000086808861650697624855682582757395061057, 4570597, 2000046079500, 2000047076101, 67382266, 115008734028686139352127222438899187000086808861650697624855682582757395061057, 115000337099550903204000753402871036297796149986674806570676279839532181277292, 4851511, 2000047076101, 2000054906859, 576255968, 115000337099550903204000753402871036297796149986674806570676279839532181277292, 114937252553494271814697321389921975114913601497877347426864829296304559872781, 5198449, 2000054906859, 2000063344594, 681756488, 114937252553494271814697321389921975114913601497877347426864829296304559872781, 114874168010579577154048090614542156544814480918177722403424196794955743302030, 5808678, 2000063344594, 2000072390306, 747606072, 114874168010579577154048090614542156544814480918177722403424196794955743302030, 114811083473813655201781925060952382457119886129382851913665900656965788972534, 6441664, 2000072390306, 2000077526822, 423820171, 114811083473813655201781925060952382457119886129382851913665900656965788972534, 114777026417937971014428971607735073176154159555973527720077552538212314736007, 6936592, 2000077526822, 2000082045000, 371102744, 114777026417937971014428971607735073176154159555973527720077552538212314736007, 114747998927731493596421716656176165373638983117969217813083170691053156793688, 7268996, 2000082045000, 2000092309679, 827838186, 114747998927731493596421716656176165373638983117969217813083170691053156793688, 114684914385541658656026059154822944040295957473485305826407018722641554956479, 7773120, 2000092309679, 2000095667547, 265515765, 114684914385541658656026059154822944040295957473485305826407018722641554956479, 114665054492048574822219541531012136634171933205715914222258972215270201475226, 8220158, 2000095667547, 2000103185351, 587523009, 114665054492048574822219541531012136634171933205715914222258972215270201475226, 114621829841840883816441546459468385985076206770933341027699542601715986248380, 8576728, 2000103185351, 2000114673025, 871028545, 114621829841840883816441546459468385985076206770933341027699542601715986248380, 114558745298863714310151891564851897661154443637270880599837209595445934409204, 9187883, 2000114673025, 2000126773712, 883302035, 114558745298863714310151891564851897661154443637270880599837209595445934409204, 114495660759545259572350261489332643266426720258549336314237020846386464754671, 9925199, 2000126773712, 2000139488427, 892417126, 114495660759545259572350261489332643266426720258549336314237020846386464754671, 114432576217694987429088217605206789839096467512528467748779856149444196669929, 10681859, 2000139488427, 2000152818186, 898714507, 114432576217694987429088217605206789839096467512528467748779856149444196669929, 114369491673959803739826918198446576334742282458619939295443180369841629920666, 11457448, 2000152818186, 2000166764007, 901668992, 114369491673959803739826918198446576334742282458619939295443180369841629920666, 114306407129951324699520023163019114049599884159940591724980692267317790406932, 12251580, 2000166764007, 2000175209840, 527733233, 114306407129951324699520023163019114049599884159940591724980692267317790406932, 114269496170919912096362432789765082673109058089510072180028136263009233331916, 12888170, 2000175209840, 2000181326910, 376930302, 114269496170919912096362432789765082673109058089510072180028136263009233331916, 114243322588071394194334273050030645509483403339746143923554383156073856132722, 13297780, 2000181326910, 2000196507918, 905554434, 114243322588071394194334273050030645509483403339746143923554383156073856132722, 114180238047306042588380508880014319376730932806046535317098626535067990452822, 13894066, 2000196507918, 2000198883427, 137848832, 114180238047306042588380508880014319376730932806046535317098626535067990452822, 114170593276054393708912947917757119219440141528309136496309818764588905879557, 14372358, 2000198883427, 2000212308057, 767430198, 114170593276054393708912947917757119219440141528309136496309818764588905879557, 114117153503905284129760909359023496880305567225401433812070000197928650839449, 14804926, 2000212308057, 2000228728354, 903974481, 114117153503905284129760909359023496880305567225401433812070000197928650839449, 114054068959455985425806640867036140032436750832262446947628546512865116326653, 15606723, 2000228728354, 2000245769838, 901563798, 114054068959455985425806640867036140032436750832262446947628546512865116326653, 113990984416315372534206872639513216542039263963325686416185979072682972069722, 16488642, 2000245769838, 2000263433541, 898941790, 113990984416315372534206872639513216542039263963325686416185979072682972069722, 113927899873989236559503926521297888226342962644653211709212254658375422194405, 17387268, 2000263433541, 2000281720497, 895910018, 113927899873989236559503926521297888226342962644653211709212254658375422194405, 113864815333022044965565770482455930871367499467403259520700841373703452848951, 18302356, 2000281720497, 2000300631744, 891626906, 113864815333022044965565770482455930871367499467403259520700841373703452848951, 113801730788286019251920830303795915057941382717919923450743405255545066490343, 19233674, 2000300631744, 2000312873558, 559274241, 113801730788286019251920830303795915057941382717919923450743405255545066490343, 113761965918400596954418294936052550722037464888177521869361525937236534166249, 20000103, 2000312873558, 2000320168319, 329016603, 113761965918400596954418294936052550722037464888177521869361525937236534166249, 113738646245785921307931320474290811401253572921585156632353747340058161626256, 20476299, 2000320168319, 2000340331263, 885310252, 113738646245785921307931320474290811401253572921585156632353747340058161626256, 113675561705573046378089664539418657692058753820501905361992741618029516562448, 21144129, 2000340331263, 2000361121621, 880001087, 113675561705573046378089664539418657692058753820501905361992741618029516562448, 113612477162647081381075922175107496585691787212661347009620181180202432303915, 22122859, 2000361121621, 2000382540438, 875850384, 113612477162647081381075922175107496585691787212661347009620181180202432303915, 113549392619316329669093009085194593108514295299018529638840237130752828077682, 23117002, 2000382540438, 2000404588762, 870355228, 113549392619316329669093009085194593108514295299018529638840237130752828077682, 113486308075726087474337563281120920512024001255384327574661536392612317490554, 24126377, 2000404588762, 2000414257402, 371970019, 113486308075726087474337563281120920512024001255384327574661536392612317490554, 113459198284848303314083651389717967999393766355328884534849366144178958560689, 24851336, 2000414257402, 2000427267643, 494687752, 113459198284848303314083651389717967999393766355328884534849366144178958560689, 113423223532915609762725323495929903215422411225970141808506848122479497794894, 25368066, 2000427267643, 2000450578133, 862571852, 113423223532915609762725323495929903215422411225970141808506848122479497794894, 113360138992715777889129711317774863419958659056791534073743502069852989759773, 26190146, 2000450578133, 2000474521289, 856525286, 113360138992715777889129711317774863419958659056791534073743502069852989759773, 113297054449861157443630930465772816859626899590367292492290779122962935726482, 27244219, 2000474521289, 2000491055474, 575368420, 113297054449861157443630930465772816859626899590367292492290779122962935726482, 113254435668470541458596901977881205511720873398075302694990273524330975537136, 28134784, 2000491055474, 2000499098168, 276777691, 113254435668470541458596901977881205511720873398075302694990273524330975537136, 113233969905580354480649385618445929481678508260660600768758926737720527299665, 28670971, 2000499098168, 2000524309828, 848304443, 113233969905580354480649385618445929481678508260660600768758926737720527299665, 113170885364335301661533543091946445274027220059318818946582768708663946773613, 29395990, 2000524309828, 2000550157333, 842687457, 113170885364335301661533543091946445274027220059318818946582768708663946773613, 113107800821388646718221743587517863013490057185593953163119432030403549426361, 30493406, 2000550157333, 2000576641747, 838037855, 113107800821388646718221743587517863013490057185593953163119432030403549426361, 113044716278033112818513361389318541320125783456597323538098705269599218459346, 31604997, 2000576641747, 2000603764136, 833272014, 113044716278033112818513361389318541320125783456597323538098705269599218459346, 112981631736309313442877537036646398268467753572159084890491611485586899883897, 32730636, 2000603764136, 2000631525571, 828543829, 112981631736309313442877537036646398268467753572159084890491611485586899883897, 112918547192195524478007023863643164755326782692192481621891611178299109648154, 33870200, 2000631525571, 2000659927121, 823909883, 112918547192195524478007023863643164755326782692192481621891611178299109648154, 112855462651672376385790594390495727936584729854258629880774029067459014371025, 35023572, 2000659927121, 2000688969863, 818854854, 112855462651672376385790594390495727936584729854258629880774029067459014371025, 112792378108161851077926452489299404993315490137099606715074090636781565936184, 36190638, 2000688969863, 2000710302767, 586850410, 112792378108161851077926452489299404993315490137099606715074090636781565936184, 112746905417847545120316069951020610505157382782941423644142749830340099726817, 37202593, 2000710302767, 2000718654872, 227544099, 112746905417847545120316069951020610505157382782941423644142749830340099726817, 112729293564908034992391187651470451538906664138081046607525591080690665836413, 37794235, 2000718654872, 2000748983226, 810636843, 112729293564908034992391187651470451538906664138081046607525591080690665836413, 112666209023670615234085762910623174458123534006486578305881639844107282285937, 38565421, 2000748983226, 2000779956008, 805432151, 112666209023670615234085762910623174458123534006486578305881639844107282285937, 112603124480858774545665788248539244571021783492859531153721513424905185025683, 39772931, 2000779956008, 2000811574301, 801122699, 112603124480858774545665788248539244571021783492859531153721513424905185025683, 112540039937960118806773704451393914699846178847183240658603263963967869990855, 40993722, 2000811574301, 2000843839191, 796246956, 112540039937960118806773704451393914699846178847183240658603263963967869990855, 112476955395243434821963932988309302497212538650197475495638644731480473594739, 42227698, 2000843839191, 2000865292450, 517925989, 112476955395243434821963932988309302497212538650197475495638644731480473594739, 112435694697162144818640978889126107792849853485636705575729632904400340058916, 43254605, 2000865292450, 2000876751767, 274207290, 112435694697162144818640978889126107792849853485636705575729632904400340058916, 112413870851890007523841967552160477988211825924010460705239036541501824339967, 43880024, 2000876751767, 2000910313119, 788558144, 112413870851890007523841967552160477988211825924010460705239036541501824339967, 112350786309833797421950668290638124193000411416798123046688794453718671079997, 44734844, 2000910313119, 2000944524341, 783394675, 112350786309833797421950668290638124193000411416798123046688794453718671079997, 112287701768035231377499992159953758613623397461973703474523853866892130698072, 46007841, 2000944524341, 2000971172512, 596921979, 112287701768035231377499992159953758613623397461973703474523853866892130698072, 112239375167044973082687456083900777193093398278003360686049163365085971273497, 47140127, 2000971172512, 2000979386530, 182420482, 112239375167044973082687456083900777193093398278003360686049163365085971273497, 112224617224561016455673616868842247233286696881558358634451002719793387854707, 47783908, 2000979386530, 2001014900783, 775854251, 112224617224561016455673616868842247233286696881558358634451002719793387854707, 112161532681958414037603093847885986645926248269989316729801757496472712015944, 48592267, 2001014900783, 2001051068201, 771229429, 112161532681958414037603093847885986645926248269989316729801757496472712015944, 112098448139952078187668360661545978681007265025721609718054529256280587234856, 49903539, 2001051068201, 2001087889888, 767275400, 112098448139952078187668360661545978681007265025721609718054529256280587234856, 112035363597402028440581868674011009104693099399195996486810854477967773724084, 51227416, 2001087889888, 2001125366950, 763288137, 112035363597402028440581868674011009104693099399195996486810854477967773724084, 111972279054059070443935845783287046029388178958261763754148789999675637415359, 52563825, 2001125366950, 2001163500494, 759364907, 111972279054059070443935845783287046029388178958261763754148789999675637415359, 111909194512140705805756091364476356109597521313115929756269449622220485479121, 53912695, 2001163500494, 2001202291632, 755525439, 111909194512140705805756091364476356109597521313115929756269449622220485479121, 111846109969684735852464486225814207645341127423672225635081560923995759438401, 55273958, 2001202291632, 2001241741478, 751521619, 111846109969684735852464486225814207645341127423672225635081560923995759438401, 111783025425663738310640806594200220012202052381253136190065124802870096181389, 56647548, 2001241741478, 2001274231906, 606595624, 111783025425663738310640806594200220012202052381253136190065124802870096181389, 111731844916036636712362275417455485049816325674669628506398799310327144410751, 57900174, 2001274231906, 2001281851146, 141172308, 111731844916036636712362275417455485049816325674669628506398799310327144410751, 111719940883040240180574629661151157642577345086747940659552737494936561390159, 58593571, 2001281851146, 2001322621755, 744592522, 111719940883040240180574629661151157642577345086747940659552737494936561390159, 111656856340782575627956112665453915150752371705285881589603161902975844442715, 59431452, 2001322621755, 2001364054426, 740528102, 111656856340782575627956112665453915150752371705285881589603161902975844442715, 111593771798723207363118349935374074456822704931302609616586717915727692990854, 60841642, 2001364054426, 2001406150283, 736987828, 111593771798723207363118349935374074456822704931302609616586717915727692990854, 111530687256015173259319646679929221430294844604079361792997687784858576082022, 62263911, 2001406150283, 2001448910452, 733429872, 111530687256015173259319646679929221430294844604079361792997687784858576082022, 111467602712658976029447050430727628127108286487790474505062277468344078575374, 63698203, 2001448910452, 2001492336060, 729929752, 111467602712658976029447050430727628127108286487790474505062277468344078575374, 111404518170890336293823363593429540467545921493368289616284526392948547464412, 65144461, 2001492336060, 2001536428240, 726497324, 111404518170890336293823363593429540467545921493368289616284526392948547464412, 111341433627922639899204538026701726192356378764611174457872120777870532699436, 66602632, 2001536428240, 2001581188124, 722975838, 111341433627922639899204538026701726192356378764611174457872120777870532699436, 111278349086121330356193619440564861087620976719920274079963383118465322646411, 68072662, 2001581188124, 2001620058499, 616308442, 111278349086121330356193619440564861087620976719920274079963383118465322646411, 111224314664476077953530691978762877648340561402833138840144777447402436588811, 69446364, 2001620058499, 2001626616850, 103291982, 111224314664476077953530691978762877648340561402833138840144777447402436588811, 111215264542988390397579414011794402802366117490443179592920562218463526677403, 70187402, 2001626616850, 2001672715556, 716686504, 111215264542988390397579414011794402802366117490443179592920562218463526677403, 111152179999674339872743526310405559956088552212013931891488748728527523738925, 71048096, 2001672715556, 2001719485382, 713118577, 111152179999674339872743526310405559956088552212013931891488748728527523738925, 111089095458050101418007938592134660953112029370127642338992125812725060566198, 72553403, 2001719485382, 2001766927474, 710063893, 111089095458050101418007938592134660953112029370127642338992125812725060566198, 111026010915384298643085814857348387926895036210243682973037409775786689720458, 74070371, 2001766927474, 2001814869793, 703666631, 111026010915384298643085814857348387926895036210243682973037409775786689720458, 110963151862345428815978365573306388448810506198702852209039296025815752701910, 75596176, 2001814869793, 2001815042978, 3514479, 110963151862345428815978365573306388448810506198702852209039296025815752701910, 110962926372484418020183554377212420732609873106198994710971622456158483505817, 76359512, 2001815042978, 2001863833043, 703092410, 110962926372484418020183554377212420732609873106198994710971622456158483505817, 110899841829611508171014561460802410145239953216243319490380334926252601822799, 77139113, 2001863833043, 2001913298820, 700693546, 110899841829611508171014561460802410145239953216243319490380334926252601822799, 110836757287793153874328581565194344979078007821684726017360161366356763251149, 78690798, 2001913298820, 2001963441465, 697477663, 110836757287793153874328581565194344979078007821684726017360161366356763251149, 110773672745032320206794028083502507322165359942976913556897925976919329350359, 80253969, 2001963441465, 2002009240430, 626186385, 110773672745032320206794028083502507322165359942976913556897925976919329350359, 110716784413456498685168971258198458757635654221282663253859301944406972175951, 81750009, 2002009240430, 2002014262135, 68286827, 110716784413456498685168971258198458757635654221282663253859301944406972175951, 110710588201449262017652004068122926680331378788633490456648460139132619262672, 82537115, 2002014262135, 2002065761988, 691747340, 110710588201449262017652004068122926680331378788633490456648460139132619262672, 110647503659152280761249537408427270304476817692927459591974397299213335362530, 83414603, 2002065761988, 2002117942187, 688662250, 110647503659152280761249537408427270304476817692927459591974397299213335362530, 110584419117313322880706572908817566078491848053170232100930005673954670091691, 85011987, 2002117942187, 2002170803898, 685812265, 110584419117313322880706572908817566078491848053170232100930005673954670091691, 110521334574736174988661704948277926618676560247836863946876774992027264790131, 86620698, 2002170803898, 2002224348289, 682972527, 110521334574736174988661704948277926618676560247836863946876774992027264790131, 110458250031059556820337365981297231323763112630118197694904681220921087730490, 88240698, 2002224348289, 2002278576528, 680174879, 110458250031059556820337365981297231323763112630118197694904681220921087730490, 110395165489025844900298425602397829590348388941858138560469895804070521129268, 89871950, 2002278576528, 2002333489790, 677416505, 110395165489025844900298425602397829590348388941858138560469895804070521129268, 110332080946305592584257567580667834459747139144429293092791985443300358535782, 91514421, 2002333489790, 2002389089250, 674678249, 110332080946305592584257567580667834459747139144429293092791985443300358535782, 110268996403710519379177614769903421102035856609349789826157032463902724031035, 93168074, 2002389089250, 2002442376672, 636246951, 110268996403710519379177614769903421102035856609349789826157032463902724031035, 110209254163526918400467275577077500476415877354186299824615933069465136065437, 94788109, 2002442376672, 2002445376086, 35751060, 110209254163526918400467275577077500476415877354186299824615933069465136065437, 110205911861669877267145482971565458057328846748394112166633381082233272478812, 95620013, 2002445376086, 2002502351481, 669368336, 110205911861669877267145482971565458057328846748394112166633381082233272478812, 110142827318060626897294829286871667481962053325010212872720163689176091320662, 96508796, 2002502351481, 2002560016616, 666733258, 110142827318060626897294829286871667481962053325010212872720163689176091320662, 110079742775979912364700373305936539248802317256979081127662410724455050034816, 98195800, 2002560016616, 2002618372679, 664150987, 110079742775979912364700373305936539248802317256979081127662410724455050034816, 110016658233774427867307312693236696057963061413839901994158574602410524909296, 99893857, 2002618372679, 2002677420860, 661600532, 110016658233774427867307312693236696057963061413839901994158574602410524909296, 109953573690635716473354572254589489594298176356376834769921802058558620914140, 101602937, 2002677420860, 2002737162349, 659085117, 109953573690635716473354572254589489594298176356376834769921802058558620914140, 109890489148659641061185031285847408766200245143689552845237728078057454035379, 103323011, 2002737162349, 2002797598343, 656590056, 109890489148659641061185031285847408766200245143689552845237728078057454035379, 109827404605423641520530492076502748056373997657927540282127334714463021871439, 105054049, 2002797598343, 2002858730038, 654211272, 109827404605423641520530492076502748056373997657927540282127334714463021871439, 109764320062459068567026271207096310833427598491394817102980848045118651955333, 106796023, 2002858730038, 2002920077285, 646274548, 109764320062459068567026271207096310833427598491394817102980848045118651955333, 109701723912500484745642487148776035922656874971544454313159071720270423752953, 108542023, 2002920077285, 2002920558634, 5704814, 109701723912500484745642487148776035922656874971544454313159071720270423752953, 109701235519964946023978611259433354308846594737750218579159323162629441927527, 109417690, 2002920558634, 2002983085334, 648959561, 109701235519964946023978611259433354308846594737750218579159323162629441927527, 109638150977892969816287289962098476545515883035618239837206840069202391710730, 110312670, 2002983085334, 2003046311345, 647035806, 109638150977892969816287289962098476545515883035618239837206840069202391710730, 109575066434976705812917004005349629220004249785431115870054444087860896105668, 112087289, 2003046311345, 2003110237874, 644629237, 109575066434976705812917004005349629220004249785431115870054444087860896105668, 109511981892731646361056364358816392135827326746712986227853241465818119262931, 113872739, 2003110237874, 2003174866134, 642335901, 109511981892731646361056364358816392135827326746712986227853241465818119262931, 109448897349487853206411866489334419585164163197410083163486154573392203669785, 115668994, 2003174866134, 2003240197337, 640060079, 109448897349487853206411866489334419585164163197410083163486154573392203669785, 109385812807291062401607696415277634628814502164675995204924122397782650210202, 117476030, 2003240197337, 2003306232701, 637807529, 109385812807291062401607696415277634628814502164675995204924122397782650210202, 109322728265061728540855281802345780626136817533203825248526045825887363720295, 119293823, 2003306232701, 2003372973446, 635627886, 109322728265061728540855281802345780626136817533203825248526045825887363720295, 109259643722527661252484273634422919562062166861412091129869313992672371128074, 121122350, 2003372973446, 2003440420795, 633198014, 109259643722527661252484273634422919562062166861412091129869313992672371128074, 109196559179259230616800526488487433654564530581388608168927985244479700415449, 122961589, 2003440420795, 2003442963668, 23903617, 109196559179259230616800526488487433654564530581388608168927985244479700415449, 109194193661798552142430657403347965986327165728565957960339130279825959188343, 123915123, 2003442963668, 2003508575972, 607462387, 109194193661798552142430657403347965986327165728565957960339130279825959188343, 109133474636526686520015927278482924533097953418728199851839661333016542603210, 124845950, 2003508575972, 2003577440205, 629131862, 109133474636526686520015927278482924533097953418728199851839661333016542603210, 109070390094486423392914300030741617841316670539606781590645871731674991907012, 126672112, 2003577440205, 2003647014727, 626966830, 109070390094486423392914300030741617841316670539606781590645871731674991907012, 109007305551342664688410286706514983728415331636509788619543125364061982699844, 128543355, 2003647014727, 2003717300770, 624913652, 109007305551342664688410286706514983728415331636509788619543125364061982699844, 108944221008811273406116688499520385966115354421279119941535635609269682393275, 130425225, 2003717300770, 2003788299571, 622627922, 108944221008811273406116688499520385966115354421279119941535635609269682393275, 108881136466647306845877195312445149398571267652409721248890036448066987550586, 132317702, 2003788299571, 2003829787234, 359817159, 108881136466647306845877195312445149398571267652409721248890036448066987550586, 108844563883114627328357206513227585724017038293519532489473481965805601242920, 133816866, 2003829787234, 2003860012371, 260927166, 108844563883114627328357206513227585724017038293519532489473481965805601242920, 108818051923624510373460217344716312319055513641780788086892543283390204756685, 134770505, 2003860012371, 2003932440411, 619013768, 108818051923624510373460217344716312319055513641780788086892543283390204756685, 108754967381057671707746159158884064742300332509471085016572734057781649954667, 136134398, 2003932440411, 2004005584937, 616554174, 108754967381057671707746159158884064742300332509471085016572734057781649954667, 108691882838394758650776093429331581864549198110156847176667519859484818301684, 138058581, 2004005584937, 2004011668828, 50995461, 108691882838394758650776093429331581864549198110156847176667519859484818301684, 108686663411482188769017755162135810745859024175680135377220981172854922206572, 139100020, 2004011668828, 2004079447197, 563918387, 108686663411482188769017755162135810745859024175680135377220981172854922206572, 108628798295864005512455752305364826318556968587389225647566419761594491467742, 140072817, 2004079447197, 2004154028442, 612892258, 108628798295864005512455752305364826318556968587389225647566419761594491467742, 108565713753601830738931864560991780480497127324020759493326576493681452702472, 141938525, 2004154028442, 2004229329927, 610913386, 108565713753601830738931864560991780480497127324020759493326576493681452702472, 108502629210830437610507103193680153488545984800959693934816482264560567731209, 143894252, 2004229329927, 2004305352908, 609014318, 108502629210830437610507103193680153488545984800959693934816482264560567731209, 108439544668385651936123106215111483275576339246838398118438040041282562351292, 145860460, 2004305352908, 2004382098646, 607129925, 108439544668385651936123106215111483275576339246838398118438040041282562351292, 108376460125375757851812557046925201340237773734115804533999742630940413607367, 147837133, 2004382098646, 2004459568402, 605262078, 108376460125375757851812557046925201340237773734115804533999742630940413607367, 108313375583321290972800215948363041280557923445252865363139074380489421386482, 149824255, 2004459568402, 2004537763444, 603455379, 108313375583321290972800215948363041280557923445252865363139074380489421386482, 108250291040429385491135448813565288402706660616304194084571276657990084205183, 151821810, 2004537763444, 2004616685039, 601415716, 108250291040429385491135448813565288402706660616304194084571276657990084205183, 108187206498117629843365377203810135877094960489053517174118619012673151865239, 153829784, 2004616685039, 2004626837653, 76843736, 108187206498117629843365377203810135877094960489053517174118619012673151865239, 108179133160158920690860847044507911922456635364206870025895361149508458149584, 154962335, 2004626837653, 2004696334460, 523061490, 108179133160158920690860847044507911922456635364206870025895361149508458149584, 108124121955356050489816494324377739304354378662470388994455254976112305334687, 155976571, 2004696334460, 2004776712981, 598076610, 108124121955356050489816494324377739304354378662470388994455254976112305334687, 108061037412690721203365091446517640619511748369353528111587926877087100253091, 157876931, 2004776712981, 2004857821880, 596249021, 108061037412690721203365091446517640619511748369353528111587926877087100253091, 107997952869857079119829152962898405959557987379414915115361147595448879005027, 159916076, 2004857821880, 2004939662437, 594513071, 107997952869857079119829152962898405959557987379414915115361147595448879005027, 107934868327357401118851186600682191248264439234753377343929035848298892320070, 161965583, 2004939662437, 2005022235936, 592787243, 107934868327357401118851186600682191248264439234753377343929035848298892320070, 107871783784912373766631492252147264612421718588914490383949470768945172156742, 164025440, 2005022235936, 2005105543664, 591075699, 107871783784912373766631492252147264612421718588914490383949470768945172156742, 107808699242255866378203853998844723633798486523047528030726380504226816276649, 166095634, 2005105543664, 2005189586910, 589422020, 107808699242255866378203853998844723633798486523047528030726380504226816276649, 107745614699888318084074567239508270766429426560235180350375370925031796634415, 168176152, 2005189586910, 2005274366968, 587533726, 107745614699888318084074567239508270766429426560235180350375370925031796634415, 107682530156827502135920802556923859152678072058544435245186007760429859928275, 170266984, 2005274366968, 2005289127186, 101573932, 107682530156827502135920802556923859152678072058544435245186007760429859928275, 107671602909904158351717534769826516213540715636056913003433164307203044657300, 171493904, 2005289127186, 2005359885132, 484589075, 107671602909904158351717534769826516213540715636056913003433164307203044657300, 107619445614351225155555244453560287906516522991279587739030124361700241635285, 172549150, 2005359885132, 2005446142702, 584501751, 107619445614351225155555244453560287906516522991279587739030124361700241635285, 107556361071538055135978781797658556515696073745533115532851246167809880885770, 174479538, 2005446142702, 2005533140979, 582805634, 107556361071538055135978781797658556515696073745533115532851246167809880885770, 107493276528977111932412686087609193646205344595997165767339130962636852503515, 176601239, 2005533140979, 2005620881268, 581212866, 107493276528977111932412686087609193646205344595997165767339130962636852503515, 107430191986563070495481688456031596528546201628061070364425812371479112210470, 178733207, 2005620881268, 2005709364877, 579626194, 107430191986563070495481688456031596528546201628061070364425812371479112210470, 107367107444241490370640475455025915733779230232888327146512735068743854364627, 180875434, 2005709364877, 2005798593118, 578052086, 107367107444241490370640475455025915733779230232888327146512735068743854364627, 107304022901309000966006964094165141204760018309979669744939121939495730349637, 183027907, 2005798593118, 2005888567304, 576532192, 107304022901309000966006964094165141204760018309979669744939121939495730349637, 107240938358541166712346483812387643203273655330093790969739413239193356225689, 185190619, 2005888567304, 2005979288752, 574782062, 107240938358541166712346483812387643203273655330093790969739413239193356225689, 107177853816060633774514990475443484676537401309461459214584733011280030100050, 187363559, 2005979288752, 2005999206922, 125309825, 107177853816060633774514990475443484676537401309461459214584733011280030100050, 107164072658867370465528345084506765795905853002316149220344942758837848730026, 188688159, 2005999206922, 2006070758783, 448216729, 107164072658867370465528345084506765795905853002316149220344942758837848730026, 107114769273369907962247553695314138014721293808686334407761199419277127866911, 189784074, 2006070758783, 2006162978720, 572016099, 107114769273369907962247553695314138014721293808686334407761199419277127866911, 107051684730745285847054381892866125165153549618625696774427114161790868651861, 191740089, 2006162978720, 2006255949889, 570436068, 107051684730745285847054381892866125165153549618625696774427114161790868651861, 106988600188536157056255433435145169608525493744369800364861806799214469607441, 193943661, 2006255949889, 2006349673621, 568969638, 106988600188536157056255433435145169608525493744369800364861806799214469607441, 106925515645827421217609971290396742304248867547982588428385895797817198387453, 196157426, 2006349673621, 2006444151248, 567505821, 106925515645827421217609971290396742304248867547982588428385895797817198387453, 106862431103156129708073858915490352752420750668549539748072153984543305619217, 198381377, 2006444151248, 2006539384106, 566053232, 106862431103156129708073858915490352752420750668549539748072153984543305619217, 106799346560480913958155269670926393640125633146597403556913283053051769753163, 200615506, 2006539384106, 2006635373534, 564650961, 106799346560480913958155269670926393640125633146597403556913283053051769753163, 106736262017865348403054775141762498511389703497634538465581077526777446076077, 202859805, 2006635373534, 2006732120874, 563027578, 106736262017865348403054775141762498511389703497634538465581077526777446076077, 106673177475479923714344491383230806536428100261171528967269185392003635840690, 205114267, 2006732120874, 2006757759095, 148164818, 106673177475479923714344491383230806536428100261171528967269185392003635840690, 106656542408408974468973223205686075474953028250585145984816049445215638655039, 206539908, 2006757759095, 2006829627473, 413702454, 106656542408408974468973223205686075474953028250585145984816049445215638655039, 106610092932314997733412020435324209959298350058635177349958492620185813878534, 207676225, 2006829627473, 2006927894677, 560492619, 106610092932314997733412020435324209959298350058635177349958492620185813878534, 106547008390069272829265973487024933454333751013319955582337967871214246688475, 209653654, 2006927894677, 2007026923840, 559016154, 106547008390069272829265973487024933454333751013319955582337967871214246688475, 106483923847340765283286255168738329353794510958546381280217106193037986412082, 211938565, 2007026923840, 2007126716316, 557661753, 106483923847340765283286255168738329353794510958546381280217106193037986412082, 106420839304788747040386507134133338897246983291967546007498417220445674055429, 214233613, 2007126716316, 2007227273464, 556306990, 106420839304788747040386507134133338897246983291967546007498417220445674055429, 106357754761936875071814184999709158919991313227567139013145352281282119608061, 216538792, 2007227273464, 2007328596644, 554962447, 106357754761936875071814184999709158919991313227567139013145352281282119608061, 106294670219702863522319817398435626221347443236202940435412806703112310390546, 218854097, 2007328596644, 2007430687222, 553664213, 106294670219702863522319817398435626221347443236202940435412806703112310390546, 106231585677274142892469500020463882903037352853125834490620262111481238548770, 221179521, 2007430687222, 2007533546566, 552157310, 106231585677274142892469500020463882903037352853125834490620262111481238548770, 106168501134622176683333491738573092547921281318228252631268372285793524247162, 223515060, 2007533546566, 2007565478990, 170236793, 106168501134622176683333491738573092547921281318228252631268372285793524247162, 106149012157678007603540132309545486090063418208828408951615116460554189815166, 225045156, 2007565478990, 2007637176047, 380839641, 106149012157678007603540132309545486090063418208828408951615116460554189815166, 106105416591872870680516749339370248127546596833066628947902345445688968298165, 226221678, 2007637176047, 2007741577039, 549823965, 106105416591872870680516749339370248127546596833066628947902345445688968298165, 106042332049306711797636087259192637562995428259487107710588302498868837530209, 228216461, 2007741577039, 2007846750920, 548440774, 106042332049306711797636087259192637562995428259487107710588302498868837530209, 105979247506761277790758026261942688410046891558850348496718933099007498177574, 230582315, 2007846750920, 2007952699071, 547186261, 105979247506761277790758026261942688410046891558850348496718933099007498177574, 105916162964246380126726870963751682512651346054008307459141862781407845795396, 232958264, 2007952699071, 2008059422877, 545928935, 105916162964246380126726870963751682512651346054008307459141862781407845795396, 105853078421354645539620477149991739484391819098003899811267440679100413613057, 235344306, 2008059422877, 2008166923725, 544681056, 105853078421354645539620477149991739484391819098003899811267440679100413613057, 105789993878451716004433473035924885258268908066323772411828067415724353058978, 237740435, 2008166923725, 2008275203005, 543475526, 105789993878451716004433473035924885258268908066323772411828067415724353058978, 105726909336073787641532037757483641836522532205442458070818424671149550258312, 240146649, 2008275203005, 2008384262112, 542075966, 105726909336073787641532037757483641836522532205442458070818424671149550258312, 105663824793774420147215949766573471817113300047439310235306102741962968159108, 242562943, 2008384262112, 2008423075252, 191610501, 105663824793774420147215949766573471817113300047439310235306102741962968159108, 105641481906776275604493216510132466517291392356932567371277597034182613049188, 244200966, 2008423075252, 2008494102445, 349451857, 105641481906776275604493216510132466517291392356932567371277597034182613049188, 105600740250737290300221204727345485166237830483059258009388127483585159127902, 245417553, 2008494102445, 2008604725403, 539919948, 105600740250737290300221204727345485166237830483059258009388127483585159127902, 105537655708067971098733755860895769928020081527470129488673545805108245710893, 247425762, 2008604725403, 2008716132390, 538621785, 105537655708067971098733755860895769928020081527470129488673545805108245710893, 105474571165910897450759277215755393373087556107967587810214259878832169165515, 249872281, 2008716132390, 2008828324816, 537457179, 105474571165910897450759277215755393373087556107967587810214259878832169165515, 105411486622928078674104968048639586916539628164357741380448139439262200468149, 252328868, 2008828324816, 2008941304090, 536287873, 105411486622928078674104968048639586916539628164357741380448139439262200468149, 105348402080251198882801038512946379074353973386448069558515113226431923678059, 254795523, 2008941304090, 2009055071626, 535127558, 105348402080251198882801038512946379074353973386448069558515113226431923678059, 105285317538086501826858366833547771893932111365043859371074740539292204783129, 257272241, 2009055071626, 2009169628844, 534005919, 105285317538086501826858366833547771893932111365043859371074740539292204783129, 105222232995203242651957406126797066991840815729682111064995467975204137601092, 259759022, 2009169628844, 2009284977163, 532706465, 105222232995203242651957406126797066991840815729682111064995467975204137601092, 105159148452803594521662015863311776976709511216641727275305913518129556077797, 262255863, 2009284977163, 2009331270210, 212361569, 105159148452803594521662015863311776976709511216641727275305913518129556077797, 105133951655693115071659805547209131246348300121487697431811001197546604365733, 264005340, 2009331270210, 2009401118009, 319390304, 105133951655693115071659805547209131246348300121487697431811001197546604365733, 105096063910114936599461506154470094028826432206946828169586489227620158526397, 265261905, 2009401118009, 2009518052809, 530710106, 105096063910114936599461506154470094028826432206946828169586489227620158526397, 105032979367688035687989083421890409293000024423628386074064258218397144453212, 267279721, 2009518052809, 2009635782996, 529492295, 105032979367688035687989083421890409293000024423628386074064258218397144453212, 104969894824687869148281453686385976400457283100655428638550704641892529300896, 269806734, 2009635782996, 2009754310003, 528411882, 104969894824687869148281453686385976400457283100655428638550704641892529300896, 104906810282128215473146484553365478495599882763286167402187326289564084589346, 272343802, 2009754310003, 2009873635269, 527326343, 104906810282128215473146484553365478495599882763286167402187326289564084589346, 104843725739654047806003907551841027469221128507102736076109729668540850565143, 274890925, 2009873635269, 2009993760236, 526250983, 104843725739654047806003907551841027469221128507102736076109729668540850565143, 104780641197162546003647944764163276277828045588313517128340170408895395242093, 277448100, 2009993760236, 2010114686350, 525212834, 104780641197162546003647944764163276277828045588313517128340170408895395242093, 104717556654280275559265245249797627926030833413034144969142740968833356685338, 280015327, 2010114686350, 2010236415058, 524017605, 104717556654280275559265245249797627926030833413034144969142740968833356685338, 104654472111927110353513281017615333885397799616451555064507573030851322643055, 282592607, 2010236415058, 2010290800207, 232576909, 104654472111927110353513281017615333885397799616451555064507573030851322643055, 104626421405309192076133491695287957160221810718003314933143354516652722103838, 284457125, 2010290800207, 2010358947814, 290553023, 104626421405309192076133491695287957160221810718003314933143354516652722103838, 104591387569200422392477199040224726152582162546220468190751058895910187488310, 285753631, 2010358947814, 2010482286073, 522201950, 104591387569200422392477199040224726152582162546220468190751058895910187488310, 104528303026498577536996865935668209417908801699206325016441910913550608833459, 287777322, 2010482286073, 2010606431294, 521094917, 104528303026498577536996865935668209417908801699206325016441910913550608833459, 104465218483964709474505771410097112415691930139334486544338245482625450441303, 290384757, 2010606431294, 2010731384940, 520153905, 104465218483964709474505771410097112415691930139334486544338245482625450441303, 104402133941500256929531532339823470879237059779306284801867668722721864946773, 293002244, 2010731384940, 2010857148478, 519217107, 104402133941500256929531532339823470879237059779306284801867668722721864946773, 104339049398778042616673924919004025561208091977358328694469187076413377334023, 295629784, 2010857148478, 2010983723377, 518591875, 104339049398778042616673924919004025561208091977358328694469187076413377334023, 104275964856248516946891009344722839191048470755904060932928872526658363402185, 298267377, 2010983723377, 2011111111111, 516662086, 104275964856248516946891009344722839191048470755904060932928872526658363402185, 104212880313639424765589609273198082398330793722669431932394052100552687231877, 300915024, 2011111111111, 2011302415947, 780851080, 104212880313639424765589609273198082398330793722669431932394052100552687231877, 104118891154530808707845150921528718409420204372159439619436090796727638218026, 304230345, 2011302415947, 2012366882840, 4117912781, 104118891154530808707845150921528718409420204372159439619436090796727638218026, 103611360903853762728092702148783436845102178938782162020106983234228760632441, 317311053, 2012366882840, 2013484981369, 4049740535, 103611360903853762728092702148783436845102178938782162020106983234228760632441, 103103830652791224644633553023834170906713584062759008474462178132339238027498, 339463445, 2013484981369, 2014657507458, 3994784597, 103103830652791224644633553023834170906713584062759008474462178132339238027498, 102596300402112765622285726707524040036725167004651090215623084099156950752751, 362268794, 2014657507458, 2015885272861, 3941832454, 102596300402112765622285726707524040036725167004651090215623084099156950752751, 102088770151503761445189644652752889974572520769070123090989134380643029943111, 385728957, 2015885272861, 2017169105555, 3892112667, 102088770151503761445189644652752889974572520769070123090989134380643029943111, 101581239900721590405546837052849105222252504840794734506386903407128883362322, 409846335, 2017169105555, 2018509850146, 3845134262, 101581239900721590405546837052849105222252504840794734506386903407128883362322, 101073709650068361127701277556869072799946661525850806955573923875251283560304, 434623851, 2018509850146, 2019908368292, 3800708364, 101073709650068361127701277556869072799946661525850806955573923875251283560304, 100566179399088534223053194477135827892333465136428994371033198113648309338424, 460064918, 2019908368292, 2021365539130, 3758633064, 100566179399088534223053194477135827892333465136428994371033198113648309338424, 100058649148566538879611000728350549624379482181888662350147802572474030632539, 486173416, 2021365539130, 2022882259729, 3718733437, 100058649148566538879611000728350549624379482181888662350147802572474030632539, 99551118897875063987180147255080340910191822413768147998542169761228225989745, 512953677, 2022882259729, 2024459445544, 3680851655, 99551118897875063987180147255080340910191822413768147998542169761228225989745, 99043588646925407760701466927026862341657864488577286626427084174548939687980, 540410466, 2024459445544, 2026098030889, 3644845527, 99043588646925407760701466927026862341657864488577286626427084174548939687980, 98536058396235534432442241222262106883483229817304345789243163847819692734183, 568548967, 2026098030889, 2027798969430, 3610586415, 98536058396235534432442241222262106883483229817304345789243163847819692734183, 98028528145429276058146287785331057745311752883958497321109133082816898855157, 597374775, 2027798969430, 2029563234684, 3577957588, 98028528145429276058146287785331057745311752883958497321109133082816898855157, 97520997894662973701130794483762686731340646242838606427083979827943205109711, 626893882, 2029563234684, 2031391820540, 3546852843, 97520997894662973701130794483762686731340646242838606427083979827943205109711, 97013467644071505402788443522497521670149067613428124723835485286064788229079, 657112676, 2031391820540, 2033285741796, 3517175323, 97013467644071505402788443522497521670149067613428124723835485286064788229079, 96505937393425455661077254725504330263843191173394169712605211111136731239891, 688037928, 2033285741796, 2035246034710, 3488836469, 96505937393425455661077254725504330263843191173394169712605211111136731239891, 95998407142619212956893733771015647766137821007029345743187049239879536436992, 719676793, 2035246034710, 2037273757570, 3461755130, 95998407142619212956893733771015647766137821007029345743187049239879536436992, 95490876891726824244903755093386203895286925392023569878036369481421559949959, 752036805, 2037273757570, 2039369991282, 3435856810, 95490876891726824244903755093386203895286925392023569878036369481421559949959, 94983346641113745604145456371289984142327856666340779176299217153384889058530, 785125874, 2039369991282, 2041535839982, 3411072948, 94983346641113745604145456371289984142327856666340779176299217153384889058530, 94475816390366393200967057792503167747829321374857035583159767688415615053963, 818952287, 2041535839982, 2043772431658, 3387340348, 94475816390366393200967057792503167747829321374857035583159767688415615053963, 93968286139585080689009749778641701506612547526069326507789442116865847415587, 853524706, 2043772431658, 2046080918800, 3364600649, 93968286139585080689009749778641701506612547526069326507789442116865847415587, 93460755888805977092172438706356244232014522063148453870942162054893527682350, 888852171, 2046080918800, 2048462479068, 3342799845, 93460755888805977092172438706356244232014522063148453870942162054893527682350, 92953225638200409885237165124541227117947904313540833894911857835741864284819, 924944102, 2048462479068, 2050918315986, 3321887894, 92953225638200409885237165124541227117947904313540833894911857835741864284819, 92445695387431396822335894859752718051334279270756745660129614625935517377384, 961810298, 2050918315986, 2053449659651, 3301818338, 92445695387431396822335894859752718051334279270756745660129614625935517377384, 91938165136681090074740507924876796171272099369944824164386910113277139703565, 999460945, 2053449659651, 2056057767474, 3282547983, 91938165136681090074740507924876796171272099369944824164386910113277139703565, 91430634885924403849286278329927326232632208161183049023316418510689747062704, 1037906619, 2056057767474, 2058743924941, 3264036608, 91430634885924403849286278329927326232632208161183049023316418510689747062704, 90923104635200678031902281270359152929564091489081568521561088103225324948425, 1077158288, 2058743924941, 2061509446402, 3246246709, 90923104635200678031902281270359152929564091489081568521561088103225324948425, 90415574384419560197501607323869329390334252370301222617894122955597460874089, 1117227322, 2061509446402, 2064355675884, 3229143255, 90415574384419560197501607323869329390334252370301222617894122955597460874089, 89908044133671944253509892878211741116661383937902848484688632137309141050524, 1158125497, 2064355675884, 2067283987935, 3212693495, 89908044133671944253509892878211741116661383937902848484688632137309141050524, 89400513882934284366689109909568175654668502389957636941466358121391175100673, 1199865001, 2067283987935, 2070295788495, 3196866761, 89400513882934284366689109909568175654668502389957636941466358121391175100673, 88892983632129408362262930575038545488072500074298227583135359429238492302156, 1242458443, 2070295788495, 2073392515795, 3181634293, 88892983632129408362262930575038545488072500074298227583135359429238492302156, 88385453381504421115759885270926112305233582972723629360138013968946504068012, 1285918862, 2073392515795, 2076575641295, 3166969108, 88385453381504421115759885270926112305233582972723629360138013968946504068012, 87877923130725949793492609161161775927010502585804951807351251138148403723074, 1330259733, 2076575641295, 2079846670642, 3152845823, 87877923130725949793492609161161775927010502585804951807351251138148403723074, 87370392880032121197562914655469190519134532463673375906511043486291432975749, 1375494981, 2079846670642, 2083207144675, 3139240576, 87370392880032121197562914655469190519134532463673375906511043486291432975749, 86862862629242910928564417792020477427189268700670745238688738068381431547907, 1421638985, 2083207144675, 2086658640454, 3126130869, 86862862629242910928564417792020477427189268700670745238688738068381431547907, 86355332378551129212811178029802759264921278615693966302625767660853123323451, 1468706596, 2086658640454, 2090202772336, 3113495502, 86355332378551129212811178029802759264921278615693966302625767660853123323451, 85847802127734235318643474849013892506231683552224736549945631964368442560878, 1516713142, 2090202772336, 2093841193078, 3101314448, 85847802127734235318643474849013892506231683552224736549945631964368442560878, 85340271877028856414749960859298715151240418211100827130240053076889694927562, 1565674445, 2093841193078, 2097575594992, 3089568777, 85340271877028856414749960859298715151240418211100827130240053076889694927562, 84832741626238044013391554233202256760478256670839868550382853389696421488374, 1615606830, 2097575594992, 2101407711130, 3078240586, 84832741626238044013391554233202256760478256670839868550382853389696421488374, 84325211375473236954190419771655346933992878167491098548922721258740314192802, 1666527142, 2101407711130, 2105339316520, 3067312919, 84325211375473236954190419771655346933992878167491098548922721258740314192802, 83817681124798235278309276349432133314231003860648267928975478617636269000334, 1718452757, 2105339316520, 2109372229446, 3056769700, 83817681124798235278309276349432133314231003860648267928975478617636269000334, 83310150874059741901293611466333499635278273315105116669934954550831501526713, 1771401599, 2109372229446, 2113508312770, 3046595673, 83310150874059741901293611466333499635278273315105116669934954550831501526713, 82802620623352035319069011493768483719161838505004309279921326266645114882028, 1825392157, 2113508312770, 2117749475310, 3036776349, 82802620623352035319069011493768483719161838505004309279921326266645114882028, 82295090372593085841455006031921663369314111091197220509274122064035269491590, 1880443497, 2117749475310, 2122097673263, 3027297955, 82295090372593085841455006031921663369314111091197220509274122064035269491590, 81787560121874219843446357722646076419728033521735462684678428582911934176625, 1936575284, 2122097673263, 2126554911687, 3018147381, 81787560121874219843446357722646076419728033521735462684678428582911934176625, 81280029871132166205698898387884157084570454360314711051071563542650889709643, 1993807798, 2126554911687, 2131123246034, 3009312141, 81280029871132166205698898387884157084570454360314711051071563542650889709643, 80772499620391100641856012111786720409532255852058285830691780813577831077775, 2052161953, 2131123246034, 2135804783745, 3000780337, 80772499620391100641856012111786720409532255852058285830691780813577831077775, 80264969369567783299199408271989672817056070226803164323253026102562171367207, 2111659318, 2135804783745, 2140601685900, 2992540608, 80264969369567783299199408271989672817056070226803164323253026102562171367207, 79757439118913802062694043332871333088869809027474702198296575883918860425344, 2172322136, 2140601685900, 2145516168944, 2984582109, 79757439118913802062694043332871333088869809027474702198296575883918860425344, 79249908868125800447406891028047013763204922549560487470729250161224329101193, 2234173347, 2145516168944, 2150550506461, 2976894478, 79249908868125800447406891028047013763204922549560487470729250161224329101193, 78742378617415800793501413804974780455721333987441382492380693619244943414131, 2297236613, 2150550506461, 2155707031036, 2969467793, 78742378617415800793501413804974780455721333987441382492380693619244943414131, 78234848366628638334709617669320110898971246670067294404898797682623676824173, 2361536336, 2155707031036, 2160988136175, 2962292562, 78234848366628638334709617669320110898971246670067294404898797682623676824173, 77727318115868800123724664057532510759255358272687201514628413931282023247855, 2427097690, 2160988136175, 2166396278310, 2955359686, 77727318115868800123724664057532510759255358272687201514628413931282023247855, 77219787865203018719003846825067819850442385301125621459947753271949874756080, 2493946643, 2166396278310, 2171933978883, 2948660445, 77219787865203018719003846825067819850442385301125621459947753271949874756080, 76712257614445928063477442809480003157587809252653832689651745405890837217640, 2562109984, 2171933978883, 2177603826505, 2942186456, 76712257614445928063477442809480003157587809252653832689651745405890837217640, 76204727363699679772743397570493796920456525575969588419473474920677518773903, 2631615354, 2177603826505, 2183408479212, 2935929674, 76204727363699679772743397570493796920456525575969588419473474920677518773903, 75697197112963415480053471023041771336739144625173921367047936408622246303269, 2702491275, 2183408479212, 2189350666807, 2929882370, 75697197112963415480053471023041771336739144625173921367047936408622246303269, 75189666862233952965358044544181191436148475508340239193105913981819830704169, 2774767180, 2189350666807, 2195433193299, 2924037096, 75189666862233952965358044544181191436148475508340239193105913981819830704169, 74682136611472721225902979959712055255360608554700206914325215367092243195620, 2848473448, 2195433193299, 2201658939440, 2918386684, 74682136611472721225902979959712055255360608554700206914325215367092243195620, 74174606360747673574509672095401710931450652155382160962141332756286171534243, 2923641437, 2201658939440, 2208030865372, 2912924227, 74174606360747673574509672095401710931450652155382160962141332756286171534243, 73667076109957764728763095142862509238035235555605707780630435751937273930554, 3000303520, 2208030865372, 2214552013376, 2907643061, 73667076109957764728763095142862509238035235555605707780630435751937273930554, 73159545859212962167157518256011208889667634337803849419332071106539982042717, 3078493122, 2214552013376, 2221225510745, 2902536751, 73159545859212962167157518256011208889667634337803849419332071106539982042717, 72652015608518377251110063396298983803359135933527709611212516152046091043809, 3158244761, 2221225510745, 2228054572775, 2897599082, 72652015608518377251110063396298983803359135933527709611212516152046091043809, 72144485357728091820912002327007258892930148356886103554587376424345676040211, 3239594088, 2228054572775, 2235042505876, 2892824043, 72144485357728091820912002327007258892930148356886103554587376424345676040211, 71636955107016483022002409205759200347605797046284801778399735830350085816004, 3322577930, 2235042505876, 2242192710831, 2888205817, 71636955107016483022002409205759200347605797046284801778399735830350085816004, 71129424856266067663400133743847560376398961244999564886683135993021561735992, 3407234335, 2242192710831, 2249508686181, 2883738765, 71129424856266067663400133743847560376398961244999564886683135993021561735992, 70621894605508242269439534298039612254832455951745469252352656883255494144818, 3493602620, 2249508686181, 2256994031765, 2879417431, 70621894605508242269439534298039612254832455951745469252352656883255494144818, 70114364354788439781793100343237389307661014534211824724544511702863303518581, 3581723421, 2256994031765, 2264652452415, 2875236509, 70114364354788439781793100343237389307661014534211824724544511702863303518581, 69606834104034857337354591289395976989627717029518359043479154125881483439315, 3671638743, 2264652452415, 2272487761808, 2871190854, 69606834104034857337354591289395976989627717029518359043479154125881483439315, 69099303853313095563336906975690498280018599303473703131954980964075727687856, 3763392018, 2272487761808, 2280503886497, 2867275457, 69099303853313095563336906975690498280018599303473703131954980964075727687856, 68591773602557679048506238103834413993599334818473453244899052632167152521790, 3857028158, 2280503886497, 2288704870114, 2863485463, 68591773602557679048506238103834413993599334818473453244899052632167152521790, 68084243351835236036701552768782562978729207008169726283901513313931578064314, 3952593618, 2288704870114, 2297094877771, 2859816127, 68084243351835236036701552768782562978729207008169726283901513313931578064314, 67576713101069556985876406849453941230875012994333414815254041056128382507730, 4050136457, 2297094877771, 2305678200651, 2856262825, 67576713101069556985876406849453941230875012994333414815254041056128382507730, 67069182850365433002060758058466889036763207599558198716481289778998012356391, 4149706406, 2305678200651, 2314459260821, 2852821064, 67069182850365433002060758058466889036763207599558198716481289778998012356391, 66561652599619970998310655354538339091473270161700819799038394187819752697310, 4251354935, 2314459260821, 2323442616254, 2849486436, 66561652599619970998310655354538339091473270161700819799038394187819752697310, 66054122348888220336657016189777207252865050383721931368492460606350188491988, 4355135329, 2323442616254, 2332632966095, 2846254648, 66054122348888220336657016189777207252865050383721931368492460606350188491988, 65546592098133030722816677125622215249408749991200710537164907172265246994599, 4461102762, 2332632966095, 2342035156166, 2843121494, 65546592098133030722816677125622215249408749991200710537164907172265246994599, 65039061847400268052341006781466811368452812762950460219828480163870168968012, 4569314377, 2342035156166, 2351654184737, 2840082864, 65039061847400268052341006781466811368452812762950460219828480163870168968012, 64531531596653947653489254705370631632809599725318754170432946404590289136147, 4679829375, 2351654184737, 2361495208566, 2837134717, 64531531596653947653489254705370631632809599725318754170432946404590289136147, 64024001345905573283511812788430051317106587089944123868485688958963009540766, 4792709098, 2361495208566, 2371563549232, 2834273101, 64024001345905573283511812788430051317106587089944123868485688958963009540766, 63516471095161620999539272166134424568536448960419648292499168292625990087716, 4908017126, 2371563549232, 2381864699773, 2831494127, 63516471095161620999539272166134424568536448960419648292499168292625990087716, 63008940844427652822806744722415772226418334267386800807368718527114231786784, 5025819378, 2381864699773, 2392404331648, 2828793984, 63008940844427652822806744722415772226418334267386800807368718527114231786784, 62501410593684246112305854520808128169598879590888202685781988217261967854548, 5146184210, 2392404331648, 2403188302039, 2826168904, 62501410593684246112305854520808128169598879590888202685781988217261967854548, 61993880342957083529526863666742747434370945094004150747884707707909634080354, 5269182528, 2403188302039, 2414222661519, 2823615193, 61993880342957083529526863666742747434370945094004150747884707707909634080354, 61486350092182694096542424973888059745222828778267871540856496099642411278898, 5394887904, 2414222661519, 2425513662095, 2821129198, 61486350092182694096542424973888059745222828778267871540856496099642411278898, 60978819841438103245558034643754978721576911170864437756622981810785903352594, 5523376696, 2425513662095, 2437067765666, 2818707319, 60978819841438103245558034643754978721576911170864437756622981810785903352594, 60471289590717483480414032079675487125251549922405414867382942765960826804928, 5654728176, 2437067765666, 2448891652905, 2816345993, 60471289590717483480414032079675487125251549922405414867382942765960826804928, 59963759339962519695384245032738223454126061944944904831720799338653484093429, 5789024666, 2448891652905, 2460992232592, 2814041701, 59963759339962519695384245032738223454126061944944904831720799338653484093429, 59456229089252514638678896669314486285666888989825398117424267790016790767760, 5926351681, 2460992232592, 2473376651441, 2811790955, 59456229089252514638678896669314486285666888989825398117424267790016790767760, 58948698838497049534013083774411225049879624692770975397327168943495483576213, 6066798080, 2473376651441, 2486052304424, 2809590292, 58948698838497049534013083774411225049879624692770975397327168943495483576213, 58441168587750791502776320812641003296772495116022774026041758188703485670694, 6210456223, 2486052304424, 2499026845650, 2807436287, 58441168587750791502776320812641003296772495116022774026041758188703485670694, 57933638337024401633249333376375104505436665185893180799859691130435577016692, 6357422143, 2499026845650, 2512308199817, 2805325522, 57933638337024401633249333376375104505436665185893180799859691130435577016692, 57426108086258377885987157725533856149499693037643465061372067845335859972470, 6507795722, 2512308199817, 2525904574270, 2803254602, 57426108086258377885987157725533856149499693037643465061372067845335859972470, 56918577835546102230065778905985889255015731030731002983827719582872148460703, 6661680882, 2525904574270, 2539824471725, 2801220143, 56918577835546102230065778905985889255015731030731002983827719582872148460703, 56411047584794131054193616968311875430438848769473806957850594199707785450601, 6819185778, 2539824471725, 2554076703668, 2799218774, 56411047584794131054193616968311875430438848769473806957850594199707785450601, 55903517334048639945355762429836228009878530892518370527107495218346726522566, 6980423019, 2554076703668, 2568670404505, 2797247127, 55903517334048639945355762429836228009878530892518370527107495218346726522566, 55395987083297742487497930917346966028293113122743642295933385369285224439713, 7145509884, 2568670404505, 2583615046489, 2795301823, 55395987083297742487497930917346966028293113122743642295933385369285224439713, 54888456832560189298861168099822237630875149790264659656258419692297813466423, 7314568564, 2583615046489, 2598920455487, 2793379487, 54888456832560189298861168099822237630875149790264659656258419692297813466423, 54380926581831228734964376132126117968672040585668366586711147731106968974594, 7487726412, 2598920455487, 2614596827637, 2791476740, 54380926581831228734964376132126117968672040585668366586711147731106968974594, 53873396331072305120231851667217007928996855180254859824916960557925226767739, 7665116209, 2614596827637, 2630654746951, 2789590170, 53873396331072305120231851667217007928996855180254859824916960557925226767739, 53365866080341867495463526293723847971332353886712541730164474973397060387471, 7846876452, 2630654746951, 2647105203942, 2787716369, 53365866080341867495463526293723847971332353886712541730164474973397060387471, 52858335829613513841144855508614349390246316191824657901851568627211315033636, 8033151652, 2647105203942, 2663959615326, 2785851890, 52858335829613513841144855508614349390246316191824657901851568627211315033636, 52350805578862843595118768995760637098192681865071927719404684825632780181100, 8224092657, 2663959615326, 2681229844882, 2783993260, 52350805578862843595118768995760637098192681865071927719404684825632780181100, 51843275328125527571993308910182252095439527234457026605724953502090446041137, 8419856989, 2681229844882, 2698928225555, 2782136978, 51843275328125527571993308910182252095439527234457026605724953502090446041137, 51335745077391452415950336986372330035257321933456299167454432741636396995871, 8620609214, 2698928225555, 2717067582878, 2780279496, 51335745077391452415950336986372330035257321933456299167454432741636396995871, 50828214826652158504463149671367264658453276846678494072610833151367035958661, 8826521322, 2717067582878, 2735661259813, 2778417220, 50828214826652158504463149671367264658453276846678494072610833151367035958661, 50320684575900972908021555187894564420838564573862669054972982074475482469830, 9037773140, 2735661259813, 2754723143110, 2776546512, 50320684575900972908021555187894564420838564573862669054972982074475482469830, 49813154325148427078012526178698460703082247076305335053180261543143799005731, 9254552777, 2754723143110, 2774267691295, 2774663671, 49813154325148427078012526178698460703082247076305335053180261543143799005731, 49305624074409821343448354078609443341230933541774463521307757912346743419141, 9477057085, 2774267691295, 2794309964405, 2772764931, 49305624074409821343448354078609443341230933541774463521307757912346743419141, 48798093823682690847548382771126718340467553427005568082756581977013335152474, 9705492163, 2794309964405, 2814865655598, 2770846455, 48798093823682690847548382771126718340467553427005568082756581977013335152474, 48290563572928103252073001030888822551010173857428410501312219743157984295193, 9940073892, 2814865655598, 2835951124772, 2768904333, 48290563572928103252073001030888822551010173857428410501312219743157984295193, 47783033322184034364409669126001865321309805950135397407275219088501751802251, 10181028505, 2835951124772, 2857583434359, 2766934554, 47783033322184034364409669126001865321309805950135397407275219088501751802251, 47275503071449133113726552680585634790410964172180554341967575260859734646800, 10428593201, 2857583434359, 2879780387444, 2764933022, 47275503071449133113726552680585634790410964172180554341967575260859734646800, 46767972820703864892583711260372678152190079848951108221120839711340407371104, 10683016794, 2879780387444, 2902560568391, 2762895539, 46767972820703864892583711260372678152190079848951108221120839711340407371104, 46260442569979513638850712840262522151449454081788512506980775028803704297628, 10944560420, 2902560568391, 2925943386182, 2760817787, 46260442569979513638850712840262522151449454081788512506980775028803704297628, 45752912319227129635128264356333376252594584523871113781711752488587922130294, 11213498285, 2925943386182, 2949949120659, 2758695321, 45752912319227129635128264356333376252594584523871113781711752488587922130294, 45245382068487649749673119934054194704160461902666199468254865199333195435060, 11490118475, 2949949120659, 2974598971928, 2756523566, 45245382068487649749673119934054194704160461902666199468254865199333195435060, 44737851817753575203231093447167658380678377409067999347273888578771356226707, 11774723818, 2974598971928, 2999915113156, 2754297797, 44737851817753575203231093447167658380678377409067999347273888578771356226707, 44230321567008683007282446943707293714929493881942546666613778047870222316680, 12067632815, 2999915113156, 3025920747045, 2752013128, 44230321567008683007282446943707293714929493881942546666613778047870222316680, 43722791316267711659793227854645446060393075091181611398336570571954946458378, 12369180645, 3025920747045, 3052640166290, 2749664498, 43722791316267711659793227854645446060393075091181611398336570571954946458378, 43215261065527428522294004501444032266972198226399814391592233095024503473503, 12679720238, 3052640166290, 3080098818344, 2747246657, 43215261065527428522294004501444032266972198226399814391592233095024503473503, 42707730814791845245460419904985052856034541491937772554081147150528101482441, 12999623436, 3080098818344, 3108323374859, 2744754152, 42707730814791845245460419904985052856034541491937772554081147150528101482441, 42200200564050213707269307990486791607201285709815755923161854116045005991401, 13329282245, 3108323374859, 3137341806196, 2742181299, 42200200564050213707269307990486791607201285709815755923161854116045005991401, 41692670313306820055398378961423159654311748796221135068753457252087226272171, 13669110185, 3137341806196, 3167183461447, 2739522177, 41692670313306820055398378961423159654311748796221135068753457252087226272171, 41185140062560799534064758976145606273097429043313561196070466690228232888589, 14019543747, 3167183461447, 3197879154446, 2736770602, 41185140062560799534064758976145606273097429043313561196070466690228232888589, 40677609811813163621849035600838405359960403492841115560192716960859305808303, 14381043969, 3197879154446, 3229461256300, 2733920101, 40677609811813163621849035600838405359960403492841115560192716960859305808303, 40170079561077200016052571917388006045007760273684205793831153354988101521371, 14754098144, 3229461256300, 3261963795027, 2730963879, 40170079561077200016052571917388006045007760273684205793831153354988101521371, 39662549310345933951100562961331780615445203874955610055557878170825434224957, 15139221664, 3261963795027, 3295422562941, 2727894823, 39662549310345933951100562961331780615445203874955610055557878170825434224957, 39155019059593925053807665285355410886495719103281721740907967573135771031636, 15536960027, 3295422562941, 3329875232493, 2724705436, 39155019059593925053807665285355410886495719103281721740907967573135771031636, 38647488808855491870214545271170196567431942468559105460064196943386713706979, 15947891007, 3329875232493, 3365361481374, 2721387827, 38647488808855491870214545271170196567431942468559105460064196943386713706979, 38139958558112326507153889433308627610233619895161420851722252714121854065861, 16372627015, 3365361481374, 3401923127728, 2717933652, 38139958558112326507153889433308627610233619895161420851722252714121854065861, 37632428307372653088915706789375416375104211264422148633588308689130314626324, 16811817674, 3401923127728, 3439604276464, 2714334103, 37632428307372653088915706789375416375104211264422148633588308689130314626324, 37124898056635203887641492112989149119661684963400832250749512674103369284719, 17266152607, 3439604276464, 3478451477733, 2710579852, 37124898056635203887641492112989149119661684963400832250749512674103369284719, 36617367805890497396979748760029627823735518971077781218351463141569995702941, 17736364492, 3478451477733, 3518513898767, 2706660985, 36617367805890497396979748760029627823735518971077781218351463141569995702941, 36109837555153679949579697715136727183928943555622550896431101518352019862164, 18223232385, 3518513898767, 3559843510423, 2702566983, 36109837555153679949579697715136727183928943555622550896431101518352019862164, 35602307304408842192095389219966885451602132840382123936496305128092829011917, 18727585356, 3559843510423, 3602495289904, 2698286627, 35602307304408842192095389219966885451602132840382123936496305128092829011917, 35094777053669755076018930257610238078103525206108507803020665400642418338396, 19250306463, 3602495289904, 3646527441337, 2693807959, 35094777053669755076018930257610238078103525206108507803020665400642418338396, 34587246802935381810555394535238615911056058298250191745962812447735301605735, 19792337106, 3646527441337, 3692001636057, 2689118194, 34587246802935381810555394535238615911056058298250191745962812447735301605735, 34079716552190182166946806878549920018634986428193095053564175099104735183840, 20354681808, 3692001636057, 3738983274682, 2684203644, 34079716552190182166946806878549920018634986428193095053564175099104735183840, 33572186301447813895841310052778097200646780007932443237826915818950582435738, 20938413450, 3738983274682, 3787541773333, 2679049618, 33572186301447813895841310052778097200646780007932443237826915818950582435738, 33064656050703159919553045601403520614192787028386533312872234078511867744935, 21544679046, 3787541773333, 3837750876617, 2673640333, 33064656050703159919553045601403520614192787028386533312872234078511867744935, 32557125799970380513998623597431276266049800636369668364968256428542764368126, 22174706087, 3837750876617, 3889689000358, 2667958793, 32557125799970380513998623597431276266049800636369668364968256428542764368126, 32049595549220633614625365600305304251742786213251007069951947194279531582712, 22829809548, 3889689000358, 3943439607399, 2661986649, 32049595549220633614625365600305304251742786213251007069951947194279531582712, 31542065298488482324182867500638699727176754279527871540754376644944018986262, 23511399619, 3943439607399, 3999091620303, 2655704077, 31542065298488482324182867500638699727176754279527871540754376644944018986262, 31034535047747888650096513214444190345065525005409559876843142532974254058422, 24220990261, 3999091620303, 4056739875199, 2649089597, 31034535047747888650096513214444190345065525005409559876843142532974254058422, 30527004797004503247968686314989062066935749746825171703615333742783794216289, 24960208685, 4056739875199, 4116485621680, 2642119876, 30527004797004503247968686314989062066935749746825171703615333742783794216289, 30019474546263024984357341959756816009181773290432453949362747568151465087987, 25730805866, 4116485621680, 4178437074280, 2634769547, 30019474546263024984357341959756816009181773290432453949362747568151465087987, 29511944295520843547533617342687914931428723217745094482309537407165988873946, 26534668238, 4178437074280, 4242710021848, 2627010956, 29511944295520843547533617342687914931428723217745094482309537407165988873946, 29004414044783545597714819821124108108393408595359557873160083138159236746854, 27373830711, 4242710021848, 4309428502045, 2618813877, 29004414044783545597714819821124108108393408595359557873160083138159236746854, 28496883794039842890800842946032480764032379793180779500119068094686092932719, 28250491190, 4309428502045, 4378725549217, 2610145204, 28496883794039842890800842946032480764032379793180779500119068094686092932719, 27989353543295653064784092761374758062798028252925818476563360818219587614442, 29167026812, 4378725549217, 4450744025144, 2600968611, 27989353543295653064784092761374758062798028252925818476563360818219587614442, 27481823292560292381289993677113638425483720612674289607466279132779500769056, 30126012114, 4450744025144, 4525637543577, 2591244110, 27481823292560292381289993677113638425483720612674289607466279132779500769056, 26974293041813631821229489672048177463599083574748466689026852215089072399780, 31130239431, 4525637543577, 4603571501134, 2580927588, 26974293041813631821229489672048177463599083574748466689026852215089072399780, 26466762791074897483651044330443252281895848531726230072109109021436477269793, 32182741822, 4603571501134, 4684724229148, 2569970253, 26466762791074897483651044330443252281895848531726230072109109021436477269793, 25959232540331871433643992289380477561588032558049244605275010289720403270317, 33286818907, 4684724229148, 4769288283309, 2558317976, 25959232540331871433643992289380477561588032558049244605275010289720403270317, 25451702289592981214759334876102796381869333901414473675700278958102461554473, 34446066041, 4769288283309, 4857471890760, 2545910537, 25451702289592981214759334876102796381869333901414473675700278958102461554473, 24944172038850299166551591089910110610622937501775938159321617551889602742318, 35664407344, 4857471890760, 4949500577511, 2532680760, 24944172038850299166551591089910110610622937501775938159321617551889602742318, 24436641788114291095584505582501420503727128292543235205689003469024338815478, 36946133169, 4949500577511, 5045619002969, 2518553427, 24436641788114291095584505582501420503727128292543235205689003469024338815478, 23929111537372629437263940855342246757922284595533670588922370241455319961896, 38295942727, 5045619002969, 5146093032971, 2503444066, 23929111537372629437263940855342246757922284595533670588922370241455319961896, 23421581286630258044769810408914707220858999591980467728741923649073188007528, 39718992700, 5146093032971, 5251212088326, 2487257426, 23421581286630258044769810408914707220858999591980467728741923649073188007528, 22914051035889444818160627997760015701449816174402231214679276367261963076285, 41220952830, 5251212088326, 5361291812535, 2469885740, 22914051035889444818160627997760015701449816174402231214679276367261963076285, 22406520785146155030294797847002483375766363747163388142020930300191513582980, 42808069669, 5361291812535, 5476677110468, 2451206386, 22406520785146155030294797847002483375766363747163388142020930300191513582980, 21898990534408128226970578796219015569510400714787207881658546886814017485613, 44487239903, 5476677110468, 5597745619623, 2431079695, 21898990534408128226970578796219015569510400714787207881658546886814017485613, 21391460283664901790727967914041083602908970612787642782595432069905409880306, 46266094949, 5597745619623, 5724911687529, 2409342264, 21391460283664901790727967914041083602908970612787642782595432069905409880306, 20883930032925174615371492309322372007344414466033047196054744914703721161113, 48153098870, 5724911687529, 5858630943575, 2385823000, 20883930032925174615371492309322372007344414466033047196054744914703721161113, 20376399782185529084889600312563905082438661697409072948778481544442678677085, 50157662093, 5858630943575, 5999405571524, 2360192908, 20376399782185529084889600312563905082438661697409072948778481544442678677085, 19868869531444484057858747122268665885079198349899002239881089198682171933533, 52290273934, 5999405571524, 6147790411300, 2332901339, 19868869531444484057858747122268665885079198349899002239881089198682171933533, 19361339280701796586503169259616765207598746701235794164145451259208342964800, 54562657635, 6147790411300, 6304400046307, 2298584996, 19361339280701796586503169259616765207598746701235794164145451259208342964800, 18853809029960655290981553548900905390421098946860265050229008396145894880962, 56987952419, 6304400046307, 6410000000000, 1460169482, 18853809029960655290981553548900905390421098946860265050229008396145894880962, 18526734277970591267771357601390065256523197546502490246313213441266100742389, 59085116079, 6410000000000, 6469917067130, 800591120, 18526734277970591267771357601390065256523197546502490246313213441266100742389, 18346278779219825533154782770845454529326805977345849816164982403051673271918, 60420593962, 6469917067130, 6474122807018, 56009382, 18346278779219825533154782770845454529326805977345849816164982403051673271918, 18333747462573706123296661038319860998813092516874102629594785050510360736816, 60939804547, 6474122807018, 6539645390071, 853083125, 18333747462573706123296661038319860998813092516874102629594785050510360736816, 18140760647179309983682089167826071917999612483627193442288782982677999797182, 61511518444, 6539645390071, 6606612903226, 846740187, 18140760647179309983682089167826071917999612483627193442288782982677999797182, 17947773831783458603146185887135142408635954137994127424399554988936676130913, 62596378178, 6606612903226, 6645101745895, 475279517, 17947773831783458603146185887135142408635954137994127424399554988936676130913, 17838748528479438313730650937234273181915184278841475914853082734478435757852, 63461525740, 6645101745895, 6675072463768, 366333291, 17838748528479438313730650937234273181915184278841475914853082734478435757852, 17754787016388806538679890126759386043549763287206848069331640958427969506756, 64025907442, 6675072463768, 6745073260073, 836555344, 17754787016388806538679890126759386043549763287206848069331640958427969506756, 17561800200993665330905079169789340341764315211563423591290849120007189445397, 64855925902, 6745073260073, 6816666666667, 828881402, 17561800200993665330905079169789340341764315211563423591290849120007189445397, 17368813385596540883183443325705570835796119208083134742538922578657040505622, 66032946220, 6816666666667, 6830803410465, 160507311, 17368813385596540883183443325705570835796119208083134742538922578657040505622, 17331218277738707196189657117800002071510038933843067431880700724358809945120, 66745106924, 6830803410465, 6889906367041, 663108057, 17331218277738707196189657117800002071510038933843067431880700724358809945120, 17175826570202419431702550816764361339317404463347467500493673633706447003543, 67360304431, 6889906367041, 6964848484848, 816607716, 17175826570202419431702550816764361339317404463347467500493673633706447003543, 16982839754807609546795847736110456535821787385057303209001349740685803819378, 68487758404, 6964848484848, 7027973877427, 667400747, 16982839754807609546795847736110456535821787385057303209001349740685803819378, 16823688026999047574588478088516175555985927902263294996143467803052663434835, 69652085879, 7027973877427, 7041551724138, 141905726, 16823688026999047574588478088516175555985927902263294996143467803052663434835, 16789852939410676832008186751813017292944024762985652943380302031610427893198, 70299464815, 7041551724138, 7120077519380, 803070032, 16789852939410676832008186751813017292944024762985652943380302031610427893198, 16596866124014944788677135245824486049741822517229130549561151799172173364950, 71086072098, 7120077519380, 7200490196078, 793982610, 16596866124014944788677135245824486049741822517229130549561151799172173364950, 16403879308620817341807315357583251209279057813988082282418932040238243483797, 72442741703, 7200490196078, 7237683392161, 357748070, 16403879308620817341807315357583251209279057813988082282418932040238243483797, 16316157776257732296125933685228282499572449242874453803915162465358010467636, 73447933363, 7237683392161, 7282857142857, 429252010, 16316157776257732296125933685228282499572449242874453803915162465358010467636, 16210892493224598058861203193029243736374708765941510744798291339494507244377, 74157088883, 7282857142857, 7367248995984, 779385889, 16210892493224598058861203193029243736374708765941510744798291339494507244377, 16017905677828595207761592522639578600208426593989399208345612529154575191581, 75279208848, 7367248995984, 7453739837398, 769389474, 16017905677828595207761592522639578600208426593989399208345612529154575191581, 15824918862434037598411031141574270834543636256092438833859546884236282875740, 76762514263, 7453739837398, 7461139639404, 64532690, 15824918862434037598411031141574270834543636256092438833859546884236282875740, 15808627525515449218203504424851044578591220236128535332786480442584235490406, 77576260176, 7461139639404, 7542407407407, 696781611, 15808627525515449218203504424851044578591220236128535332786480442584235490406, 15631932047038562098372235630100194385872059497581543667219983519304337589802, 78355692715, 7542407407407, 7633333333333, 751073829, 15631932047038562098372235630100194385872059497581543667219983519304337589802, 15438945231642857984616326336179301720901405660772988978678736596711706361808, 79868779165, 7633333333333, 7699710537247, 529553992, 15438945231642857984616326336179301720901405660772988978678736596711706361808, 15301097274774606022867797851390700461194620831018002816131030423547741305570, 81255065965, 7699710537247, 7726603375527, 211554744, 15301097274774606022867797851390700461194620831018002816131030423547741305570, 15245958416247502957224747726990082229307024473975166762377286310867435689966, 82079519288, 7726603375527, 7822307692308, 731831062, 15245958416247502957224747726990082229307024473975166762377286310867435689966, 15052971600850492935463949321299022439868690417736561252411912880723088483414, 83175212309, 7822307692308, 7920541125541, 718811980, 15052971600850492935463949321299022439868690417736561252411912880723088483414, 14859984785455821832547389074583062229040182950404265327099363835306643793935, 84909187301, 7920541125541, 7954951723164, 244192436, 14859984785455821832547389074583062229040182950404265327099363835306643793935, 14793567024033754094062573203394735737994058717764353486076038196930879676158, 86095865772, 7954951723164, 8021403508772, 464235441, 14793567024033754094062573203394735737994058717764353486076038196930879676158, 14666997970059918921127789845231393357477412275624050503840610753502570515795, 87007442613, 8021403508772, 8125000000000, 696384028, 14666997970059918921127789845231393357477412275624050503840610753502570515795, 14474011154664524427946373126085988481658748083205070504932198000989141204992, 88551242231, 8125000000000, 8228639898899, 664704356, 14474011154664524427946373126085988481658748083205070504932198000989141204992, 14286036773293946774412432027420741588276948291654816145866117708203161628281, 90438864082, 8228639898899, 8231441441441, 17938933, 14286036773293946774412432027420741588276948291654816145866117708203161628281, 14281024339269786967670452609886496781656957943551641761309020782532521864014, 91406600803, 8231441441441, 8340844748858, 668977720, 14281024339269786967670452609886496781656957943551641761309020782532521864014, 14088037523874248983131009364823550984636157187247905845010921181838335254092, 92444034547, 8340844748858, 8453333333333, 653360394, 14088037523874248983131009364823550984636157187247905845010921181838335254092, 13895050708478507373341037621319029001467081653997233325049590313713222146829, 94492085358, 8453333333333, 8522813544898, 386153406, 13895050708478507373341037621319029001467081653997233325049590313713222146829, 13778506522552887730228791044073392229900044215911265036681779864154497344656, 96176785072, 8522813544898, 8569037558685, 252070370, 13778506522552887730228791044073392229900044215911265036681779864154497344656, 13702063893083149893060934784177615956296996624385461993214874840650187104022, 97254055535, 8569037558685, 8688095238095, 622728528, 13702063893083149893060934784177615956296996624385461993214874840650187104022, 13509077077687269896302309668693468125710412430266276558438430496973191350573, 98808470700, 8688095238095, 8810652173913, 602456216, 13509077077687269896302309668693468125710412430266276558438430496973191350573, 13316090262291429946489474511746117465580925983869365095350008838247466733826, 101084259177, 8810652173913, 8839822977139, 137648989, 13316090262291429946489474511746117465580925983869365095350008838247466733826, 13270976271811128793862717419009084622433503103386398775208984019339526398898, 102512991695, 8839822977139, 8936862745098, 447115650, 13270976271811128793862717419009084622433503103386398775208984019339526398898, 13123103446895894565140876429068314430397120141169897896540208789843207966517, 103717817248, 8936862745098, 9066890547264, 563528660, 13123103446895894565140876429068314430397120141169897896540208789843207966517, 12930116631499842946428393493200405168674706182018816214896810460021882972894, 105891541173, 9066890547264, 9182392346833, 467235897, 12930116631499842946428393493200405168674706182018816214896810460021882972894, 12763446021070647113800786696107963485111899373755068465877961413049603509211, 108250764533, 9182392346833, 9200909090909, 72880991, 12763446021070647113800786696107963485111899373755068465877961413049603509211, 12737129816104910427960518695241601011920524839777421582926159684885165246386, 109539051802, 9200909090909, 9339102564103, 516764513, 12737129816104910427960518695241601011920524839777421582926159684885165246386, 12544143000708655107323240996115505271397726002883419072478466567404176276802, 111070432519, 9339102564103, 9481666666667, 487152078, 12544143000708655107323240996115505271397726002883419072478466567404176276802, 12351156185313283305547074943100421116473641906545794503065596780531709739276, 113811945810, 9481666666667, 9553697044961, 228428730, 12351156185313283305547074943100421116473641906545794503065596780531709739276, 12255915770330473304168454303651809407626001767993489956303830910901895518228, 115912399357, 9553697044961, 9628809523810, 229818029, 12255915770330473304168454303651809407626001767993489956303830910901895518228, 12158169369917585834100200900369034306865951832215607311918652730889602669731, 117365494225, 9628809523810, 9780752688172, 425547336, 12158169369917585834100200900369034306865951832215607311918652730889602669731, 11965182554522727279649216923190535145744834462897881971488228122562042469812, 119627768334, 9780752688172, 9937732240437, 383831941, 11965182554522727279649216923190535145744834462897881971488228122562042469812, 11772195739127338178737045163043367871902980204873881066781741845579756268979, 122714809917, 9937732240437, 9957461170062, 44076930, 11772195739127338178737045163043367871902980204873881066781741845579756268979, 11748385519589188602235838319967036374988487946810017877674418860480682253346, 124478128791, 9957461170062, 10100000000000, 296594388, 11748385519589188602235838319967036374988487946810017877674418860480682253346, 11579208923731619542357098500868790785326998466564056403945758400791312963993, 126126874296, 10100000000000, 10267824858757, 283769850, 11579208923731619542357098500868790785326998466564056403945758400791312963993, 11386222108336162811846087398755975796560738865353245692907159603301262986497, 129282627545, 10267824858757, 10398081400337, 164285658, 11386222108336162811846087398755975796560738865353245692907159603301262986497, 11240855268847950941858688158878509838538294968316546568601549553789514416814, 132326355070, 10398081400337, 10441494252874, 54276670, 11240855268847950941858688158878509838538294968316546568601549553789514416814, 11193235292940088496472625549992802400544245367317170365561056948123690537651, 134105498314, 10441494252874, 10621315789474, 52023918, 11193235292940088496472625549992802400544245367317170365561056948123690537651, 11000248477544705552343533450872061879022021718063390399452619754290975642837, 136429264952, 10621315789474, 10807619047619, 3924, 11000248477544705552343533450872061879022021718063390399452619754290975642837, 10807261662149560027232040213498220601263609139992136342716886379089587977866, 140242264334, 10807619047619, 10880786009858, 1449, 10807261662149560027232040213498220601263609139992136342716886379089587977866, 10733325018106978829661902837225436334308070792871749259918571285640291176299, 142948580271]
def RP : List ℤ := raw_ints% [29805965679107891286107303829068541094107917564202389851142851450208743064953067645038007449872530723604732858963422679857710032023282949324704581829504126, 55379201540712338800986169987606089567650209697026479213584227991138752518850568985109105343009039606756103721681344015103392226997077177017844579577902999, 78179703045874628821822816225827705291602889073999152410163408836819207919873020334919107632046462544098630597885889567879898701328745075341904619538699752, 98897215036428374590848276619159875493175329827861622106107806290273511724499519986191462040574461856761856944385813771976596109428059123860973413487959530, 117934505562651055458751985944811100239972404734933350404355875289560557705744543769862224226879932538621445059374742863340387519673252758232485969028404848, 135558995502104858452162266654639068220936575295589033564399295672568675957891582043520935600930644950615430184132904430134753430199063529641248296669427963, 151963214283715305008050862573052917668258655275146601012108310181157754946256458295592577984414434782941379503078339862215195352785045210888411598402583187, 167293532949707612437303407592766665282745434998562760843054053495740184206464709910136367815332129653846014264625101630766601469752875219746223238927248693, 181665633748560131090290884546590737818788574710008908250126942167313637445816132217126980134351025406035000730512613577645662202432467556486624509129953223, 195173627778321530837867140875334160780144002515966975341786883333818247196082802613081629506395319493310742002346109956742369489949862588660028540886542698, 207895807184241617502467807402034427294808208378917538859506605195193766861187459024215707805656295648317393070214872991303268295501140121588921808181981650, 219898470877780461123844491736262263027503100483276762073958146399251797583224904181161631307672041890949726357109213800780320783213249018541178493811815845, 231238578262662209716983405272952549461188705418265050833089020786727860170627760712068845747755454636504447014131579503659495677431066844631671867531159791, 241965654103180762467302036076366449714306256857602733944922087400690372636427383452931175711693150725098331363049227372643151606148533897785946806271036821, 252123195202270212982464907668177524874420936760094511580445800037788917018340935492484356776041037115323056178911084482976616034781288558585652170956664591, 261749734285099906718170912155258168921461165285797467919426577952957476549365670462442662325328459043570989012986765320822321874485731714714364971479484677, 270879661175948353299180962371897152094973693834892778614878198257960553744278766419982307351886987109311073165815870920453774391994622479413758120244123075, 279543867868987020493871289738522214468489290124804257817770071031066665914786319410654273567502397342426879713335714220267106198823874388465183260044799570, 287770263073839731819216017075668188342411541240762930498628034793982032461993997108820754555308174627545553699383748415509097768188705543581067782361008627, 295584188204020931401407768298518089328713995486656375061768531886113045877414315919331483292602010502388679638686523458498880645426487517712769322651920075, 303008757716328007211254968003632883295224270355744115933390611424527113665439616620092886820375585868938202261202346340282561400114525837646422128694084875, 310065140532329523493404187301697394129962390417419448993592270408968232975051191056786722257767188934578239411968836355803011001368065038926098601637324722, 316772794970748090730573946692299962111190028649502401572709873996876001155510533716690217675826074353723185713894438905959381435723062076344201815057196030, 323149666565040801472160479416483572909029690781150024646349422743266330662292431373023452972590462209194299977407701120350212368514981499103586529166148188, 329212355934313641530440591098371414654852596486992868176524424174346979484047926805060632457326836443285687592759336590827605533434258779339185126687107969, 334976262257315259795153619640126751191577881224816113342591833936844351977468262209451447186170534183122285765297433320127136467668093747698611540004406132, 340455706695174623383433772357521184054035522492015783441868127370746408718734466873041912501017107213845501126952170750924115943345729805250945311472478013, 345664039201109393530067021106728184688605432760169412780056061397946996521199977963267681818939467591312578336303786082241802794912564764152521198334800975, 350613731463346851107173830586029523700666344139681715988852196037186481258896629454893776077107356610814608907126927097292556088823988915529966679278364599, 355316458194063712340016777271368934589815691243648917368599491840965767807908305145700158627601852492058056496083713384673841506605078437884799837828829348, 359783168561807852095620553973429270718555664527521791299463455639284091280744648040348032501243932532381282016306536325469179695608490278809206062493625503, 364024149238466284283189691677165230639258619269216937762199848761197641757965455159899833874446091718110479303067936754808108120901100980225541268824451615, 368049080273132025528104167849921678229980388778362499919062768019377445174993229616237186317381925055658603383569454929422623991413928952177812007560094177, 371867084798517272598837125936041837754134534473989429303280833804052277198365395040917142467483087427108895699437380263286861878639591666211947789615446790, 375486773409172580068961478871052736958905599319151090598496616133798417439344413117183047482366437439863822584474973731305664873217871196947309376865309200, 378916283915901595934152512319751264381840199493261971025612650581497980472195065824779551548474804384544413532159006895955497420699463657652948053633086665, 382163317070722472746006981301010453625489258038323306064907456736660678179876566439508984043013870982379780877306791406370179132045268371085208817063024509, 385235168766396563576195104750612249111146090493570305103104424500402976241168529387856160848823130214135227608667540081758418260543928910459812108865225325, 388138759139963979375707436010023678278080714996286104154463856094785611827729331014334021298343535779552178006402729808757973878052193838340089470972601884, 390880658947812508272171491767838733802741866358305687974099364019864924762295115053074724543386029245236103162574132587895404181048346892077275708289807573, 393467113528145179744031461080337545268968946644214071371983336379473605900164716194838518815310157862457698863000297909470617061308421460133249295266771696, 395904064623395178398800400486172198191439212581546018730842021522166186687011146078807988042536588779546052387566970515985384330184964398884783388777324722, 398197170298649699588002470301254767207385244286149009492866276532159164581421384479050857451952625768920177196118582303240828469500305249458822246360459100, 400351823161275668611862885605867708401404419835841975411702658265373474885852696933715874061277593331577045745632570705791892639132344287627818411883866777, 402373167060716518417334173098265369207398404235171388470736932343562227204405040904552862071559437728514374435423548517611731343270513738327237757502226077, 404266112425063600976162816644798470340706606936945286248881361028015520828865473602251604287856317915244878125717107210590792923908627417413017113903389148, 406035350371859025377841352783508907712672275377884354829656205171960409278564422088632324402979012573615280682348308637803940339260323346300033399159350903, 407685365714136824760276742211662841389473653009374932461511289250725095915209138873834616222482812292919336060881635935354959501184224162642785387613580892, 409220448968528191110966209775604590404019607969614691519949704154885606138400626132995835945573713725298595257136238420845991078289481009092669253086279637, 410644707459991271036979825666391432370821884739885737072092651823697345478210580581193321119964445807675243427521574146650030764009167428403253147603588335, 411962075607084718918597258673175432065726034118668488687513582791861768794781466470195464172582420229115659483838037429855938962145320721100339619659504472, 413176324462444246628584791817453245989009583305299282617713086060703403499755187996504924128833742374722520629557318748316890510840057588302233240151701008, 414291070575040403012294116553146234272411088490950619004488432161154843941949431593628077394987947205591353076337862990946406283588138231284308556018912625, 415309784233724291011181637764375326284059772788824873225629654445453956960558778124104188490926560060652970025342617451367506392912186544972876520837050868, 416235797145363466438408263954216027380003161587664490074827041459618123768381042514171831867419784158050164798324062408345887087624322519129995440895799834, 417072309595412759336706792113109743973494702209145333781094625924191364993125410081795454078092149485562354850559475783165589798754241482130577031063377918, 417822397133952599852755311130450337272012787156923649198179652622268351172232315042176137729060392036254821559969779683054991769702102122180361838885196894, 418489016825974363024560693277978981592843908727849667370037697299799157905816915290608076715236491603851341467878433237373823276670232391710638338279859393, 419075013100924833908701480826893507632800217473154416338966836893277467410416229447322602212314306487468868185725070315706341976448383376434682654198324602, 419583123233177425411440218083738268895583066004556838639607106785571249532146465410913194954405371619285549081823391261704132481050227414516656757217581828, 420015982482122552022192720427427672661916266086597062406415834703675922528829476723139027423732144414313810360642042946665871583238064131825590722882053117, 420376128917917455866234377566915619319765619237345149845012931843887354475063763201640016749820563232293303043358303763387064571981944471993264892902928017, 420666007956567089201409069968788516343354041229818114664473480660116532209338828914243200879782438809142243694088865601962310624923793949116251710367865661, 420887976625888102919030528581304687272342173998492027472579212276124121572838664607610275381554849016610018482046585555406189918638880880846257763770454447, 421044307582007912016025969479202810010306691511434454817972360845533830003448348345922846510988248535940285647722378651085493772003982646735031418246151008, 421137192894344476835511723137986714593865512607624023088430089071386719759332707806128865083785954445540418589203453500543915635958338570924008433827514083, 421168747615477482839675513401931142024700146381993360947667171398830221977871726706397692492574079802616760361012124715073770843268559303232278439607346629]
def MiP : List ℤ := raw_ints% [1121763465607409488174010802293126117802704769969554815152501800022757551, 683176186409461575464732725973774284614116203874193697035239327053782272, 493646939926165612032744696199800343660888315547263913012883604849950482, 390759350663220301122544106368441802662569173962174103669248515119945000, 325885681106247456854513746363922238759860897447017747597002379600611339, 280835962195223730571580429284227001525526295183629269502370868741659227, 247461031609645290648323289006548728615612801369983097091104125714070709, 221580436114695976021106480279163125829421488660551680840957288899137399, 200823625475826156165571384896430518762865405308577993292847666483940531, 183741132981572802838030160903459906285481281538060325869708582733913038, 169393562742612225322549708742863514492428654931885478546322691335682333, 157143347289248814008705764138850970300328373198826152878265639611471709, 146541281121803428325527981379102391852314575502060515609198387793172365, 137260941329916268419274108240818220352697908160677326495081516503987868, 129058895744600575187917722547881819338647630675927608376677784134902244, 121749553035851577983089517182200075382941177245789060321752896962833204, 115188706110510625499079509456907946136919398849404586086556607284514291, 109262437731295566507329677868720730066174013550739419681337860308587077, 103879444575473468369370638316340584989646405780543265108175919052913782, 98965604200580626375082520349461835338120942341234701214932238989319995, 94460051388423056848575390190096391730559636253760616967731560942609066, 90312293319360931081920892611650814685664161180033355505274279731802995, 86480054214280754448594814430772224950582525600905860273840632338847186, 82927641527237767304283641017083053774880367048618090583879560986481214, 79624691154647957283008454734120611007161611976765787288846969307659884, 76545192180585953129841765030002453264734595235040788866802030136597929, 73666720584803571954672580911683711468356155716144481356085277616073192, 70969831095833333226594207719418849019007193049953374621324789194447626, 68437570093734979990212982789638080316509742695946920257119081597552125, 66055082141326749662062883111669806456262302807377218291437907752395613, 63809289637419478664858515336389167109757650353812338737509600501640425, 61688630090900990868689350338751118147491000607505496792981328959490993, 59682839180584703109096720140964473876423033203924084073641078095409661, 57782770480401087468482307252870571280476007112105409855284493487397456, 55980244760267980374249420671959296098706680382219610209822047476711156, 54267923306657781803363834663183557721932875129614914220086569116029355, 52639200875531728815025228151903675468144364136485537169734953952295114, 51088114788296723520709380578896998804495645652178252225528600115808058, 49609267376896779772979599389923572243914307116711815402738761270622240, 48197759526763074455152251284018161132968713600912313292138946531262019, 46849133492676291949489784936667185828935183745041612228506925092126253, 45559323499782997004670838171094092922749517661416401767856622363182825, 44324612910366527395714404914043011117709698289147594946752144469231425, 43141596951822741272907012762307672771755815272718439602333818758946701, 42007150174272341066041781713874079354515770607046894368145336287100764, 40918397946260775619281351973592373113722151758458756554064110639734155, 39872691410913646604472564537426100927548507110985952260897657044996059, 38867585418046991738232158903491107429372644762124160528334898713646191, 37900819024223649770004097790436421435656639717414869671358022910751902, 36970298215850475431538378223373879558334759806008339131635519300758211, 36074080562690291034645176400041899037059038059436540135504733750123342, 35210361552649426255698586265613098774849886046689967184386439539212367, 34377462395015549578793831526989705776781803578181757176195560922477868, 33573819109757254717687022599947732330631556700963876338443990093703925, 32797972746098760168865023067988818742699000099507695370689897760146648, 32048560595191946696582173332935510793205782989087424258184477806229620, 31324308280006657445984874184994177541954990506604073836494242287765531, 30624022621104884804990921818903921499395012422089820589847259915880464, 29946585190209921141112124628661041185354680049742654667754616980543602, 29290946474800994033947929129580252907608512810165496549069001452497602, 28656120586664786313452935368659233193609757605656643387109922087827951, 28041180455671695998969336372146720970840268653914205006149495961974804, 27445253457227505670834669296812178560494650741630125043887637361808506, 26867517428055701118033351815896626299142382298383534974719704263544856, 26307197030338414031993125059027696950934374742569721284337864525101189, 25763560428907446850094177143500621034704538343533041243506336818015440, 25235916250234007333438262564338335948186287596711344087502958588429616]
def MeP : List ℤ := raw_ints% [1, 4896116775975550780284589642611307636488298976169072660, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def ViP : List ℤ := raw_ints% [10967745922124136676963595383, -17688669268547561386519296037, -688138684756238841648691341, -3470318987308317296197652421, -5242719191452692897886504718, -858104929881605307540431424, -4072876171369846790422507970, -1404418690373068221379089243, -1656566208532015283936639911, -2106058475954330825175572184, -281655983150203811026712393, -1576636231753337209287658699, -287567271395621032635564908, -348168433801639071653381508, -604659473386509320796589753, 428563351283590852678007099, -349462977349812676539296107, 390557362719613588674319280, 324871788409123252097554211, 99767052559044684450316908, 733112159882532627010354682, 151663525954084957762107978, 596398432175168303018808958, 497291189799868258282801352, 272863996655346910736155995, 676004172067168523897549800, 196994447230635528919056764, 473848998382243907139829782, 357682087126131103254311772, 144382676761679098921311436, 419631265904607222053833482, 21094515774209613534650980, 212170494216233149302178021, 105996185487800032690311159, -75966123787055620915380255, 138454566128913595352253529, -181703315700181339510115803, -24238896926497167293615637, -100286269532472792463663052, -237492552607758330016041471, -44689238145067304972180145, -289947872896283835156847012, -139286786224128725910058538, -179228554237468841494279980, -271983006322873886777400062, -86328520427570337235945384, -270186610612342595939719059, -121307882390560188635171797, -133520673829869918754506217, -194149224425702850967512455, -17817501212962793643800798, -160461470940978059137291572, -20631259459216086292536893, -21021582672260362556701009, -67465039870827234085119234, 89356706984712153613724564, -33716783701633222592885908, 86115288065100806169254203, 82138246657508276725001096, 34932637036716917158136852, 164731521577482955413894045, 46709091088169269000761067, 141010972239013442346766336, 125383763696423724791220381]
def VeP : List ℤ := raw_ints% [439098938838, 1756395755349, 3951890449534, 7025583021394, 10977473470928, 15807561798136, 21515848003018, 28102332085575, 35567014045805, 43909893883710, 53130971599289, 63230247192542, 74207720663469, 86063392012070, 98797261238346, 112409328342296, 126899593323920, 142268056183218, 158514716920190, 175639575534837, 193642632027157, 212523886397152, 232283338644821, 252920988770164, 274436836773182, 296830882653873, 320103126412239, 344253568048278, 369282207561992, 395189044953381, 421974080222443, 449637313369180, 478178744393591, 507598373295675, 537896200075435, 569072224732868, 601126447267975, 634058867680757, 667869485971213, 702558302139343, 738125316185147, 774570528108625, 811893937909778, 850095545588605, 889175351145106, 929133354579281, 969969555891130, 1011683955080653, 1054276552147851, 1097747347092723, 1142096339915269, 1187323530615489, 1233428919193383, 1280412505648952, 1328274289982195, 1377014272193112, 1426632452281703, 1477128830247973, 1528503406091940, 1580756179813713, 1633887151413928, 1687896320896299, 1742783688282460, 1798549253698505]
def cNP : List ℤ := raw_ints% [-334709043033573506987414, 269907673165093404945668, 7000108690961088477058, 26476432703463114137250, 31999018502518877550577, 4364547372851589495547, 17756330964747169670857, 5357432137958786855236, 5617154298678979776803, 6427180407575472488939, 781405315469093492062, 4009593281436506167825, 675065897769918665104, 758946955657172223017, 1230182847872943767897, -817419722144300179821, 627339041945177282965, -662159157171653897899, -521805272809678332034, -152232441038581366654, -1065371791123937155602, -210381977364397857336, -791331989023183146626, -632338447316320111952, -333085933417171521895, -793461928226375314446, -222659016057485542488, -516454422413683108891, -376399690958095264571, -146873653932372130250, -413100965836661280531, -20117297910890210662, -196209988880719872032, -95139613869880256824, 66237203357854022143, -117369389961169429654, 149868787363562786626, 19466116595215781197, 78474206803129376114, 181192438207823432935, 33263593083873696655, 210678734840235999085, 98853380938954003559, 124309577413017163013, 184450280980681618094, 57272551447044264577, 175434914844491899167, 77125474542338173316, 83157706018483636820, 118499282486390900249, 10661705593311261132, 94171066836417599685, 11879548535165512541, 11880144287256516383, 37433993181167454992, -48695540828547970153, 18051834749795062466, -45310862608337826522, -42485768803746253437, -17767657998004616881, -82413230809687857913, -22991102200499144032, -68306561298195220631, -59787637565814840694]
def fP : List ℤ := raw_ints% [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def gP : GasLit where
  P := 256
  T := 999997120790
  Q := 256
  Qm := 240
  Qv := 96
  W := 80
  N := 64
  Ln := 427
  Sg := 473244352085428890469631042005039278801145966237480161413251677837181121672026885
  LIv := 283904694028599334108302234421134026001164996929168315281217545808488867749014
  LEIv := 320871909030333695936730866818174657264897161702216345811401
  L := gdOf gdP
  R := RP
  Mi := MiP
  Me := MeP
  v0 := 50301613494123125310883779867
  e0 := 1
  Vi := ViP
  Ve := VeP
  G2v := 20811099275410466085108746707557842276948584876412589987479386804866956378877
  Bq := (79837491800816330374820032128692674719198011 / 730750818665451459101842416358141509827966271488 : ℚ)
  Tb := (2873152135 / 1099511627776 : ℚ)
  cN := cNP
  f := fP
def gdN : List ℤ := raw_ints% [2000000000000, 2000000000001, 329291, 115792089237316195423570985008687907853269984665640564039457584007913129639936, 115791973445284854137520208380751064855617268643195079412089068500740624389400, 6, 2000000000001, 2000000000002, 375636, 115791973445284854137520208380751064855617268643195079412089068500740624389400, 115791925482688972543614380347981446405965672015781244530264618748219112043480, 12, 2000000000002, 2000000000005, 409024, 115791925482688972543614380347981446405965672015781244530264618748219112043480, 115791830318622884124048774629459216780003948652006028859008016488999497432659, 23, 2000000000005, 2000000000011, 452954, 115791830318622884124048774629459216780003948652006028859008016488999497432659, 115791705199039359858744863812948241321826138534267888062901967395728021501795, 42, 2000000000011, 2000000000022, 512356, 115791705199039359858744863812948241321826138534267888062901967395728021501795, 115791546125549685322818259003035951062397035162850363214197953148310305624924, 72, 2000000000022, 2000000000045, 595490, 115791546125549685322818259003035951062397035162850363214197953148310305624924, 115791312482973138979779354944080359677529638708854251509688939382966837080004, 122, 2000000000045, 2000000000094, 716993, 115791312482973138979779354944080359677529638708854251509688939382966837080004, 115790966596801122642995559115354765421969838576759021677014362954309050507069, 212, 2000000000094, 2000000000195, 904326, 115790966596801122642995559115354765421969838576759021677014362954309050507069, 115790472300076605313638365668522643236508159120155505941494413832493483527834, 366, 2000000000195, 2000000000403, 1212377, 115790472300076605313638365668522643236508159120155505941494413832493483527834, 115789764750679230234440499450732541842692793345071395878741194540678085655752, 632, 2000000000403, 2000000000834, 1756879, 115789764750679230234440499450732541842692793345071395878741194540678085655752, 115788745319122013984334044963323718070864428454286428164516406515313088160159, 1090, 2000000000834, 2000000001727, 2780968, 115788745319122013984334044963323718070864428454286428164516406515313088160159, 115787277343505389990656282157648903529071733031475388412593154413262883401619, 1881, 2000000001727, 2000000003574, 4681056, 115787277343505389990656282157648903529071733031475388412593154413262883401619, 115785167052627942223993223238345148823140842478816687710163948535366176315656, 3245, 2000000003574, 2000000007398, 7219921, 115785167052627942223993223238345148823140842478816687710163948535366176315656, 115782130199618883206042657512107371701628374807731825590394346613091557491408, 5600, 2000000007398, 2000000015314, 10377967, 115782130199618883206042657512107371701628374807731825590394346613091557491408, 115777760882106131492689338715202110857992125743447598131784764900860467842730, 9664, 2000000015314, 2000000031700, 15173656, 115777760882106131492689338715202110857992125743447598131784764900860467842730, 115771474877172873196989404627109112302897679443998741234365399000075979675471, 16678, 2000000031700, 2000000065623, 21848110, 115771474877172873196989404627109112302897679443998741234365399000075979675471, 115762430592456931873321728142538432979140703427451605649004256277169584640694, 28784, 2000000065623, 2000000135851, 31522205, 115762430592456931873321728142538432979140703427451605649004256277169584640694, 115749418487567752294161822598982653334584623721067202653833218503920457929644, 49678, 2000000135851, 2000000281248, 45372795, 115749418487567752294161822598982653334584623721067202653833218503920457929644, 115730697708013546809592788872245293649154598254316349371831809541722850501901, 85743, 2000000281248, 2000000582302, 65305858, 115730697708013546809592788872245293649154598254316349371831809541722850501901, 115703763488384457662877610678722354301028560578627942522087060210706001244365, 148000, 2000000582302, 2000001205732, 93980885, 115703763488384457662877610678722354301028560578627942522087060210706001244365, 115665012562197683200060606519436843665852769808363222990090670347321748424565, 255484, 2000001205732, 2000002496994, 135193048, 115665012562197683200060606519436843665852769808363222990090670347321748424565, 115609260480600166363918176807861044326470393018416789172459753634159513954863, 441088, 2000002496994, 2000005172208, 194828728, 115609260480600166363918176807861044326470393018416789172459753634159513954863, 115529048487374376074846062460234359104418423662143311603074570344676607070798, 761679, 2000005172208, 2000010716850, 278329372, 115529048487374376074846062460234359104418423662143311603074570344676607070798, 115413645258278359346603149824482591281543847909534797857079843811065311372202, 1315651, 2000010716850, 2000019296467, 308500254, 115413645258278359346603149824482591281543847909534797857079843811065311372202, 115284556673286078219608670237913903143593913562772470587049144033852291900628, 2104908, 2000019296467, 2000022215164, 95304449, 115284556673286078219608670237913903143593913562772470587049144033852291900628, 115247611441722948123656477138943028752632944128701159024010088588971263953525, 2646941, 2000022215164, 2000046079500, 577384393, 115247611441722948123656477138943028752632944128701159024010088588971263953525, 115008734028686139352127222438899187000086808861650697624855682582757395061057, 3930858, 2000046079500, 2000077526822, 552075950, 115008734028686139352127222438899187000086808861650697624855682582757395061057, 114777026417937971014428971607735073176154159555973527720077552538212314736007, 6072503, 2000077526822, 2000095667547, 280633078, 114777026417937971014428971607735073176154159555973527720077552538212314736007, 114665054492048574822219541531012136634171933205715914222258972215270201475226, 7745186, 2000095667547, 2000175209840, 956274670, 114665054492048574822219541531012136634171933205715914222258972215270201475226, 114269496170919912096362432789765082673109058089510072180028136263009233331916, 10992149, 2000175209840, 2000198883427, 238146634, 114269496170919912096362432789765082673109058089510072180028136263009233331916, 114170593276054393708912947917757119219440141528309136496309818764588905879557, 13796758, 2000198883427, 2000312873558, 994039847, 114170593276054393708912947917757119219440141528309136496309818764588905879557, 113761965918400596954418294936052550722037464888177521869361525937236534166249, 17613074, 2000312873558, 2000414257402, 730130302, 113761965918400596954418294936052550722037464888177521869361525937236534166249, 113459198284848303314083651389717967999393766355328884534849366144178958560689, 22809805, 2000414257402, 2000491055474, 509005479, 113459198284848303314083651389717967999393766355328884534849366144178958560689, 113254435668470541458596901977881205511720873398075302694990273524330975537136, 26837805, 2000491055474, 2000710302767, 1244802039, 113254435668470541458596901977881205511720873398075302694990273524330975537136, 112746905417847545120316069951020610505157382782941423644142749830340099726817, 33375104, 2000710302767, 2000865292450, 756580922, 112746905417847545120316069951020610505157382782941423644142749830340099726817, 112435694697162144818640978889126107792849853485636705575729632904400340058916, 40756507, 2000865292450, 2000971172512, 490174344, 112435694697162144818640978889126107792849853485636705575729632904400340058916, 112239375167044973082687456083900777193093398278003360686049163365085971273497, 45690063, 2000971172512, 2001274231906, 1260040360, 112239375167044973082687456083900777193093398278003360686049163365085971273497, 111731844916036636712362275417455485049816325674669628506398799310327144410751, 53322429, 2001274231906, 2001620058499, 1255901335, 111731844916036636712362275417455485049816325674669628506398799310327144410751, 111224314664476077953530691978762877648340561402833138840144777447402436588811, 64532944, 2001620058499, 2001814869793, 645911784, 111224314664476077953530691978762877648340561402833138840144777447402436588811, 110963151862345428815978365573306388448810506198702852209039296025815752701910, 73285726, 2001814869793, 2002009240430, 620495292, 110963151862345428815978365573306388448810506198702852209039296025815752701910, 110716784413456498685168971258198458757635654221282663253859301944406972175951, 79466587, 2002009240430, 2002442376672, 1275212990, 110716784413456498685168971258198458757635654221282663253859301944406972175951, 110209254163526918400467275577077500476415877354186299824615933069465136065437, 89258669, 2002442376672, 2002920077285, 1277345235, 110209254163526918400467275577077500476415877354186299824615933069465136065437, 109701723912500484745642487148776035922656874971544454313159071720270423752953, 102726420, 2002920077285, 2003442963668, 1281563144, 109701723912500484745642487148776035922656874971544454313159071720270423752953, 109194193661798552142430657403347965986327165728565957960339130279825959188343, 116906567, 2003442963668, 2003829787234, 883838690, 109194193661798552142430657403347965986327165728565957960339130279825959188343, 108844563883114627328357206513227585724017038293519532489473481965805601242920, 129264038, 2003829787234, 2004011668828, 404426934, 108844563883114627328357206513227585724017038293519532489473481965805601242920, 108686663411482188769017755162135810745859024175680135377220981172854922206572, 136795313, 2004011668828, 2004626837653, 1297464805, 108686663411482188769017755162135810745859024175680135377220981172854922206572, 108179133160158920690860847044507911922456635364206870025895361149508458149584, 147350692, 2004626837653, 2005289127186, 1300127234, 108179133160158920690860847044507911922456635364206870025895361149508458149584, 107671602909904158351717534769826516213540715636056913003433164307203044657300, 163593960, 2005289127186, 2005999206922, 1306326742, 107671602909904158351717534769826516213540715636056913003433164307203044657300, 107164072658867370465528345084506765795905853002316149220344942758837848730026, 180507422, 2005999206922, 2006757759095, 1312030739, 107164072658867370465528345084506765795905853002316149220344942758837848730026, 106656542408408974468973223205686075474953028250585145984816049445215638655039, 198085087, 2006757759095, 2007565478990, 1317831748, 106656542408408974468973223205686075474953028250585145984816049445215638655039, 106149012157678007603540132309545486090063418208828408951615116460554189815166, 216322278, 2007565478990, 2008423075252, 1323641180, 106149012157678007603540132309545486090063418208828408951615116460554189815166, 105641481906776275604493216510132466517291392356932567371277597034182613049188, 235215467, 2008423075252, 2009331270210, 1329472444, 105641481906776275604493216510132466517291392356932567371277597034182613049188, 105133951655693115071659805547209131246348300121487697431811001197546604365733, 254762143, 2009331270210, 2010290800207, 1335324079, 105133951655693115071659805547209131246348300121487697431811001197546604365733, 104626421405309192076133491695287957160221810718003314933143354516652722103838, 274960700, 2010290800207, 2011302415947, 1341196799, 104626421405309192076133491695287957160221810718003314933143354516652722103838, 104118891154530808707845150921528718409420204372159439619436090796727638218026, 295810351, 2011302415947, 2012366882840, 1347090903, 104118891154530808707845150921528718409420204372159439619436090796727638218026, 103611360903853762728092702148783436845102178938782162020106983234228760632441, 317311053, 2012366882840, 2013484981369, 1353006686, 103611360903853762728092702148783436845102178938782162020106983234228760632441, 103103830652791224644633553023834170906713584062759008474462178132339238027498, 339463445, 2013484981369, 2014657507458, 1358944358, 103103830652791224644633553023834170906713584062759008474462178132339238027498, 102596300402112765622285726707524040036725167004651090215623084099156950752751, 362268794, 2014657507458, 2015885272861, 1364904081, 102596300402112765622285726707524040036725167004651090215623084099156950752751, 102088770151503761445189644652752889974572520769070123090989134380643029943111, 385728957, 2015885272861, 2017169105555, 1370885977, 102088770151503761445189644652752889974572520769070123090989134380643029943111, 101581239900721590405546837052849105222252504840794734506386903407128883362322, 409846335, 2017169105555, 2018509850146, 1376890123, 101581239900721590405546837052849105222252504840794734506386903407128883362322, 101073709650068361127701277556869072799946661525850806955573923875251283560304, 434623851, 2018509850146, 2019908368292, 1382916576, 101073709650068361127701277556869072799946661525850806955573923875251283560304, 100566179399088534223053194477135827892333465136428994371033198113648309338424, 460064918, 2019908368292, 2021365539130, 1388965354, 100566179399088534223053194477135827892333465136428994371033198113648309338424, 100058649148566538879611000728350549624379482181888662350147802572474030632539, 486173416, 2021365539130, 2022882259729, 1395036472, 100058649148566538879611000728350549624379482181888662350147802572474030632539, 99551118897875063987180147255080340910191822413768147998542169761228225989745, 512953677, 2022882259729, 2024459445544, 1401129897, 99551118897875063987180147255080340910191822413768147998542169761228225989745, 99043588646925407760701466927026862341657864488577286626427084174548939687980, 540410466, 2024459445544, 2026098030889, 1407245609, 99043588646925407760701466927026862341657864488577286626427084174548939687980, 98536058396235534432442241222262106883483229817304345789243163847819692734183, 568548967, 2026098030889, 2027798969430, 1413383552, 98536058396235534432442241222262106883483229817304345789243163847819692734183, 98028528145429276058146287785331057745311752883958497321109133082816898855157, 597374775, 2027798969430, 2029563234684, 1419543666, 98028528145429276058146287785331057745311752883958497321109133082816898855157, 97520997894662973701130794483762686731340646242838606427083979827943205109711, 626893882, 2029563234684, 2031391820540, 1425725875, 97520997894662973701130794483762686731340646242838606427083979827943205109711, 97013467644071505402788443522497521670149067613428124723835485286064788229079, 657112676, 2031391820540, 2033285741796, 1431930094, 97013467644071505402788443522497521670149067613428124723835485286064788229079, 96505937393425455661077254725504330263843191173394169712605211111136731239891, 688037928, 2033285741796, 2035246034710, 1438156225, 96505937393425455661077254725504330263843191173394169712605211111136731239891, 95998407142619212956893733771015647766137821007029345743187049239879536436992, 719676793, 2035246034710, 2037273757570, 1444404161, 95998407142619212956893733771015647766137821007029345743187049239879536436992, 95490876891726824244903755093386203895286925392023569878036369481421559949959, 752036805, 2037273757570, 2039369991282, 1450673784, 95490876891726824244903755093386203895286925392023569878036369481421559949959, 94983346641113745604145456371289984142327856666340779176299217153384889058530, 785125874, 2039369991282, 2041535839982, 1456964968, 94983346641113745604145456371289984142327856666340779176299217153384889058530, 94475816390366393200967057792503167747829321374857035583159767688415615053963, 818952287, 2041535839982, 2043772431658, 1463277581, 94475816390366393200967057792503167747829321374857035583159767688415615053963, 93968286139585080689009749778641701506612547526069326507789442116865847415587, 853524706, 2043772431658, 2046080918800, 1469611473, 93968286139585080689009749778641701506612547526069326507789442116865847415587, 93460755888805977092172438706356244232014522063148453870942162054893527682350, 888852171, 2046080918800, 2048462479068, 1475966498, 93460755888805977092172438706356244232014522063148453870942162054893527682350, 92953225638200409885237165124541227117947904313540833894911857835741864284819, 924944102, 2048462479068, 2050918315986, 1482342490, 92953225638200409885237165124541227117947904313540833894911857835741864284819, 92445695387431396822335894859752718051334279270756745660129614625935517377384, 961810298, 2050918315986, 2053449659651, 1488739283, 92445695387431396822335894859752718051334279270756745660129614625935517377384, 91938165136681090074740507924876796171272099369944824164386910113277139703565, 999460945, 2053449659651, 2056057767474, 1495156698, 91938165136681090074740507924876796171272099369944824164386910113277139703565, 91430634885924403849286278329927326232632208161183049023316418510689747062704, 1037906619, 2056057767474, 2058743924941, 1501594550, 91430634885924403849286278329927326232632208161183049023316418510689747062704, 90923104635200678031902281270359152929564091489081568521561088103225324948425, 1077158288, 2058743924941, 2061509446402, 1508052640, 90923104635200678031902281270359152929564091489081568521561088103225324948425, 90415574384419560197501607323869329390334252370301222617894122955597460874089, 1117227322, 2061509446402, 2064355675884, 1514530774, 90415574384419560197501607323869329390334252370301222617894122955597460874089, 89908044133671944253509892878211741116661383937902848484688632137309141050524, 1158125497, 2064355675884, 2067283987935, 1521028734, 89908044133671944253509892878211741116661383937902848484688632137309141050524, 89400513882934284366689109909568175654668502389957636941466358121391175100673, 1199865001, 2067283987935, 2070295788495, 1527546302, 89400513882934284366689109909568175654668502389957636941466358121391175100673, 88892983632129408362262930575038545488072500074298227583135359429238492302156, 1242458443, 2070295788495, 2073392515795, 1534083250, 88892983632129408362262930575038545488072500074298227583135359429238492302156, 88385453381504421115759885270926112305233582972723629360138013968946504068012, 1285918862, 2073392515795, 2076575641295, 1540639342, 88385453381504421115759885270926112305233582972723629360138013968946504068012, 87877923130725949793492609161161775927010502585804951807351251138148403723074, 1330259733, 2076575641295, 2079846670642, 1547214333, 87877923130725949793492609161161775927010502585804951807351251138148403723074, 87370392880032121197562914655469190519134532463673375906511043486291432975749, 1375494981, 2079846670642, 2083207144675, 1553807965, 87370392880032121197562914655469190519134532463673375906511043486291432975749, 86862862629242910928564417792020477427189268700670745238688738068381431547907, 1421638985, 2083207144675, 2086658640454, 1560419973, 86862862629242910928564417792020477427189268700670745238688738068381431547907, 86355332378551129212811178029802759264921278615693966302625767660853123323451, 1468706596, 2086658640454, 2090202772336, 1567050091, 86355332378551129212811178029802759264921278615693966302625767660853123323451, 85847802127734235318643474849013892506231683552224736549945631964368442560878, 1516713142, 2090202772336, 2093841193078, 1573698043, 85847802127734235318643474849013892506231683552224736549945631964368442560878, 85340271877028856414749960859298715151240418211100827130240053076889694927562, 1565674445, 2093841193078, 2097575594992, 1580363523, 85340271877028856414749960859298715151240418211100827130240053076889694927562, 84832741626238044013391554233202256760478256670839868550382853389696421488374, 1615606830, 2097575594992, 2101407711130, 1587046235, 84832741626238044013391554233202256760478256670839868550382853389696421488374, 84325211375473236954190419771655346933992878167491098548922721258740314192802, 1666527142, 2101407711130, 2105339316520, 1593745866, 84325211375473236954190419771655346933992878167491098548922721258740314192802, 83817681124798235278309276349432133314231003860648267928975478617636269000334, 1718452757, 2105339316520, 2109372229446, 1600462096, 83817681124798235278309276349432133314231003860648267928975478617636269000334, 83310150874059741901293611466333499635278273315105116669934954550831501526713, 1771401599, 2109372229446, 2113508312770, 1607194595, 83310150874059741901293611466333499635278273315105116669934954550831501526713, 82802620623352035319069011493768483719161838505004309279921326266645114882028, 1825392157, 2113508312770, 2117749475310, 1613943017, 82802620623352035319069011493768483719161838505004309279921326266645114882028, 82295090372593085841455006031921663369314111091197220509274122064035269491590, 1880443497, 2117749475310, 2122097673263, 1620707014, 82295090372593085841455006031921663369314111091197220509274122064035269491590, 81787560121874219843446357722646076419728033521735462684678428582911934176625, 1936575284, 2122097673263, 2126554911687, 1627486222, 81787560121874219843446357722646076419728033521735462684678428582911934176625, 81280029871132166205698898387884157084570454360314711051071563542650889709643, 1993807798, 2126554911687, 2131123246034, 1634280264, 81280029871132166205698898387884157084570454360314711051071563542650889709643, 80772499620391100641856012111786720409532255852058285830691780813577831077775, 2052161953, 2131123246034, 2135804783745, 1641088755, 80772499620391100641856012111786720409532255852058285830691780813577831077775, 80264969369567783299199408271989672817056070226803164323253026102562171367207, 2111659318, 2135804783745, 2140601685900, 1647911298, 80264969369567783299199408271989672817056070226803164323253026102562171367207, 79757439118913802062694043332871333088869809027474702198296575883918860425344, 2172322136, 2140601685900, 2145516168944, 1654747484, 79757439118913802062694043332871333088869809027474702198296575883918860425344, 79249908868125800447406891028047013763204922549560487470729250161224329101193, 2234173347, 2145516168944, 2150550506461, 1661596890, 79249908868125800447406891028047013763204922549560487470729250161224329101193, 78742378617415800793501413804974780455721333987441382492380693619244943414131, 2297236613, 2150550506461, 2155707031036, 1668459087, 78742378617415800793501413804974780455721333987441382492380693619244943414131, 78234848366628638334709617669320110898971246670067294404898797682623676824173, 2361536336, 2155707031036, 2160988136175, 1675333624, 78234848366628638334709617669320110898971246670067294404898797682623676824173, 77727318115868800123724664057532510759255358272687201514628413931282023247855, 2427097690, 2160988136175, 2166396278310, 1682220040, 77727318115868800123724664057532510759255358272687201514628413931282023247855, 77219787865203018719003846825067819850442385301125621459947753271949874756080, 2493946643, 2166396278310, 2171933978883, 1689117871, 77219787865203018719003846825067819850442385301125621459947753271949874756080, 76712257614445928063477442809480003157587809252653832689651745405890837217640, 2562109984, 2171933978883, 2177603826505, 1696026621, 76712257614445928063477442809480003157587809252653832689651745405890837217640, 76204727363699679772743397570493796920456525575969588419473474920677518773903, 2631615354, 2177603826505, 2183408479212, 1702945799, 76204727363699679772743397570493796920456525575969588419473474920677518773903, 75697197112963415480053471023041771336739144625173921367047936408622246303269, 2702491275, 2183408479212, 2189350666807, 1709874886, 75697197112963415480053471023041771336739144625173921367047936408622246303269, 75189666862233952965358044544181191436148475508340239193105913981819830704169, 2774767180, 2189350666807, 2195433193299, 1716813355, 75189666862233952965358044544181191436148475508340239193105913981819830704169, 74682136611472721225902979959712055255360608554700206914325215367092243195620, 2848473448, 2195433193299, 2201658939440, 1723760662, 74682136611472721225902979959712055255360608554700206914325215367092243195620, 74174606360747673574509672095401710931450652155382160962141332756286171534243, 2923641437, 2201658939440, 2208030865372, 1730716249, 74174606360747673574509672095401710931450652155382160962141332756286171534243, 73667076109957764728763095142862509238035235555605707780630435751937273930554, 3000303520, 2208030865372, 2214552013376, 1737679545, 73667076109957764728763095142862509238035235555605707780630435751937273930554, 73159545859212962167157518256011208889667634337803849419332071106539982042717, 3078493122, 2214552013376, 2221225510745, 1744649952, 73159545859212962167157518256011208889667634337803849419332071106539982042717, 72652015608518377251110063396298983803359135933527709611212516152046091043809, 3158244761, 2221225510745, 2228054572775, 1751626871, 72652015608518377251110063396298983803359135933527709611212516152046091043809, 72144485357728091820912002327007258892930148356886103554587376424345676040211, 3239594088, 2228054572775, 2235042505876, 1758609675, 72144485357728091820912002327007258892930148356886103554587376424345676040211, 71636955107016483022002409205759200347605797046284801778399735830350085816004, 3322577930, 2235042505876, 2242192710831, 1765597725, 71636955107016483022002409205759200347605797046284801778399735830350085816004, 71129424856266067663400133743847560376398961244999564886683135993021561735992, 3407234335, 2242192710831, 2249508686181, 1772590360, 71129424856266067663400133743847560376398961244999564886683135993021561735992, 70621894605508242269439534298039612254832455951745469252352656883255494144818, 3493602620, 2249508686181, 2256994031765, 1779586906, 70621894605508242269439534298039612254832455951745469252352656883255494144818, 70114364354788439781793100343237389307661014534211824724544511702863303518581, 3581723421, 2256994031765, 2264652452415, 1786586665, 70114364354788439781793100343237389307661014534211824724544511702863303518581, 69606834104034857337354591289395976989627717029518359043479154125881483439315, 3671638743, 2264652452415, 2272487761808, 1793588922, 69606834104034857337354591289395976989627717029518359043479154125881483439315, 69099303853313095563336906975690498280018599303473703131954980964075727687856, 3763392018, 2272487761808, 2280503886497, 1800592941, 69099303853313095563336906975690498280018599303473703131954980964075727687856, 68591773602557679048506238103834413993599334818473453244899052632167152521790, 3857028158, 2280503886497, 2288704870114, 1807597979, 68591773602557679048506238103834413993599334818473453244899052632167152521790, 68084243351835236036701552768782562978729207008169726283901513313931578064314, 3952593618, 2288704870114, 2297094877771, 1814603250, 68084243351835236036701552768782562978729207008169726283901513313931578064314, 67576713101069556985876406849453941230875012994333414815254041056128382507730, 4050136457, 2297094877771, 2305678200651, 1821607952, 67576713101069556985876406849453941230875012994333414815254041056128382507730, 67069182850365433002060758058466889036763207599558198716481289778998012356391, 4149706406, 2305678200651, 2314459260821, 1828611271, 67069182850365433002060758058466889036763207599558198716481289778998012356391, 66561652599619970998310655354538339091473270161700819799038394187819752697310, 4251354935, 2314459260821, 2323442616254, 1835612360, 66561652599619970998310655354538339091473270161700819799038394187819752697310, 66054122348888220336657016189777207252865050383721931368492460606350188491988, 4355135329, 2323442616254, 2332632966095, 1842610354, 66054122348888220336657016189777207252865050383721931368492460606350188491988, 65546592098133030722816677125622215249408749991200710537164907172265246994599, 4461102762, 2332632966095, 2342035156166, 1849604359, 65546592098133030722816677125622215249408749991200710537164907172265246994599, 65039061847400268052341006781466811368452812762950460219828480163870168968012, 4569314377, 2342035156166, 2351654184737, 1856593460, 65039061847400268052341006781466811368452812762950460219828480163870168968012, 64531531596653947653489254705370631632809599725318754170432946404590289136147, 4679829375, 2351654184737, 2361495208566, 1863576715, 64531531596653947653489254705370631632809599725318754170432946404590289136147, 64024001345905573283511812788430051317106587089944123868485688958963009540766, 4792709098, 2361495208566, 2371563549232, 1870553147, 64024001345905573283511812788430051317106587089944123868485688958963009540766, 63516471095161620999539272166134424568536448960419648292499168292625990087716, 4908017126, 2371563549232, 2381864699773, 1877521765, 63516471095161620999539272166134424568536448960419648292499168292625990087716, 63008940844427652822806744722415772226418334267386800807368718527114231786784, 5025819378, 2381864699773, 2392404331648, 1884481535, 63008940844427652822806744722415772226418334267386800807368718527114231786784, 62501410593684246112305854520808128169598879590888202685781988217261967854548, 5146184210, 2392404331648, 2403188302039, 1891431405, 62501410593684246112305854520808128169598879590888202685781988217261967854548, 61993880342957083529526863666742747434370945094004150747884707707909634080354, 5269182528, 2403188302039, 2414222661519, 1898370283, 61993880342957083529526863666742747434370945094004150747884707707909634080354, 61486350092182694096542424973888059745222828778267871540856496099642411278898, 5394887904, 2414222661519, 2425513662095, 1905297043, 61486350092182694096542424973888059745222828778267871540856496099642411278898, 60978819841438103245558034643754978721576911170864437756622981810785903352594, 5523376696, 2425513662095, 2437067765666, 1912210536, 60978819841438103245558034643754978721576911170864437756622981810785903352594, 60471289590717483480414032079675487125251549922405414867382942765960826804928, 5654728176, 2437067765666, 2448891652905, 1919109570, 60471289590717483480414032079675487125251549922405414867382942765960826804928, 59963759339962519695384245032738223454126061944944904831720799338653484093429, 5789024666, 2448891652905, 2460992232592, 1925992917, 59963759339962519695384245032738223454126061944944904831720799338653484093429, 59456229089252514638678896669314486285666888989825398117424267790016790767760, 5926351681, 2460992232592, 2473376651441, 1932859312, 59456229089252514638678896669314486285666888989825398117424267790016790767760, 58948698838497049534013083774411225049879624692770975397327168943495483576213, 6066798080, 2473376651441, 2486052304424, 1939707453, 58948698838497049534013083774411225049879624692770975397327168943495483576213, 58441168587750791502776320812641003296772495116022774026041758188703485670694, 6210456223, 2486052304424, 2499026845650, 1946535991, 58441168587750791502776320812641003296772495116022774026041758188703485670694, 57933638337024401633249333376375104505436665185893180799859691130435577016692, 6357422143, 2499026845650, 2512308199817, 1953343541, 57933638337024401633249333376375104505436665185893180799859691130435577016692, 57426108086258377885987157725533856149499693037643465061372067845335859972470, 6507795722, 2512308199817, 2525904574270, 1960128668, 57426108086258377885987157725533856149499693037643465061372067845335859972470, 56918577835546102230065778905985889255015731030731002983827719582872148460703, 6661680882, 2525904574270, 2539824471725, 1966889891, 56918577835546102230065778905985889255015731030731002983827719582872148460703, 56411047584794131054193616968311875430438848769473806957850594199707785450601, 6819185778, 2539824471725, 2554076703668, 1973625679, 56411047584794131054193616968311875430438848769473806957850594199707785450601, 55903517334048639945355762429836228009878530892518370527107495218346726522566, 6980423019, 2554076703668, 2568670404505, 1980334473, 55903517334048639945355762429836228009878530892518370527107495218346726522566, 55395987083297742487497930917346966028293113122743642295933385369285224439713, 7145509884, 2568670404505, 2583615046489, 1987014616, 55395987083297742487497930917346966028293113122743642295933385369285224439713, 54888456832560189298861168099822237630875149790264659656258419692297813466423, 7314568564, 2583615046489, 2598920455487, 1993664422, 54888456832560189298861168099822237630875149790264659656258419692297813466423, 54380926581831228734964376132126117968672040585668366586711147731106968974594, 7487726412, 2598920455487, 2614596827637, 2000282145, 54380926581831228734964376132126117968672040585668366586711147731106968974594, 53873396331072305120231851667217007928996855180254859824916960557925226767739, 7665116209, 2614596827637, 2630654746951, 2006865970, 53873396331072305120231851667217007928996855180254859824916960557925226767739, 53365866080341867495463526293723847971332353886712541730164474973397060387471, 7846876452, 2630654746951, 2647105203942, 2013414028, 53365866080341867495463526293723847971332353886712541730164474973397060387471, 52858335829613513841144855508614349390246316191824657901851568627211315033636, 8033151652, 2647105203942, 2663959615326, 2019924365, 52858335829613513841144855508614349390246316191824657901851568627211315033636, 52350805578862843595118768995760637098192681865071927719404684825632780181100, 8224092657, 2663959615326, 2681229844882, 2026394970, 52350805578862843595118768995760637098192681865071927719404684825632780181100, 51843275328125527571993308910182252095439527234457026605724953502090446041137, 8419856989, 2681229844882, 2698928225555, 2032823752, 51843275328125527571993308910182252095439527234457026605724953502090446041137, 51335745077391452415950336986372330035257321933456299167454432741636396995871, 8620609214, 2698928225555, 2717067582878, 2039208531, 51335745077391452415950336986372330035257321933456299167454432741636396995871, 50828214826652158504463149671367264658453276846678494072610833151367035958661, 8826521322, 2717067582878, 2735661259813, 2045547053, 50828214826652158504463149671367264658453276846678494072610833151367035958661, 50320684575900972908021555187894564420838564573862669054972982074475482469830, 9037773140, 2735661259813, 2754723143110, 2051836970, 50320684575900972908021555187894564420838564573862669054972982074475482469830, 49813154325148427078012526178698460703082247076305335053180261543143799005731, 9254552777, 2754723143110, 2774267691295, 2058075841, 49813154325148427078012526178698460703082247076305335053180261543143799005731, 49305624074409821343448354078609443341230933541774463521307757912346743419141, 9477057085, 2774267691295, 2794309964405, 2064261118, 49305624074409821343448354078609443341230933541774463521307757912346743419141, 48798093823682690847548382771126718340467553427005568082756581977013335152474, 9705492163, 2794309964405, 2814865655598, 2070390161, 48798093823682690847548382771126718340467553427005568082756581977013335152474, 48290563572928103252073001030888822551010173857428410501312219743157984295193, 9940073892, 2814865655598, 2835951124772, 2076460202, 48290563572928103252073001030888822551010173857428410501312219743157984295193, 47783033322184034364409669126001865321309805950135397407275219088501751802251, 10181028505, 2835951124772, 2857583434359, 2082468359, 47783033322184034364409669126001865321309805950135397407275219088501751802251, 47275503071449133113726552680585634790410964172180554341967575260859734646800, 10428593201, 2857583434359, 2879780387444, 2088411625, 47275503071449133113726552680585634790410964172180554341967575260859734646800, 46767972820703864892583711260372678152190079848951108221120839711340407371104, 10683016794, 2879780387444, 2902560568391, 2094286858, 46767972820703864892583711260372678152190079848951108221120839711340407371104, 46260442569979513638850712840262522151449454081788512506980775028803704297628, 10944560420, 2902560568391, 2925943386182, 2100090765, 46260442569979513638850712840262522151449454081788512506980775028803704297628, 45752912319227129635128264356333376252594584523871113781711752488587922130294, 11213498285, 2925943386182, 2949949120659, 2105819903, 45752912319227129635128264356333376252594584523871113781711752488587922130294, 45245382068487649749673119934054194704160461902666199468254865199333195435060, 11490118475, 2949949120659, 2974598971928, 2111470676, 45245382068487649749673119934054194704160461902666199468254865199333195435060, 44737851817753575203231093447167658380678377409067999347273888578771356226707, 11774723818, 2974598971928, 2999915113156, 2117039289, 44737851817753575203231093447167658380678377409067999347273888578771356226707, 44230321567008683007282446943707293714929493881942546666613778047870222316680, 12067632815, 2999915113156, 3025920747045, 2122521777, 44230321567008683007282446943707293714929493881942546666613778047870222316680, 43722791316267711659793227854645446060393075091181611398336570571954946458378, 12369180645, 3025920747045, 3052640166290, 2127913969, 43722791316267711659793227854645446060393075091181611398336570571954946458378, 43215261065527428522294004501444032266972198226399814391592233095024503473503, 12679720238, 3052640166290, 3080098818344, 2133211479, 43215261065527428522294004501444032266972198226399814391592233095024503473503, 42707730814791845245460419904985052856034541491937772554081147150528101482441, 12999623436, 3080098818344, 3108323374859, 2138409687, 42707730814791845245460419904985052856034541491937772554081147150528101482441, 42200200564050213707269307990486791607201285709815755923161854116045005991401, 13329282245, 3108323374859, 3137341806196, 2143503732, 42200200564050213707269307990486791607201285709815755923161854116045005991401, 41692670313306820055398378961423159654311748796221135068753457252087226272171, 13669110185, 3137341806196, 3167183461447, 2148488472, 41692670313306820055398378961423159654311748796221135068753457252087226272171, 41185140062560799534064758976145606273097429043313561196070466690228232888589, 14019543747, 3167183461447, 3197879154446, 2153358497, 41185140062560799534064758976145606273097429043313561196070466690228232888589, 40677609811813163621849035600838405359960403492841115560192716960859305808303, 14381043969, 3197879154446, 3229461256300, 2158108070, 40677609811813163621849035600838405359960403492841115560192716960859305808303, 40170079561077200016052571917388006045007760273684205793831153354988101521371, 14754098144, 3229461256300, 3261963795027, 2162731125, 40170079561077200016052571917388006045007760273684205793831153354988101521371, 39662549310345933951100562961331780615445203874955610055557878170825434224957, 15139221664, 3261963795027, 3295422562941, 2167221234, 39662549310345933951100562961331780615445203874955610055557878170825434224957, 39155019059593925053807665285355410886495719103281721740907967573135771031636, 15536960027, 3295422562941, 3329875232493, 2171571588, 39155019059593925053807665285355410886495719103281721740907967573135771031636, 38647488808855491870214545271170196567431942468559105460064196943386713706979, 15947891007, 3329875232493, 3365361481374, 2175774948, 38647488808855491870214545271170196567431942468559105460064196943386713706979, 38139958558112326507153889433308627610233619895161420851722252714121854065861, 16372627015, 3365361481374, 3401923127728, 2179823598, 38139958558112326507153889433308627610233619895161420851722252714121854065861, 37632428307372653088915706789375416375104211264422148633588308689130314626324, 16811817674, 3401923127728, 3439604276464, 2183709341, 37632428307372653088915706789375416375104211264422148633588308689130314626324, 37124898056635203887641492112989149119661684963400832250749512674103369284719, 17266152607, 3439604276464, 3478451477733, 2187423431, 37124898056635203887641492112989149119661684963400832250749512674103369284719, 36617367805890497396979748760029627823735518971077781218351463141569995702941, 17736364492, 3478451477733, 3518513898767, 2190956534, 36617367805890497396979748760029627823735518971077781218351463141569995702941, 36109837555153679949579697715136727183928943555622550896431101518352019862164, 18223232385, 3518513898767, 3559843510423, 2194298668, 36109837555153679949579697715136727183928943555622550896431101518352019862164, 35602307304408842192095389219966885451602132840382123936496305128092829011917, 18727585356, 3559843510423, 3602495289904, 2197439146, 35602307304408842192095389219966885451602132840382123936496305128092829011917, 35094777053669755076018930257610238078103525206108507803020665400642418338396, 19250306463, 3602495289904, 3646527441337, 2200366510, 35094777053669755076018930257610238078103525206108507803020665400642418338396, 34587246802935381810555394535238615911056058298250191745962812447735301605735, 19792337106, 3646527441337, 3692001636057, 2203068455, 34587246802935381810555394535238615911056058298250191745962812447735301605735, 34079716552190182166946806878549920018634986428193095053564175099104735183840, 20354681808, 3692001636057, 3738983274682, 2205531753, 34079716552190182166946806878549920018634986428193095053564175099104735183840, 33572186301447813895841310052778097200646780007932443237826915818950582435738, 20938413450, 3738983274682, 3787541773333, 2207742150, 33572186301447813895841310052778097200646780007932443237826915818950582435738, 33064656050703159919553045601403520614192787028386533312872234078511867744935, 21544679046, 3787541773333, 3837750876617, 2209684274, 33064656050703159919553045601403520614192787028386533312872234078511867744935, 32557125799970380513998623597431276266049800636369668364968256428542764368126, 22174706087, 3837750876617, 3889689000358, 2211341512, 32557125799970380513998623597431276266049800636369668364968256428542764368126, 32049595549220633614625365600305304251742786213251007069951947194279531582712, 22829809548, 3889689000358, 3943439607399, 2212695872, 32049595549220633614625365600305304251742786213251007069951947194279531582712, 31542065298488482324182867500638699727176754279527871540754376644944018986262, 23511399619, 3943439607399, 3999091620303, 2213727873, 31542065298488482324182867500638699727176754279527871540754376644944018986262, 31034535047747888650096513214444190345065525005409559876843142532974254058422, 24220990261, 3999091620303, 4056739875199, 2214416326, 31034535047747888650096513214444190345065525005409559876843142532974254058422, 30527004797004503247968686314989062066935749746825171703615333742783794216289, 24960208685, 4056739875199, 4116485621680, 2214738167, 30527004797004503247968686314989062066935749746825171703615333742783794216289, 30019474546263024984357341959756816009181773290432453949362747568151465087987, 25730805866, 4116485621680, 4178437074280, 2214668260, 30019474546263024984357341959756816009181773290432453949362747568151465087987, 29511944295520843547533617342687914931428723217745094482309537407165988873946, 26534668238, 4178437074280, 4242710021848, 2214179135, 29511944295520843547533617342687914931428723217745094482309537407165988873946, 29004414044783545597714819821124108108393408595359557873160083138159236746854, 27373830711, 4242710021848, 4309428502045, 2213240711, 29004414044783545597714819821124108108393408595359557873160083138159236746854, 28496883794039842890800842946032480764032379793180779500119068094686092932719, 28250491190, 4309428502045, 4378725549217, 2211819984, 28496883794039842890800842946032480764032379793180779500119068094686092932719, 27989353543295653064784092761374758062798028252925818476563360818219587614442, 29167026812, 4378725549217, 4450744025144, 2209880645, 27989353543295653064784092761374758062798028252925818476563360818219587614442, 27481823292560292381289993677113638425483720612674289607466279132779500769056, 30126012114, 4450744025144, 4525637543577, 2207382672, 27481823292560292381289993677113638425483720612674289607466279132779500769056, 26974293041813631821229489672048177463599083574748466689026852215089072399780, 31130239431, 4525637543577, 4603571501134, 2204281846, 26974293041813631821229489672048177463599083574748466689026852215089072399780, 26466762791074897483651044330443252281895848531726230072109109021436477269793, 32182741822, 4603571501134, 4684724229148, 2200529158, 26466762791074897483651044330443252281895848531726230072109109021436477269793, 25959232540331871433643992289380477561588032558049244605275010289720403270317, 33286818907, 4684724229148, 4769288283309, 2196070136, 25959232540331871433643992289380477561588032558049244605275010289720403270317, 25451702289592981214759334876102796381869333901414473675700278958102461554473, 34446066041, 4769288283309, 4857471890760, 2190844113, 25451702289592981214759334876102796381869333901414473675700278958102461554473, 24944172038850299166551591089910110610622937501775938159321617551889602742318, 35664407344, 4857471890760, 4949500577511, 2184783266, 24944172038850299166551591089910110610622937501775938159321617551889602742318, 24436641788114291095584505582501420503727128292543235205689003469024338815478, 36946133169, 4949500577511, 5045619002969, 2177811556, 24436641788114291095584505582501420503727128292543235205689003469024338815478, 23929111537372629437263940855342246757922284595533670588922370241455319961896, 38295942727, 5045619002969, 5146093032971, 2169843422, 23929111537372629437263940855342246757922284595533670588922370241455319961896, 23421581286630258044769810408914707220858999591980467728741923649073188007528, 39718992700, 5146093032971, 5251212088326, 2160782239, 23421581286630258044769810408914707220858999591980467728741923649073188007528, 22914051035889444818160627997760015701449816174402231214679276367261963076285, 41220952830, 5251212088326, 5361291812535, 2150518465, 22914051035889444818160627997760015701449816174402231214679276367261963076285, 22406520785146155030294797847002483375766363747163388142020930300191513582980, 42808069669, 5361291812535, 5476677110468, 2138927252, 22406520785146155030294797847002483375766363747163388142020930300191513582980, 21898990534408128226970578796219015569510400714787207881658546886814017485613, 44487239903, 5476677110468, 5597745619623, 2125866051, 21898990534408128226970578796219015569510400714787207881658546886814017485613, 21391460283664901790727967914041083602908970612787642782595432069905409880306, 46266094949, 5597745619623, 5724911687529, 2111168249, 21391460283664901790727967914041083602908970612787642782595432069905409880306, 20883930032925174615371492309322372007344414466033047196054744914703721161113, 48153098870, 5724911687529, 5858630943575, 2094656278, 20883930032925174615371492309322372007344414466033047196054744914703721161113, 20376399782185529084889600312563905082438661697409072948778481544442678677085, 50157662093, 5858630943575, 5999405571524, 2076010459, 20376399782185529084889600312563905082438661697409072948778481544442678677085, 19868869531444484057858747122268665885079198349899002239881089198682171933533, 52290273934, 5999405571524, 6147790411300, 2055579520, 19868869531444484057858747122268665885079198349899002239881089198682171933533, 19361339280701796586503169259616765207598746701235794164145451259208342964800, 54562657635, 6147790411300, 6304400046307, 2028663952, 19361339280701796586503169259616765207598746701235794164145451259208342964800, 18853809029960655290981553548900905390421098946860265050229008396145894880962, 56987952419, 6304400046307, 6410000000000, 1290320269, 18853809029960655290981553548900905390421098946860265050229008396145894880962, 18526734277970591267771357601390065256523197546502490246313213441266100742389, 59085116079, 6410000000000, 6469917067130, 707905984, 18526734277970591267771357601390065256523197546502490246313213441266100742389, 18346278779219825533154782770845454529326805977345849816164982403051673271918, 60420593962, 6469917067130, 6474122807018, 49533522, 18346278779219825533154782770845454529326805977345849816164982403051673271918, 18333747462573706123296661038319860998813092516874102629594785050510360736816, 60939804547, 6474122807018, 6539645390071, 754653660, 18333747462573706123296661038319860998813092516874102629594785050510360736816, 18140760647179309983682089167826071917999612483627193442288782982677999797182, 61511518444, 6539645390071, 6606612903226, 749387972, 18140760647179309983682089167826071917999612483627193442288782982677999797182, 17947773831783458603146185887135142408635954137994127424399554988936676130913, 62596378178, 6606612903226, 6645101745895, 420777086, 17947773831783458603146185887135142408635954137994127424399554988936676130913, 17838748528479438313730650937234273181915184278841475914853082734478435757852, 63461525740, 6645101745895, 6675072463768, 324368924, 17838748528479438313730650937234273181915184278841475914853082734478435757852, 17754787016388806538679890126759386043549763287206848069331640958427969506756, 64025907442, 6675072463768, 6745073260073, 740931368, 17754787016388806538679890126759386043549763287206848069331640958427969506756, 17561800200993665330905079169789340341764315211563423591290849120007189445397, 64855925902, 6745073260073, 6816666666667, 734388701, 17561800200993665330905079169789340341764315211563423591290849120007189445397, 17368813385596540883183443325705570835796119208083134742538922578657040505622, 66032946220, 6816666666667, 6830803410465, 142237830, 17368813385596540883183443325705570835796119208083134742538922578657040505622, 17331218277738707196189657117800002071510038933843067431880700724358809945120, 66745106924, 6830803410465, 6889906367041, 587683093, 17331218277738707196189657117800002071510038933843067431880700724358809945120, 17175826570202419431702550816764361339317404463347467500493673633706447003543, 67360304431, 6889906367041, 6964848484848, 723879374, 17175826570202419431702550816764361339317404463347467500493673633706447003543, 16982839754807609546795847736110456535821787385057303209001349740685803819378, 68487758404, 6964848484848, 7027973877427, 591715279, 16982839754807609546795847736110456535821787385057303209001349740685803819378, 16823688026999047574588478088516175555985927902263294996143467803052663434835, 69652085879, 7027973877427, 7041551724138, 125821355, 16823688026999047574588478088516175555985927902263294996143467803052663434835, 16789852939410676832008186751813017292944024762985652943380302031610427893198, 70299464815, 7041551724138, 7120077519380, 712085131, 16789852939410676832008186751813017292944024762985652943380302031610427893198, 16596866124014944788677135245824486049741822517229130549561151799172173364950, 71086072098, 7120077519380, 7200490196078, 704063564, 16596866124014944788677135245824486049741822517229130549561151799172173364950, 16403879308620817341807315357583251209279057813988082282418932040238243483797, 72442741703, 7200490196078, 7237683392161, 317229117, 16403879308620817341807315357583251209279057813988082282418932040238243483797, 16316157776257732296125933685228282499572449242874453803915162465358010467636, 73447933363, 7237683392161, 7282857142857, 380625355, 16316157776257732296125933685228282499572449242874453803915162465358010467636, 16210892493224598058861203193029243736374708765941510744798291339494507244377, 74157088883, 7282857142857, 7367248995984, 691028669, 16210892493224598058861203193029243736374708765941510744798291339494507244377, 16017905677828595207761592522639578600208426593989399208345612529154575191581, 75279208848, 7367248995984, 7453739837398, 682019207, 16017905677828595207761592522639578600208426593989399208345612529154575191581, 15824918862434037598411031141574270834543636256092438833859546884236282875740, 76762514263, 7453739837398, 7461139639404, 57197760, 15824918862434037598411031141574270834543636256092438833859546884236282875740, 15808627525515449218203504424851044578591220236128535332786480442584235490406, 77576260176, 7461139639404, 7542407407407, 617463814, 15808627525515449218203504424851044578591220236128535332786480442584235490406, 15631932047038562098372235630100194385872059497581543667219983519304337589802, 78355692715, 7542407407407, 7633333333333, 665291523, 15631932047038562098372235630100194385872059497581543667219983519304337589802, 15438945231642857984616326336179301720901405660772988978678736596711706361808, 79868779165, 7633333333333, 7699710537247, 468837287, 15438945231642857984616326336179301720901405660772988978678736596711706361808, 15301097274774606022867797851390700461194620831018002816131030423547741305570, 81255065965, 7699710537247, 7726603375527, 187256146, 15301097274774606022867797851390700461194620831018002816131030423547741305570, 15245958416247502957224747726990082229307024473975166762377286310867435689966, 82079519288, 7726603375527, 7822307692308, 647430601, 15245958416247502957224747726990082229307024473975166762377286310867435689966, 15052971600850492935463949321299022439868690417736561252411912880723088483414, 83175212309, 7822307692308, 7920541125541, 635299823, 15052971600850492935463949321299022439868690417736561252411912880723088483414, 14859984785455821832547389074583062229040182950404265327099363835306643793935, 84909187301, 7920541125541, 7954951723164, 215654243, 14859984785455821832547389074583062229040182950404265327099363835306643793935, 14793567024033754094062573203394735737994058717764353486076038196930879676158, 86095865772, 7954951723164, 8021403508772, 409799726, 14793567024033754094062573203394735737994058717764353486076038196930879676158, 14666997970059918921127789845231393357477412275624050503840610753502570515795, 87007442613, 8021403508772, 8125000000000, 613991662, 14666997970059918921127789845231393357477412275624050503840610753502570515795, 14474011154664524427946373126085988481658748083205070504932198000989141204992, 88551242231, 8125000000000, 8228639898899, 585073430, 14474011154664524427946373126085988481658748083205070504932198000989141204992, 14286036773293946774412432027420741588276948291654816145866117708203161628281, 90438864082, 8228639898899, 8231441441441, 15789908, 14286036773293946774412432027420741588276948291654816145866117708203161628281, 14281024339269786967670452609886496781656957943551641761309020782532521864014, 91406600803, 8231441441441, 8340844748858, 587661440, 14281024339269786967670452609886496781656957943551641761309020782532521864014, 14088037523874248983131009364823550984636157187247905845010921181838335254092, 92444034547, 8340844748858, 8453333333333, 572506792, 14088037523874248983131009364823550984636157187247905845010921181838335254092, 13895050708478507373341037621319029001467081653997233325049590313713222146829, 94492085358, 8453333333333, 8522813544898, 337539381, 13895050708478507373341037621319029001467081653997233325049590313713222146829, 13778506522552887730228791044073392229900044215911265036681779864154497344656, 96176785072, 8522813544898, 8569037558685, 220083762, 13778506522552887730228791044073392229900044215911265036681779864154497344656, 13702063893083149893060934784177615956296996624385461993214874840650187104022, 97254055535, 8569037558685, 8688095238095, 542206744, 13702063893083149893060934784177615956296996624385461993214874840650187104022, 13509077077687269896302309668693468125710412430266276558438430496973191350573, 98808470700, 8688095238095, 8810652173913, 522097027, 13509077077687269896302309668693468125710412430266276558438430496973191350573, 13316090262291429946489474511746117465580925983869365095350008838247466733826, 101084259177, 8810652173913, 8839822977139, 118872124, 13316090262291429946489474511746117465580925983869365095350008838247466733826, 13270976271811128793862717419009084622433503103386398775208984019339526398898, 102512991695, 8839822977139, 8936862745098, 385256654, 13270976271811128793862717419009084622433503103386398775208984019339526398898, 13123103446895894565140876429068314430397120141169897896540208789843207966517, 103717817248, 8936862745098, 9066890547264, 482472020, 13123103446895894565140876429068314430397120141169897896540208789843207966517, 12930116631499842946428393493200405168674706182018816214896810460021882972894, 105891541173, 9066890547264, 9182392346833, 396677695, 12930116631499842946428393493200405168674706182018816214896810460021882972894, 12763446021070647113800786696107963485111899373755068465877961413049603509211, 108250764533, 9182392346833, 9200909090909, 61647801, 12763446021070647113800786696107963485111899373755068465877961413049603509211, 12737129816104910427960518695241601011920524839777421582926159684885165246386, 109539051802, 9200909090909, 9339102564103, 433701403, 12737129816104910427960518695241601011920524839777421582926159684885165246386, 12544143000708655107323240996115505271397726002883419072478466567404176276802, 111070432519, 9339102564103, 9481666666667, 402236956, 12544143000708655107323240996115505271397726002883419072478466567404176276802, 12351156185313283305547074943100421116473641906545794503065596780531709739276, 113811945810, 9481666666667, 9553697044961, 185534468, 12351156185313283305547074943100421116473641906545794503065596780531709739276, 12255915770330473304168454303651809407626001767993489956303830910901895518228, 115912399357, 9553697044961, 9628809523810, 184973507, 12255915770330473304168454303651809407626001767993489956303830910901895518228, 12158169369917585834100200900369034306865951832215607311918652730889602669731, 117365494225, 9628809523810, 9780752688172, 333530880, 12158169369917585834100200900369034306865951832215607311918652730889602669731, 11965182554522727279649216923190535145744834462897881971488228122562042469812, 119627768334, 9780752688172, 9937732240437, 284404633, 11965182554522727279649216923190535145744834462897881971488228122562042469812, 11772195739127338178737045163043367871902980204873881066781741845579756268979, 122714809917, 9937732240437, 9957461170062, 30947275, 11772195739127338178737045163043367871902980204873881066781741845579756268979, 11748385519589188602235838319967036374988487946810017877674418860480682253346, 124478128791, 9957461170062, 10100000000000, 199454129, 11748385519589188602235838319967036374988487946810017877674418860480682253346, 11579208923731619542357098500868790785326998466564056403945758400791312963993, 126126874296, 10100000000000, 10267824858757, 135301477, 11579208923731619542357098500868790785326998466564056403945758400791312963993, 11386222108336162811846087398755975796560738865353245692907159603301262986497, 129282627545, 10267824858757, 10398081400337, 30260, 11386222108336162811846087398755975796560738865353245692907159603301262986497, 11240855268847950941858688158878509838538294968316546568601549553789514416814, 132326355070, 10398081400337, 10441494252874, 6178, 11240855268847950941858688158878509838538294968316546568601549553789514416814, 11193235292940088496472625549992802400544245367317170365561056948123690537651, 134105498314, 10441494252874, 10621315789474, 1847, 11193235292940088496472625549992802400544245367317170365561056948123690537651, 11000248477544705552343533450872061879022021718063390399452619754290975642837, 136429264952]
def RN : List ℤ := raw_ints% [30254651027231986546955053520018104328295516201415528357068413868021705171494498559749726719943921478684639585812139972427529484304474891777473469394972464, 58629346316250143888350428799013761894119163475130860198661295166768725612919518757543430317771234615384300612417034307325695840972565666366305488415462398, 85994455022939000437108845181126336992647891848167965702871951349425096433261415890157285633745048156911790575256486786818364403076405423535786308320439307, 112695806362060063683169155405431674144972234516506785401414316635894585044308394711262846253142081270826527719707448936415018528368289088795696880750712447, 138907694767420277701834995068254873776691092599757057001776831837246191115722711700364566533956939592209187395364259537044038581164693667522866033709509874, 164732952700984236852652070665387718741726848219795890158304754553787570971913128674751801088246467990850024490455175891714201168420694895005076646109272393, 190238913108109416245926344946568670470109311400598646549002060817569013481402351076108226685191910448389686505866421297579783331998419343265464501563417133, 215472949670441076992455722429294279871574050903065290340821523050273442293803012664569033297731611437115018935760273923083691915157066423489185696404511620, 240470168464140165247827033982005534997539263179755291285086268390523544685701452997190410162213682107106839449812820467367509487520538981546970334924761614, 265257617965972516874340835762426462675443245590297254582638527633146284356394871528733706700823741344933976413785021258888913482030473928843195160434539277, 289856776998906056106739224385655506880532372536048617069641347111885125179847730501039127854603726538841830344256984192070365739717577688934416227642362696, 314285116017465563038794044560903565788757961010712224497331244108394698665790050701218415652154372378199185635395650008453758439965432192350708750528388663, 338557125226660661011274328960302054341975915399766384378414258515507146096014159354163303310738497095511391961652066703502219400024160031793468799017022183, 362685018810786036115217236967718364490238037796189461710311414934353602896985600195660280516239739730890356270898145152998784924770430499704242360870254739, 386679233370340688043976705977067019083665713922805940310220841084729052046330052838877631250857277365444731208736314078484187174264944648401496509102040127, 410548790585799576898119351421857790284233772939124180022518692252818884633465495005647636199080130109980263690079638597017227848832577074128820534620135933, 434301567390602083979299083452122050117771849718433060079554481036777567292706814021779898528944263444592466886195821825415026072781688034854364414661638132, 457944501380972016428219413024214858548581745037891729197205722352247169252683114889360284290775817543064718800388922339887681637998526506775760725891634758, 481483749782170331385847958424732703202036835059744878279402701593775722844071125025943462331947572984937093123908380577028491185418339512144010117866406590, 504924814405174123349872087969212990591768786441171666701416061073243488941868604728424847033917424254320847108572711187971971718784722146062426738515215501, 528272641235246212312397920465382557326498709351743718817577051009592829399754285114637537428131667345521578081451058428400424059851754798988775996783335045, 551531700785396327741219599222944096513871669804045940890836470104828236915162554018702798795870698533568291761958379234475282095260463789917055767447320152, 574706053649610480166974161075263757739559699599308337478275974662446277954062897317698465940828203860862922740532523385096105354969138362602623005320195076, 597799404517041574851247377049348056965867329716059087236559210910771802220620578757551577104121608889813376228664370358460201183315379027336493159006933683, 620815147081847422790390696198491046436403350497629091098504626107477433519027978779642278203030667163837664325275150218135332788282437225029785974995494571, 643756401691421456260916958802539719618871486901764406539148038021602634911078347779476921154360685096739373093499938613532360694942823996541565235349975290, 666626047145260300733465102046318383378656827304742459403370385092906647998052478289188729171647968084225808426095348898358644148452553786768954434778600334, 689426747739207928775571032089873234240342760113373965629748627574935482545893181473539471138236302757856449661834346201963306943028829467663647059069878776, 712160976412627935940456115293317259933839116795529939731683666501709013615528972789648026207097936136254116858582525207990622804139648119069616239080056500, 734831034676766327544474367122552371952260434252624373453001721607509294754548630519040351650311923608308288948679492264783677016901368830014249601237267022, 757439069865562752427173921979572796404514614535213145843107593435510743954418833206746167015403713617235558270186671127827538633083860374749133313047377887, 779987090144417833153753059952175364530379378358542142224224650205876665349249750446895563145633774460456884152230306628941379523424350544938901291151557675, 802476977630033343731032415528302008225289542506480483919974459709695445519202822182805682304794105322427541488748649832681541117895367348226833725938602646, 824910499909691172294493833222658730911877242822899322855161850553828385883120893560588920273994064867805357604732735579324407537832648326133199860189638314, 847289320197036044274788980080656654599000519105990489759740774849474642605120466314824083673143678409085426725060679037450787321000882729129273810960495902, 869615006320473496869288306037127040993113911192144186720705145614842071336634338004237044030074855170434089686149264840113875095343847091823211406953674382, 891889038707368990408028879055446133442505085294424565907480577482882610433224668836812093392177502049068513280039328705952782770843349246020477272019911829, 914112817500585972493132716060322272766804922862342827880020710742621330605966806253040955765855447106549986669319121925709539928400272035503735886310510280, 936287668922197941436919110856859059671962682861445158918951432530620932585546792594806470861890903258964080907178192501348040640624831685747948338077790512, 958414850981429825753283646664853286384907483571052034029303735630932850654979995741739238171924554641751503516337018740057543519933970519982628466024092059, 980495558609236879438383447166620959602699263231206243741054617535008062025176846424955446559527026169277132917172384579196498734262307836770559814078229709, 1002530928289799195154619605032346777300483606650156448446478134734885376374306040138111922295080867879524735853363353155064138725320547696663371872311834919, 1024522042249114148553258147383808756629680184595733572763074588570427632927382325473852188433281432516742345228106616291139218927631207272304088197326385333, 1046469932252426643916194069854292486414242960348603370588514383225786344881950245352855065088596551342771931287878133301818206070750588158453443234769011249, 1068375583055145426779283891064088064214916952831103470588726975835102667490025783430164629371784052756085554548043156280667213961644032357596663191425111579, 1090239935545911354951607777846190117766419984734719353336121902067602973351984206757866979648532153864673942601477528990277518141822017656985736485085820498, 1112063889615416337709844439510248124683653866659568862856276457721332497668392587491406987408544366062655422544994674003483675843254146481230799930130600605, 1133848306780263009374605725491525829817714642209690081051521516392937655928184553957295343378793249893274072492260413446345170933941195677336736407824315453, 1155594012587477989230165180678313452812645928767875615948860666963626682562457032128893133926449872742798635029615637003339033411254589871318183504309304288, 1177301798822142165372405473186069086992203700943204255450371640746565744829433974637263828931522194389510804894072206026622446334386338215073808369047774852, 1198972425537894951832343369655263414873857820336022328474840100149866941508213555376457158900169987734538997472133526521279486316867011235899659808432755678, 1220606622927736089652118638233221892525032378714990649237261664370488813213585846015348647433444255556733797179510876494473100130294170194309691028186334588, 1242205093050530622484839952582131145014585925749371911902577737205525962950482728653149758857849683376924810457539099092488630506223670361577215932387303040, 1263768511426872346460022430980762769732886755609583751066709007329820288622860763474025607165520013527035033036534340403699523444088346053928313679098480050, 1285297528516438492961806442791290617435888229831312698802818289092780568039164995190749523010924161563339608490333595605892601518588100487201813859975993278, 1306792771087640378203432637729197188779421133650690337023882922322725003261757051956117187097630221302310744888819879673988345577589180724938096248400668025, 1328254843489213343155288354259579453255046150228765058481026169223419811822587591138297539063237704811773448700514884836983100884770883040376624654574246633, 1349684328832371034310465585851156357601128864858312668498682163301079671742072353509602286516620824657682367673226139321612929039062490194217339711768553114, 1371081790091254121115424973618221172509666641350088152075572120876056624151254297812760064107730520946168466275274166737545193932697588922760892605874256510, 1392447771128615126365831775732196835646276158865778467707616482454209681539462868183693893831537133245871508317531475556385828969752762382622329463996237802, 1413782797652984905632734297187186470032828855671102325240247143274586396098042340076976608804795324716139346069154488112701157155391283972892007733775075428, 1435087378112950306395846869024584533812220479020892468790470297240940539260883942786346469629456763642563778999577472970264499187673340866954319128767839466, 1456362004533626292038877996523500524055134414401116471445147082197875791950702849894683887355477774647708022453431950855218586609912862012091250522149412130, 1477607153299920442722267689847668515589887713025979729291935263435842342512287214337717222897290719782566731499238042223278385630158338592545381794303591418, 1498823285890755611094587180837334814049585581719122431078593580855345117827551643235611095203340942641435771745949859982480943843421747078007874222586585105, 1520010849568031043058538967980195890775014058341945078566333735289435111581885330223460126142578195385920350137606981916536952656133872546341442273641908822, 1541170278023757798850242606328060471556295772202047105542410261933739285127286029172760653672569728101544236415885274681238565185995657318945507818168594405, 1562301991988495918568612018787520120279444872364616485472233471088194773137396638744252415411963842407280032203209501218920020437016617044710270401896623335, 1583406399803944211800484679054275707207464916535192988679371659496147387269967621799039381365697174219193485592339185263942294992042535684687290674596686600, 1604483897962285112900392003170566626788007990382271612734042651148152581795490450912366220237405732515074298268843545499463587076025229299387844099514946368, 1625534871614663508727955149483585678371067111719899362335348357060715237344053520407395974572307415452527753461901176362833521840053430430449521988657506802, 1646559695050977000884115774040946579389663746359904028164944455095459781246671334672935697723729139618631015271466618421531058541748503465193535145807129176, 1667558732152973249037514388715133638656718751064907317482263261065785545797707368371925859603248283678284896161529487310481897422468113179441437186667824109, 1688532336822485699313455533540191147450158616150086670696716328129272262907318186084894705399047869256194597332333992607951337886816272394515551739265721221, 1709480853386490238422662518466005371843365992793096543890710540055164769231361522112293963999464797606213187817268391013789472197474458688410422622741942893, 1730404616980530464538898692323371282355802503887277153436638235092605640451903867769208522308074358937608506520350634037525786817626664829514011996408417443, 1751303953911936861949806638438984996593933521439690999508361553535246677387739782629502233426302068843753195240595003675613549156355728414497753118450786466, 1772179182004153912261604581291736969147592055425101523829569032099357782920931000944759166406045043841582206608453031741914848272941322537851776732460960298, 1793030610923387924385001804233192322002021424855718910235654244531182154090291188101517732951075256064951603382833088417488110055485369400736327289531095471, 1813858542488696103485676100624395583121596160245945371685530074923753609968864838178425663942421488206066086711996130174395213021483253674921201109007702736, 1834663270966553204836409267600997084065779922276111784064336896262855938466390865928639191065819599714887634119938652693530039254802201503649866152482435748, 1855445083350855231651024842126772541228112504215414299420522492645628590317205709326578461954665665108527423452505754527905303388617987205860920394685690344, 1876204259629249324145808983819097667292662220856366276264528683999857047487314116821439159251768463400215035143001363109233048173858334252408216623852723390, 1896941073036614615304759696541867703813819615930468611218000602421445425041956836332079438919287497972108857782242318540909927491272546175905522984882422032, 1917655790296459830336427196241167731289382829768094648510824661348636727293053948411603638767039455358073718989897766386955605651431823107878834865720843542, 1938348671850949274952634642457283593242098111855839112033460649530563063737107762179271228910149241717731490977281905007312095842576942040179467111543200774, 1959019972080219138850416663103468069386089901169274039687758490489125727379424743327465854732792845256664988489272078696074524222617281337655310235791663821, 1979669939511600328622961989908711720477208148278829986079120308978592291681838902910222512523560720828658927880946347306007796770506408870376649546756765843, 2000298817019321973902632112455779616335158657161730358895769784971485768171470575048450488285212909837727913693117684171173055587292778399688117754153693677, 2020906842015230993953397591567470406888828729126684697292703906269029743113232584980248644335663383991454241175676456299214239088172960387083668571318825181, 2041494246631027374134748429948445172015333402424343693656700888685219817224054449115942175749812764254368960562037595569788357501216938815805708149986895949, 2062061257892481816840193949884778874631788842938432362616546558303035404919327424399366515055056505835155271082131095154662969751145694535844666481569024584, 2082608097886071959905685911789867275133500307558162119969804687454035315108432408851930145664824092823087359823097909969820321054374532404760376403938369194, 2103134983918445180564197052575076883351972727061728965397465753610670464683974203786847481670948864394014025950457743428980325289600086493718404596456614116, 2123642128669089929035324814136290843636578979699240337861072098570690590059293643691413737774450126375649876220263453906738986218868754808374977766885810541, 2144129740336573385601986777778080458607016819321595851052732615505433453647192316919839442167079166385097961775968415547973532861114987159018373377742123371, 2164598022778680847996226994953618321229812201053431101727366237763536636012301116883481627658460565276450889965665936846954760036608743469972348330120633716, 2185047175646771486468279909424804769714989788538162494831207230503386881257594503694173813092843603100193304501785730285118803906505129181609865158969141161, 2205477394514645819817036434688417990788343894537688976083511542691192057346176401858248503398650660620877569153969429951073643192943297256831013049311975224, 2225888871002202346724695885716861814481673060605690678530562938520072185916213818223340885810413487061230206440132659476138036825764639624315103238079378626, 2246281792894144103605648873143084742861413950265338488069508864167088455276173146432442274895309977404200890561747330000665193700117121006182027819143378623, 2266656344253980413250405652268603217713098722902532574443984795672086423062789844543980418984846913422554692292125187162650841355664673174109987124785509481, 2287012705533554647021200522912320818165782756525853314005693022446211388532867078353840793952038829550659324647818106934617696703723614198227504322939210036, 2307351053678315364383214370683923599183439242493341524849915565043827709461983409118078670823739255010794746362528923880852093842947097937434141678888522872, 2327671562228535641460439489323597402120166078178404019846015861555524566863004111290252811783934228924155311438406280189642194796579480547419060047230081659, 2347974401416673685909362210154419461963100446287252059447153795249468941927330920507990296411946638377712990921162749508258052479979430039697092574233260933, 2368259738261056895409555804420718412268106767890955037280739416013305301287270537264049502841212493808229055554834307531573716793288561449975028351006164719, 2388527736656061293511606958417506354841018153192151419949535145400572338219199432513676116977370719918652382921965324217154960744347999817737874596730469725, 2408778557458948716329848236232666574535887249140510931368947144219719378852059840697570540337204012765227795468469949736727369885539804867402004804788218628, 2429012358573515177882758363034407524349289357889658884872742266827765603337240818493782692716256725464485247716016098382405955258883207701549095564631485433, 2449229295030695466022722222105454663173289336248187699268885498264700535409176447593927661070476405931050964607097847878122455204992590681835190411904005228, 2469429519066261173746533370416177964846515122498722111292535789445888248791368358236283139985871922158862083364883088914121243560213792228083927308945537029, 2489613180195742014433578107795312808890001889000791107820840905510797790826806703104422866753407201134022615162804620102076429470320536514617922422642990911, 2509780425286693369429570248236885248876756353906327204946774541930155935175209499354873783360692381864968804565723522695247395983751399523616385283568329796, 2529931398628426540339260604117730944984347994472351496208042775779431409099534161919075782118919320394473502019338153508058500597033158299743652962138730632, 2550066241999312096881315279798219623387942079872644285689955892367607749960022890630666406771289164230829313072827081284100740041426328323737659845554595388, 2570185094731760996955801567273549817967686454921347926814743782874204689842995966980892092830457109943660945529873017597116224208158572497752453504527513511, 2590288093774982783540094373806346697372128750147703408213082647919770015783623759768458385816205047379164827892711363485379718503279979887004077053323771149, 2610375373755615109942616558803144528961664107468926368974178155966658416463865259702699312043391377590186782954811294863908026017337557353660877916425285888, 2630447067036314089343708965263048178352532637146541486045639496722444440181222567480531458819746978314266400673544567108885943427106947190802893254142367924, 2650503303772390486588442404393653798708493536555852248621031277988502398538595685008896616117096320377358107870201175219445057380272035339495664689166774304, 2670544211966572551494669770047551779923716762105588792082250457120258887693819937833639666283985467871995870372101174037466753027191894577526170931789136907, 2690569917521972316485111715468171357777093739484303509580833490601391818162806168575709650475709950687064149873032618934928184640386010838049955822235020960, 2710580544293328431375098393775346949780268745051472692475237344119110751505951386453870506928854913316045840059887318667024633081574001926627450728285234209, 2730576214136595070023748429957412381369331690616836993703573307267217791657428083893618876594205000316428485746334065179290205104064193996722614774226398345, 2750557046956943103715772431745062391607001626550140976628505570295627318492326168680591488074792507705632326464490718816085344932590409920186973198136116048, 2770523160755236581983851543807135168506866370442120966917915950453554786818231513956845946963859971926493078333138636083417758462486625237017292253922833165, 2790474671673044581401492955786066125616167834434798858561554817757417715614922903774009187333672759283547281783916706571542219678517367001453018578578118496, 2810411694036245665791065260530496894477383968634367090499713148664605755093576554612629899919704508902966500375192770845968281707292161264512044447753973573, 2830334340397279537178933468374947905055205000360482186879257803702608798994084910016736329188471743834985010789877633191729184456337965971391325410198850079, 2850242721576097936268207143343182575355577284612779887956610034078360292472922517190480660252993454172367536232146815019360544551089673203801129359194186393]
def MiN : List ℤ := raw_ints% [645083599170974841409286698449792398024779126906064142969104401269862225, 331015814204204092456181763908176014829859886728063700161172351628636770, 209504135938623285524181936624773155038492601627266031518982323658033612, 150321407048217885620895845531773931137156161820336678591611200024841310, 116396326776926868570496428114661741005060127047490000456415024112799876, 94676774822115184683132868245451388283292801692135032068037013631747838, 79666252170833211343136793407702911647752596547437939019925841992187915, 68705270871778355351397713749770668688545198767388778511053801607569769, 60364622753928703250718537311655717929466957637725429079167070135274833, 53812242499773885436721648369345531005537706100251828102391941084963315, 48532525822834841707132136209788969356760975628730024365636410325189463, 44189660197116869027576176440816263188727596993094549303075205287220972, 40555875566861742532566084732626983005458492484969298033854146820597100, 37471394283555021832328531426266983005970811285993856050661558720507183, 34820909936552327580262429084714092487126571916630059225282599306024409, 32519170180242381701130444378100181731155088425907883065134510069237746, 30501811816175111109209290543538758964862441439784572260405089105642274, 28719348681151936476163434614028092076502086376286907769325095727722176, 27133118272453032040742936834454853249895609388544086027554472032300464, 25712482399137789413650219946286416650005521196948266498243423704068352, 24432852246072352200777036716981420917598024752370097803737944441608343, 23274268325494785260231717449796542915239080302856582596582027508613542, 22220361850433209900514405134550697311953495245852203787010406985734051, 21257583302603717095047689300565680572344501808027191678433124552290536, 20374621407530548753182742942110612371360615185705130919572303330589857, 19561959923814287094302845742025336086649562749068418514628500478575132, 18811535606184372779962352660358719873102651559478463730965547391822017, 18116471415589811970275591083341308641485815867910418547991662824137788, 17470866366736462821090142559235725056096920780301014286861446890397580, 16869628478771229585598356462253507127248026976971526761059451743474934, 16308340865650144168621791908784163987354273618078107928264232053858298, 15783153548416051898235826250279575865325848747721613800050484802854157, 15290695408798975909991652402084063760573011685591303273843818002228322, 14828002044599651303654803842300289919562495522003774528485406542172379, 14392456276654230376105600457959245784324736278403987681878706946596419, 13981738794325188615818198589595507829386102643720590145723884785781539, 13593786980835264646250114982050739395785811915760831519421491161574072, 13226760380331497766080080878710023832939891307295542136759028493501794, 12879011590259195470870446601220737071407896217553178503209735284607012, 12549061610598371299929618073668479263866535648315041701499003433846747, 12235578874062743411258872735739990606024998665200522000870690754000431, 11937361331907908608523297396464090078591372468141706881735201203218810, 11653321088474733858920954138809067509143768939514206928450250146718120, 11382471171416684841830690433663025710518218476834173007169882782173086, 11123914099295775090046416205497423421813562845135305048334064740175597, 10876831968098155673325923441004143299664081184948434875927987063330216, 10640477826431823727139045410362899339090117453233015417393760734928522, 10414168148192221795898093514473005602561402991477917772046762535917020, 10197276243221184698131907770724618061904251003726147696867478185059423, 9989226472420038360483362689424189834822095926176463389531678922583455, 9789489155064154935796276459956216583143183097667246681331979550638188, 9597576073611404710571288507858960818117775925019472896440370996200408, 9413036495817135738770926517445525085957408779530641040742459285274763, 9235453646031955638205270728023380929509974935899433932175476755157128, 9064441567618803511168739766804039853742141874988608400977596269898960, 8899642326845456216514116711570811595459544641458106228743964809598709, 8740723515679593718648344885917614672209982265287114420827269783741573, 8587376016871625403844354663507214143209101261283739785894726287755745, 8439311999746877753731686566550286365003265836440232054544088301395650, 8296263119399165292524112443372000090967405532906604724912080546147173, 8157978895609467497126541239959418070262063030035316230035980427462162, 8024225250910800328573715689055325407081880273530702913853744498654318, 7894783189869328618811147661118161736240136555027069810913542333003777, 7769447603923285574530967006732946260717178721814145372161774371165814, 7648026188074158228680692376625276493625095302299735425771402564917853, 7530338457407749916215335285374843578751508498095904388183014784692403, 7416214852876905476664631489480508399637539420932585358714245257421348, 7305495927036970864409123515907012388825484877823137653895208924086397, 7198031601518045666929658140996805449432057613643917041550183214791915, 7093680488968818394269502209205771806815827147454502231001636556133752, 6992309273035525340530049236359022079940757034857955361598536391086671, 6893792140663485931331564509844660618461965174423543375966405237012297, 6798010261642269801101155528998226547475156669443634288584532859538940, 6704851310871188240910260352280823272214935537920680268165808013960095, 6614209029309989096579419589135313345327928750233753151897399963506541, 6525982820009345012695357635987557393215836008583203726077443149619122, 6440077375994639179291034411138738019468711251857069668020504425214893, 6356402337111254800595787878454080607272931885584882479607511902492324, 6274871973235722056999219721880411294143648981777551833313274841911991, 6195404891519540846047289884621338659239146767968775388417501589626886, 6117923765565482009406882480772666229201304208815038265887101285432722, 6042355084643307331353080228777732092177929658265936308800271870324414, 5968628921236286091546285556274933172007585607330070469003566276874748, 5896678715374353840159732013981005262480553353733431172948907797980202, 5826441074356630871425767368718282469246473122512178398954614624736762, 5757855586597360499135275720710940198432387552741242804990295679279298, 5690864648446943652293887044887995417224893331591329142635070096435852, 5625413302945211889122546403508454186813769675505951751976522335880534, 5561449089558774442490521358768438108246264609316563376176747710879642, 5498921904039404984868066701765184643605175854581411377705863542996806, 5437783867617061565094975305843696955850711319713651237884243835042666, 5377989204810191674259189075406578335183443889615256665826405354448341, 5319494129198285297128347803442861826421186621425135567237559913270667, 5262256736557926705725095076277298868984250656144103330586285809809232, 5206236904814500583266108741754258892432116685410907791466070205931755, 5151396200307795764015319474487841512525966385439576617054971866463336, 5097697789911521611702602165176349583789616047069822906793960079961200, 5045106358584652250131704334282143859102311142716188808987552383082942, 4993588031966937099110513124163113727601015467942121915752896991400995, 4943110303662213262603682675975048581962091354367028334399973239220730, 4893641966881638528467879016098582335580272867169789636880946637591941, 4845153050144911366607738790208323786693239738417808119357885776378385, 4797614756761204674224971853981992943875914517782168206475220951448232, 4750999407833134943453498438351154439381040434427609546112088173532747, 4705280388546816412247914298168902383192775266635393439730912991110628, 4660432097529088237021232010048835145776501288243208469354567129195590, 4616429899069511014768335620508802199478047008733702899167410335292465, 4573250078019849951948692960349551887475004312889768670091217275479580, 4530869797197623959739312962204338362241410033127031378285499381187096, 4489267057133018345251856909787891624395577734175683821095214006206821, 4448420658010137432953333438720241377726888469865107168400936582930632, 4408310163664305973934782363680945678447470380413659608572712194146195, 4368915867506998984588300756428413560819883035968272677257356338441299, 4330218760259064894188296947167733298342802221104687746715782687627758, 4292200499381275421236875135525508008910361525784531990020625978573350, 4254843380098949710211240615903977135510763606847627356140387311095105, 4218130307924516313064204382140475085169939210557738539820596321480425, 4182044772588445668021464593307411281317666610391797709420314792285097, 4146570823295054129418230110694912347822502787684748013878527560253076, 4111693045225290376282890965992440741535164566186487679729668376134067, 4077396537213804363483107139423409202768499100760439487183841507174944, 4043666890532402598003365790499687742737058399485699104978647628892189, 4010490168716443016850610794215636350992331042033253710713429602628889, 3977852888374846881639655936797549246554944812321979795339992828137157, 3945742000928230107437931811446801446287506458434354157846558510090948, 3914144875223206223789576075810899963641732924228269811888636305071259, 3883049280974209551715641472804883723527681647378889097791491806690408, 3852443372987250110459559737404798030904504987882857130169367670592252, 3822315676122859468176191459164892929086259769942376023674063751502617, 3792655070958135894959781145621202207003401840723198089276648291586963, 3763450780110263028078091204967806418678720432241544484423872441255761]
def MeN : List ℤ := raw_ints% [1, 4249415200756889948436380134400515341135168982651205854, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127]
def ViN : List ℤ := raw_ints% [759975914999918232578520615, -14663627786537734594509616899, 3017278409072490392821231498, -462364911538891693466578700, -2186515989281047044846613846, 1672003544107237266152838734, -1682360217075813290986679975, 463538688421480123120263647, 20856466663598487332864359, -779484354955663145729628420, 724979660193753486918698528, -712377965536087484834346756, 203037079220082005716724426, 65702316012080864531752936, -441658962765381616352024413, 429492711349428785373994955, -403968289315690477242471461, 108706518170948313884118996, 68689681586541199032788903, -296665893313659893150896176, 291390143479529324588324324, -262768094342166751809633649, 63602667367912054101561991, 64540661703294803491382369, -218552714458825867339782431, 213602004904143720938803954, -185106838260109433755783454, 38399803761841506958046248, 59341191026659831102474985, -170645065430900915573323379, 164588532912086561239296026, -137332011013713961906778214, 22862398502439458483191426, 54440996419006776111593041, -138657354168875727853832565, 131339765677734834151589849, -105544418151970925589880154, 12704921921996063568251314, 50277428333011557278194690, -115806123841916158726634578, 107719387466920915558357200, -82947828132726472707477112, 5906883480284682275258925, 46943571640040989695242605, -98574183362043433417779486, 90280341260520358600691166, -66119367695731331646496462, 1166460065239580601479946, 44107013154480348803480022, -85239832637747343530238630, 76698543704238847515890732, -53477274942996890697920561, -2584202662703382256404485, 41153849047502169854955355, -75096433711744226492904297, 65333817086079600153157446, -44235788911602645537680928, -5931158850107162403922104, 37984423389980487220085388, -67208057751071460365003158, 55943764717784122161211308, -36954588700836597135588110, -8256560748618400162150288, 35563695175890340554587313]
def VeN : List ℤ := raw_ints% [381100735687, 1524402942746, 3429906621178, 6097611770982, 9527518392159, 13719626484709, 18673936048632, 24390447083927, 30869159590595, 38110073568635, 46113189018048, 54878505938834, 64406024330993, 74695744194525, 85747665529428, 97561788335706, 110138112613355, 123476638362377, 137577365582772, 152440294274539, 168065424437680, 184452756072192, 201602289178078, 219514023755336, 238187959803967, 257624097323971, 277822436315347, 298782976778097, 320505718712218, 342990662117713, 366237806994580, 390247153342820, 415018701162432, 440552450453417, 466848401215775, 493906553449506, 521726907154609, 550309462331085, 579654218978934, 609761177098155, 640630336688749, 672261697750716, 704655260284056, 737811024288768, 771728989764853, 806409156712310, 841851525131140, 878056095021343, 915022866382919, 952751839215867, 991243013520188, 1030496389295882, 1070511966542948, 1111289745261388, 1152829725451202, 1195131907112405, 1238196290245064, 1282022874849589, 1326611660928361, 1371962648495257, 1418075837631158, 1464951228807478, 1512588824771820, 1560988641538372]
def cNN : List ℤ := raw_ints% [-23192624359128364031327, 223749203285793069374231, -30693343191248478117078, 3527564327536710307820, 13345434504889203154581, -8504249797094916107955, 7334508479857584450800, -1768259767232819073182, -70720983424202770090, 2378797469957468096099, -2011329401727165879458, 1811670851481342277106, -476630763643897436797, -143219682992294016226, 898557460053266634831, -819192335795266695736, 725184342894952172210, -184303314498813737461, -110328564431507631053, 452676228811126545946, -423453403261499785779, 364502083992929287733, -84391276972114966486, -82067695240395613977, 266787981517121420093, -250715995089186120768, 209222681410171433915, -41852464688809538659, -62446532178849667361, 173589137197775182671, -162027206826572109335, 130970011724199258715, -21142576740093308404, -48864922394702486026, 120899618241555984806, -111338098888596288174, 87052973692174076876, -10203248613856316471, -39342188386583813225, 88353060792477538091, -80178898112168412043, 60270638698560785717, -4192180885694411362, -32559184431624665482, 66849896485760791977, -59894290599338935255, 42931978068725151969, -741615336888364538, -27470188159229729355, 52026265037687587604, -45895172540545802406, 31384556076634856414, 1487992578299688523, -23257700063918598234, 41668386958309784764, -35604104770158822279, 23683669193523551827, 3120769027240180919, -19647332344691641711, 34183785884130584902, -27988003448878615163, 18189750770242308160, 3999527582377309726, -16958091342873735692]
def fN : List ℤ := raw_ints% [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def gN : GasLit where
  P := 256
  T := 999997120790
  Q := 256
  Qm := 240
  Qv := 96
  W := 80
  N := 64
  Ln := 277
  Sg := 119818393869546725993480329177774874481617516143557060162674100623549240835647711995
  LIv := 274859910930757621809349496791782898904955394261623556382415297275120153202432
  LEIv := 278489674596803539660726608488072173396634434447029422675630
  L := gdOf gdN
  R := RN
  Mi := MiN
  Me := MeN
  v0 := 28926549020141212282660170469
  e0 := 1
  Vi := ViN
  Ve := VeN
  G2v := 7715604399666316073048035851651784479432550975904641116756372795566377121414
  Bq := (27741145594835673561234466866838271316337243 / 730750818665451459101842416358141509827966271488 : ℚ)
  Tb := (846812735 / 549755813888 : ℚ)
  cN := cNN
  f := fN
def AP0 : List ℤ := raw_ints% [71016307102963472337291, -56185968133929542939740, 23226082478661864920278, 4139891918997489071475, -11317598212705454381980, 3182340710221839333659, 5085888587066097782568, -4561299529544443991828, -1147231055734948431589, 3824410337008806758700, -1113698006737678195786, -2346307996004548832021, 2115516582391247558757, 734619432205384188452, -2084102136417952305418, 482800554733592702527, 1504565643525926298277, -1239364743035418222214, -592441543689504474163, 1362543382251016404267, -195087728592084007480, -1118237391425296932255, 811687451280310414295, 521314339665520041225, -982021463090189453007, 38634410045363714777, 900361320441460517941, -564979714115308354368, -478238098813598178362, 751926275812414465291, 55802469567458943403, -760582194161876156122, 405916505870623896132, 449807874233303416099, -600117648003914733278, -116957014562605558145, 662709226825543719483, -294688319558083049618, -430459734654727368438, 493771117156524725939, 158726747754315318294, -589883908791302459025, 212021621029812602833, 417244883242732075506, -415855561696758662273, -188651339678928056122, 533411860244437733215, -147736007882595002505, -408293714957627940235, 356628622631890936059, 211182796514905750370, -488444643884539919318, 96076215717434432531, 402301972062318268787, -310111178853104653265, -229090324092856702610, 452064353301212174361, -53571092340588246040, -398335897638461828055, 272455419021977799160, 244128357974373910491, -422351452034540973773, 17969777166551142069, 395736141381490274946, -241103234583522194709, -257398351784863628306, 397909581071280280541, 12312104303922230765, -394046971539985654707, 214297321132464050616, 269579718953972693155, -377621717489313254494, -38489191182803089915, 392948991966108903277, -190756347184175967174, -281104214394875418129, 360523463658080921725, 61575776376868569373, -392183025110018887616, 169405832054667056919, 292317961035559794030, -345714684166223407292, -82505183827471623410, 391374702176495862426, -148926748992514404670, -303758479907846463714, 332176270802086078136, 102031604607065621800, -387962942239194714265, 123244727435800928603, 318609725346664508378, -307772533027705950954, -158907779072956907323, 445912945447873230218]
def DP0 : List ℤ := raw_ints% [13075449655959, -2698620646785, -319898649887, 653693518638, -146414557493, -193977016452, 148203823749, 32387634152, -95216809329, 24738031364, 46928617968, -38386550821, -12168056436, 31675255741, -6762547305, -19494674900, 14902565292, 6629383486, -14223214091, 1903800168, 10220774643, -6960137012, -4199989342, 7443206811, -275813033, -6060618889, 3589259434, 2869853228, -4265502004, -299455146, 3863525919, -1952919469, -2050749860, 2593987417, 479505033, -2578092626, 1088191556, 1509338941, -1644464205, -502244227, 1773817664, -606041625, -1133932158, 1074727814, 463719023, -1247295575, 328678636, 864365568, -718516622, -404973490, 891616590, -166961662, -665626807, 488551280, 343674067, -645829461, 72887536, 516181579, -336280428, -287010708, 472983763, -19170088, -402171525, 233424418, 237409774, -349653075, -10307530, 314302381, -162854839, -195191639, 260510873, 25299182, -246096663, 113828923, 159825679, -195307577, -31783516, 192879829, -79383694, -130515404, 147070415, 33441625, -151145266, 54798256, 106490504, -110952060, -32469925, 117628301, -35600809, -87682944, 80694685, 39692950, -106112220, 36024778, 66469195, -65550708]
def AP1 : List ℤ := raw_ints% [62178436487667477252434, -45755255750866521856823, 11731299993761307164958, 10924160443094371955746, -9744128660757933849059, -2463651898010617263288, 7164213346657364850448, -1231889989241903895956, -4556183628832156459047, 2725147349807558416944, 2344808892391100803030, -3045457215975219199250, -613840537179834808541, 2653301822943053953462, -527056144378227248077, -1991628851648710936419, 1239250450014642262401, 1163987557228905433058, -1478551836090069748144, -447006908863200405279, 1477481158423647057763, -215853388699540456618, -1178927789854872326166, 618819971296115781538, 834618984071835883536, -909529003504904831767, -358678488823168518053, 925526096781143909687, -5854022400565601516, -870667616479567581522, 381896117101613259708, 610967569245347857173, -557917507051288453173, -373946287628308417004, 695699804275085667631, 36167913370472767292, -626471970989559016407, 184701686827856333999, 540096066587017062637, -419216489583433358390, -305934519081022782178, 485930416739974956033, 118937447610129095937, -531265734437423776279, 130126875853093103015, 420677716867119366651, -268479776441874681829, -310683970203128085038, 402709611718304811621, 106182875509908627425, -402141916366062658818, 44646202478982549291, 380291220995731626428, -216928507852737597662, -252056419178843554303, 292319080539203801129, 132339213956446843654, -345019388386158611464, 32203988149818964091, 298468874635186761708, -142194623339974753912, -232688851642093832137, 241053349067474750032, 107623541697981725470, -261175340274808022127, -184323182062839324, 251629738911520806311, -112371489749266040050, -179708399864345306930, 172655531513370959935, 99725458960497978598, -205889419042470649566, -611038425816901757, 183614028250447213542, -71440467752175402367, -140417691019950791548, 125891631366558432053, 70466844411878839874, -137737757174486826312, -8748941069139325562, 126691081290822836243, -45982881797502156903, -87974852252805324001, 71780981505103843621, 47305633552535283646, -79403797825868751601, -5418001489130280982, 61529569864520403502, -14269909095602609590, -45684787256686184913, 29792835858699274770, 25854576265438618047, -52868848824078175643, 54367689204379266783]
def DP1 : List ℤ := raw_ints% [10648041903272, -1363050717050, -844134157429, 562811440255, 113348800555, -273244823676, 40026050835, 128626232494, -67848325032, -52084097820, 60912334812, 11138282333, -43948641850, 8010470250, 27896580049, -16056982789, -13996203030, 16544901737, 4666181677, -14418276840, 1972916358, 10109185415, -4985547272, -6325973455, 6493174139, 2414379177, -5879774428, 35129332, 4939093874, -2049385236, -3103529189, 2684216939, 1704884108, -3007137925, -148282654, 2437121294, -682045412, -1893761390, 1396166132, 968040032, -1461223038, -339970253, 1443802727, -336296989, -1034057115, 627795633, 691200372, -852543916, -213931682, 771165160, -81498069, -660871721, 358918026, 397091413, -438527850, -189062824, 469425057, -41731377, -368387757, 167171809, 260584042, -257154759, -109373695, 252857254, 170009, -221113329, 94075914, 143340215, -131209241, -72207123, 142037467, 401639, -114994059, 42630254, 79836415, -68199693, -36372811, 67740910, 4099760, -56565589, 19561568, 35658633, -27721147, -17406318, 27837084, 1809697, -19580801, 4326560, 13196632, -8199134, -6778795, 13205902, -12937674, 11985496, -5583777, -6129573]
def AP2 : List ℤ := raw_ints% [47434234904909370925217, -34600318022797073634168, 8244269488955694833786, 8775164685040069069291, -7129510554993014896489, -2483275234836383692152, 5565391661975347034704, -458703751219824677526, -3834385415026310508903, 1849763062019695534287, 2219151431683818831847, -2335773245553713123646, -839691519121360082161, 2210977011101207169020, -163975664079189290595, -1788119159328274483226, 851497627123268396357, 1167610749859559953387, -1163969651124983550112, -574307076818127352405, 1253717766491794821467, -4098249166121341962, -1080088535425233174792, 399104776312676750842, 829791785079808479671, -701292065915462072977, -450696514466513386208, 783427695444425488918, 129423930615341291440, -787484510129303295828, 211821630080761751847, 614745245306196834450, -409088849411835034383, -431983467555632995268, 570646796782180260738, 153919123991837279699, -566632533770956092513, 54840328064060040075, 530220867744309255449, -281465598112286380750, -364350188375482836332, 385828219149322625258, 211563531867013268390, -466693161702844658143, 4137523862731220503, 419825510486703366970, -151412077769959764867, -354821732278287511328, 300662385785697872726, 200856327054507762535, -349105052996854857673, -66969435130572101193, 372095750495209780509, -97559591312348790882, -301949381709737190768, 200471133754907522544, 218838312617900858285, -288255798869394414518, -83392666152036512490, 297440056820960715031, -29626303967731410064, -279333043406219801636, 146564173947033130913, 199911484464003283734, -211003486577887526910, -113062494650357452686, 250458611946831532726, 3474418869690803032, -233353439591066089043, 82690487126227337231, 193117785216417001986, -156839471720084823975, -118316112157063171177, 189730518961915333665, 42763313341353360157, -198032528045759616509, 36732622760241586672, 170371104451790445270, -95181106115503002636, -127888680974927328081, 138243871154508790610, 68997301158945648444, -153461955474795627551, -12583625327850115582, 151365356733384805945, -42327427192935585150, -127549157427474748493, 81677239164890561802, 97664473998275162908, -116171814465935783501, -50923502489183078810, 133152623542218328308, -17501461707990440853, -77425876835074678337]
def DP2 : List ℤ := raw_ints% [8052094346916, -957895326558, -678076478856, 411793629114, 114251639829, -212265379293, 14904009144, 108249050092, -46053775945, -49292929851, 46717911922, 15236402040, -36622081950, 2492186445, 25046036677, -11032864861, -14039769595, 13024746940, 5995032975, -12234639835, 37458308, 9261648901, -3215403221, -6289385823, 5006559976, 3033781823, -4977037542, -776658502, 4467215555, -1136707345, -3122718633, 1968182043, 1969485387, -2466600700, -631043765, 2204332001, -202508135, -1859135568, 937398087, 1152879279, -1160209493, -604732225, 1268316053, -10692925, -1031962328, 354052147, 789396740, -636507996, -404674781, 669459320, 122247342, -646629597, 161416755, 475693129, -300740462, -312637412, 392193886, 108063969, -367117930, 34830310, 312820030, -156354081, -203162406, 204283307, 104282491, -220084230, -2908738, 186128931, -62840478, -139828683, 108199252, 77769908, -118824704, -25517903, 112594125, -19899287, -87940306, 46811091, 59928727, -61723730, -29352129, 62202361, 4859678, -55695554, 14838990, 42603409, -25992474, -29611350, 33557707, 14014395, -34911203, 4371621, 18424743, 3967623, -28756783, 10476992]
def AP3 : List ℤ := raw_ints% [54936228812018472349222, -39838379632880980732745, 9054708233561498075275, 10359430489009676825849, -7902416868505642733223, -3251450209292972657339, 6281175359239138940361, -86812113060416049276, -4483057486680597192126, 1729708752144462917569, 2787599050016042359505, -2391755726887727633889, -1322767548020848115055, 2407100250132138392507, 211645864956651793467, -2082539444834804186802, 591852632750452841687, 1533673726868546607718, -1044135884982333269499, -960338882481741028228, 1267878020695841842896, 367752449503287057423, -1231076399544346398131, 97699983229347837657, 1081351938258951497669, -494963335634237670903, -777788713109492454210, 708998110330179510325, 472227508555188842896, -838793038665596582307, -110118098065120655583, 793206631135103250714, -166463619788997531326, -695698429007262259247, 428820401685438946614, 473656202807990417249, -556536763515454504270, -259362459444672867293, 638875822073046945823, -9599220192089204909, -583744118154623880457, 208925760450044377629, 494475675654201494672, -400823636310709634563, -306041815493910482514, 483566214634479328280, 125837531136137902308, -526753801357193968041, 92868219375015116213, 459277708040631361246, -252650505342809341120, -359446843888693125902, 394624688185823576753, 185358273870937895359, -444679513083293149663, -17445141074977682808, 449238376495795640162, -167453610183084616497, -364542582537716138649, 299195255284377533283, 245975546370411085170, -397295458163116719327, -76933592610002286686, 414418365202006229275, -84268266369659836680, -378920121793349529417, 240022512564161480072, 271858947536628899222, -342070980884017318284, -133541438869897292883, 395500101225322147882, -32509541808239941886, -374465353370403414268, 182416287896903668247, 298481056185285136172, -305781421085881013866, -167504943311417281458, 370096266894805460586, 15178955068589911641, -375416390631705984138, 142210606849955781042, 312519948398421180433, -269951866287550902227, -199846168076436051005, 353132131708798268881, 50956572437417804150, -372750810382476841674, 104821501417341391640, 327177215168700364160, -238787532239964666034, -229370204161002861176, 329482803471272715128, 113945502505565958449, -419976649847570196659]
def DP3 : List ℤ := raw_ints% [9271082168114, -1052059580524, -800496218711, 456435949698, 149594178295, -239565542016, 2820662624, 126561798545, -43064769190, -61919579918, 47837620197, 24001931314, -39870619269, -3216702667, 29169957184, -7668641587, -18441441860, 11683814659, 10024712388, -12372825330, -3361285305, 10556354418, -787123732, -8196079634, 3533568603, 5235543618, -4504193856, -2833784351, 4758276844, 590931392, -4029248124, 800879094, 3171806313, -1853561098, -1941914594, 2165057113, 957744232, -2240116972, 31969415, 1847087005, -628252779, -1413406994, 1089304695, 790927624, -1188641719, -294250293, 1171906047, -196603789, -925328609, 484493805, 656141435, -685780482, -306683647, 700551158, 26170649, -641792206, 227833342, 472390681, -369284299, -289182364, 444924008, 82072452, -421157556, 81584434, 349494625, -210913769, -227596689, 272844943, 101484560, -286365433, 22427441, 246138380, -114243937, -178110862, 173856245, 90743010, -191032271, -7465174, 175920388, -63494815, -132949050, 109418934, 77178729, -129936532, -17864164, 124504588, -33357765, -99198393, 68976818, 63123794, -86386888, -28462000, 99940257, -25831722, -71157932, 47190584]
def AP4 : List ℤ := raw_ints% [12833902124086874024649, -9840843269105304446041, 3313568172248700246539, 1767625113503053102194, -2519282838426806383443, 296045452272727494647, 1483340666775148933801, -1044199741776370738265, -484130643121692741643, 1066274036029720844661, -240297643354419258210, -710813158782451218368, 617058188404480337239, 213769487592201367635, -632202780762639471484, 186320586374470712770, 434997580162292010511, -426496980359075402519, -113241147664994827344, 428524914714992360527, -145100974698405917230, -302611007683796026072, 320703098703632810558, 66514234199908744653, -315034451893423873399, 116243159210996814230, 227962955513999041938, -255374735842080559356, -41160783386162449150, 245245303166871356599, -96919643871934564359, -180539312211600735827, 212032923488588484095, 25481609005251288637, -199296943740045848957, 84567433090934977354, 147254702858147025217, -181645442676333157221, -14486296465987190613, 167329256024682286998, -77265798456354394954, -121775466775027663703, 159354226278328559961, 5714124796692830844, -143846437053063565289, 73593892494223863950, 100744025259975893063, -142332465058302041995, 2205204694217636035, 125468208609741160306, -72461872744820979061, -82227909659956590481, 128771351834098884634, -10075599335740817021, -109940652870813857298, 72983442516717785588, 65024902959758429872, -117360954927218920652, 18326750988190656660, 95666627833694386373, -74370131953900778170, -48363217605031881869, 107034108513976021595, -27083174219479416641, -81485690058127567463, 75863207927725961253, 31776301199045382177, -96841310624459365536, 36170969234071512979, 66597474976875267049, -76699781738700613551, -15085861162597454207, 85942931277178967179, -45128957355016350389, -50574963896374293403, 76149450117322292930, -1590440792822753770, -73695337408760470865, 53308970329217449688, 33321825858932723920, -73482570417036819305, 17701362145383916252, 59876672165573089785, -59955012893847571789, -15365367380325845528, 68535479524112119935, -32712254716811374864, -44535576134584175582, 63954099715916639229, -1348417094872283136, -62070567344621770171, 42489053978097287185, 40472724316087434531, -87007478854397959909]
def DP4 : List ℤ := raw_ints% [2290134975171, -385000935581, -136588321237, 145511338372, -13620591835, -56574970528, 33927698342, 13667557265, -26547154368, 5337614507, 14217007840, -11196667380, -3540825461, 9608542888, -2609776992, -5636268809, 5128352353, 1267161295, -4473253245, 1415995060, 2765887581, -2749996324, -535874527, 2387795650, -829865868, -1534491279, 1622370072, 247001247, -1391219281, 520103971, 917084724, -1020119208, -116174948, 861454026, -346712936, -572854954, 670759660, 50793906, -557276362, 244484951, 366186415, -455497387, -15529082, 371753515, -180899261, -235573272, 316656996, -4668461, -252786759, 138956098, 150100465, -223779410, 16670534, 173201259, -109487455, -92896062, 159678484, -23748629, -118077353, 87433612, 54161093, -114183564, 27523595, 78890479, -69971960, -27922629, 81074255, -28850931, -50610624, 55535172, 10407322, -56490818, 28263428, 30179303, -43295821, 861594, 38039258, -26217925, -15614632, 32808819, -7530333, -24269667, 23154067, 5653754, -24026911, 10926403, 14172734, -19390543, 389507, 17082121, -11140179, -10109523, 20704841, -9175265, -9176301, 12770387]
def AP5 : List ℤ := raw_ints% [45538456391054311930288, -33059963505472491467383, 7631286709474135399489, 8588296886465809536631, -6659574539101372485855, -2613295782016633388668, 5330026806285235563418, -188471429875357893658, -3768019642810411658974, 1619027188917411620211, 2305738419315860093504, -2147270976942444395393, -989241492286929553962, 2141140441579574682194, 18266538330824261250, -1778831878053164778699, 687153226670973908614, 1254748744138432772659, -1041380849382593244629, -688795763689911996237, 1183669470155902616343, 154436103363154247766, -1084870111384898836288, 259751198349816906462, 882914626826573307419, -576545228305731066454, -572059795602641283940, 716921733920287638603, 258171301855226826671, -775112303940401617940, 53389836991691777511, 667192683908495020113, -301941722699518052815, -537694255485709500992, 476356392982112504916, 289292656759160452718, -565781393421757068788, -96156600501126393676, 556250779654276682505, -158810676131567397674, -483586480579204987019, 293101056166224967872, 330079087151242929558, -447396083538296824198, -166146154545353676546, 449362498254631358360, -34887433374951626325, -460987746304037609092, 186839307173808119275, 331321496109726729542, -331742129119493755462, -232835315997447045050, 387535103363237777183, 38149105486025749123, -413966243776509346143, 87724132013292214136, 347680321934190943396, -252884382309918983264, -260467700999312194684, 319606346380565157230, 113216372383602750857, -381988246102547822401, 24167435000420456713, 344621130677383144103, -169421312273705819364, -288375632246869970560, 272628981253459711204, 165411730249883961297, -336890678256285216412, -37072154983280007246, 347816471267694219163, -102257296524205616752, -298411206192207006571, 222122286654360388097, 216529097194716357630, -297891371096399674706, -83349942485091029664, 340615679062644639860, -35459269800538471112, -307567357276039284902, 178233794280938237099, 254863411269623107105, -254518166878513936173, -128469727710284011253, 331569770027822454925, 22057364193663424618, -309267936516044974622, 130161804522426533933, 288732930524921706587, -216126561875124714762, -167075962095962798662, 316668929585762120254, 64478663016611846676, -291387613417408610027]
def DP5 : List ℤ := raw_ints% [7693627124360, -886673329204, -663636788728, 384650579680, 120233683430, -203288506972, 6123734342, 106375469055, -40309116848, -51216244432, 42947669070, 17950021821, -35465326109, -277624241, 24915950499, -8903452513, -15087548028, 11652985985, 7190148760, -11551060405, -1411557709, 9302650427, -2092695677, -6692029057, 4115985913, 3850716733, -4554531841, -1549257046, 4397030921, -286508134, -3389135648, 1452682657, 2451438673, -2059033748, -1186053574, 2201020868, 355076173, -1950405335, 528905930, 1530167545, -881373137, -943496542, 1215873043, 429384406, -1104566440, 81578503, 1025591701, -395542371, -667529153, 636163408, 425022227, -673460171, -63119421, 652165263, -131600972, -496704050, 344068390, 337525766, -394476862, -133103387, 427781737, -25781725, -350225292, 164025469, 265981476, -239565887, -138480497, 268712996, 28172913, -251839668, 70544506, 196147521, -139111067, -129208147, 169370248, 45153441, -175815301, 17439250, 144126282, -79578606, -108421394, 103163230, 49613812, -122002565, -7732788, 103300318, -41421911, -87542290, 62430908, 45980116, -83027227, -16105873, 69340409, -14617470, -68390538, 34374178]
def AP6 : List ℤ := raw_ints% [26491974398920752063379, -19471716677437618863218, 4914846144913419858710, 4779957293894342681145, -4212464568183760126239, -1143903385390340333231, 3217208384601843843222, -552030929928041368725, -2110992092461688921781, 1316248882872166852788, 1075741211403461561431, -1509897929077955575542, -213659630575716998299, 1324733935161129997379, -387969540198233125114, -951849380054539169043, 745431027072612707456, 488284755587193355399, -847072345545609996473, -68921353091466962731, 781013703492951037345, -283245464515868296216, -563757113858136907985, 486699773891116530318, 306645755309013476146, -581303887259692449664, -18245889970502408857, 528277316403212128784, -201518206363894726576, -408740728651073910144, 373070138348609169700, 206970982640402888203, -426773477464994625839, -17475547503643320415, 416991498689642497642, -175422476380847197431, -306199464602634622894, 290205033675294350776, 171873171859367097362, -360228920432979043113, 4273725015854149545, 332812703917884550782, -142822377447857657757, -263721244947284502865, 262376702753097287771, 128890074155589572439, -302803214971183135634, 3860390595422515806, 298023965731699905834, -144433113379018332071, -217608664207655917265, 232506264843582152135, 112307775332951085570, -283086636592208648940, 24460138866298968085, 260441840221860926434, -138220448963088329790, -196255121060427564682, 229853236169207602097, 82941459857962083077, -260418768290856428529, 35275858172633826879, 243370359284548822408, -150797587582362213918, -167086956264279689090, 224116591931659543901, 62899485205651847238, -253372016708841559401, 58708394793543826018, 221345183633375945015, -160510562894692842141, -145513133161861387162, 229558202420555628650, 34408854932510878664, -242982074690346742858, 79872266502597477540, 204766485493813349774, -177918814549439711958, -118054395187832377099, 232533641035350494817, 7394866908257955040, -235943143499845939101, 106066355440202132430, 183938507157840817629, -193205167404333764931, -91800575742273295528, 237671909763836814361, -23084413531629560433, -224942517683173894506, 128326094433528611418, 165718222605445081208, -205025410040510011421, -81594946809696598887, 271369096214038274780]
def DP6 : List ℤ := raw_ints% [4531406320596, -571052190770, -369357924012, 243307876279, 52629219570, -122705103163, 17936356539, 59595701534, -32770808535, -23894915559, 30199540386, 3876904740, -21942568599, 5896560533, 13332475277, -9658558665, -5871310680, 9478686089, 719450971, -7621668628, 2588885046, 4834159685, -3921115741, -2324213738, 4149958223, 122818898, -3356092785, 1209288169, 2318690612, -2002022014, -1051349562, 2053265192, 79673964, -1802431081, 719204065, 1191186948, -1071636188, -602646080, 1199712871, -13522950, -1000788536, 408242825, 716706213, -678080484, -316821388, 708055328, -8588482, -630922410, 290996252, 417296018, -424421572, -195168936, 468379642, -38534671, -390706622, 197464890, 267019983, -297854166, -102371206, 306162608, -39504797, -259626537, 153249828, 161765460, -206712550, -55271347, 212119676, -46827383, -168210849, 116219127, 100385522, -150890019, -21549628, 144993277, -45412480, -110928830, 91836200, 58060421, -108965430, -3301693, 100372526, -42991619, -71035339, 71090696, 32183100, -79386128, 7346245, 68201375, -37068627, -45606460, 53755482, 20381281, -64576679, 18497772, 44279045, -34094838]
def AP7 : List ℤ := raw_ints% [30159028953728701108263, -21879132183975799236341, 4968851277424188581352, 5738360763456996202392, -4396864188229545452926, -1815553340375801596975, 3555475017330293779948, -82377820904142025118, -2572055282382909947894, 1061178842039837725165, 1589146522575697297562, -1469602759728943295619, -704321769105029435862, 1478400560193563674749, 8536927541903426346, -1248621735258877147011, 486369921559824295155, 871588995384996569454, -752814469270640380437, -469136421346692850753, 845803298477387104440, 77365217021778797877, -769889448265636084388, 221454623897856013851, 609184837769757335649, -441252552676035652419, -370696542827303836456, 533720300956853278952, 139436216518487664136, -548479098881863715448, 91848810515182601889, 459743575307065159857, -253158183959894977784, -335578631497045002526, 372144230041824098375, 160043517001927280307, -400203126506322454565, -2982679949077667140, 383610536017499616197, -153299310815909222386, -293629883909834117417, 250693938853878875036, 187064253495996181601, -316556909420053285536, -47321085485136917435, 311942153561296248929, -70074545421579856820, -275436340782210502105, 179942197455861191073, 186692240248390935690, -239125317512074182764, -90133794269928005317, 268765363665591552425, -23480432668544246235, -243753275733234855963, 113578943142767560100, 193378562875766565523, -188411520561334390525, -108469989564415242966, 220087124857904835583, 21429650343157753385, -223026662396438736274, 69215573077904683963, 185122189979852157778, -136390096815627293291, -127532799742540123509, 183173013001940866550, 49882869498329012388, -194230181373378836427, 25358965336260545943, 179322160932990357337, -95142848338932200880, -135339523272717502361, 142771619030729629157, 77370652821399305853, -168900837814288316066, -9550088586990348542, 166561009106917672915, -53176586621964788354, -142474974865938939198, 106324330869441732695, 98031807842805452519, -140130572424514585179, -43484938463494126119, 153945991820580517677, -15922624458713240986, -144217411178994747227, 68810415589619524414, 117610228304216873019, -114657994596072663830, -70402779064441712272, 142627834708461433025, -30263841848978196, -108915466353239597134]
def DP7 : List ℤ := raw_ints% [5091653679540, -577327005550, -443415890248, 253958619855, 83530791684, -135606674060, 2676585471, 72612038427, -26420298703, -35298937667, 29393594785, 12780085776, -24487864957, -129748614, 17489341028, -6301900846, -10480298060, 8423946402, 4897185546, -8253930035, -707123957, 6601723404, -1784157829, -4617301052, 3150124573, 2495276527, -3390671520, -836741107, 3111393723, -492892145, -2335357353, 1217978423, 1529959502, -1608580340, -656152795, 1556882999, 11014101, -1345069641, 510550780, 929105623, -753852293, -534703601, 860295892, 122295555, -766777013, 163857755, 612782504, -380941059, -376137723, 458557306, 164532025, -467061606, 38849437, 384010584, -170387543, -276265032, 256348170, 140560293, -271644414, -25193875, 249763531, -73838900, -188132611, 132046254, 117629087, -160958696, -41761274, 154923176, -19271498, -129839836, 65636443, 88959501, -89415216, -46168939, 96030901, 5173601, -85973653, 26152817, 66763874, -47472153, -41703693, 56798784, 16793478, -56645110, 5582093, 48170866, -21897814, -35658796, 33120421, 19375186, -37395502, 7559, 25918202, 6860, -30803131, 14484655]
def AP8 : List ℤ := raw_ints% [10538029853712774247580, -7840369747026142418287, 2337789915761740998592, 1757030502036705357459, -1857300840762620404835, -108764548499863750344, 1354161571055594972853, -518976990126739221545, -664641486418698535127, 808722270431226083026, 178417715496557243270, -677133743180043183934, 274005761004933984141, 476657980176496093247, -421766586561031033429, -133943609817648851099, 482977566058882989484, -101537707534429376762, -326201500241540895265, 288736106215959021641, 164469778964994714169, -328889563766164556694, 46850932156436627134, 271781737423376327319, -180124174362068381008, -160017113068453851970, 243442879344039995003, -7435010103489809802, -235537303278285819583, 97534767819824840076, 135181981941193811041, -209240175848817053301, -52737021188184100364, 164261766685814609437, -90100664614773392537, -171951969632393229671, 116471224770046557467, 21198202025849484751, -189129258854583824185, -1303050295408920070, 102332256580571196658, -144246678079077340118, -99438947265488430942, 95871538942298308327, -44369723221457014881, -163307708404148641958, 43025605683681221953, 32808554462096655773, -148078777373347861948, -46903375991838104499, 77789727968893664275, -93561033452617159030, -107897098940942123227, 57746960431745221372, -11508029496344763685, -133650412555146915612, 9587898899560326329, 43342216596424458793, -102174555180693203284, -53143460129138242124, 66568539768460163755, -47016880950181811147, -86762137046758495311, 44779639085151327878, 16769796037761731035, -88988129966677794880, 6997322197740316155, 54746001555826051012, -54014722750324166700, -32292977816211513413, 65662977587862320324, -7241483840320155324, -47810054859600542552, 48252677743502822540, 37458731211999987865, -40468355514994321311, 23117417971781383067, 61556733295728896056, -12869167949928599304, 1243162879727945283, 66816396433940374272, 18032032581915165970, -5722988637255092590, 56952222234395269808, 43717392372243729681, -1176284902437895949, 44074873971754933512, 57147750883315587747, 11186232683166619399, 31510756975737568657, 63069003393070970860, 24345135049600728555, 16003889695177592610, 77048036210234852261]
def DP8 : List ℤ := raw_ints% [1824590076778, -271626010987, -135769652061, 107275898909, 5004088087, -51648048685, 16862381844, 18763583148, -20134856733, -3963105811, 13543384245, -4971899610, -7895246095, 6410225419, 1876137027, -6257946056, 1220925740, 3650174201, -3014036477, -1605009169, 3006075578, -401741960, -2189620185, 1365246618, 1142370365, -1638691578, 47233873, 1413432957, -553291940, -725432770, 1062876371, 253724975, -748897061, 389456952, 704975543, -453100083, -78278313, 663151817, 4339702, -323800405, 433758747, 284235828, -260546805, 114668120, 401422492, -100608276, -72991488, 313485591, 94498458, -149173030, 170788175, 187504042, -95544958, 18129828, 200498126, -13697492, -58970375, 132402386, 65592769, -78261632, 52653355, 92557504, -45507837, -16235701, 82077650, -6148722, -45832624, 43083584, 24540986, -47543874, 4995701, 31425843, -30219757, -22352531, 23008841, -12523476, -31773686, 6329195, -582548, -29832478, -7671004, 2319685, -21994418, -16086009, 412377, -14721696, -18186357, -3391607, -9102284, -17356897, -6383036, -3997549, -18334831, -3628121, -5257785, -12975806]
def AP9 : List ℤ := raw_ints% [11372949072403304434470, -8535757278022508690458, 2501244970908607907459, 1852327117651577886317, -2048267826892585711655, -146858753146396208153, 1416858156223654963481, -597022745818603630175, -742274438379845579024, 830552899229397186234, 157361719321721243150, -746845525154840693436, 259988468549406171876, 479782972093398654351, -464400810472829917790, -166553536945927723617, 486348804464514852057, -113847836317728058090, -358907167696511280521, 283434122825778497265, 171119925154835455091, -344416963535791937556, 32793709166804826890, 285910456254579261552, -174808687707904174854, -170632862605516876161, 252756244002451542844, 16966583783895042828, -234145681378634545515, 102714800825586420788, 165711261839183865165, -187135669372255798911, -48694454342316636004, 193535219620377257383, -52186745874180627170, -157186628681430526667, 137057688950688000978, 68721048363834759684, -159642425756430369473, 15892157637490920240, 145853634347553366247, -97410786829760313886, -80466883999180880815, 130328751658184909252, 10179125863893530109, -132424341426817009163, 65509298193841992803, 85966219474298695248, -104514854689047974153, -28417301337067697288, 117531223151161412151, -39860210733607299343, -86540172526662450100, 81654058716757917873, 40357444017451504164, -101734915603413352203, 19580795768022754460, 83134299774039780092, -61490686743776777402, -47053383112991278571, 85528696251550246043, -4098970902204182833, -76498489686233427829, 43933933363826096465, 49284418193429393915, -69354986573225106041, -6993729216612565513, 67268527520355189970, -28968554806463699835, -47687555451450326752, 53617759898613626195, 14043188030276688609, -56044934193095463068, 16633482282015388103, 42820986599576418960, -38695823125679437064, -17373996577509284818, 43415619807289657798, -6982291130901377902, -35218659556512104847, 24925937407577340628, 17403983796902482077, -30086813828016092223, 91446993964553836, 25586137827632414010, -12938510703267438223, -14322405910343574681, 16604420716196406800, 4399595459254134116, -15557027683614359579, 3779499057012841647, 11321611266947526735, -13571399941740551370, 11173531768739619023]
def DP9 : List ℤ := raw_ints% [1986418820767, -290617728038, -143133433356, 118305967194, 6756743326, -54039311553, 19398211676, 20955249450, -20678376554, -3495399224, 14937692916, -4717552509, -7947007696, 7058202273, 2332901570, -6301627232, 1368947134, 4016148556, -2958690536, -1669905867, 3147997191, -281202708, -2303448760, 1324958021, 1218156745, -1701382803, -107787005, 1405081990, -582677057, -889263332, 950592210, 234275636, -882359664, 225575372, 644440010, -533186205, -253765283, 559760903, -52927528, -461511037, 292920304, 230006170, -354189994, -26306706, 325508879, -153182679, -191255065, 221259937, 57253686, -225383083, 72761623, 150389884, -135100333, -63579395, 152619506, -27973573, -113110523, 79682398, 58076039, -100552234, 4590363, 81608286, -44648379, -47714776, 63969141, 6145564, -56316316, 23106092, 36240066, -38822425, -9688011, 36838679, -10417242, -25552318, 22001044, 9412073, -22409803, 3433965, 16503488, -11129042, -7403826, 12195015, -35316, -9414533, 4535934, 4783907, -5284092, -1333934, 4493845, -1040137, -2968407, 3389946, -2658924, 3076669, -2445113, -777594]
def AP10 : List ℤ := raw_ints% [32367682353535045791748, -23318108164717711350766, 5011496468395433927391, 6231112548302219217089, -4426869574731560408942, -2152819493421434081561, 3592991566675355539631, 222558643293348228444, -2656607982187157383581, 768591662660321955361, 1753215948183466614985, -1211361313637761102731, -962681791515903349872, 1301549772553920375674, 338211365395174740796, -1187310261973205040639, 123630725395657512812, 950892735693259275008, -419452385589554550036, -674858279331213151037, 588014723046952929802, 386181064683995135213, -636119153020815912507, -133400153707041835363, 609454330066853918495, -86119050422822065979, -511185122653727552450, 240904128145333568929, 385597740732679501630, -349350520170552364390, -230527084493531104441, 390129119751027514795, 86234305855201151441, -391022022274933547510, 54940034058825945706, 338220735895828402235, -159382278426088993823, -264616324460717766913, 241014784136639407780, 161367696457654785964, -275233179323766319943, -61778425878614726538, 282329469466932153792, -41569696537654214841, -247252854399044078608, 119895451432054475895, 194886237641817853669, -182810738604706693329, -117719994047317836635, 209845335382593887582, 41453395867126697245, -214955396771130833752, 37920093076503613499, 187200238558183792765, -98564147937169490191, -144433105722981971227, 145453687147222220730, 83300077024936389775, -164361662078738423976, -22466779833487416188, 164114768273566239899, -38190258470250207601, -139117260721002690564, 83542338372811164649, 101909272579518572850, -115224506227266530396, -53160047792122250675, 124995995021119076104, 6014545252284565596, -118693332704728883959, 37282121285877620296, 95237783763356573176, -67160330180629657184, -63858523553071004599, 84161842906628408495, 27577832895185977392, -84884143939312666591, 4579611831661069604, 74242295607024749794, -30208439985315835897, -54146757608487358892, 44479254234510728196, 31473825038944181619, -48521976150578185591, -9776922953977499009, 42899434429999819071, -6292892894044426301, -31035393168970409723, 13437696467174794723, 20161700060997055614, -16390480880865997131, -11290901226373304479, 25235836406924105315, -25784619688575712164]
def DP10 : List ℤ := raw_ints% [5426528357635, -582281917467, -481491915851, 255691701938, 99047883992, -137037564294, -7231281729, 74999057062, -19135720111, -38943331903, 24228495323, 17468089743, -21558551805, -5140310212, 16630556310, -1601884777, -11433874620, 4693645723, 7044659210, -5738251899, -3529724247, 5454656781, 1074743549, -4619343662, 614808311, 3440949915, -1530439755, -2313928824, 1981783842, 1237087213, -1981737119, -414884964, 1782735258, -237476365, -1386650865, 620034036, 977145108, -845080202, -537421877, 870894649, 185771575, -807009255, 112972543, 638994748, -294711937, -455709294, 406711844, 249215468, -422785363, -79492869, 392383866, -65897701, -309731261, 155278635, 216673982, -207798460, -113336076, 212987237, 27729814, -192942337, 42768580, 148409743, -84900888, -98663599, 106276609, 46713060, -104644982, -4797362, 90200770, -26994458, -65701937, 44144898, 39993408, -50221407, -15679758, 45984569, -2363855, -36513160, 14155696, 24175681, -18921911, -12757210, 18738735, 3597462, -15039523, 2101924, 9876517, -4074239, -5823964, 4510739, 2960354, -6303561, 6135868, -5721026, 2438479, 3372174]
def AP11 : List ℤ := raw_ints% [15223601898769786232734, -11562028915051693360011, 3845081934017005530777, 2167028919686407558294, -2856204616182784527377, 271133282869622913017, 1746097461780689406399, -1055513417469011019449, -612142725199183160701, 1160591835943035738714, -113710671128894951002, -787309790335039903915, 552932727376804063241, 363352294247404368039, -612406031290994969602, 47204561472260560113, 497387652604294329777, -299233915483751290405, -262255773425858446944, 384959849316323309684, 8583460106313764362, -364687511132781923387, 159624194579402466770, 199251227674151421071, -288621426316254318032, -73720546293853632207, 249035056069399631692, -128075977628967767924, -217023737238150544407, 166648094257689474286, 42040479593803215492, -250191422596597498590, 27670701766142227221, 140519798019836250471, -174889239444310045913, -110899243690482406356, 154600119171059236110, -55068618297102724522, -181191870914921778096, 84954209864492655756, 63871088786987136029, -176358590252311403944, -12894088486097814664, 124627102716612651172, -98898783259078236918, -101971065192397941379, 123228865184643686894, 1150438722214459336, -135439917398669453974, 62877789217900991855, 90606911434472917725, -112878925371660457818, -13444342425077819984, 129194235206824950875, -40824710090834782297, -77355094387346353811, 116273560852039626031, 41582910972550860308, -96458430351907628542, 58866515441325931082, 107303035694225570867, -71531459700685451731, -9453031586959669528, 128470562255619886853, -11561505688304997422, -64182983682221139141, 105218449327665945787, 53535786057249686237, -81951452033661597141, 47082065965562075765, 100808920896261238545, -62281325223974113422, -19239720102317478734, 110470515064347292958, -14331181733435087242, -71420481876224364922, 82080220430954361918, 39010338467392532157, -90967556802525952418, 25500449801725803680, 77531660274914642005, -75426978163084560306, -37589962799833502179, 85242443730055478647, -32623231884451865309, -86647034568107143721, 60094273939828190381, 18411889633307284465, -104022517796234374872, 8389047522475517841, 60246284587444877236, -85084173140435411845, -56499371929339922385, 88678386124355920291]
def DP11 : List ℤ := raw_ints% [2690684738921, -446757110471, -167451141054, 164971614154, -12474421581, -66596578017, 34295297529, 17281483562, -28895396104, 2525799751, 15747020611, -10033095660, -6018478451, 9307661711, -661190376, -6444657718, 3598095708, 2934625554, -4018489558, -83763305, 3333271535, -1368761170, -1605275300, 2187598792, 526294755, -1676334301, 813653834, 1302335122, -945355686, -225603599, 1270896233, -133127507, -640653427, 755952583, 454669142, -601430328, 203351139, 635320622, -282933028, -202101323, 530321268, 36856403, -338694818, 255591804, 250652461, -288150358, -2559462, 286728883, -126682868, -173751829, 206051440, 23363636, -213757705, 64315528, 116045668, -166111065, -56576706, 124995174, -72656500, -126151343, 80106789, 10084456, -130559726, 11193287, 59198777, -92458076, -44819447, 65366665, -35779926, -72991613, 42966179, 12646386, -69185634, 8551762, 40607100, -44465592, -20135933, 44738822, -11949529, -34616676, 32087375, 15236248, -32919838, 12003862, 30376391, -20072426, -5859290, 31539074, -2423284, -16580071, 22308165, 14112756, -21102461, 12808544, 18375507, -12395060]
def AP12 : List ℤ := raw_ints% [6207044741775331626042, -5162181935543770432876, 2659921037084794520262, -139042799063933656423, -1166111387208463960669, 1003384603840296346212, -89134553183506903313, -593438801007499038488, 556699198618967972192, -38894425820918169370, -379963291520522796148, 349613585493468897663, -220806213719803461, -276659928268333303887, 235496783291715752434, 25067588936664889795, -216219770743117752139, 164182755706658746750, 42358397726737366441, -177652729982933961829, 117878177636947846993, 51781615950906491405, -148185828601532924358, 83483620331162746231, 58929610103597964353, -126998900398337518776, 59657849060165532018, 61314778793175132762, -107909621097718688906, 39561304814001588817, 63877304624100088829, -93815704647264779733, 25699014910233406334, 62971186923156666367, -79777942935619351772, 12829144812582111367, 63141379727242384983, -69481632440047340239, 4373243679828950615, 60580528066412814163, -58612903951383952810, -4087796976481444578, 59345575978121690103, -50747959977105376167, -9202086080193270729, 55982151949953151871, -42238790556696627074, -14624920406286254439, 53898625135419933906, -36158382838912051154, -17492189045174326436, 50246668719139698032, -29599125605837634055, -20675638567198136431, 47704959594175197550, -24978149191477006125, -21946825968539167664, 44101388066207802386, -20115215461652126077, -23438948200190566756, 41411839377856945695, -16774323788376641085, -23549068904358956391, 38091989895250568208, -13414946239419057798, -23774030608723216117, 35507932588792410512, -11229528394065332659, -23049652602382656854, 32634586124474511187, -9185238230065864697, -22379980460940503230, 30370925659385439928, -8042650398311218346, -21095463307247438396, 28055314003913343247, -7110931028906835629, -19871782884936883242, 26269646250397072286, -6847887766871299668, -18323026033494165813, 24616233830899617910, -6816713538672862595, -16859896322785774280, 23381478332174528675, -7160748513921029662, -15351613083391091110, 22212546298797606850, -7128343164220122261, -14846692734689780496, 21873014272330240101, -6033311852948410825, -19154391294413236857, 31158511119473824780]
def DP12 : List ℤ := raw_ints% [1201329304359, -309054178039, 10744146119, 67353465064, -46164168499, 3399613340, 19281763651, -15716249912, 968359250, 8439939522, -6992637974, 4006581, 4582527323, -3579201186, -351119639, 2801562135, -1974192223, -473987798, 1854467788, -1150336293, -473287901, 1270678348, -672589049, -446655488, 906651654, -401575989, -389526638, 647553541, -224422035, -342787474, 476555209, -123641453, -287096248, 344837351, -52597440, -245634615, 256573880, -15334087, -201758480, 185463338, 12292260, -169633121, 137915996, 23781665, -137608293, 98768438, 32537083, -114104416, 72850011, 33543796, -91721271, 51437487, 34208779, -75154721, 37471430, 31353736, -60003285, 26066201, 28929721, -48686034, 18785262, 25122053, -38711435, 12987698, 21927829, -31201707, 9401211, 18385018, -24800592, 6650654, 15439335, -19962997, 5036962, 12588172, -15951236, 3852228, 10257201, -12919695, 3208925, 8180944, -10471988, 2763001, 6511134, -8603319, 2510388, 5127678, -7068788, 2161275, 4288656, -6019560, 1581870, 4784500, -7414674, 4342346, 1303005, -4500151]
def AP13 : List ℤ := raw_ints% [2507875203902454200366, -2144411269220564044276, 1541504607593152950873, -588450881915386483933, -31489207744779394617, 489781767550495068672, -387202179709392228760, 228841514064883215870, 142132949102807905075, -201284966135752158274, 250615648754097380806, -9644138852762101200, -62974033669198045948, 202380937589111854142, -68469282997330410502, 28993612539317948069, 135134825235296150252, -76967675672842698263, 81418811782659358665, 69766821007315014774, -58178037149302252418, 101578523292738533272, 16344081097466787229, -26980088629043916636, 96871245669670722154, -20320838788518675213, 5926620939162642004, 75072145578582182535, -39018885650453160424, 32891053640519529975, 44095346827771464811, -41373619746228186581, 49073829018374923734, 11450258845189955120, -31210726383791106242, 52453463239650521492, -16487994356500712324, -13774919140430428024, 43699485480106280470, -35172948440309077281, 5197373885372947183, 25781889609793363952, -42392244009895185252, 20472237366485287984, 3273196251794280767, -38444435148332378073, 28230872521929351223, -18597781838717613059, -25912006304790953820, 26741320574780654400, -35013404780021059259, -9023823783947299295, 16643477476119907366, -42573407212134612616, 7313228796090211096, 755605634978454819, -40037029822547137116, 18651857596506713405, -16608481930156712215, -28611364199283379325, 22074050436413020878, -30704387646603025022, -11673530110951046875, 16932127612320913152, -37583459231859078957, 6060682005053953910, 5044255140250471959, -35185311969863396758, 19766448356842337467, -9767784612956445869, -23982149483660421095, 25839480013301279862, -22737254765217387194, -6939888408223616223, 22945750967201929564, -29548597569656335888, 11256304408689198317, 12449280632932243441, -27668698332257185625, 25527116113032362109, -1946312210462557489, -17215938287231480667, 31929982285872524067, -15307251644858706047, -1055785554331281635, 28956003387833263970, -23089365062250845796, 16028127410973407358, 18153671919159964577, -22895824141100918936, 29106786277696515153, 3771165754665705198, -16666992375490509285, 38588017109540469134]
def DP13 : List ℤ := raw_ints% [499041709587, -179106233907, 45470907533, 1818786161, -22534099047, 14767984452, -7435422120, -4012574393, 5011416284, -5566803337, 192892880, 1142678797, -3352188307, 1040631364, -406111125, -1750943535, 925486882, -911071366, -728276578, 567741281, -928435414, -140148827, 217366137, -734233154, 145071508, -39893974, -476925809, 234147959, -186583260, -236630719, 210165388, -236100860, -52203659, 134907266, -215050801, 64142122, 50866456, -153225331, 117140619, -16445565, -77527749, 121173794, -55636700, -8459176, 94499280, -66013235, 41375786, 54856210, -53877009, 67143256, 16472267, -28923107, 70439627, -11521311, -1133536, 57197815, -25377268, 21522018, 35313820, -25951467, 34385289, 12453275, -17207475, 36386476, -5590033, -4432513, 29456674, -15766247, 7423009, 17364492, -17825950, 14945337, 4346323, -13692285, 16800262, -6097916, -6425935, 13607763, -11962025, 868997, 7323828, -12942103, 5911518, 388480, -10151287, 7712208, -5100695, -5504097, 6613750, -8010329, -988760, 4163182, -9182645, 3778447, -814454, -5988425]
def AP14 : List ℤ := raw_ints% [7590268516443580551815, -6452690368552015705773, 3670741383408102629969, -712699887981029688882, -1073438328872941276351, 1255670368001680436334, -414302113439639944610, -445872704865791810121, 656896183796369934756, -251907442079600139727, -258315547503671810964, 412692593405843163826, -163205611881068044073, -179547557903650762488, 289262524186684704474, -111778981497272390709, -138233080769627051176, 217570269303392841320, -79872614521559896519, -113039341011940387494, 171661111432370017500, -58843295283290046050, -96046889649249251975, 140137467151223768520, -44297870780331359819, -83756303874052984306, 117353514464654310978, -33862803824610196450, -74396309692217053800, 100233023523942567832, -26173485632912306167, -66974929719099589374, 86970685287966880984, -20402381549310167815, -60890580410455366023, 76440746654733738133, -16022676566375396232, -55756073437747652575, 67906212506457262987, -12684836466253134323, -51310681458557721629, 60866121247695130792, -10150887856936832211, -47369179430677475267, 54965795457052335580, -8252626952155691480, -43795378284515350188, 49945236786386126104, -6866164455816738258, -40487932948576964694, 45610369961903122707, -5899959639651096551, -37366803987885195343, 41809778826983454391, -5282481105487651412, -34367898424833650988, 38420826639258377040, -4952836321168124250, -31443301296640391105, 35346279057212481294, -4861802456818722531, -28553450585549789873, 32504269742279160440, -4966112537967232125, -25665592298980011105, 29821318414120275738, -5219574893014536415, -22762722870934353422, 27241806386623441865, -5583854727097856754, -19832458226564223048, 24719257655251979984, -6025224440803820211, -16862770207303990545, 22203632440605836544, -6493218553106911802, -13871009932192153226, 19674686381768377018, -6952156015032062785, -10881563499174118105, 17134603158638779783, -7392501723649896385, -7890299930702280362, 14536415563497720836, -7708849015119805824, -5032514879576750156, 11937739472078998233, -7696375700360952739, -2941202928937997585, 10330062027167032709, -8119987966054143170, -2376140719785377406, 13949264912252080537, -18880542877287924827]
def DP14 : List ℤ := raw_ints% [1501653008067, -426500616080, 55071904387, 62000758911, -57771444993, 15801582456, 14487108188, -18544924469, 6271770225, 5737837436, -8254284215, 2961404588, 2973981794, -4396360558, 1565678917, 1791087668, -2616142796, 893769515, 1179986464, -1675187134, 537832185, 823592271, -1129022979, 335754589, 597940543, -789943893, 215126994, 446443915, -568598514, 140455879, 340212246, -418427785, 93017893, 263197391, -313394823, 62331928, 205889695, -238102389, 42245807, 162357598, -183028219, 29015251, 128733599, -142052373, 20285570, 102408261, -111116664, 14535800, 81572961, -87464467, 10769903, 64936192, -69176170, 8322057, 51557635, -54888871, 6738709, 40745644, -43626447, 5715802, 31976493, -34675427, 5046870, 24848177, -27505509, 4586570, 19056648, -21728792, 4243439, 14359871, -17053139, 3960417, 10560840, -13249445, 3691808, 7514388, -10155466, 3419145, 5099108, -7650333, 3144842, 3198156, -5613829, 2836505, 1764280, -3987392, 2449248, 891757, -2983970, 2234660, 622998, -3484333, 4492931, -3162333, 513171, 1670604]
def AP15 : List ℤ := raw_ints% [4988088988509113108641, -4152935049526814850877, 2177407464778008021468, -239657634345325025110, -714466845915398515216, 582515288364367561136, 11065388974558053531, -360127382149704039766, 235311365968946641268, 86583566950216789301, -228351056886062140352, 95234656265966729966, 107100318205248758206, -150669347733668421470, 22708031186922651370, 105828918139521207354, -95686962072780794972, -18281614167726527049, 94211704352956077994, -54056158813713685375, -40937661170584626387, 77433097380307324160, -22173809493857480194, -51500730465674974299, 58464550100033360026, 1660449894246233546, -53614238642030349205, 39297447618287289107, 18478386152573919072, -49803955588322535419, 21361929930930752874, 29117161813751559641, -42041437592256276688, 5681101624044120767, 34407317499615463970, -31960265573985913162, -7070093768757669244, 35237657590602652483, -20931891054059262358, -16533677173068520494, 32557988293191278786, -10083916240875313162, -22637442478901309760, 27345837571915333027, -293663990377305762, -25560439549307912306, 20561777138728078196, 7815762670027110888, -25684562080457260174, 13097174254603766552, 13873584179887841681, -23538484332195651443, 5725397683221963553, 17748728882548167728, -19739651414019286744, -932658885280477196, 19517960826597080999, -14928905118192726776, -6436707832139844835, 19429519193195056950, -9716426841099120898, -10533277739033957386, 17853366049370796926, -4633894159624818241, -13145706529409947895, 15223689029020044742, -92474594933642748, -14359243962968638068, 11994479808267375664, 3628936411060243287, -14376915414005257271, 8581921667748996636, 6396984109628349632, -13481936701648038594, 5325667010278028182, 8218771114719737903, -12002535225998264018, 2479768154366684458, 9191790197180939416, -10230284357390498886, 154043164121695226, 9520783945298171047, -8430458143789619521, -1639271061385878697, 9440742803597526569, -6794830206711212695, -2928903897289402309, 8997523790635933843, -5006174611996517433, -4479533181456836625, 8936326800309498224, -2940386324463644323, -8179493485624921055, 13678337398374981465]
def DP15 : List ℤ := raw_ints% [966460042748, -252991297449, 18518878067, 41266913498, -26800624429, -422036603, 11701107266, -6643106805, -2155681598, 5072250801, -1904792896, -1943360711, 2495650190, -345128333, -1482336875, 1239817103, 219824672, -1054223027, 564277313, 399497840, -707744389, 190138152, 414917646, -443130577, -11854037, 360894520, -249652742, -110886725, 282526198, -114635426, -147906315, 202267069, -25901100, -148724420, 131031971, 27504304, -130121620, 73394363, 55064055, -103020203, 30322964, 64706761, -74316849, 758938, 62829461, -48080322, -17388275, 54374706, -26387499, -26604600, 42967618, -9949621, -29366075, 31097982, 1399145, -27883805, 20311908, 8340975, -23981050, 11423165, 11796027, -19045901, 4709249, 12727033, -14041476, 81259, 12021367, -9567118, -2757804, 10409735, -5920433, -4204778, 8443486, -3177955, -4672896, 6502173, -1279980, -4520622, 4793918, -68778, -4050235, 3417097, 633071, -3473764, 2382105, 978299, -2863318, 1517845, 1293970, -2459321, 770938, 2043123, -3254983, 1854310, 635031, -1838559]
def BsP : List Blk := [⟨(1 : ℚ), (0 : ℚ), (21447485891347866308077 / 365105150036574287470660 : ℚ), DP0⟩,
  ⟨(3276730368397 / 4398046511104 : ℚ), (-2846434036817249496802584327549855809799 / 9671406556917033397649408000000000000000 : ℚ), (264484213123056782577 / 5142326056853158978460 : ℚ), DP1⟩,
  ⟨(1305092809445 / 2199023255552 : ℚ), (-50459512470861903514431699337636266627633 / 96714065569170333976494080000000000000000 : ℚ), (1432551375017176819673 / 36510515003657428747066 : ℚ), DP2⟩,
  ⟨(8542441030865 / 17592186044416 : ℚ), (-8733377158418276106796407556106148303303 / 12089258196146291747061760000000000000000 : ℚ), (16591175188275269403923 / 365105150036574287470660 : ℚ), DP3⟩,
  ⟨(6896403054357 / 17592186044416 : ℚ), (-181136711433848873382792786417759206259407 / 193428131138340667952988160000000000000000 : ℚ), (775187970104422406735 / 73021030007314857494132 : ℚ), DP4⟩,
  ⟨(2976343721197 / 8796093022208 : ℚ), (-3275016434406850332866121948892436228973 / 3022314549036572936765440000000000000000 : ℚ), (3438243414800643975774 / 91276287509143571867665 : ℚ), DP5⟩,
  ⟨(4805667573359 / 17592186044416 : ℚ), (-251003728701191018592854999347220598140897 / 193428131138340667952988160000000000000000 : ℚ), (2000196399719197712392 / 91276287509143571867665 : ℚ), DP6⟩,
  ⟨(511616124031 / 2199023255552 : ℚ), (-282055736375561776914842081200209473889673 / 193428131138340667952988160000000000000000 : ℚ), (4554132525111658667207 / 182552575018287143735330 : ℚ), DP7⟩,
  ⟨(3532845575111 / 17592186044416 : ℚ), (-15526003837186727201177233263846439039421 / 9671406556917033397649408000000000000000 : ℚ), (795642070920482614446 / 91276287509143571867665 : ℚ), DP8⟩,
  ⟨(3132095659693 / 17592186044416 : ℚ), (-8345227062488155416624620250623650617991 / 4835703278458516698824704000000000000000 : ℚ), (3434720484968852681757 / 365105150036574287470660 : ℚ), DP9⟩,
  ⟨(2597141326789 / 17592186044416 : ℚ), (-370036424786292096417260675745534622838311 / 193428131138340667952988160000000000000000 : ℚ), (128622313539193965297 / 4804015132060187993035 : ℚ), DP10⟩,
  ⟨(2124937635887 / 17592186044416 : ℚ), (-408851434379226432243644719811994253074577 / 193428131138340667952988160000000000000000 : ℚ), (2298824032527992263163 / 182552575018287143735330 : ℚ), DP11⟩,
  ⟨(108661779151 / 1099511627776 : ℚ), (-17906657758888708979164490742088108331339 / 7737125245533626718119526400000000000000 : ℚ), (1874576557933074068649 / 365105150036574287470660 : ℚ), DP12⟩,
  ⟨(1295321823375 / 17592186044416 : ℚ), (-100919024941704288683653862844431468802141 / 38685626227668133590597632000000000000000 : ℚ), (151479625587894055647 / 73021030007314857494132 : ℚ), DP13⟩,
  ⟨(422113244307 / 8796093022208 : ℚ), (-587400478506638731396024528063810947569941 / 193428131138340667952988160000000000000000 : ℚ), (2292321067637891354063 / 365105150036574287470660 : ℚ), DP14⟩,
  ⟨(349141633395 / 17592186044416 : ℚ), (-151637304143068635474707076414507938439379 / 38685626227668133590597632000000000000000 : ℚ), (753221144340329635171 / 182552575018287143735330 : ℚ), DP15⟩]
def RPd : RadLit where
  NA := 93
  CT := CTl
  hq := (365103327107 / 365105150036574287470660 : ℚ)
  Cq := Cql
  δc := dcL
  s := 1
  W := 48
  sh := 112
  Gs := (List.range 16).map (grp paT)
  As := [AP0, AP1, AP2, AP3, AP4, AP5, AP6, AP7, AP8, AP9, AP10, AP11, AP12, AP13, AP14, AP15]
  Bs := BsP
  ns := List.replicate 16 96
  Tls := [9916535809627000250981222793058125222233601, 6711915447024921836769667028511263275209834, 6183148445886325108320574203608909135519371, 8969919670266225197747663861893189609803561, 2106519086111828713291590562560577669300362, 7758864428163037297718246048326436156453724, 5141039358708297133199037277234900244585199, 4607042773091085707429849084136073866042655, 1675623419669489519033875007307741405248308, 1568163495380289563469599332805931773449758, 3504419186012446585470701346078817688734583, 2386368582025812044431790464775866129552171, 907138013463251214580065100910853194049560, 640913243933900595316971836706401804079754, 919383594683689532710759058941303914334379, 520841849872565186816793585976521786111611]
  etas := [(0 : ℚ), (37404884055593501 / 316912650057057350374175801344 : ℚ), (62745745870815631 / 633825300114114700748351602688 : ℚ), (11711144910478457 / 79228162514264337593543950336 : ℚ), (319361129837801841 / 1267650600228229401496703205376 : ℚ), (4412697932863827 / 19807040628566084398385987584 : ℚ), (439808553525426143 / 1267650600228229401496703205376 : ℚ), (516309778300344375 / 1267650600228229401496703205376 : ℚ), (147397393848122127 / 316912650057057350374175801344 : ℚ), (69714487683429021 / 158456325028528675187087900672 : ℚ), (647189962250053657 / 1267650600228229401496703205376 : ℚ), (933573703881399087 / 1267650600228229401496703205376 : ℚ), (846941453063133933 / 1267650600228229401496703205376 : ℚ), (1267034594534226415 / 1267650600228229401496703205376 : ℚ), (2812784006849544619 / 1267650600228229401496703205376 : ℚ), (5428270652266624033 / 1267650600228229401496703205376 : ℚ)]
def AN0 : List ℤ := raw_ints% [128062240450582495904990, 56462992399781840042644, -24566019514480631783832, -3914778344825843261677, 14186545475402308072866, -7708779384944937306735, -3092635151793717429467, 7414319368146059862390, -3705645061511401086300, -2261994182429799282759, 4586146743230946213179, -2178736713712781834751, -1623596931985352870304, 3132139670849476452347, -1484396757873358983867, -1182486069665196776383, 2303617405810752633142, -1121080567546830485775, -886053384027386034790, 1791744091495984313761, -904859167881194449296, -684899896580080250951, 1452699097553404844558, -761697196582817571582, -544910002489773837355, 1214817442585838345989, -659072870437106172552, -444749402614638106662, 1040129111498775574092, -581184574769454639782, -371379368535168390282, 907226025853329651109, -519497703231633612836, -316741499580668640786, 803278396790722484615, -468938897707911467921, -275727641254954942330, 720142975198506166264, -426232268397509413679, -244956392472210427573, 652404432818819438763, -389142191524501868789, -222128084270877718116, 596296320657401153534, -356059463633477533202, -205606094651729405961, 549105895461507330047, -325786433062885747850, -194190809695727990258, 508808668088893401382, -297403738401020774681, -186968134814875690836, 473844923620563367231, -270192618556824275389, -183220421070548647882, 442968816531956574390, -243578250123335251362, -182338868972346836798, 415168960262011346305, -217116060153156619992, -183815487441077678889, 389587405550057997387, -190456338714882502485, -187180283074309983042, 365491812566431391916, -163335763867743275886, -191957976035843835428, 342280362857165999283, -135620225610117303854, -197799041738905682070, 319369840095480553219, -107170894278000635164, -204137241599306822255, 296399455860933269430, -78081052291201496447, -210727602295893775000, 272941609195746391385, -48373935477233692206, -217047132936356461731, 248787853764937260795, -18199693028385324552, -222419153292139596081, 224122695166341042509, 11707755722356365493, -227676783152408605008, 198171079781730224546, 42371796542875882399, -226914856302816827151, 176213392736657606753, 66033700150089784647, -233653690677747314893, 158457027233051036648, 65746669726337992401, -335438186847296173093]
def DN0 : List ℤ := raw_ints% [13139918009214, 2854306899667, -302503623674, -819401135723, -354668976464, 117953850039, 240902943062, 104614563866, -56317144290, -101869843792, -43577016771, 29460551933, 51879994739, 22560625079, -16562984250, -29847998066, -13480274027, 9914881450, 18703521766, 8830237806, -6260037046, -12456746424, -6136643219, 4130131565, 8672643941, 4436429460, -2825448330, -6241698218, -3296924244, 1992948763, 4608431925, 2499374042, -1444077845, -3472142606, -1922574398, 1072644486, 2659262187, 1494515999, -815807173, -2064342429, -1170174815, 634929892, 1620534128, 920192116, -505395072, -1283993485, -724799879, 411105641, 1025120986, 570314588, -341295361, -823449748, -447045907, 288646709, 664527824, 347981451, -248085867, -537994620, -267977352, 216103583, 436291899, 203178068, -190224173, -353851387, -150651730, 168678261, 286552559, 108174311, -150317004, -231242627, -73934263, 134180664, 185629479, 46592851, -119812086, -147861567, -24969133, 106746114, 116582165, 8125878, -94619289, -90843109, 4521426, 83774680, 69474071, -14152842, -72212021, -53426964, 19074674, 64302630, 41545747, -16422603, -79822959, -14904930, 34221738, 48071868]
def AN1 : List ℤ := raw_ints% [89418105288470362243581, 45161184762039306419427, -13690238606380116360938, -9217865178706131447600, 10851490651329229441684, 28270591066985140154, -6937373440283072969003, 3672961161851141033254, 2940967267120086119015, -4353228592436929454787, 281172140058119079341, 3219231491603009266357, -2120315005473020010534, -1291866001016468687177, 2534574983575455121906, -484941199367720347412, -1791005949812941167881, 1556326238020455422734, 559555771380513227913, -1673604594783975561812, 618802088189327940813, 1081745433175032978550, -1220072936160130583433, -134198855937544723143, 1201252257020123551104, -645619024982772988973, -623279532790181985812, 1021760978684410404759, -82916221495954422404, -848644622765452811240, 671689588200419353631, 357059929004529035912, -826670384941541307406, 249602588434868452125, 628803554241501779155, -627321002658322529910, -136039266437343045611, 702377054289864425845, -315279184753157109193, -423652804113698078367, 608083665778994272544, 14445214993462198628, -557908936694895492706, 381764233551021157201, 297778409880245994851, -541686098849632397443, 102288796351644825598, 466018138558960085216, -387082541539807665128, -169950231021479575562, 503269583821991147650, -156843744911369344004, -359713732061069165844, 402797166390285272744, 95381509444413152693, -438125283451133208789, 212786927845155041023, 292201516110395501900, -383490443419732404685, -20765935003433983081, 396134447681435404932, -231183252867889620986, -220732101741114189830, 373937623306620454619, -19438904708449603407, -343907935676167822796, 250281087362973537885, 176303336526769196716, -348237936675465509009, 56254029248052084652, 309318594283700237365, -249584992548128660580, -135090809915552636292, 330886730430810996839, -72706208302844434350, -274767620633995403810, 249908844991701214182, 111613958246655511011, -309541581135100021611, 85827315723332334584, 253498372205489156065, -242775620843277238567, -93100466692282716810, 296176779523288548732, -89417456861551216342, -236031029680813903791, 238136823561823733355, 80040562827689676073, -287595802805194980067, 97435694775802530827, 225650297132106546804, -244481119039204516720, -46129205423346985357, 363648128151554799315]
def DN1 : List ℤ := raw_ints% [10509791276568, 1590658286714, -712284929946, -626771597033, 1300686022, 264593094975, 119340307546, -83026842261, -108382861756, -6245539795, 64388002375, 38473619347, -21398152184, -38521773669, -6792531137, 23206085347, 18713823761, -6261393770, -17470296186, -6038696173, 9887235374, 10462000843, -1081178326, -9104861063, -4609107286, 4195493101, 6491144975, 497570951, -4814162579, -3604516158, 1813755700, 3977223554, 1137980240, -2717981238, -2571915670, 529224304, 2593658212, 1105476569, -1410940914, -1924102364, 43437661, 1594724334, 1037507608, -769571865, -1331504717, -239185464, 1036783167, 819461110, -342406802, -965092057, -286305699, 625112071, 666446128, -150264685, -657261710, -303992266, 397562334, 496944172, -25630533, -465717416, -258897950, 235476132, 380018523, 18819801, -317201353, -219928235, 147598804, 277763872, 42750141, -223964932, -172181846, 88796020, 207228219, 43385552, -156222922, -135383951, 57611680, 152235878, 40218741, -113183064, -103279129, 37736186, 114380714, 32901549, -82746870, -79541417, 25471627, 87197518, 28145540, -62100058, -64100350, 11522433, 86535971, 10457602, -52800240, -46425252]
def AN2 : List ℤ := raw_ints% [65732897919374457575440, 34348693250229143391184, -9137948598951094288414, -8058339139390540951930, 7703141498555772375116, 1425380556702448982235, -5622074848127971565758, 1623025289658534630342, 3299907676579201866293, -2814912133251580320759, -1129872637330354876620, 2792144665057521346583, -518782407169368182003, -1985205666505755760340, 1487882280920226221750, 875858838489265673668, -1708365325825498737369, 201843869191799034649, 1373630452353007369395, -913645463751813564108, -667960342000789066029, 1196871073676827726679, -61540133359257175481, -1005292838346463583510, 649653740864554567775, 555800046498432827184, -879924711986861064071, 26735249391843162552, 810299160855510413998, -467676554801446415495, -446822397161768173351, 715220695010751659368, 21422705299058798466, -649908636499945103845, 384753666336758745681, 404927121808125034595, -572423355538152427486, -19211432240697695387, 572180197982313677349, -295521314535976553817, -342788956187908176753, 503378796860234291151, 48839559525075008184, -485349115443386457886, 260790978772931224611, 327107852309218628340, -423342998198287221952, -43181743454338853250, 447781503568578179765, -207534806901121416751, -289906054477035205067, 386750553641638451469, 63374335489548203006, -395761961619975524234, 187708764756480613719, 282381426070608459254, -337432118051394628126, -60430941828195235414, 372933901959616726357, -154008275426663220663, -259916898124040073111, 313409386915154603669, 73181106038720337164, -340417326722016448209, 139795425749305385670, 254177710675737658015, -282116614811707222355, -72627359897992570373, 324116612905880940170, -118703655705461727726, -240512521444599363383, 265022553536084677086, 79760721493111109322, -303797758829882989597, 108465243103949128292, 235726064247205205563, -245753164225983169971, -80229846499023938097, 292694411570818862423, -95914502589379676070, -228080138068738814068, 234834690241250936717, 84499217291370347028, -281659885127643322953, 89086222729312638884, 226555405945212108266, -225062665220311392450, -89927813318802584014, 275272167816982268443, -77874693029488336981, -227574163276168342342, 212246682561959627749, 118606237085026934145, -205866426496708600688]
def DN2 : List ℤ := raw_ints% [7993536896450, 1061731214510, -622685775730, -444925997206, 65579547405, 214427289673, 52734654326, -93160137211, -70083209764, 25097310555, 55845818418, 9413429988, -32882460669, -22613599852, 12268082067, 22135309801, 2427042931, -15370838075, -9537292686, 6518416207, 10939492468, 527700359, -8099181022, -4924034078, 3967884998, 5923053565, 169846356, -4862514444, -2653019779, 2397801869, 3633103317, -103067547, -2963042938, -1663084185, 1660136365, 2226859641, -70941796, -2006259320, -984209498, 1084655086, 1513691403, -139602772, -1319016702, -673982375, 804055428, 989917711, -96069447, -947961969, -418130231, 555936697, 705982171, -110132193, -654806064, -295717677, 423619694, 482063230, -82220882, -483264531, -190086029, 305572582, 350981511, -78069315, -345953127, -135343129, 234439235, 247902906, -60802659, -258524061, -90208616, 174145270, 182831796, -52427213, -190262900, -64723833, 134025306, 133132679, -41412171, -143950260, -44945605, 101834218, 99900979, -34249863, -108774425, -32779671, 79424941, 75174443, -28618088, -83461058, -22495097, 62629515, 55648823, -29626187, -48989256, -26888322, 45838613, 46821067]
def AN3 : List ℤ := raw_ints% [75069536797596594169130, 39532464564584692748969, -10133147970573319693398, -9507230964992306446815, 8612453325112772202427, 1986637230908998074693, -6396687367871160826797, 1504649026443391301602, 3901197843903481924573, -2953175910217792417591, -1538384321567961144921, 3063434962814192541111, -306060870494932023924, -2297628024293440700318, 1447831984293799869083, 1153077408191299070561, -1803883597524146639356, 7635395774006106267, 1547441589153976174973, -831045162605004547201, -864753487943700457633, 1220387494078527266304, 100966104334000890724, -1113432297995718783588, 555361102088823512776, 702832912266143127855, -873767263646239602250, -116510458613776087841, 879676606856024309556, -372942628005602958505, -567513522502896426564, 688754580593381421549, 149190815897920085682, -698253656785437309856, 285515258774258743629, 504854893517133252405, -534468355199805506443, -140833247998127846469, 601054804664220480008, -194703120857001887948, -430715044743407416783, 451168947755590860135, 163256431782072140617, -500647670999763395505, 153476032609515110419, 401197202568218472849, -360273515768289087238, -155049123765508592424, 446251922541299910819, -96238369219795204469, -353245302589905809220, 309102266903471925086, 169598379797084484389, -379164143864933521280, 69737824555778981812, 330997507542305649774, -246968179609246595742, -161848685590649844949, 337458012909903211286, -32432844388127462621, -293378173829964617305, 208102498615568991176, 165300573071075242810, -286118406701094516496, 15242717046637415420, 268013518938674898946, -164207476105586375061, -152993033961275456058, 248717583295281313444, 4149255556582055743, -232764228512137805645, 135763720461104458872, 143034554516253538587, -208241783654925572915, -8715419956963124961, 203291369510553629124, -109628730861821136622, -122568198200262791641, 178098364026598474639, 9490272641042559194, -170374592353238046615, 96661137382831176314, 101683144723692237709, -151988061125439735403, 802825905493447776, 144090343837023600319, -91537339523679755397, -80421084420512656910, 135261135259724783705, -11505454771773934870, -123750100478286975513, 88475225316719567081, 84752756561627921131, -52708344700513318171]
def DN3 : List ℤ := raw_ints% [9199890423852, 1177362663524, -734644867395, -497446968200, 91402095987, 243971197864, 48888422624, -110135240754, -73525579836, 34171381620, 61271908583, 5553547184, -38057348120, -22004894853, 16151059568, 23372941181, 91810731, -17315773727, -8675050953, 8438859010, 11154434335, -865774035, -8970410803, -4209345410, 5017560157, 5881605819, -740179254, -5278840722, -2115616356, 3045471744, 3498663516, -717777289, -3183456028, -1234129660, 2069824230, 2079205885, -520053023, -2107503559, -648442774, 1362871397, 1356693134, -466651433, -1360593063, -396640027, 986172561, 842440139, -344948637, -944723817, -193896013, 677398846, 564241440, -294728795, -627344224, -109865448, 496552004, 352824382, -220207418, -437293278, -40030516, 344911495, 233050229, -176341998, -290771209, -14757257, 247200607, 144293205, -128083730, -198383783, 3153218, 168535048, 93659669, -94017493, -130417966, 5200701, 115584112, 59389537, -63265922, -87590691, 4447148, 76069594, 41120595, -41214983, -58696374, -295404, 50514650, 30574900, -25592723, -41010458, -3323498, 34056628, 23197263, -21170059, -12542806, -19213656, 19107868, 25460323]
def AN4 : List ℤ := raw_ints% [17891334238710373542996, 10347014083711492969378, -1435593234340551984335, -3149847302980187724554, 1368053680581249866501, 1550373515940724175722, -1256748190173149698266, -770599114332734510001, 1115968741732438763628, 297675138423057313737, -940548677504848584944, 24483092055779598375, 760396832659855603557, -225108965184580626699, -559050140649291055924, 360275560215301922926, 380496164421948028117, -409415943131604855249, -194550946916247885510, 427959757957634657217, 54687201745986809240, -379821283998310400023, 82974514653390356933, 328547788572773507686, -160523123311015213580, -229603479968821349471, 233589915530177956045, 151823699652284325479, -243830326870431706125, -44623305723606545075, 255102284315108272774, -22823414183169861870, -211041672220565879874, 105631102960471976347, 179102986400943600737, -138771338531389010011, -105861671314273589637, 180048459095807487167, 57407735726492165043, -171518062429337561972, 16696409903200603760, 171143657409503286062, -56118173972610454102, -129165671404390421985, 108480057985712546665, 100667273714537220467, -122226175949147140962, -43603294927620920871, 141995161634241754686, 7163594169871564993, -126228973115770888006, 44355321992165468332, 115816712531882472334, -69967217104892273172, -78651376067014029332, 100552077869384494641, 50635780004226969196, -104405396434839145448, -7311585635847382643, 108611874452304551104, -21700139792278134583, -90369375954078219178, 55533194229079833886, 73250781062172384081, -71674834077145745903, -41735814184404739381, 85980517879675021394, 15514537075864784692, -82990788115427743951, 16006169633959886016, 76568793940775213405, -37596231663968983271, -57247723458179229675, 57262434521936881795, 37201961998006652545, -64561411713930316323, -11101966810471385487, 66689960876566968995, -10912231829297009884, -57633229867207377588, 32128632379151848116, 44454355358776374106, -45189843163943090740, -24576213149549691892, 53155320712525086159, 4787742975856451607, -51882629665432502774, 15171574346940422781, 44177222884121187579, -31299598930805459617, -30899337315910618999, 42650609215657379434, 20546784818625372557, -29177063412488516744]
def DN4 : List ℤ := raw_ints% [2407929706196, 166800472965, -243395701938, -79017456473, 71330279487, 47932678859, -25037981958, -31505063563, 7411254127, 20891949651, 489687490, -13797581123, -3728649792, 8496731454, 5046349874, -4930093319, -4922963848, 2177012818, 4467353728, -533675310, -3471595369, -711497991, 2646958092, 1216680948, -1639151004, -1572368140, 964520730, 1463198462, -253137583, -1368966145, -115935994, 1015350162, 481589989, -774166357, -568940270, 411826458, 664862500, -201291141, -571226839, -52830891, 514639640, 160407929, -351029131, -280353437, 247447645, 285805734, -97007302, -300606461, 14432833, 242062272, 80967089, -201266782, -115763925, 123907917, 150845050, -72339432, -142051464, 9474681, 134055133, 25511876, -101203032, -59242592, 74441970, 69392086, -38494770, -75553226, 12988563, 66195667, 12163857, -55440330, -25936610, 37629280, 35862400, -22199311, -36707282, 6014305, 34423299, 5366752, -27006973, -14344933, 18911318, 18316689, -9491105, -19558736, 1678468, 17329608, 4828110, -13394300, -9041288, 8503647, 11182536, -5132301, -6943156, -4658006, 9211191, 6357224]
def AN5 : List ℤ := raw_ints% [62069323904884186481523, 32938632978684917541237, -8150145118010519807286, -8166997552891298973363, 7047907463440608730366, 1982248070868011576230, -5384790110817439723200, 933848813463980313676, 3500057495606213109638, -2281094814113605430309, -1629100307403160852519, 2549218361186744189112, 104823516042536713129, -2114415482673400029413, 959630921342562841712, 1283963180556914669270, -1428728661669769856228, -359525625405561638771, 1416843939304470789432, -408548843665242308281, -999174012233021502246, 887686102479101898253, 427190222394353739325, -994365145831575981042, 162933208569780639747, 816840333032357183922, -567944660053022766676, -413457731454530282925, 750555830221936769506, -9010313985824850483, -667924423125767067281, 391593636001485074702, 413581495730714013650, -563961138143182092080, -66257987190474646181, 583727735200115826781, -247635231658425027733, -386769678464955660590, 450222303689017815036, 142357143634831931945, -495920812687767089363, 160103611300667567015, 386449670163638245175, -337954381545202670266, -180224730591018070447, 443078215893608545339, -66639940719906027316, -364054297411396217490, 261683310674574534382, 229101603124978908738, -374460316565489144498, 2484227512083326233, 358147998107458768339, -175296768588982637069, -252163199236941648556, 321825228558515413919, 70540487731634957495, -332473229721757589126, 107251486879483942046, 279510757717952544702, -252849077325559523433, -125123501160051927263, 310757962217070450309, -31091088978368645745, -285929991979719070082, 188328122915182190011, 180923214404445170605, -270992128637610894108, -34281933180199698800, 286813310146499950538, -112007930973204597453, -219951528092619037512, 226073655755318438541, 100178879494812510376, -267888746931476943977, 37383901858333410436, 249672433564563790921, -166165539869737762390, -154183102507822693609, 236916819785996729310, 40143892717672342589, -259500364275275145060, 99957873968267330258, 198625632035939738699, -188633860720928747639, -109758314974098610745, 251872322268041094903, -29824976411665987636, -227316835659682259810, 132811375927590830950, 168573033365048910698, -231453447669044087422, -20233301375424887683, 301058501138262628487]
def DN5 : List ℤ := raw_ints% [7665391405596, 946959088342, -631082052845, -407080313529, 91200157545, 205377192604, 30342222443, -98810593657, -56792695040, 36186411627, 50987037845, -1902047595, -35022660432, -14584964106, 17984365720, 18512054225, -4323064810, -15854394267, -4264728555, 9750626894, 8113518361, -3663112536, -8011141641, -1234948129, 5831464973, 3823016444, -2626655483, -4504001413, -51113406, 3584310993, 1989176415, -1989796776, -2571193817, 286397818, 2393190252, 963358496, -1428219141, -1578633263, 474108790, 1569195920, 481441533, -1104625957, -918447071, 465768763, 1089119206, 155826499, -809937075, -553988552, 461581879, 718081697, 4534758, -622391133, -290036432, 397259635, 482792041, -100775752, -452355057, -138981303, 344988539, 297263263, -140123550, -331515365, -31596687, 276823503, 173703276, -158981742, -226871000, 27344184, 217963226, 81100357, -151738531, -148599605, 62740173, 159855690, 21255133, -135255879, -85769524, 75828907, 111019390, -17923622, -110393999, -40515683, 76707369, 69408664, -38478657, -84129288, -9491322, 68921255, 38364256, -46392118, -60684633, 5053996, 71641754, 4586938, -49986672, -34682186]
def AN6 : List ℤ := raw_ints% [36333450041658091375290, 19572187843322981458730, -4503752137494510983745, -5070011529413328794689, 3969091033615907856793, 1511879530576618432241, -3164762172294011209527, 219482938785771662172, 2213216264341354500819, -1092657436254277268129, -1236941392795209242002, 1406871195317551794992, 376249188276995547323, -1309758764470194918962, 291566205582683601852, 968402655526412141556, -686997143900480805572, -494091949673450424574, 833188938100104371578, 41754553174956963452, -735234559968753617416, 328832837835667843304, 501219642049403256164, -523431770995661568417, -178597776154123738611, 569305656413290609677, -106595726280370435290, -448529365212423457423, 332182353033198964590, 256798741766926184715, -417682874927554356201, -13526326661931637234, 404093976188832940168, -176189368503756530054, -271783863016171627662, 312613082485823052193, 108508373902383605957, -332407577678847856628, 78432408826976982528, 283348599848552478244, -203618172606851835858, -151295140194137288880, 278507655577864594960, 13372769252938130829, -257779378149298481569, 127252819460580729785, 189132096576568745960, -205066244603439342277, -66394871217141170517, 235767782984356862944, -46603945468084222698, -191273722284815230096, 147256913531197736077, 114776263627798729286, -189219232736568146623, -7707528955576493245, 188826267865293985323, -80363469372054477077, -132760386508793879696, 146627726816566787702, 57650596342972897200, -161714217098545827106, 29682336846461769858, 141249408705288086588, -93242229746584129116, -82988552611827119432, 130840938436479711518, 16567767305984308598, -126845198319931980552, 48859939670601270522, 95974878976849771376, -89218853607436980365, -42957767864235321130, 104202172488847415732, -9298650949474019564, -88397497601251152734, 52220909781640677054, 55547624337944260500, -71821671547221184059, -13610716899314300193, 70552028759193018352, -20914102131783121630, -49842395680072116381, 42450627930932621207, 22235032320757357693, -45157807143026754382, 4881119188472566257, 35928444799718568407, -18983750385924976124, -16540565880622112796, 24303073586199947479, 1597800677441222066, -29275124043164781026, -30558890767082251071]
def DN6 : List ℤ := raw_ints% [4554787704152, 523287494454, -391771059464, -229250856481, 69559230958, 120704791984, 7131347232, -62481605873, -27204025092, 27475576670, 28138897778, -6827130881, -21694523537, -4431373092, 13564335633, 8901430146, -5941138460, -9323331637, 435864249, 7174924273, 3005557099, -4297907251, -4217048510, 1353677321, 4064302239, 717529793, -2849462053, -1993389069, 1456759236, 2241429222, -68709621, -1944151031, -803277007, 1174776184, 1281663585, -422122746, -1227476950, -275010831, 943669270, 644289970, -454953913, -796085000, 36342717, 666199260, 312796894, -442254185, -456225227, 140559206, 475012548, 89369791, -349154867, -255903698, 189902518, 298097278, -11562592, -269761520, -109340598, 172036882, 180976523, -67777208, -181100831, -31665000, 143546378, 90272589, -76543978, -114973197, 13870314, 101175115, 37131017, -69491481, -61549642, 28236405, 65259887, 5548729, -50259617, -28289808, 28671969, 35322670, -6377992, -31500379, -8897065, 20202497, 16394037, -8181479, -15831255, -1630370, 11433652, 5755772, -4777954, -6688324, 418926, 7312518, -7271984, 6636741, 345074, -5000110]
def AN7 : List ℤ := raw_ints% [41400792226355465132898, 21670629258187798935827, -5746517580960655227595, -5135503393867433406529, 4881405602036513235198, 963164087460908085442, -3619128265622835461617, 980690870302609655265, 2191988439947823660802, -1784255427400555460312, -836147745365057343428, 1830063847578960081291, -231127732962280261605, -1376700914363786048841, 897033284804468416152, 698719776878854760339, -1113218263688521443159, -7024026503709622609, 967875247923068054549, -498133023877457833562, -568035098155117668303, 750284744266315573381, 105401009315150439389, -711121071343899485756, 303932598905356518244, 480019219761366216943, -525283788694091021514, -132052830313067882185, 559481694500686798828, -178682624835211359623, -398940845399961566144, 396971091917547847240, 155858015097204519455, -440568819316520265026, 114279960250023608331, 354528879965980501375, -293491484684854770695, -153428173481697367381, 370129433120983800989, -54240422869264080181, -304785171637115200711, 232215124945020383437, 165001224164286222917, -300944548417596173940, 23339305168579523125, 278981304150571896803, -169741074862821180684, -159338899696074903142, 257369034291224700755, 14115356280905939415, -243442916624514694179, 129616734965970696116, 164474228331693489668, -207565147521350059449, -33947505491117505042, 220676466884104764784, -84674496965507633604, -156338968777946285907, 170990701489590866071, 57840257968718260520, -188538986048102314135, 52917089598326992057, 152047487521793654734, -129066460946809403323, -69043534565224053072, 161252615104160068892, -19867549058317128326, -136928074506982817019, 94469570990920435369, 78665097085442460084, -127223541285288991376, -3011025659606894461, 120248429834178570637, -58889929847906255750, -77201913975303794418, 95071985133227205472, 21806077484266046375, -95287142377399836940, 30292423704788028643, 70049571387738038904, -60769607779023038901, -29962866213115104248, 67929474957845459007, -6431686667310336298, -53464526859476573540, 30831424285745736620, 29980017574078131024, -39118691951806708846, -8975596537995213324, 33714307116495299422, -6333409160087795651, -25251774906478055191, 26171175869968550407, 61653497030343325971]
def DN7 : List ℤ := raw_ints% [5043131431017, 667683454811, -396831761392, -281945262938, 44313684956, 138034424290, 31864194831, -61882320309, -44422824398, 18572942597, 36603194169, 4193867607, -22803336920, -13633573043, 9786909931, 14423982254, -84459409, -10830462944, -5199873073, 5543276984, 6857659516, -903802893, -5729174690, -2303649437, 3426881794, 3535852528, -838918382, -3357386941, -1013624765, 2140853079, 2016492253, -749854090, -2008627452, -493971108, 1453511643, 1141749958, -566562134, -1297800287, -180643280, 964403259, 698285348, -471638739, -817866713, -60317579, 685756793, 396911481, -354492402, -544855146, 28438878, 466836925, 236604972, -285824022, -343425924, 53481133, 331051864, 120967920, -212711030, -221577445, 71389832, 221656787, 59260892, -162203658, -131165315, 66844590, 148730349, 17458110, -114634360, -75351452, 59781389, 92117357, -2077225, -79040033, -36881671, 46068248, 54054488, -11813079, -49184282, -14898140, 32825279, 27132680, -12746498, -27533690, -2483858, 19672509, 10808764, -10013794, -12448898, 2721353, 9738806, 1742984, -6620747, -6537196, 14671449, -5933069, -5453590, 1303034]
def AN8 : List ℤ := raw_ints% [14732890960951208836331, 8014483702789914034027, -1676458737983900402763, -2216758393166191928102, 1573335230765892830023, 748176900987359791566, -1265142662745592182333, -102065309249248614018, 1012094712403444300111, -340759227808337513543, -627926177228179644926, 489187176436853993229, 354951530440190346458, -573979971337463283966, -35000561070236327010, 481195962309093689375, -139084316150467834118, -373568577105265332579, 300265341903530361142, 193434022624076263643, -327020167125394930467, -35755815782041052405, 320862826164521191532, -100394013892494845445, -237136910560436086328, 203348076900374955868, 130581836909785619654, -224331203222566651468, -24643768356257655216, 239567798576745260909, -89804077478820765809, -152501056235602098907, 136001723758510916682, 116113602625365693758, -195896767161750960071, 17084120048376817586, 151576464019795023919, -39329568515795503079, -152339300187869418037, 150616033506316770111, 45127843658702277180, -112120070968927966207, -27671549523059063772, 169070677610920049006, -85317718871554518620, -69873062546230339491, 72917891483467164618, 86398207691401128452, -146306033971961668957, 34196931158890915761, 84438008857369143686, -19343004562672430776, -109885034034369817007, 114339835504312294975, 17581040856903362731, -71480722251755765503, -19523070883766067150, 117126073954113925197, -63406836346957467728, -47017913774223406240, 53504019244220887866, 52443640612560674244, -95724986629442683708, 17643774755654325547, 65112661580262271033, -25070728511087076821, -62355235910409099403, 63874811202846814869, 24466623558694898473, -63100879403760471657, 3892638572608496506, 57556586615687468963, -22913677701591568416, -48903035367725214182, 53312912256263084437, 9984787504943886952, -35996498770840564536, -10972706446207513157, 59215020400187296676, -38827873679340866006, -8955175566786133392, 10944222413248068687, 33815358438430078246, -56168912552096358176, 30506616327437868241, -223684272505033400, 10501139928876018145, -41999178750221639463, 49274795785989180484, -28186620440680222460, 12011516290507593142, -21379556701286545336, 45451886354774513502, -27880006218009734908]
def DN8 : List ℤ := raw_ints% [1865109415299, 194786450446, -171293847998, -90874320123, 34422458139, 48252846066, -3316263053, -28572581878, -8483923942, 13947818325, 9784256012, -6440679821, -9507263732, 531956521, 6740071912, 1802117134, -4491922288, -3359950227, 2019204343, 3191287601, -326810871, -2751365971, -808828295, 1797373208, 1451712335, -878987946, -1425153626, 147884491, 1359012123, 481919407, -774658924, -654322774, 529381471, 846756883, 70042156, -589667608, -145231764, 534153649, 501614345, -142793822, -337152039, 79096229, 459477601, 220493204, -171753185, -170506452, 192216139, 309732659, 68898181, -161922068, -35309107, 190958684, 189180428, -27697293, -107233122, 27891104, 159358910, 82165431, -58032262, -62902264, 58730685, 102119036, 17930694, -63038911, -23123832, 54793101, 53475140, -19515232, -47953393, -2818501, 39706711, 15061301, -30627064, -31813104, 5676988, 19500503, -5663773, -29122584, -18194770, 3998346, 4655779, -13706298, -21691911, -11225045, -78419, -3507545, -13365567, -14939857, -8142065, -3305628, -5605493, -11353249, -6634500, -10304053, -4617313, -2471248]
def AN9 : List ℤ := raw_ints% [16026457175890234485256, 8715204791361343597969, -1914310044069681682177, -2328138924591888147711, 1717503519136580084725, 777520548113564127627, -1416048526274517787233, -8777947591817532942, 1049952771391266248889, -408080462356852088971, -658183173243692910874, 599452342325970145987, 292580446920866786230, -616778702054900769185, 18887737834567352754, 520518189943100435430, -235963469515839646606, -343571091245793831393, 361685349435302537347, 148714314425651719225, -380209614448156912088, 43115610927714393897, 328052890620217541155, -179574318141252237659, -208877481425662392667, 265385989703629606600, 77469141365122381206, -271345778151050232370, 60690461517620691237, 230787368940302107070, -154863607609054996896, -135466167358376455783, 215283920199529751329, 34889241743305159883, -210721469973230656877, 73036643536589640872, 172750377165601362627, -142320662551122909260, -90042680970031506993, 185007648494765900464, 6379115605808597130, -172919885817895489006, 81930067063766527863, 134227927593972346591, -135497509203678420429, -59420324785008170520, 164874083448477284562, -14303548226271015447, -147460463400923717632, 88705292123527653953, 106739587068027386105, -131728170324469372589, -37348999986793487056, 150686809358487298809, -30187442918010573072, -129286738643518151442, 94250122097896450838, 86136385256177764907, -129709872742123394510, -20532164346905634521, 140358437313850170569, -42879809023776796085, -115677860989816359090, 99093968120087174456, 70135810077264257927, -128726104679904975753, -7098512845758209053, 132682347331999035025, -53331914659527023728, -105049496499072533428, 103509950787557117228, 57323728107282922281, -128333809988052588340, 4085083590840802804, 126813120243433827548, -62190108902586579451, -96350100865094582110, 107645810737092446302, 46662446502598577157, -128254711310260169462, 13834232564464097561, 122119804030617660356, -69946149410174599807, -88728798712145833354, 111559631132056484252, 37118272175302771670, -128021652377760404632, 23655724407454725874, 118154237602226837129, -77896394484254512230, -80776844877586859372, 116714483914638377625, 22173321793166282684, -142719702854154419352]
def DN9 : List ℤ := raw_ints% [2028179370678, 222422210634, -179900469215, -99201340921, 35772513806, 54008432071, -285209378, -29641357830, -10160028907, 14619902240, 11989674847, -5308941697, -10216171430, -287065551, 7290855091, 3057381474, -4131221780, -4047236235, 1552387659, 3710346793, 394079956, -2813020040, -1446747509, 1583181581, 1894604172, -521469471, -1723832503, -364196658, 1309202798, 831051107, -688126876, -1035760195, 159065929, 910836139, 299438544, -672039042, -525545579, 315720412, 616152798, -20184840, -519980870, -234188527, 364786650, 350176732, -146059578, -385530826, -31822105, 312176608, 178718764, -204688563, -240459229, 64905252, 249318140, 47557504, -193951882, -134647878, 117195088, 168083889, -25342000, -165013089, -48020324, 123404684, 100705414, -67902079, -118729725, 6237640, 111079893, 42538958, -79832164, -74947318, 39546068, 84354602, 2558412, -75672455, -35359045, 52196060, 55563445, -22949093, -60100250, -6176769, 51950961, 28351102, -34266236, -41048861, 13012784, 42761230, 7528055, -35823737, -22501366, 22230180, 30601296, -5538587, -33962469, -5026746, 25206660, 16619013]
def AN10 : List ℤ := raw_ints% [45595905783884257215721, 22552875662911600901972, -7380540746283055439341, -4190530269731003528335, 5666174583722602059213, -524266286532699805918, -3364051949873051767828, 2264615868953578677199, 1103549128390947588825, -2335524600904998124817, 574103654377595324518, 1466724716684478588602, -1368949041915788023123, -308181195484999969508, 1317148230408698423365, -598485542830150373660, -700824253385341237924, 974223244273592390028, -52233462017638990659, -795678226418797061471, 592562619405589112947, 292994308063240724955, -717131953645833810537, 244502018697295211105, 474132318962859414660, -545092193783040145512, -37422543728421939835, 526739462540952233456, -332487340651608914979, -239236172416617480765, 482519778299715973409, -116939573307138825916, -356865837173083520972, 370941755906164674299, 73418223681310901687, -393582549806474360884, 220563794085493509640, 218135796146404644018, -359395823735315691485, 58854536060972325851, 304572428223332434720, -270355274962740787759, -89247986672156354392, 328424244610425629663, -147071056899769682183, -203383222342073209581, 293751360811386679624, -12431566541045903683, -269697058268672533447, 212161274805927210663, 111136021890238988118, -282252114060398169319, 101031337205279367343, 204522875068813543492, -243442188356258085440, -18999791538198276013, 254399259861156689342, -163448168736267964691, -127092503787382834434, 255013552522499710415, -58454973158876313317, -205268562479623766423, 208849080659120025645, 51834350825814217583, -241222995513870880541, 126179751159230910268, 147543163181327535254, -230169269805038555874, 23228015824757100125, 211712109598792568741, -175708931608873721425, -80479702923343486256, 233458383254971518231, -89051559785292987001, -165677183218133161461, 209526936940121325627, 12748673710521849704, -216570930037769982728, 145420051032865892867, 110146765026874512670, -224070437764561622768, 53685206840086720233, 184275218168526796215, -187024099510941315014, -47240768795031199634, 221168139166588456448, -113301654796423122655, -138605111872412300798, 213041514380029120556, -16489983479164152282, -200660919890565656985, 161722510239374726936, 86174228586563761632, -211393537650590399770]
def DN10 : List ℤ := raw_ints% [5248445477073, 857539348732, -323811587797, -327272759754, -24120678250, 128305752132, 73580945282, -31154443790, -58147840062, -12752284841, 29336030909, 24839905489, -5104637878, -20018695975, -8382937334, 9080588168, 11714409005, 584489143, -8305865273, -5782633398, 2677990216, 6149333274, 1969840064, -3593673906, -3891441090, 251903064, 3346322953, 1995219265, -1357130886, -2589366231, -594017420, 1716930035, 1691185942, -317347689, -1613625437, -858044325, 805507092, 1260164583, 196010204, -963730096, -812975156, 255106033, 892547343, 380087150, -499931087, -686889062, -27657377, 570953807, 427451395, -213119361, -515228637, -175572693, 338392346, 383520495, -28502888, -363440594, -222383636, 164692185, 314752654, 68722877, -229876556, -222799373, 52677270, 233540365, 116381111, -129649858, -192694647, -18527286, 160890212, 127223644, -55520742, -153453632, -55771340, 98863580, 119129430, -6906382, -111787230, -71519145, 51614852, 100043950, 22838213, -74691827, -72226966, 17382450, 77536293, 37844521, -44108859, -64593055, -4763342, 55222859, 42401922, -21525123, -50304522, -19535907, 34926980, 41283941]
def AN11 : List ℤ := raw_ints% [22907237760894501654969, 11795182844666029285043, -3334615434071989591822, -2618399226862939587095, 2742853610630857244337, 284294357143605285557, -1903449289565011848669, 739404498814780275953, 997538485911226594052, -1063575992358216181683, -200570615258613128606, 938369632785808230709, -349790799866047172153, -561018597711881037218, 601714522327699581182, 125377924043411915586, -571793939748318001258, 227388132705585245879, 357152163511645695055, -401884771442732049565, -67969328621484926515, 394009305723719436177, -172712960873706903367, -240275911326867317428, 302189467040162884729, 35011941809247969309, -288566982315472216857, 148417106134326419411, 174420848661555518286, -237884900785617786226, -9107517011191091805, 227469213238574629542, -127741060145668829512, -126993636185744145833, 200385386922344631071, -2079449922133800304, -181136673953371225427, 117605476970632457328, 100208851337299465646, -168305025735527188266, 13530675955573030183, 153195736268730752487, -103853790459667540348, -77051727852103894856, 148626675771890041920, -15578745856366026540, -128052070528336665343, 96206818432182063646, 65138879820787678545, -128511636114801526384, 19201269427040312000, 112770354421268796337, -84627593044721334078, -53643325461599546640, 115094024018310790312, -16628815008210372858, -97651092556446054699, 76354798422624448059, 48744769274564268051, -100299558658108899149, 14938088175592284907, 87880403437114545345, -65048741416370147654, -43893932069260780826, 88758476984112299527, -9353520607429861646, -77796367740868618427, 55018480605434532467, 42672523428202227255, -75926649353382472261, 3888244941878554025, 70196225975433931158, -42908265570422583186, -41471745901046509566, 64217626684877117715, 3732338881450459786, -62130932484523481760, 31011842913443338228, 41886167413776583810, -51504260074625048541, -11409670803216866237, 54841904083781507795, -17961671329766390303, -42011297510844565894, 39057813187802524311, 19762501403259835398, -46798075331980220680, 6288921966763764422, 43140565956971873975, -27252171359720331492, -27036812432624121694, 41865947576629434816, -1259138723670475016, -66245232573494074414]
def DN11 : List ℤ := raw_ints% [2744943703748, 387446400732, -202329527903, -158424569785, 13079942183, 72598014650, 24024419644, -28161643091, -26479980846, 4455177383, 18768375714, 6347037138, -9292574712, -9145166663, 1756158177, 7408740863, 2734196299, -3996510171, -4195164146, 663291434, 3601274963, 1480996003, -1935792266, -2290437414, 249952045, 1942436290, 942878983, -1046679964, -1349465438, 48874052, 1155474329, 614579598, -578985377, -866158785, -8525412, 704663681, 434280148, -351366480, -560526083, -42813855, 460669123, 296855196, -209400848, -384107458, -38293716, 299428626, 214038042, -137900249, -258918497, -36821206, 205853253, 147066195, -88755308, -181319916, -24946023, 139506581, 103886496, -63165666, -123795587, -17562037, 98415676, 69393739, -44607727, -85931639, -8627162, 68361608, 46060738, -34036744, -57700312, -2815319, 48426452, 28203866, -25972985, -38320211, 2122072, 33658396, 16007356, -20600068, -24134933, 5094239, 23330283, 7280360, -16224372, -14371496, 6928263, 15631287, 2001348, -13079991, -7872137, 7440662, 10976806, 314515, -15764128, 285449, 9041729, 5562548]
def AN12 : List ℤ := raw_ints% [10552851834857544102828, 5925423787748130394846, -849666462089953131034, -1824872527383303903804, 917255707728501545849, 728445222169628566832, -690621687732351154971, -384741288337917069473, 694735078024158885013, -26084498625927363115, -422689246545617286272, 67066704974881506525, 404045326269427039400, -288028958993088768888, -132325241459605313235, 190931508361124343057, 136528734989344277633, -306976507345120760778, 94207861620800608237, 133538977000696710276, -35651139408856360252, -199488671099933740324, 205613017623484145165, 1151102179740958610, -86097180876259342680, -64462333941868832337, 201397650271365987956, -117871909219139988487, -38240400305621151542, 25209215400376077024, 124382920529768972083, -170515022328207900168, 52187431771624028085, 39110625335570974459, 35706818485222595913, -149335329637639908109, 126270026984191073882, -9267943762393773219, -14701725564758532712, -84521105779879313527, 148241854834798426856, -78839381250258143950, -8234021368146853025, -21424454968001334192, 117269323334134580516, -126539331201075752094, 39908159646019830196, 4884362649062759196, 60914486694554351614, -129430684718593649175, 94853109551888280083, -14217440982309351454, 15739373693189186588, -93215988344383808170, 123794685339162456134, -60677994677920847403, 6290652168596511021, -44694963027926368166, 113476561531709445870, -103541118416471080565, 33351566335880830930, -14064222621134072748, 74892824958088859293, -117871843782567499602, 76536652064203756042, -17523299003742612831, 34187931665956599484, -98181590878979063217, 108254872652990609216, -49571943028438537264, 16074706347673649929, -59584350879415761706, 110353325398902307848, -88250230047731900876, 29631859957113924146, -27169628115089490627, 83870270317656560602, -109400794062934909618, 64224511263376722598, -20410887103455704798, 47057822704781720932, -101095727997895192277, 97171591699338701809, -41990497847587299877, 23263190877905866024, -70162307495691983049, 108212414552790209089, -76637634466908568411, 26961738953550318132, -37055994976663659230, 91448886562854407256, -102673009500948399993, 50448275980061426437, -31637842511950952919]
def DN12 : List ℤ := raw_ints% [1378948926220, 98722092267, -141011956145, -52979801881, 33514634218, 26340477615, -12500851943, -19613159379, -649428935, 9388990350, 1341404360, -7331498406, -4770841166, 2011147050, 2674361793, -1769004440, -3691195405, -1054180027, 1393976503, 347908326, -1823341598, -1763110631, 9273899, 652571402, -460199904, -1355671746, -748828413, 229476356, 143005986, -667481311, -866164385, -251080826, 178311928, -154341467, -612250942, -491219697, -34223611, 51549274, -281490610, -469067860, -237074932, 23536088, -58224509, -303068218, -311043087, -93318643, 10866583, -128957129, -260770147, -181894527, -25952801, -27351952, -154230069, -195026998, -91027211, -8986970, -60810889, -147048035, -127796510, -39209934, -15750269, -79895370, -119788653, -74099063, -16162507, -30041789, -82196320, -86346976, -37672104, -11639037, -41105611, -72535920, -55269482, -17682048, -15447667, -45435321, -56469314, -31586306, -9564557, -21010583, -43007114, -39386326, -16216340, -8559795, -24597238, -36144636, -24388701, -8174656, -10704096, -25167178, -26919772, -12601277, -7528738, -11436747, -22174144, -18814678]
def AN13 : List ℤ := raw_ints% [4819116271187821449321, 3038118884355327452206, -28708309446642992026, -977239041092214139878, 40138351286257174461, 551910615674457169784, -52701984252280358222, -365738772863130100928, 63077248689559349227, 261147991494058988092, -70548005212178065921, -194116411673934514268, 75232556267047616145, 147244006225773295061, -77658193054790769311, -112441278246692707801, 78245875483828480187, 85407909053584627792, -77394468097380944327, -63734899183366265049, 75385148370041291805, 45947671746483785007, -72456253126641264769, -31125164881908703055, 68786129435573597185, 18652151548507984679, -64526944501281208444, -8112726964162809638, 59802233644747900490, -790137403767489992, -54721229925334167574, 8271304510565980439, 49378152153008952302, -14495189651620729063, -43859833393851081229, 19588877985477828773, 38243873179576946517, -23657154349557691275, -32603221016429912623, 26787150144209708716, 27003940746506831988, -29056642132858484869, -21508458012886932347, 30535346391304364226, 16173975233347133610, -31288594114334912074, -11052929858619715115, 31379397874984533915, 6193904814620867768, -30868038918503150170, -1639179279017484439, 29816009953307955371, -2571403038576445126, -28281673774272350098, 6406086810600946830, 26326484547332361666, -9835147388129315093, -24008845217787924296, 12837091511649939393, 21389895714997352614, -15393231473210708402, -18528459938288531764, 17491356604781315705, 15482278935968228599, -19127143329277405300, -12312264277136104938, 20296660701366930164, 9072454242985745182, -21007487594774898881, -5822084101885832548, 21264278114163601821, 2607871256739218418, -21089653570640838935, 512090608164884853, 20498200766333231110, -3493841887444457375, -19519097590493719135, 6287506898579598018, 18176843458824444486, -8855520086231346018, -16503884439547793678, 11175219819751346582, 14571594388198965560, -13169027023038700305, -12379554715716464441, 14856395451953663757, 10066671661682302212, -16028582080498209923, -7366032149638437264, 17168540604090021832, 5017904796955161072, -17750075413684701209, -3808641202879396007, 14188596560154294088]
def DN13 : List ℤ := raw_ints% [707022978166, 3335596378, -75513432713, -2318352322, 25392550932, 2010066380, -11883430212, -1780742287, 6501833308, 1567048477, -3882531595, -1365112602, 2438913672, 1180289143, -1574955654, -1013832738, 1026975269, 866039213, -665311012, -735660102, 419965207, 621304971, -250761107, -521362727, 133158665, 434351420, -51539341, -358866502, -4482265, 293652843, 42015707, -237565000, -66086012, 189582586, 80311263, -148777539, -87358453, 114318035, 89212406, -85446049, -87375134, 61479677, 82984867, -41799660, -76909692, 25845451, 69811942, -13112615, -62191304, 3143362, 54426739, 4468595, -46793309, -10092194, 39494160, 14050716, -32665856, -16634881, 26400661, 18097128, -20749688, -18659711, 15734048, 18517969, -11356141, -17835183, 7595337, 16756132, -4424482, -15396594, 1799098, 13862359, 320712, -12231772, -1986473, 10574145, 3245417, -8939568, -4149704, 7368726, 4754048, -5906269, -5085756, 4555111, 5208299, -3362426, -5100840, 2233341, 4959351, -1380952, -4653882, 951345, 3376406, 863428, -3833459, -1032383]
def AN14 : List ℤ := raw_ints% [15369131485166983872537, 7705330289749636971728, -2244526209083612593848, -1395007711195288349848, 1618938321308088975784, -140342673155502989052, -824866655595422377171, 593283199503586355808, 136126579765489636025, -491912538990596578115, 257753427687914202388, 168302590073731496518, -322086110454721788931, 117331532694659263461, 164651814150179042977, -224829988861790672608, 42632343093351410970, 153995133585582284735, -159760498736168018210, -2866599098527196138, 140357300744130201418, -111705405344211782836, -32059633722801160291, 125072526508202721495, -74214117597658506424, -50889835167987770554, 108866034411551422979, -44026887447075508258, -62515486142260511004, 92162571695219149218, -19345042251471235515, -68753389028772610569, 75270987895738972067, 851209038831156410, -70746468598093903998, 58479988570645843835, 17162520583711144853, -69287911656057349886, 42080661808778628273, 29952280492053353524, -64992100213028144625, 26376570459848663523, 39463811762023034872, -58383585970711693721, 11674288406379988569, 45884318508314531703, -49945732675750880211, -1724372096579279659, 49387701489817355664, -40149637069520502870, -13534964816386788092, 50169039875812650980, -29459086840682890712, -23507197947592892265, 48450261366112505824, -18340774782623337366, -31432000540799227422, 44508181217081152707, -7247360343577115027, -37163267004323906790, 38653942457990940695, 3378403046427221617, -40615497524892349129, 31257669346441809879, 13129551284505716359, -41784380337268726726, 22715518861803219380, 21636665170968548433, -40738010999775572149, 13457153325362520863, 28584129990858734173, -37623961107510776420, 3934210321655599301, 33733776499531200257, -32670751232273708515, -5436898112140961699, 36892199953400863256, -26149498873895025630, -14174822798175176387, 38010136896110684927, -18442278937910158708, -22005832296253722062, 36994530187509904850, -9850026591089473886, -28363118814452885618, 34068664847078778174, -953376821482332074, -33572831049326962062, 28871035638372989870, 8477946924223913444, -36132897053462783729, 21780832692227264991, 19305124755935278261, -29091317645995743851]
def DN14 : List ℤ := raw_ints% [1793164052028, 260789772689, -107795346383, -93508310494, -6456948599, 31460613043, 19276707912, -3843007773, -12247206316, -5725351343, 3366228119, 5844328969, 1943450784, -2502462922, -3149174997, -552387776, 1851692607, 1787709898, -29923637, -1369703030, -1020995885, 274908085, 1007651695, 562504025, -363305140, -732811961, -279698399, 375148425, 522816726, 103812115, -349246279, -362138952, 3880805, 305799121, 239758589, -66766187, -255858531, -147549182, 99753613, 205648434, 79315990, -112803178, -158667076, -30170770, 112787067, 116789850, -3836332, -104554705, -80891381, 25955248, 91579565, 51194127, -38893723, -76328875, -27514251, 44904473, 60556757, 9391455, -45869080, -45443698, 3783412, 43328452, 31765975, -12711393, -38539565, -19960694, 18113927, 32493724, 10226737, -20696599, -25955740, -2585981, 21126838, 19495427, -3091224, -19985735, -13497565, 6971330, 17811577, 8234189, -9361497, -14994904, -3803989, 10436335, 11943664, 318442, -10684017, -8753545, 2448962, 9943948, 5710702, -4822152, -6922751, -4376519, 4703975, 7433975]
def AN15 : List ℤ := raw_ints% [17342694599537121487300, 1873581090102520797026, -989238635421988046764, 350413168225709265011, -76330398848867729915, 3767704406380243493, 3783442106836137792, -1114694641425121160, -133343193218594618, 174641694222837589, -37756677791742307, -10526515718997079, 7083772904584491, -1164731721440341, -1081805456696307, 770991677491875, 3114786743718, -489184221851408, -521525872284923, -42093912181430, -312797426410155, 418903883386381, -79737043145881, -350989056625978, -359718720203625, -134485552065344, -207610221727721, 454247381196868, -183956875889577, -238077274910332, -302550938482822, -215189510845145, -83460802446126, 444010688294432, -252639158985323, -114072769564953, -342161281695892, -254621056807092, 43471290415440, 412070221122463, -268034844120974, 3133885116751, -438360392044041, -236027443355568, 153716506348381, 372317622021860, -238701516763849, 93142194608066, -595249313439773, -158207285085294, 247545049654520, 325336799597798, -138304638404890, 156099257622168, -801961644723073, -27637242107426, 312525651459829, 328745317632931, 54669498518700, 109988549845662, -1016911790031958, 271379098430323, 339709283974638, 402036414330287, 484851078795837, -223031225601269, -1062295001843986, 689557276840952, 239667309756855, 986630622874927, 881625721860815, -339657648541131, -1476435031660154, 1332214702094365, -41231945726164, 2371991896137081, 1705444091242876, -954757199734157, -1818592854203438, 2393643769872697, -677752053061121, 7022897531861530, 3328876323390073, -2588190389312834, -2053255733260471, 4543661084274661, -2012880184644490, 37964722040723843, 9688799905661371, -10922932784658867, -1890965041622194, 22633378000240777, -36612541302272880, -733414210153701338]
def DN15 : List ℤ := raw_ints% [436014827787, 114938875662, 27077204335, 4408769958, 173346232, -144301394, -36218189, 3764429, 4348075, 838670, -210542, -128537, -19293, 16441, 10799, -41, -5883, 5835, -440, 3052, 3828, 683, -2828, 2726, -961, 1397, 2885, 1103, -1351, 1623, -1094, 401, 2024, 1092, -468, 1331, -941, -153, 1372, 848, 9, 1253, -642, -398, 915, 558, 207, 1260, -319, -475, 593, 240, 258, 1263, -42, -447, 447, -71, 135, 1195, 303, -363, 408, -470, -206, 933, 577, -192, 749, -639, -235, 970, 834, 24, 1348, -924, -493, 894, 1121, 302, 2987, -1350, -1000, 755, 1592, 672, 12081, -2938, -3156, 520, 5934, 9145, -174528, 8300, 4888, 389]
def BsN : List Blk := [⟨(1 : ℚ), (0 : ℚ), (842777218324126608901048 / 7955937174222674888870975 : ℚ), DN0⟩,
  ⟨(3276730368397 / 4398046511104 : ℚ), (-2846434036817249496802584327549855809799 / 9671406556917033397649408000000000000000 : ℚ), (588460281326338070516592 / 7955937174222674888870975 : ℚ), DN1⟩,
  ⟨(1305092809445 / 2199023255552 : ℚ), (-50459512470861903514431699337636266627633 / 96714065569170333976494080000000000000000 : ℚ), (86517600607263456964168 / 1591187434844534977774195 : ℚ), DN2⟩,
  ⟨(8542441030865 / 17592186044416 : ℚ), (-8733377158418276106796407556106148303303 / 12089258196146291747061760000000000000000 : ℚ), (494032395345862850448752 / 7955937174222674888870975 : ℚ), DN3⟩,
  ⟨(6896403054357 / 17592186044416 : ℚ), (-181136711433848873382792786417759206259407 / 193428131138340667952988160000000000000000 : ℚ), (23548563337256449364664 / 1591187434844534977774195 : ℚ), DN4⟩,
  ⟨(2976343721197 / 8796093022208 : ℚ), (-3275016434406850332866121948892436228973 / 3022314549036572936765440000000000000000 : ℚ), (408478033491874411348976 / 7955937174222674888870975 : ℚ), DN5⟩,
  ⟨(4805667573359 / 17592186044416 : ℚ), (-251003728701191018592854999347220598140897 / 193428131138340667952988160000000000000000 : ℚ), (239110325186318005908928 / 7955937174222674888870975 : ℚ), DN6⟩,
  ⟨(511616124031 / 2199023255552 : ℚ), (-282055736375561776914842081200209473889673 / 193428131138340667952988160000000000000000 : ℚ), (272458488826823251317904 / 7955937174222674888870975 : ℚ), DN7⟩,
  ⟨(3532845575111 / 17592186044416 : ℚ), (-15526003837186727201177233263846439039421 / 9671406556917033397649408000000000000000 : ℚ), (10419893712778305536 / 855017428718181073495 : ℚ), DN8⟩,
  ⟨(3132095659693 / 17592186044416 : ℚ), (-8345227062488155416624620250623650617991 / 4835703278458516698824704000000000000000 : ℚ), (105470066358081382670504 / 7955937174222674888870975 : ℚ), DN9⟩,
  ⟨(2597141326789 / 17592186044416 : ℚ), (-370036424786292096417260675745534622838311 / 193428131138340667952988160000000000000000 : ℚ), (300066518501520893339272 / 7955937174222674888870975 : ℚ), DN10⟩,
  ⟨(2124937635887 / 17592186044416 : ℚ), (-408851434379226432243644719811994253074577 / 193428131138340667952988160000000000000000 : ℚ), (150752462643864746619328 / 7955937174222674888870975 : ℚ), DN11⟩,
  ⟨(108661779151 / 1099511627776 : ℚ), (-17906657758888708979164490742088108331339 / 7737125245533626718119526400000000000000 : ℚ), (69448286110532772445288 / 7955937174222674888870975 : ℚ), DN12⟩,
  ⟨(1295321823375 / 17592186044416 : ℚ), (-100919024941704288683653862844431468802141 / 38685626227668133590597632000000000000000 : ℚ), (6342917930409729783576 / 1591187434844534977774195 : ℚ), DN13⟩,
  ⟨(422113244307 / 8796093022208 : ℚ), (-587400478506638731396024528063810947569941 / 193428131138340667952988160000000000000000 : ℚ), (101144207969132616534928 / 7955937174222674888870975 : ℚ), DN14⟩,
  ⟨(349141633395 / 17592186044416 : ℚ), (-151637304143068635474707076414507938439379 / 38685626227668133590597632000000000000000 : ℚ), (22826444174983612936256 / 1591187434844534977774195 : ℚ), DN15⟩]
def RNd : RadLit where
  NA := 93
  CT := CTl
  hq := (7955963607416 / 7955937174222674888870975 : ℚ)
  Cq := Cql
  δc := dcL
  s := -1
  W := 48
  sh := 112
  Gs := (List.range 16).map (grp naT)
  As := [AN0, AN1, AN2, AN3, AN4, AN5, AN6, AN7, AN8, AN9, AN10, AN11, AN12, AN13, AN14, AN15]
  Bs := BsN
  ns := List.replicate 16 96
  Tls := [10081810261843879498674134679560350717632006, 9104017705686089339106168560723912444389624, 7684535551043477491927188133371125877754596, 6982824071811941765926336251716717080221243, 2047886569811863180595093969566584214999140, 7092267363454372403931672999355766916710618, 3391598942294974226584452402257693786824432, 3845561424281290259538359320237363405352525, 1699840205341184653563321582837167452926007, 2658210007363958666316908065826785582527671, 5392359722379240950724963576528551469696834, 2164278244816942990273918082209154141465450, 1847927185384705511708560467461538194046406, 550564216161728075447108381880606643036081, 1201505594306515116871296238498939557792171, 302199461793540424821483009191351007605822]
  etas := [(0 : ℚ), (37404884055593501 / 316912650057057350374175801344 : ℚ), (62745745870815631 / 633825300114114700748351602688 : ℚ), (11711144910478457 / 79228162514264337593543950336 : ℚ), (319361129837801841 / 1267650600228229401496703205376 : ℚ), (4412697932863827 / 19807040628566084398385987584 : ℚ), (439808553525426143 / 1267650600228229401496703205376 : ℚ), (516309778300344375 / 1267650600228229401496703205376 : ℚ), (147397393848122127 / 316912650057057350374175801344 : ℚ), (69714487683429021 / 158456325028528675187087900672 : ℚ), (647189962250053657 / 1267650600228229401496703205376 : ℚ), (933573703881399087 / 1267650600228229401496703205376 : ℚ), (846941453063133933 / 1267650600228229401496703205376 : ℚ), (1267034594534226415 / 1267650600228229401496703205376 : ℚ), (2812784006849544619 / 1267650600228229401496703205376 : ℚ), (5428270652266624033 / 1267650600228229401496703205376 : ℚ)]
def miN : List ℤ := raw_ints% [-226490210991982502099905, -71674273427854132827554, -34284693498016513052152, -19910399653998682311783, -12956095621626612715798, -9084976955200374620518, -6715721998022014170198, -5162893869911328233709, -4091092273047298231250, -3320730171159325815048, -2748708406128167692968, -2312454677375965568914, -1972228337802560888211, -1701816672031373467715, -1483367943837598770583, -1304386659458335654430, -1155916222521460508161, -1031401827461264846819, -925957599195381179296, -835881795202547477361, -758328600790540696860, -691081297446595517119, -632392553439102027625, -580870070181724056960, -535393445320792500986, -495052883799162003691, -459103435576722517880, -426930423586284557822, -398023041504450497302, -371953987804707110945, -348363609337169242431, -326947448651253294716, -307446385151851607755, -289638770656273661195, -273334111343172519049, -258367958178753633025, -244597748745656424131, -231899403313267511261, -220164522782063968083, -209298069901724812900, -199216440816656407976, -189845853626809550337, -181120995784062751165, -172983883884769512499, -165382898585232457108, -158271964566291419310, -151609851160262055075, -145359573770363219508, -139487879818987258858, -133964805854646985607, -128763294780103677447, -123858864053316647374, -119229317249480506824, -114854492627552326183, -110716043374011714439, -106797245044029286448, -103082826420487022755, -99558820592026710579, -96212433534565899872, -93031927884210725562, -90006519927460012518, -87126288118552095715, -84382091673098258175, -81765497989382190771, -79268717820099097507, -76884547262956519379, -74606315762652410303, -72427839422741993642, -70343379016664704188, -68347602165100862822, -66435549213841302729, -64602602404131812683, -62844457977378750720, -61157100899331098925, -59536781926362202190, -57979996769083351048, -56483467136925981242, -55044123472118213912, -53659089203154621264, -52325666366840894219, -51041322464650346206, -49803678433767013891, -48610497626076084394, -47459675699724377744, -46349231337907571463, -45277297718415539333, -44242114665328228090, -43242021421227820198, -42275449984487564228, -41340918961708185436, -40437027890281409392, -39562451990438376996, -38715937310050960598, -37896296228950654994, -37102403292660423295, -36333191348241318741, -35587647957474443671, -34864812064861958375, -34163770899966656949, -33483657095442956004, -32823646003764927374, -32182953197148614131, -31560832136513421933, -30956571996546031890, -30369495635033470261, -29798957695631615069, -29244342834142110808, -28705064059193819695, -28180561178972949340, -27670299346326339886, -27173767695181741660, -26690478061793228767, -26219963784834506587, -25761778578832554620, -25315495475863078129, -24880705830821459409, -24457018385941747430, -24044058390564799720, -23641466772457778155, -23248899357263309303, -22866026132910010726, -22492530556048796589, -22128108897793250267, -21772469626239052196, -21425332823418482860, -21086429634512745544, -20755501747298505335, -20432300899946738549, -20116588415422745386, -19808134760856920038]
def meN : List ℤ := raw_ints% [3196905158976488924, 300037106874, 529653368846, 381704217037, 414273777996, 92935155635, 479284793212, 166257639592, 238879268449, 421043556154, 439944519375, 306783421300, 466641308536, 460794964929, 95226732882, 37607500320, 345310374105, 430498285256, 97478225028, 246691333376, 55768701387, 247356240879, 41790671812, 264808891750, 18426784126, 93757350072, 221209124622, 283870529852, 445189823234, 245428472492, 325423491416, 159921029061, 180362915060, 168097813899, 266808436260, 486606110088, 378787441102, 406807036951, 500191899676, 207981689195, 469096100660, 248302620559, 102756145799, 24988669917, 18490444095, 148189611288, 492532533716, 432266771834, 149612890820, 215779439946, 208231092009, 545232232637, 152873560694, 412250700562, 452040537646, 526894949773, 153346490617, 493461975887, 167850914140, 467580523103, 223675799124, 473801694849, 461473013592, 294204957132, 360615720698, 364433566913, 306051810752, 98148106781, 512013649191, 123842458268, 533544429992, 509172865812, 177698294705, 75135412159, 329863264876, 341903090477, 16027823576, 91058650558, 381679002050, 175770874452, 271579841579, 156951807795, 548747569633, 189628787033, 340329699059, 354045700346, 99780023154, 109840910307, 531039875448, 40631847122, 487420275781, 370930895981, 214134120370, 56224678046, 94839861550, 421873703813, 396704247254, 84746960393, 497764894315, 225529500168, 469588491298, 87724067888, 291396530764, 305818961524, 466372252176, 341192515810, 493794317874, 377509678036, 439804710427, 389435243270, 478340360393, 529287750621, 374517868455, 348771211244, 218770470903, 198310600921, 289662351984, 77529775039, 69414040306, 234618966345, 12785368879, 378415298635, 61600994087, 541285286367, 289042406771, 26920467361, 303957853665, 343177062914, 270292211383, 306682089692]
def rnsN : List ℕ := [17592186044416, 13106921473588, 10440742475560, 8542441030865, 6896403054357, 5952687442394, 4805667573359, 4092928992248, 3532845575111, 3132095659693, 2597141326789, 2124937635887, 1738588466416, 1295321823375, 844226488614, 349141633395]
def DmN : List ℤ := raw_ints% [38261832679021, 4638964204286, -867434663614, -1105126865402, -345856588882, 176337751331, 257770993039, 94920560074, -64736063495, -102035436913, -40847164212, 30604764350, 51373138689, 21919020296, -16639939605, -29633363225, -13354261253, 9882232256, 18637916614, 8813662802, -6239384863, -12440612559, -6137935344, 4122322100, 8669714010, 4438430011, -2823150969, -6241569231, -3297870687, 1992421585, 4608630051, 2499697160, -1444009063, -3472265212, -1922660794, 1072657750, 2659310560, 1494531356, -815821782, -2064357269, -1170174564, 634936720, 1620537437, 920190287, -505397430, -1283993801, -724798860, 411106241, 1025120799, 570314196, -341295448, -823449607, -447045795, 288646690, 664527763, 347981430, -248085847, -537994601, -267977352, 216103573, 436291894, 203178071, -190224169, -353851387, -150651731, 168678260, 286552559, 108174312, -150317004, -231242628, -73934263, 134180664, 185629479, 46592851, -119812086, -147861567, -24969133, 106746114, 116582165, 8125878, -94619289, -90843109, 4521426, 83774680, 69474071, -14152842, -72212021, -53426964, 19074674, 64302630, 41545747, -16422603, -79822959, -14904930, 34221738, 48071868]
def ClP : List ℤ := raw_ints% [-1559967793860780510, -157273581225108147, -73370811030474029, 14854778902084386, -1501075823086774, 108740876454019, -52516859504918, 38414366460235, -25583176309219, 19232817769418, -15873874130543, 13281643476098, -10721652308148, 7976083109685, -4976594651338, 1713238545129, 1787473283029]
def ndP : List ℤ := raw_ints% [1, 1, 1242627842148336054353789, 8177989, 8388608, 1242627110664056246870431, 3983507, 4194304, 1242626732860635159672057, 7758247, 8388608, 1242627432357116738451872, 7554485, 8388608, 1242623924357765903681244, 14673819, 16777216, 1242620162819924160899340, 1783869, 2097152, 1242619478771804808184207, 6932875, 8388608, 1242620008096605964272418, 3359269, 4194304, 1242618991553326007539778, 13033579, 16777216, 1242615704480164044431150, 3150291, 4194304, 1242611198978946385668144, 3276730368397, 4398046511104, 1242610242280497888383945, 12075685, 16777216, 1242607507646469073284200, 1460387, 2097152, 1242606639119372465058131, 1411029, 2097152, 1242606284824706361998623, 339703, 524288, 1242604753358524920387287, 10477293, 16777216, 1242601288365450375682538, 78891, 131072, 1242596386313239183448696, 1305092809445, 2199023255552, 1242594382328031245310854, 9584327, 16777216, 1242589434719835082720078, 2304725, 4194304, 1242585705300323283340371, 4422523, 8388608, 1242583280517579723183565, 4236959, 8388608, 1242581464650131222983463, 8542441030865, 17592186044416, 1242579174877320759452136, 3893793, 8388608, 1242574723547654722482532, 7445655, 16777216, 1242568024180138167965316, 222159, 524288, 1242559404855922794593216, 6759933, 16777216, 1242549393760618855767803, 6896403054357, 17592186044416, 1242544137165662952419657, 3131555, 8388608, 1242535375854914419843572, 5951585, 16777216, 1242526912215334140845733, 2976343721197, 8796093022208, 1242520446705887657285332, 670997, 2097152, 1242522236954312066741309, 5094283, 16777216, 1242522041275679424770074, 4822585, 16777216, 1242517429046377981645858, 4805667573359, 17592186044416, 1242509488367959346729318, 4319701, 16777216, 1242497289586984969279754, 4073831, 16777216, 1242483682693744132256769, 511616124031, 2199023255552, 1242473410264041616758189, 3673389, 16777216, 1242458234206301595310059, 1725811, 8388608, 1242441967867677644628826, 3532845575111, 17592186044416, 1242438220132157116884518, 3166073, 16777216, 1242456141335158977059000, 3132095659693, 17592186044416, 1242470504477920493043716, 1404555, 8388608, 1242476120714647685968313, 329065, 2097152, 1242471087308700095242022, 2597141326789, 17592186044416, 1242457632158352620889957, 579951, 4194304, 1242437777407642157602356, 2163927, 16777216, 1242419104981357477787471, 2124937635887, 17592186044416, 1242419867978322440218703, 237253, 2097152, 1242468069852124538532989, 891621, 8388608, 1242556117118751116396580, 835283, 8388608, 1242701389448864596620281, 108661779151, 1099511627776, 1242722227827773059566058, 98749, 1000000, 1242724478666673378275607]
def ClN : List ℤ := raw_ints% [-975396137404471176, -18039847499279627, -57144266227350972, 10222735143864220, -987093121083358, 49857397058215, -2171723658801, 6183998173011, 1384150907879, 1296591874904, 3167716353948, -983073430486, 4043533649476, -2752150795221, 4693179549314, -3835562797762, 4696478466951]
def ndN : List ℤ := raw_ints% [1, 1, 678070426046866372172432, 4109003, 4194304, 678108155672580822939427, 2015253, 2097152, 678109860969070739272726, 15800979, 16777216, 678113088765990789439917, 7737939, 8388608, 678112928262283978894068, 15150227, 16777216, 678110261065602346481215, 7413993, 8388608, 678109109631895262884978, 14513471, 16777216, 678110536556010993083280, 888201, 1048576, 678112691063234351436789, 13894071, 16777216, 678113642794089013325424, 13575087, 16777216, 678112449579010822733287, 3317843, 4194304, 678110128345191806093106, 12972421, 16777216, 678108102832706498248014, 6331145, 8388608, 678107165110181387208004, 3276730368397, 4398046511104, 678106971384016564276153, 12190601, 16777216, 678110629499907421807423, 11888879, 16777216, 678113540330301034529032, 11598921, 16777216, 678115071008150021436515, 11294679, 16777216, 678114981122336384050437, 10988673, 16777216, 678113569040199832263307, 5348657, 8388608, 678111978190181028604099, 10410525, 16777216, 678111198518496349063846, 10113011, 16777216, 678111889813951162142570, 1305092809445, 2199023255552, 678112972215301779803729, 9685339, 16777216, 678115047196974550884387, 293757, 524288, 678117410374813274248399, 9142133, 16777216, 678118700329242317062619, 8860993, 16777216, 678118540256909607961423, 8584261, 16777216, 678116778063202610839197, 32523, 65536, 678114302686326583828691, 8542441030865, 17592186044416, 678112672923562047542589, 3942453, 8388608, 678110879094935298618142, 7642529, 16777216, 678110641766249083189945, 7398749, 16777216, 678111766192082254265035, 7166639, 16777216, 678113567226658324489107, 6938169, 16777216, 678115095157283380068434, 3350577, 8388608, 678115284463470176302311, 6896403054357, 17592186044416, 678114508524695839244127, 793519, 2097152, 678111108579027936612363, 6137511, 16777216, 678106069591589890919602, 5917211, 16777216, 678099804818654379776739, 5700953, 16777216, 678094569031071625913495, 2976343721197, 8796093022208, 678094154530591115735375, 2737111, 8388608, 678095080087749882179464, 5270345, 16777216, 678098811470437960634234, 5076227, 16777216, 678103694442692842127427, 1221289, 4194304, 678107882808144146581295, 4706759, 16777216, 678109072027041609467695, 4805667573359, 17592186044416, 678107312143535020262755, 2205131, 8388608, 678100672028287528545586, 4233501, 16777216, 678089754273324328953040, 4075575, 16777216, 678079487641791201803974, 1960273, 8388608, 678073412240425463045116, 511616124031, 2199023255552, 678073182475446639788302, 3752461, 16777216, 678076145300742889726378, 1801985, 8388608, 678086155373224593680185, 3465329, 16777216, 678091712827390118705828, 3532845575111, 17592186044416, 678081273742942095218201, 19501, 100000, 678046008960807752679017]
def CovP : Cov := ⟨48, BsP, 53 / 58, dyL 60 ClP, 2000000 / 901251, -(1098749 / 901251)⟩
def CovN : Cov := ⟨48, BsN ++ [mBlk DmN], 53 / 58, dyL 60 ClN, 200000 / 80499, -(119501 / 80499)⟩
def BudP : ℚ := (622702142184220569935279 / 604462909807314587353088 : ℚ)
def BudN : ℚ := (679514057538748251027749 / 1208925819614629174706176 : ℚ)
def EP : ℚ := (940994352215 / 274877906944 : ℚ)
def EN : ℚ := (1140318958169 / 274877906944 : ℚ)
def KP : ℚ := (23501918744161 / 1099511627776 : ℚ)
def KN : ℚ := (9737388142267 / 549755813888 : ℚ)
def EvP : ℕ := 14641620594118061632
def TmN : ℤ := 10081810261843856890665951475144112139029719

/-! ### The instances -/

theorem enc_valid : Enc.Valid capSource := CoefEnc.valid (by decide +kernel)
theorem enc_q1 : Enc.qh < 1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem tot_T : ((999997120790 : ℕ) : ℤ) = sumP row0 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem cos_ok : (List.range 94).all (cosChk 93 CTl) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem co_ok : coefChk Enc dcL Cql 0 = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem cq_ok : cqOK Cql = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem cq_len : Cql.length = 384 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! positive gas -/
theorem pRel : relP gP.P gasPosT gP.L = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pSep : sepL (2 * 10 ^ 12) gP.L = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pRows : rows gP.P 67 (gP.L.map (stAt gP.P gP.T 1)) = gP.R := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pR' : gP.R = gP.R.headD 0 :: (gP.R.drop 1).headD 0 :: gP.R.drop 2 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pLn : gP.L.length = gP.Ln := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pSg : SG gP.P gP.T gP.L = gP.Sg := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pLI : LI gP.P gP.T gP.Q gP.L = gP.LIv := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pLEI : LEI gP.P gP.T gP.Q gP.L = gP.LEIv := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pM : gP.chkM = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pV : gP.chkV = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pG : G2I gP.P gP.T gP.Q gP.L = gP.G2v := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pS' : gP.chkS = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pC : gP.chkC = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pE : (gP.L.map (eInt 900 gP.P 64 gP.T)).sum = EvP := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pmq : 0 ≤ massQ gP.T gP.L := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pGl : 0 < (gP.G []).length := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! negative gas -/
theorem nRel : relN gN.P gasNegT.reverse gN.L = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nSep : sepL (2 * 10 ^ 12) gN.L = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nRows : rows gN.P 131 (gN.L.map (stAt gN.P gN.T 1)) = gN.R := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nR' : gN.R = gN.R.headD 0 :: (gN.R.drop 1).headD 0 :: gN.R.drop 2 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nLn : gN.L.length = gN.Ln := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nSg : SG gN.P gN.T gN.L = gN.Sg := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nLI : LI gN.P gN.T gN.Q gN.L = gN.LIv := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nLEI : LEI gN.P gN.T gN.Q gN.L = gN.LEIv := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nM : gN.chkM = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nV : gN.chkV = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nG : G2I gN.P gN.T gN.Q gN.L = gN.G2v := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nS' : gN.chkS = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nC : gN.chkC = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nmq : 0 ≤ massQ gN.T gN.L := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nMi : gN.Mi = gN.Mi.headD 0 :: gN.Mi.tail := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nMe : gN.Me = gN.Me.headD 0 :: gN.Me.tail := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nMir : chkMir gN.W 1 (dyL gN.Qm gN.Mi.tail) (dyL gN.Qm gN.Me.tail) miN (dyL 120 meN) = true := by
  decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nl1 : gN.Mi.tail.length = miN.length := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nl2 : gN.Mi.tail.length = (dyL 120 meN).length := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! radial records -/
theorem pAll : RPd.allChk (auxT Sign.pos) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nAll : RNd.allChk (auxT Sign.neg) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pAux : auxOK (auxT Sign.pos) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nAux : auxOK (auxT Sign.neg) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pHq : RPd.hq = (1 - massQ gP.T gP.L) / (sumP (auxT Sign.pos) : ℚ) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nHq : RNd.hq = (53 / 58 - massQ gN.T gN.L) / (sumP (auxT Sign.neg) : ℚ) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pHq0 : 0 ≤ RPd.hq := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nHq0 : 0 ≤ RNd.hq := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pTot : 0 ≤ sumP (auxT Sign.pos) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nTot : 0 ≤ sumP (auxT Sign.neg) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nRn : rnOK RNd rnsN 44 = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nFb : fbOK RNd = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nDm : DmN = truncD RNd.sh 96 (mirF RNd rnsN 44 16) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nTm : abs1 ((mirF RNd rnsN 44 16).drop 96) = TmN := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! covers -/
theorem pNodes : (ndOf ndP).all CovP.nodeOK = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nNodes : (ndOf ndN).all CovN.nodeOK = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pChain : CovP.chain EP KP BudP ((ndOf ndP).headD (0, 0)) (ndOf ndP).tail = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nChain : CovN.chain EN KN BudN ((ndOf ndN).headD (0, 0)) (ndOf ndN).tail = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pEs : sumEQ CovP.W CovP.Bs ≤ EP := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nEs : sumEQ CovN.W CovN.Bs ≤ EN := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pK : 2 * CovP.s + mc4 CovP.Cl 0 * CovP.α ^ 2 ≤ KP := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nK : 2 * CovN.s + mc4 CovN.Cl 0 * CovN.α ^ 2 ≤ KN := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pBot : bot ((ndOf ndP).headD (0, 0)) (ndOf ndP).tail = 98749 / 1000000 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nBot : bot ((ndOf ndN).headD (0, 0)) (ndOf ndN).tail = 19501 / 100000 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pTop : ((ndOf ndP).headD (0, 0)).1 = 1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nTop : ((ndOf ndN).headD (0, 0)).1 = 1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pHd : (ndOf ndP).headD (0, 0) :: (ndOf ndP).tail = ndOf ndP := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nHd : (ndOf ndN).headD (0, 0) :: (ndOf ndN).tail = ndOf ndN := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! final constants -/
theorem pFin : gP.Tb + sumQ (dyL 40 gP.f) - 2 * massQ gP.T gP.L * (6931471803 / 10 ^ 10) - 14762657 / 100000000 +
    (1 / 900 + 1 / 901) / 901 * ((EvP : ℚ) / 2 ^ 64) + errS RPd 16 +
    Enc.tail (1 - massQ gP.T gP.L) 1 + BudP +
    diffSum (D : ℚ) (addQ (Zq 1098749 901251 4000000 gP.W (gP.G [])) CovP.Cl) posP ≤ posEps := by
  decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

theorem nFin : gN.Tb + sumQ (dyL 40 gN.f) + sumQ (dyL 120 meN) -
    2 * massQ gN.T gN.L * (6931471803 / 10 ^ 10) -
    5463909 / 100000000 + errS RNd 16 + ((TmN : ℚ) / 2 ^ 160 + 384 * (mirE RNd 1 16 + 1 / 2 ^ RNd.W)) +
    Enc.tail (53 / 58 - massQ gN.T gN.L) 2 + BudN +
    diffSum (D : ℚ) (addQ (Zq 119501 80499 400000 gN.W (gN.G (0 :: miN))) CovN.Cl) negP ≤ negEps := by
  decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

theorem pT0 : 0 < gP.T := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nT0 : 0 < gN.T := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pTg : (gP.T : ℤ) = sumP row0 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nTg : (gN.T : ℤ) = sumP row0 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pP64 : 64 ≤ 900 * gP.P := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pW : RPd.W + RPd.sh = 160 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nW : RNd.W + RNd.sh = 160 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pB : RPd.Bs.length = 16 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nB : RNd.Bs.length = 16 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem dc0 : 0 ≤ dcL := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pS0 : 0 ≤ CovP.s := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nS0 : 0 ≤ CovN.s := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pA0 : 0 ≤ CovP.α := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nA0 : 0 ≤ CovN.α := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pH0 : 0 < ((ndOf ndP).headD (0, 0)).1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nH0 : 0 < ((ndOf ndN).headD (0, 0)).1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

noncomputable section

theorem tgtP : tgt Sign.pos = ((1 - massQ gP.T gP.L : ℚ) : ℝ) := by
  have hF : List.Forall₂ (Rel gP.P gP.T) (capSource.gas Sign.pos) gP.L := relP_spec pTg gasPosT gP.L pRel
  show 1 - massL (capSource.gas Sign.pos) = _
  rw [massL_rel hF]
  push_cast
  ring

theorem tgtN : tgt Sign.neg = ((53 / 58 - massQ gN.T gN.L : ℚ) : ℝ) := by
  have hF := relN_spec nTg gasNegT.reverse gN.L nRel
  have hp : (gasNegT.reverse.map fun t => (mkCell 1 (sumP row0) t).reflect).Perm
      (reflectL (capSource.gas Sign.neg)) := by
    have e : (gasNegT.reverse.map fun t => (mkCell 1 (sumP row0) t).reflect) =
        (reflectL (capSource.gas Sign.neg)).reverse := by
      show _ = (((gasNegT.map (mkCell 1 (sumP row0))).map YCell.reflect)).reverse
      rw [List.map_map, List.map_reverse]
      rfl
    rw [e]
    exact List.reverse_perm _
  show 53 / 58 - massL (capSource.gas Sign.neg) = _
  rw [← massL_reflect, ← massL_perm hp, massL_rel hF]
  push_cast
  ring

theorem radP : RadOK RPd capSource (auxT Sign.pos) (tgt Sign.pos) (sumP (auxT Sign.pos)) 16 :=
  radOK_of RPd Sign.pos enc_valid tgtP pHq pHq0 pAux rfl cos_ok co_ok cq_ok cq_len pW dc0 pB pAll pTot

theorem radN : RadOK RNd capSource (auxT Sign.neg) (tgt Sign.neg) (sumP (auxT Sign.neg)) 16 :=
  radOK_of RNd Sign.neg enc_valid tgtN nHq nHq0 nAux rfl cos_ok co_ok cq_ok cq_len nW dc0 nB nAll nTot

theorem phiP : ∀ x ∈ Icc (98749 / 1000000 : ℝ) 1, CovP.Phi x ≤ BudP := fun x hx =>
  Phi_of CovP (lo := 98749 / 1000000) _ _ pS0 pA0 (blks_ok RPd pB pHq0 pAll) pEs pK pH0 pChain
    (by rw [pHd]; exact pNodes) pBot pTop ⟨by push_cast; exact hx.1, by simpa using hx.2⟩

theorem blkN : ∀ B ∈ CovN.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg := by
  intro B hB
  rcases List.mem_append.1 hB with h | h
  · exact blks_ok RNd nB nHq0 nAll B h
  · obtain rfl := List.mem_singleton.1 h
    simp [mBlk]

theorem phiN : ∀ x ∈ Icc (19501 / 100000 : ℝ) 1, CovN.Phi x ≤ BudN := fun x hx =>
  Phi_of CovN (lo := 19501 / 100000) _ _ nS0 nA0 blkN nEs nK nH0 nChain
    (by rw [nHd]; exact nNodes) nBot nTop ⟨by push_cast; exact hx.1, by simpa using hx.2⟩

/-- The source-to-polynomial bound of the positive ordinary compact field. -/
theorem posHf : PosHf capSource (Trunc.finite 384) :=
  pos_core gP RPd CovP Enc (Bud := BudP) pRel pTg pT0 pSep pRows pR' pLn pSg pLI pLEI pM pV pG pS' pC pE
    pP64 radP rfl enc_valid enc_q1 rfl rfl rfl rfl rfl phiP pGl pmq pFin

/-- The source-to-polynomial bound of the negative ordinary compact field. -/
theorem negHf : NegHf capSource (Trunc.finite 384) :=
  neg_core gN RNd CovN Enc (Bud := BudN) nRel nTg nT0 nSep nRows nR' nLn nSg nLI nLEI nM nV nG nS' nC
    nMi nMe nMir nl1 nl2 radN rfl rnsN 44 96 (fun i hi => hrn_of nRn hi)
    (fun i hi d hd => hb_of nFb hi hd) nDm nTm enc_valid enc_q1 rfl rfl rfl rfl rfl phiN nmq nFin

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf
