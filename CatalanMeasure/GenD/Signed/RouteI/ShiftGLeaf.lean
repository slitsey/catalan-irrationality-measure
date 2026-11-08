module

public import CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
public import CatalanMeasure.GenD.Signed.RouteI.T4Instance
public import CatalanMeasure.GenD.Signed.RouteI.ShiftG

@[expose] public section

/-!
# G5 shiftG, leaf engine: integer-polynomial checks for the shift sups

The sup facts of the shift records (`hX`: row, `hY`: column) are one-variable polynomial inequalities
on a finite trial.  This module holds the generic part, shared by the leaf instances:

* `wts c Λ l`: the integer weights `c · l_k · (Λ / (k+1))` (kernel division, `Λ = lcm(1..K)`);
* `trialT_wts`, `trialS_wts`: `Λ D · T(trialSeqOf l D, x)` and `Λ D · S(trialSeqOf l D, x)` as sums of
  the weights against `T_{k+1}(x)` and `x^{k+1}`;
* `combZ c0 wT wS`: the integer polynomial `c0 + Σ wT_k T_{k+1}(x) + Σ wS_k x^{k+1}` and its value;
* `logW`: the degree-65 integer majorant of `log (1 + 3 s / 4)` on `[0,1]` (Mathlib's
  `abs_log_sub_add_sum_range_le` with `n = 64`), `log_le_logW`;
* `leafX2`, `leafX1`, `leafY`: from one `checkZ` to the real inequality.
-/

open Set Filter

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf
open CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.T4Instance
  OAI.InternalCatalan

noncomputable section

/-- The integer weights `c · l_k · (Λ / (k+1))`. -/
def wts (c Λ : ℤ) (l : List ℤ) : List ℤ :=
  (List.range l.length).map (fun k => c * l.getD k 0 * (Λ / ((k : ℤ) + 1)))

theorem wts_length (c Λ : ℤ) (l : List ℤ) : (wts c Λ l).length = l.length := by simp [wts]

theorem wts_getD (c Λ : ℤ) (l : List ℤ) {k : ℕ} (hk : k < l.length) :
    (wts c Λ l).getD k 0 = c * l.getD k 0 * (Λ / ((k : ℤ) + 1)) := by
  simp [wts, List.getD_eq_getElem?_getD, hk]

/-- Divisibility, in the form the kernel checks: `(k+1) ∣ Λ` for `k < n`. -/
def divOK (Λ : ℤ) (n : ℕ) : Bool := (List.range n).all fun k => decide (Λ % ((k : ℤ) + 1) = 0)

theorem divOK_spec {Λ : ℤ} {n : ℕ} (h : divOK Λ n = true) {k : ℕ} (hk : k < n) :
    ((k : ℤ) + 1) ∣ Λ := by
  unfold divOK at h
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  exact Int.dvd_of_emod_eq_zero (by simpa using this)

theorem wts_sum {Λ : ℤ} (c : ℤ) (l : List ℤ) (hd : ∀ k, k < l.length → ((k : ℤ) + 1) ∣ Λ)
    (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range l.length, ((wts c Λ l).getD i 0 : ℝ) * f i =
      (c : ℝ) * Λ * ∑ i ∈ Finset.range l.length, (l.getD i 0 : ℝ) * f i / ((i + 1 : ℕ) : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < l.length := Finset.mem_range.mp hk
  rw [wts_getD _ _ _ hk']
  have hd' := hd k hk'
  have hne : (((k : ℤ) + 1 : ℤ) : ℝ) ≠ 0 := by push_cast; positivity
  have := Int.cast_div hd' hne
  push_cast at this ⊢
  rw [this]
  field_simp

theorem trialT_wts {Λ : ℤ} (c : ℤ) (D : ℕ) (hD : 0 < D) (l : List ℤ)
    (hd : ∀ k, k < l.length → ((k : ℤ) + 1) ∣ Λ) (x : ℝ) :
    ∑ i ∈ Finset.range l.length, ((wts c Λ l).getD i 0 : ℝ) *
        (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x =
      (c : ℝ) * Λ * D * barrierTrialT (trialSeqOf l D) x := by
  rw [wts_sum c l hd, trialT_eq_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp

theorem trialS_eq_sum (l : List ℤ) (D : ℕ) (x : ℝ) :
    barrierTrialS (trialSeqOf l D) x =
      ∑ k ∈ Finset.range l.length, ((l.getD k 0 : ℝ) / D) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialS
  have heq (k : ℕ) : trialSeqOf l D (k + 1) = (l.getD k 0 : ℝ) / D := by simp [trialSeqOf]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : l.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default l 0 hlen]
  norm_num

theorem trialS_wts {Λ : ℤ} (c : ℤ) (D : ℕ) (hD : 0 < D) (l : List ℤ)
    (hd : ∀ k, k < l.length → ((k : ℤ) + 1) ∣ Λ) (x : ℝ) :
    ∑ i ∈ Finset.range l.length, ((wts c Λ l).getD i 0 : ℝ) * x ^ (i + 1) =
      (c : ℝ) * Λ * D * barrierTrialS (trialSeqOf l D) x := by
  rw [wts_sum c l hd, trialS_eq_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp

/-! ### The combination polynomial -/

theorem evalZ_eq_sum (p : List ℤ) (x : ℝ) :
    evalZ p x = ∑ i ∈ Finset.range p.length, (p.getD i 0 : ℝ) * x ^ i := by
  induction p with
  | nil => simp [evalZ]
  | cons a q ih =>
    simp only [evalZ, List.length_cons, Finset.sum_range_succ']
    rw [ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem evalZ_mono (wS : List ℤ) (x : ℝ) :
    evalZ (0 :: wS) x = ∑ i ∈ Finset.range wS.length, (wS.getD i 0 : ℝ) * x ^ (i + 1) := by
  simp only [evalZ, Int.cast_zero, zero_add]
  rw [evalZ_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `c0 + Σ wT_k T_{k+1}(x) + Σ wS_k x^{k+1}`. -/
def combZ (c0 : ℤ) (wT wS : List ℤ) : List ℤ := addL (chebPoly c0 wT) (0 :: wS)

theorem evalZ_combZ (c0 : ℤ) (wT wS : List ℤ) (x : ℝ) :
    evalZ (combZ c0 wT wS) x = c0 + ∑ i ∈ Finset.range wT.length, (wT.getD i 0 : ℝ) *
        (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x +
      ∑ i ∈ Finset.range wS.length, (wS.getD i 0 : ℝ) * x ^ (i + 1) := by
  unfold combZ
  rw [evalZ_addL, evalZ_chebPoly, evalZ_mono]

/-- `p · (1 + x²)`. -/
def mulOneSq (p : List ℤ) : List ℤ := addL p (0 :: 0 :: p)

theorem evalZ_mulOneSq (p : List ℤ) (x : ℝ) : evalZ (mulOneSq p) x = (1 + x ^ 2) * evalZ p x := by
  unfold mulOneSq
  rw [evalZ_addL]
  simp only [evalZ, Int.cast_zero, zero_add]
  ring

/-! ### The log majorant -/

/-- `lcm (1, …, 64)`. -/
def L64 : ℤ := 1182266884102822267511361600

theorem L64_div : divOK L64 64 = true := by decide +kernel

/-- Integer coefficients of `4^65 · L64 ·` the majorant of `log (1 + 3 s / 4)`; entry `i` ↔ `s^(i+1)`. -/
def logW : List ℤ := (List.range 65).map fun (i : ℕ) =>
  if i < 64 then (-1 : ℤ) ^ i * 3 ^ (i + 1) * 4 ^ (64 - i) * (L64 / ((i : ℤ) + 1))
  else 4 * 3 ^ 65 * L64

theorem logW_length : logW.length = 65 := by simp [logW]

theorem log_le_logW {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.log (1 + 3 / 4 * s) ≤
      (∑ i ∈ Finset.range 65, (logW.getD i 0 : ℝ) * s ^ (i + 1)) / ((4 : ℝ) ^ 65 * L64) := by
  have hx : |(-(3 / 4 * s) : ℝ)| < 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith
  have h := Real.abs_log_sub_add_sum_range_le hx 64
  have hxa : |(-(3 / 4 * s) : ℝ)| = 3 / 4 * s := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
  rw [hxa] at h
  have e1 : (1 : ℝ) - -(3 / 4 * s) = 1 + 3 / 4 * s := by ring
  rw [e1] at h
  have hL64 : (0 : ℝ) < L64 := by unfold L64; norm_num
  have hpos : (0 : ℝ) < (4 : ℝ) ^ 65 * L64 := by positivity
  -- the tail
  have htail : (3 / 4 * s) ^ (64 + 1) / (1 - 3 / 4 * s) ≤ 4 * (3 / 4 * s) ^ 65 := by
    have hu0 : 0 ≤ 3 / 4 * s := by positivity
    have h1 : (1 : ℝ) / 4 ≤ 1 - 3 / 4 * s := by nlinarith
    have h2 : 0 ≤ (3 / 4 * s) ^ 65 * (3 - 4 * (3 / 4 * s)) :=
      mul_nonneg (pow_nonneg hu0 65) (by nlinarith)
    rw [div_le_iff₀ (by linarith)]
    nlinarith [h2]
  have hup : Real.log (1 + 3 / 4 * s) ≤ -(∑ i ∈ Finset.range 64, (-(3 / 4 * s)) ^ (i + 1) / (i + 1)) +
      4 * (3 / 4 * s) ^ 65 := by
    have := (abs_le.mp h).2
    linarith
  refine hup.trans (le_of_eq ?_)
  have hlt : ∀ i, i < 64 → logW.getD i 0 =
      (-1) ^ i * 3 ^ (i + 1) * 4 ^ (64 - i) * (L64 / ((i : ℤ) + 1)) := by
    intro i hi
    simp [logW, List.getD_eq_getElem?_getD, hi, show i < 65 by omega]
  have hl64 : logW.getD 64 0 = 4 * 3 ^ 65 * L64 := by
    simp [logW, List.getD_eq_getElem?_getD]
  have key : ∀ i ∈ Finset.range 64, (logW.getD i 0 : ℝ) * s ^ (i + 1) / ((4 : ℝ) ^ 65 * L64) =
      -((-(3 / 4 * s)) ^ (i + 1) / ((i : ℝ) + 1)) := by
    intro i hi
    have hi' : i < 64 := Finset.mem_range.mp hi
    rw [hlt i hi']
    have hd := divOK_spec L64_div hi'
    have hne : (((i : ℤ) + 1 : ℤ) : ℝ) ≠ 0 := by push_cast; positivity
    have hc := Int.cast_div hd hne
    push_cast at hc ⊢
    rw [hc]
    have h4 : (4 : ℝ) ^ 65 = 4 ^ (64 - i) * 4 ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    have hneg : (-(3 / 4 * s) : ℝ) ^ (i + 1) = (-1) ^ (i + 1) * 3 ^ (i + 1) * s ^ (i + 1) / 4 ^ (i + 1) := by
      rw [show (-(3 / 4 * s) : ℝ) = (-1) * (3 * s / 4) by ring, mul_pow, div_pow, mul_pow]
      ring
    rw [h4, hneg]
    have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
    have h4a : (4 : ℝ) ^ (64 - i) ≠ 0 := by positivity
    have h4b : (4 : ℝ) ^ (i + 1) ≠ 0 := by positivity
    have hLn : (L64 : ℝ) ≠ 0 := hL64.ne'
    field_simp
    ring
  have last : (logW.getD 64 0 : ℝ) * s ^ (64 + 1) / ((4 : ℝ) ^ 65 * L64) =
      4 * (3 / 4 * s) ^ 65 := by
    rw [hl64]
    push_cast
    rw [mul_pow, div_pow]
    field_simp
    ring
  have hs65 : ∑ i ∈ Finset.range 65, (logW.getD i 0 : ℝ) * s ^ (i + 1) =
      ∑ i ∈ Finset.range 64, (logW.getD i 0 : ℝ) * s ^ (i + 1) + (logW.getD 64 0 : ℝ) * s ^ (64 + 1) :=
    Finset.sum_range_succ _ 64
  rw [hs65, add_div, Finset.sum_div, Finset.sum_congr rfl key, last, Finset.sum_neg_distrib]


/-! ### From one `checkZ` to the real inequalities -/

/-- `x ∈ [-1,1]` ↦ `w = (x+1)/2 ∈ [0,1]`, `x = -1 + 2 w`. -/
theorem nonneg_on_Icc {p : List ℤ} {f : ℕ} (h : checkZ (compLin (-1) 2 p) f 0 0 = true) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 ≤ evalZ p x := by
  have hw := checkZ_sound h (m := 0) (s := 0) (w := (x + 1) / 2)
    (by simp; linarith [hx.1]) (by simp; linarith [hx.2])
  rw [evalZ_compLin] at hw
  have e : ((-1 : ℤ) : ℝ) + ((2 : ℤ) : ℝ) * ((x + 1) / 2) = x := by push_cast; ring
  rw [e] at hw
  exact hw

/-- **The second-population row sup** `hX`: `-4 T(du) - S(dv) ≤ cn / 10^8` on `[-1,1]`. -/
theorem leafX2 {Λ : ℤ} (hΛ : 0 < Λ) (du dv : List ℤ)
    (hdu : ∀ k, k < du.length → ((k : ℤ) + 1) ∣ Λ) (hdv : ∀ k, k < dv.length → ((k : ℤ) + 1) ∣ Λ)
    (cn : ℤ) {f : ℕ}
    (h : checkZ (compLin (-1) 2 (combZ (cn * 2 ^ 24 * Λ) (wts (4 * 10 ^ 8) Λ du)
      (wts (10 ^ 8) Λ dv))) f 0 0 = true) :
    ∀ x ∈ Icc (-1 : ℝ) 1, -(4 * barrierTrialT (trialSeqOf du (2 ^ 24)) x) -
      barrierTrialS (trialSeqOf dv (2 ^ 24)) x ≤ (cn : ℝ) / 10 ^ 8 := by
  intro x hx
  have hw := nonneg_on_Icc h hx
  rw [evalZ_combZ, wts_length, wts_length, trialT_wts (4 * 10 ^ 8) (2 ^ 24) (by norm_num) du hdu,
    trialS_wts (10 ^ 8) (2 ^ 24) (by norm_num) dv hdv] at hw
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have hM : (0 : ℝ) < 10 ^ 8 * 2 ^ 24 * Λ := by positivity
  set Tt := barrierTrialT (trialSeqOf du (2 ^ 24)) x with hT
  set Ss := barrierTrialS (trialSeqOf dv (2 ^ 24)) x with hS
  push_cast at hw
  have key : 0 ≤ (10 ^ 8 * 2 ^ 24 * (Λ : ℝ)) * ((cn : ℝ) / 10 ^ 8 + 4 * Tt + Ss) := by
    have e : (10 ^ 8 * 2 ^ 24 * (Λ : ℝ)) * ((cn : ℝ) / 10 ^ 8 + 4 * Tt + Ss) =
        (cn : ℝ) * 2 ^ 24 * Λ + 4 * 10 ^ 8 * Λ * 2 ^ 24 * Tt + 10 ^ 8 * Λ * 2 ^ 24 * Ss := by
      field_simp
    rw [e]
    linarith [hw]
  have := nonneg_of_mul_nonneg_right key hM
  linarith

/-- The log majorant, in the form of `col_interp`: `γ log (1 + 3 s / 4) ≤ γ · logW(s) / (4^65 L64)`. -/
theorem evalZ_logW (s : ℝ) :
    evalZ (0 :: logW) s = ∑ i ∈ Finset.range 65, (logW.getD i 0 : ℝ) * s ^ (i + 1) := by
  rw [evalZ_mono, logW_length]

/-- **The column sup** `hY`: `2 T(dv, s) + (gn/gd) log (1 + 3 s / 4) ≤ yn / yd` on `[0,1]`. -/
theorem leafY {Λ : ℤ} (hΛ : 0 < Λ) (dv : List ℤ) (hdv : ∀ k, k < dv.length → ((k : ℤ) + 1) ∣ Λ)
    (gn gd yn yd : ℤ) (hgn : 0 ≤ gn) (hgd : 0 < gd) (hyd : 0 < yd) {f : ℕ}
    (h : checkZ (addL (combZ (yn * 2 ^ 24 * Λ * 4 ^ 65 * L64 * gd)
        (wts (-2 * 4 ^ 65 * L64 * gd * yd) Λ dv) [])
        (smulL (-(gn * 2 ^ 24 * Λ * yd)) (0 :: logW))) f 0 0 = true) :
    ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv (2 ^ 24)) s +
      ((gn : ℝ) / gd) * Real.log (1 + 3 / 4 * s) ≤ (yn : ℝ) / yd := by
  intro s hs
  have hw := checkZ_sound h (m := 0) (s := 0) (w := s) (by simpa using hs.1) (by simpa using hs.2)
  rw [evalZ_addL, evalZ_combZ, evalZ_smulL, evalZ_logW, wts_length,
    trialT_wts (-2 * 4 ^ 65 * L64 * gd * yd) (2 ^ 24) (by norm_num) dv hdv] at hw
  have hlog := log_le_logW hs.1 hs.2
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have hgd' : (0 : ℝ) < gd := by exact_mod_cast hgd
  have hyd' : (0 : ℝ) < yd := by exact_mod_cast hyd
  have hgn' : (0 : ℝ) ≤ gn := by exact_mod_cast hgn
  have hL : (0 : ℝ) < L64 := by unfold L64; norm_num
  have hP : (0 : ℝ) < 4 ^ 65 * L64 := by positivity
  simp only [List.length_nil, Finset.range_zero, Finset.sum_empty, add_zero] at hw
  set Tt := barrierTrialT (trialSeqOf dv (2 ^ 24)) s with hT
  set Sl := ∑ i ∈ Finset.range 65, (logW.getD i 0 : ℝ) * s ^ (i + 1) with hSl
  push_cast at hw
  rw [le_div_iff₀ hP] at hlog
  have hM : (0 : ℝ) < 2 ^ 24 * Λ * (4 ^ 65 * L64) * gd * yd := by positivity
  have hgl : (gn : ℝ) * ((4 : ℝ) ^ 65 * L64) * Real.log (1 + 3 / 4 * s) ≤ gn * Sl := by
    have := mul_le_mul_of_nonneg_left hlog hgn'
    linarith
  have hgd0 : (gd : ℝ) ≠ 0 := hgd'.ne'
  have hyd0 : (yd : ℝ) ≠ 0 := hyd'.ne'
  have key : 0 ≤ (2 ^ 24 * Λ * (4 ^ 65 * L64) * gd * yd) * ((yn : ℝ) / yd - (2 * Tt +
      (gn / gd) * Real.log (1 + 3 / 4 * s))) := by
    have e : (2 ^ 24 * Λ * (4 ^ 65 * L64) * gd * yd) * ((yn : ℝ) / yd - (2 * Tt +
        (gn / gd) * Real.log (1 + 3 / 4 * s))) =
        (yn * 2 ^ 24 * Λ * 4 ^ 65 * L64 * gd + (-2 * 4 ^ 65 * L64 * gd * yd) * Λ * 2 ^ 24 * Tt +
          (-(gn * 2 ^ 24 * Λ * yd)) * Sl) +
        (2 ^ 24 * Λ * yd) * (gn * Sl - gn * (4 ^ 65 * L64) * Real.log (1 + 3 / 4 * s)) := by
      field_simp
      ring
    rw [e]
    have h2 : 0 ≤ (2 ^ 24 * (Λ : ℝ) * yd) * (gn * Sl - gn * (4 ^ 65 * L64) *
        Real.log (1 + 3 / 4 * s)) := mul_nonneg (by positivity) (by linarith)
    linarith [hw]
  have := nonneg_of_mul_nonneg_right key hM
  linarith


/-- The integer polynomial of the first-population row sup (see `leafX1`). -/
def x1Poly (cn Λ : ℤ) (du dv : List ℤ) : List ℤ :=
  addL (mulOneSq (combZ (Λ * (29 * cn * 2 ^ 24 - 213407 * 10 ^ 9)) (wts (4 * 29 * 10 ^ 8) Λ du)
    (wts (29 * 10 ^ 8) Λ dv))) [0, 0, 4 * 213407 * 29 * 10 ^ 8 * Λ]

/-- **The first-population row sup** `hX`: `-2 T(du) - S(dv) + dl (5/29 - 2 x²/(1+x²)) ≤ cn / 10^8`
on `[-1,1]`, with `du` on the grid `2^-23` (the doubled trial) and `dl = 213407 / 2^23`. -/
theorem leafX1 {Λ : ℤ} (hΛ : 0 < Λ) (du dv : List ℤ)
    (hdu : ∀ k, k < du.length → ((k : ℤ) + 1) ∣ Λ) (hdv : ∀ k, k < dv.length → ((k : ℤ) + 1) ∣ Λ)
    (cn : ℤ) {f : ℕ} (h : checkZ (compLin (-1) 2 (x1Poly cn Λ du dv)) f 0 0 = true) :
    ∀ x ∈ Icc (-1 : ℝ) 1, -(2 * barrierTrialT (trialSeqOf du (2 ^ 23)) x) -
      barrierTrialS (trialSeqOf dv (2 ^ 24)) x +
      (213407 / 2 ^ 23 : ℝ) * (5 / 29 - 2 * x ^ 2 / (1 + x ^ 2)) ≤ (cn : ℝ) / 10 ^ 8 := by
  intro x hx
  have hw := nonneg_on_Icc h hx
  unfold x1Poly at hw
  rw [evalZ_addL, evalZ_mulOneSq, evalZ_combZ, wts_length, wts_length,
    trialT_wts (4 * 29 * 10 ^ 8) (2 ^ 23) (by norm_num) du hdu,
    trialS_wts (29 * 10 ^ 8) (2 ^ 24) (by norm_num) dv hdv] at hw
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  set Tt := barrierTrialT (trialSeqOf du (2 ^ 23)) x with hT
  set Ss := barrierTrialS (trialSeqOf dv (2 ^ 24)) x with hS
  simp only [evalZ, Int.cast_zero, Int.cast_mul, Int.cast_ofNat, zero_add, mul_zero, add_zero] at hw
  push_cast at hw
  have hx2 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hM : (0 : ℝ) < (1 + x ^ 2) * (29 * 10 ^ 8 * 2 ^ 24 * Λ) := by positivity
  have key : 0 ≤ ((1 + x ^ 2) * (29 * 10 ^ 8 * 2 ^ 24 * (Λ : ℝ))) * ((cn : ℝ) / 10 ^ 8 -
      (-(2 * Tt) - Ss + (213407 / 2 ^ 23 : ℝ) * (5 / 29 - 2 * x ^ 2 / (1 + x ^ 2)))) := by
    have e : ((1 + x ^ 2) * (29 * 10 ^ 8 * 2 ^ 24 * (Λ : ℝ))) * ((cn : ℝ) / 10 ^ 8 -
        (-(2 * Tt) - Ss + (213407 / 2 ^ 23 : ℝ) * (5 / 29 - 2 * x ^ 2 / (1 + x ^ 2)))) =
        (1 + x ^ 2) * (Λ * (29 * cn * 2 ^ 24 - 213407 * 10 ^ 9) + 4 * 29 * 10 ^ 8 * Λ * 2 ^ 23 * Tt +
          29 * 10 ^ 8 * Λ * 2 ^ 24 * Ss) + 4 * 213407 * 29 * 10 ^ 8 * Λ * x ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith [hw]
  have := nonneg_of_mul_nonneg_right key hM
  linarith

end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf
