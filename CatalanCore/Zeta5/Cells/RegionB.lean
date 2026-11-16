module

public import CatalanCore.Zeta5.Cells.RegionA
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

/-!
# Z5-CELLS, part 9: region B, `t = (b/2)(1 + cosh x)`, `y = y_b cosh(x/2)` (ZD18)

`g_B(x) = 2c₀(log(b/4) + x) − 2 Σ_k w_k e^{−κx} − V(y_b cosh(x/2))`, `x ∈ [0, 3]`.
A cell is `(ρ, r, zB)`: the centre is `x_c = 2 log ρ` (`ρ ≥ 1` rational), so `e^{−κx_c} = q^κ`
with `q = ρ^{-2}`, `cosh(x_c/2) = (ρ+1/ρ)/2`, `sinh(x_c/2) = (ρ−1/ρ)/2` are exact rationals;
`zB ≥ e^{−x}` on the cell bounds the order-5 remainder `2 Σ|w_k| κ^5 zB^κ`; on `x ≥ x_c − r`,
`e^{−x} ≤ ρ^{-2}/(1−r)`.  Everything else is as in region A: one transcendental value `log ρ`
more per cell (ZD21), the pole distances `ρ₁, ρ_α` are global (`y ≥ y_b` on all of region B).
-/

namespace CatalanCore.Zeta5.Cells

open Set Real CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.Cert (qabs)

noncomputable section

/-! ### the exponential tower -/

def TB (K0 c0 : ℝ) (wt : ℕ → ℝ) (N : ℕ) (j : ℕ) (x : ℝ) : ℝ :=
  (if j = 0 then K0 + 2 * c0 * x else if j = 1 then 2 * c0 else 0) -
    2 * ∑ k ∈ Finset.range N,
      wt k * (-((k + 1 : ℕ) : ℝ)) ^ j * Real.exp (-(((k + 1 : ℕ) : ℝ) * x))

theorem hasDerivAt_TB (K0 c0 : ℝ) (wt : ℕ → ℝ) (N j : ℕ) (x : ℝ) :
    HasDerivAt (TB K0 c0 wt N j) (TB K0 c0 wt N (j + 1) x) x := by
  have hk : ∀ k ∈ Finset.range N, HasDerivAt
      (fun x => wt k * (-((k + 1 : ℕ) : ℝ)) ^ j * Real.exp (-(((k + 1 : ℕ) : ℝ) * x)))
      (wt k * (-((k + 1 : ℕ) : ℝ)) ^ (j + 1) * Real.exp (-(((k + 1 : ℕ) : ℝ) * x))) x := by
    intro k _
    have h1 : HasDerivAt (fun x => -(((k + 1 : ℕ) : ℝ) * x)) (-((k + 1 : ℕ) : ℝ)) x := by
      have h := (hasDerivAt_id' x).const_mul (-((k + 1 : ℕ) : ℝ))
      have e : (fun x : ℝ => -((k + 1 : ℕ) : ℝ) * x) = fun x => -(((k + 1 : ℕ) : ℝ) * x) := by
        funext y; ring
      rw [e] at h
      simpa using h
    have h2 := h1.exp.const_mul (wt k * (-((k + 1 : ℕ) : ℝ)) ^ j)
    refine h2.congr_deriv ?_
    ring
  have hs := (HasDerivAt.fun_sum hk).const_mul 2
  have hc : HasDerivAt (fun x : ℝ => if j = 0 then K0 + 2 * c0 * x else if j = 1 then 2 * c0 else 0)
      (if j + 1 = 0 then K0 + 2 * c0 * x else if j + 1 = 1 then 2 * c0 else 0) x := by
    by_cases h0 : j = 0
    · subst h0
      simpa using ((hasDerivAt_id' x).const_mul (2 * c0)).const_add K0
    · by_cases h1 : j = 1
      · subst h1; simpa using hasDerivAt_const x (2 * c0)
      · have : j + 1 ≠ 1 := by omega
        simp [h0, h1, this]
        exact hasDerivAt_const x 0
  have h := hc.fun_sub hs
  unfold TB
  refine h.congr_deriv ?_
  simp

theorem continuous_TB (K0 c0 : ℝ) (wt : ℕ → ℝ) (N j : ℕ) : Continuous (TB K0 c0 wt N j) := by
  unfold TB
  split_ifs <;> fun_prop

theorem isTower_TB (K0 c0 : ℝ) (wt : ℕ → ℝ) (N : ℕ) (c r : ℝ) :
    IsTower (TB K0 c0 wt N) c r 5 where
  cont j _ := (continuous_TB K0 c0 wt N j).continuousOn
  der j _ x _ := hasDerivAt_TB K0 c0 wt N j x

/-- `|TB 5 x| ≤ 2 Σ |w_k| κ^5 zB^κ` where `e^{−x} ≤ zB`. -/
theorem abs_TB5_le (K0 c0 : ℝ) (wt : ℕ → ℝ) (N : ℕ) {x zB : ℝ} (hz : Real.exp (-x) ≤ zB) :
    |TB K0 c0 wt N 5 x| ≤
      2 * ∑ k ∈ Finset.range N, |wt k| * ((k + 1 : ℕ) : ℝ) ^ 5 * zB ^ (k + 1) := by
  unfold TB
  simp only [show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num, if_false, zero_sub,
    abs_neg]
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)),
    abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-(((k + 1 : ℕ) : ℝ) * x)) ≤ zB ^ (k + 1) := by
    have : Real.exp (-(((k + 1 : ℕ) : ℝ) * x)) = (Real.exp (-x)) ^ (k + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hz _
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ### the change of variable `y = y_b cosh(x/2)` -/

def YB (yb : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  yb / 2 ^ j * (if j % 2 = 0 then Real.cosh (x / 2) else Real.sinh (x / 2))

theorem hasDerivAt_YB (yb : ℝ) (j : ℕ) (x : ℝ) : HasDerivAt (YB yb j) (YB yb (j + 1) x) x := by
  have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id' x).div_const 2
  unfold YB
  by_cases hj : j % 2 = 0
  · have hj' : (j + 1) % 2 ≠ 0 := by omega
    simp only [hj, hj', if_true, if_false]
    have := ((Real.hasDerivAt_cosh (x / 2)).comp x h1).const_mul (yb / 2 ^ j)
    refine this.congr_deriv ?_
    rw [pow_succ]
    field_simp
  · have hj' : (j + 1) % 2 = 0 := by omega
    simp only [hj, hj', if_true, if_false]
    have := ((Real.hasDerivAt_sinh (x / 2)).comp x h1).const_mul (yb / 2 ^ j)
    refine this.congr_deriv ?_
    rw [pow_succ]
    field_simp

theorem continuous_YB (yb : ℝ) (j : ℕ) : Continuous (YB yb j) := by
  unfold YB
  split_ifs <;> fun_prop

/-- `|YB j x| ≤ y_b / 2^j · e^{|x|/2}`. -/
theorem abs_YB_le {yb : ℝ} (hyb : 0 ≤ yb) (j : ℕ) (x : ℝ) :
    |YB yb j x| ≤ yb / 2 ^ j * Real.exp (|x| / 2) := by
  unfold YB
  have hc : |Real.cosh (x / 2)| ≤ Real.exp (|x| / 2) := by
    rw [abs_of_pos (Real.cosh_pos _), Real.cosh_eq]
    have h1 : Real.exp (x / 2) ≤ Real.exp (|x| / 2) :=
      Real.exp_le_exp.mpr (by have := le_abs_self x; linarith)
    have h2 : Real.exp (-(x / 2)) ≤ Real.exp (|x| / 2) :=
      Real.exp_le_exp.mpr (by have := neg_le_abs x; linarith)
    linarith
  have hs : |Real.sinh (x / 2)| ≤ Real.exp (|x| / 2) := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (x / 2) ≤ Real.exp (|x| / 2) :=
      Real.exp_le_exp.mpr (by have := le_abs_self x; linarith)
    have h2 : Real.exp (-(x / 2)) ≤ Real.exp (|x| / 2) :=
      Real.exp_le_exp.mpr (by have := neg_le_abs x; linarith)
    have h3 := Real.exp_pos (x / 2)
    have h4 := Real.exp_pos (-(x / 2))
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ yb / 2 ^ j)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  split_ifs
  · exact hc
  · exact hs

/-! ### rational data -/

/-- weights `w_k (−κ)^j` -/
def wTabB : ℕ → ℕ → List ℚ → List ℚ
  | _, _, [] => []
  | k, j, w :: ws => (w * (-((k + 1 : ℕ) : ℚ)) ^ j) :: wTabB (k + 1) j ws

theorem wTabB_length (k j : ℕ) (ws : List ℚ) : (wTabB k j ws).length = ws.length := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih => simp [wTabB, ih]

theorem wTabB_getD (j : ℕ) (ws : List ℚ) : ∀ (k₀ k : ℕ), k < ws.length →
    (wTabB k₀ j ws).getD k 0 = ws.getD k 0 * (-((k₀ + k + 1 : ℕ) : ℚ)) ^ j := by
  induction ws with
  | nil => intro k₀ k hk; simp at hk
  | cons w ws ih =>
    intro k₀ k hk
    cases k with
    | zero => simp [wTabB]
    | succ k =>
      simp only [wTabB, List.getD_cons_succ]
      rw [ih (k₀ + 1) k (by simpa using hk)]
      rw [show k₀ + 1 + k + 1 = k₀ + (k + 1) + 1 by omega]

/-- the powers `P q, P q², …` (`n` of them) -/
def powAux : ℕ → ℚ → ℚ → List ℚ
  | 0, _, _ => []
  | n + 1, P, q => (P * q) :: powAux n (P * q) q

def dotL : List ℚ → List ℚ → ℚ
  | w :: ws, p :: ps => w * p + dotL ws ps
  | _, _ => 0

theorem dotL_pow (q : ℝ) (qq : ℚ) (hq : (qq : ℝ) = q) :
    ∀ (ws : List ℚ) (P : ℚ) (p0 : ℝ), (P : ℝ) = p0 →
      ((dotL ws (powAux ws.length P qq) : ℚ) : ℝ) =
        ∑ k ∈ Finset.range ws.length, ((ws.getD k 0 : ℚ) : ℝ) * (p0 * q ^ (k + 1)) := by
  intro ws
  induction ws with
  | nil => intro P p0 _; simp [powAux, dotL]
  | cons w ws ih =>
    intro P p0 hP
    have hP' : (((P * qq : ℚ)) : ℝ) = p0 * q := by push_cast; rw [hP, hq]
    have := ih _ _ hP'
    simp only [List.length_cons, powAux, dotL]
    rw [Rat.cast_add, Rat.cast_mul, this, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · push_cast; rw [hP, hq]; ring

/-- `Σ |w_k| κ^5 (P z^κ)` -/
def trSumB : ℕ → ℚ → ℚ → List ℚ → ℚ
  | _, _, _, [] => 0
  | k, P, z, w :: ws => qabs w * ((k + 1 : ℕ) : ℚ) ^ 5 * (P * z) + trSumB (k + 1) (P * z) z ws

theorem trSumB_cast (z : ℚ) (ws : List ℚ) : ∀ (k₀ : ℕ) (P : ℚ), ((trSumB k₀ P z ws : ℚ) : ℝ) =
    ∑ k ∈ Finset.range ws.length, |((ws.getD k 0 : ℚ) : ℝ)| * ((k₀ + k + 1 : ℕ) : ℝ) ^ 5 *
      ((P : ℝ) * (z : ℝ) ^ (k + 1)) := by
  induction ws with
  | nil => intro k₀ P; simp [trSumB]
  | cons w ws ih =>
    intro k₀ P
    rw [trSumB, List.length_cons, Finset.sum_range_succ']
    push_cast
    rw [ih (k₀ + 1) (P * z)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    · have : ((qabs w : ℚ) : ℝ) = |(w : ℝ)| := by
        rw [CatalanMeasure.Cert.qabs_eq]; push_cast; rfl
      rw [this]; push_cast; ring

structure DesB where
  α : ℚ
  yb : ℚ
  lam : ℚ
  ws : List ℚ
  M0 : ℚ
  nA : ℕ
  ρ1 : ℚ
  ρa : ℚ

structure TabB where
  W0 : List ℚ
  W1 : List ℚ
  W2 : List ℚ
  W3 : List ℚ
  W4 : List ℚ
  L0 : ℚ × ℚ

structure CellB where
  ρ : ℚ
  r : ℚ
  zB : ℚ

/-- point values of the exponential tower at `x_c = 2 log ρ`; `lr` encloses `log ρ`. -/
def tqB (lam : ℚ) (tab : TabB) (lr : ℚ × ℚ) (Q : List ℚ) : ℕ → ℚ
  | 0 => 2 * lam * (tab.L0.1 + 2 * lr.1) - 2 * dotL tab.W0 Q
  | 1 => 2 * lam - 2 * dotL tab.W1 Q
  | 2 => -2 * dotL tab.W2 Q
  | 3 => -2 * dotL tab.W3 Q
  | 4 => -2 * dotL tab.W4 Q
  | _ => 0

def teB (lam : ℚ) (tab : TabB) (lr : ℚ × ℚ) : ℕ → ℚ
  | 0 => 2 * qabs lam * (tab.L0.2 + 2 * lr.2)
  | _ => 0

def yqB (yb ρ : ℚ) (j : ℕ) : ℚ :=
  yb / 2 ^ j * (if j % 2 = 0 then (ρ + ρ⁻¹) / 2 else (ρ - ρ⁻¹) / 2)

def cellUBB (des : DesB) (tab : TabB) (cell : CellB) : Option ℚ :=
  let Q := powAux des.ws.length 1 (cell.ρ⁻¹ ^ 2)
  let yc := yqB des.yb cell.ρ 0
  match logQ des.nA cell.ρ, V1Q des.nA des.α yc, logQ des.nA (yc ^ 2 + 1),
      logQ des.nA (yc ^ 2 + des.α ^ 2) with
  | some lr, some p1, some l1, some l2 =>
      let p0 := VyOf des.α yc p1 l1 l2
      some (cellUB des.α (tqB des.lam tab lr Q) (teB des.lam tab lr) (yqB des.yb cell.ρ)
        p0.1 p0.2 p1.1 p1.2 (2 * trSumB 0 1 cell.zB des.ws)
        (fun i => des.yb / 2 ^ i * (cell.ρ / (1 - cell.r / 2))) des.ρ1 des.ρa cell.r)
  | _, _, _, _ => none

/-- design-level conditions: the global pole distances (`y ≥ y_b` on region B) -/
def desOkB (des : DesB) : Bool :=
  decide (0 < des.α ∧ 0 < des.yb ∧ 0 < des.ρ1 ∧ 0 < des.ρa ∧ des.ρ1 ^ 2 ≤ des.yb ^ 2 + 1 ∧
    des.ρa ^ 2 ≤ des.yb ^ 2 + des.α ^ 2)

/-- **the cell check, region B** -/
def cellOkB (des : DesB) (tab : TabB) (cell : CellB) : Bool :=
  match cellUBB des tab cell with
  | none => false
  | some ub => decide (1 ≤ cell.ρ ∧ 0 < cell.r ∧ cell.r < 1 ∧ 0 < cell.zB ∧
      (cell.ρ⁻¹) ^ 2 ≤ cell.zB * (1 - cell.r) ∧ ub ≤ des.M0)

/-! ### soundness -/

/-- the real field of region B -/
def gB (c0 yb α : ℝ) (wt : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  2 * c0 * (Real.log (yb ^ 2 / 4) + x) -
    2 * ∑ k ∈ Finset.range N, wt k * Real.exp (-(((k + 1 : ℕ) : ℝ) * x)) -
    Vy α (yb * Real.cosh (x / 2))

theorem exp_neg_centre {ρ : ℝ} (hρ : 0 < ρ) : Real.exp (-(2 * Real.log ρ)) = (ρ⁻¹) ^ 2 := by
  have : 2 * Real.log ρ = Real.log (ρ ^ 2) := by rw [Real.log_pow]; norm_num
  rw [this, Real.exp_neg, Real.exp_log (by positivity), inv_pow]

theorem dotB_eq (ws : List ℚ) (wt : ℕ → ℝ) (hw : ∀ k < ws.length, wt k = ((ws.getD k 0 : ℚ) : ℝ))
    {ρ : ℚ} (hρ : 0 < ρ) (j : ℕ) :
    ((dotL (wTabB 0 j ws) (powAux ws.length 1 (ρ⁻¹ ^ 2)) : ℚ) : ℝ) =
      ∑ k ∈ Finset.range ws.length, wt k * (-((k + 1 : ℕ) : ℝ)) ^ j *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * (2 * Real.log (ρ : ℝ)))) := by
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hq : (((ρ⁻¹ ^ 2 : ℚ)) : ℝ) = Real.exp (-(2 * Real.log (ρ : ℝ))) := by
    rw [exp_neg_centre hρR]; push_cast; rfl
  have hlen : (wTabB 0 j ws).length = ws.length := wTabB_length 0 j ws
  have key := dotL_pow _ _ hq (wTabB 0 j ws) 1 1 (by simp)
  rw [hlen] at key
  rw [key]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [wTabB_getD j ws 0 k hk', hw k hk']
  have e : Real.exp (-(((k + 1 : ℕ) : ℝ) * (2 * Real.log (ρ : ℝ)))) =
      Real.exp (-(2 * Real.log (ρ : ℝ))) ^ (k + 1) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]
  push_cast
  ring

theorem TB_enc (des : DesB) (tab : TabB) (wt : ℕ → ℝ)
    (hw : ∀ k < des.ws.length, wt k = ((des.ws.getD k 0 : ℚ) : ℝ))
    (hW0 : tab.W0 = wTabB 0 0 des.ws) (hW1 : tab.W1 = wTabB 0 1 des.ws)
    (hW2 : tab.W2 = wTabB 0 2 des.ws) (hW3 : tab.W3 = wTabB 0 3 des.ws)
    (hW4 : tab.W4 = wTabB 0 4 des.ws)
    (hL : Enc (Real.log ((des.yb : ℝ) ^ 2 / 4)) tab.L0) {ρ : ℚ} (hρ : 0 < ρ) {lr : ℚ × ℚ}
    (hlr : Enc (Real.log (ρ : ℝ)) lr) :
    ∀ j ≤ 4, Enc (TB (2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4)) (des.lam : ℝ) wt
        des.ws.length j (2 * Real.log (ρ : ℝ)))
      (tqB des.lam tab lr (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) j, teB des.lam tab lr j) := by
  intro j hj
  have d := fun j => dotB_eq des.ws wt hw hρ j
  unfold Enc
  interval_cases j
  · have e1 : tqB des.lam tab lr (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) 0 =
        2 * des.lam * (tab.L0.1 + 2 * lr.1) -
          2 * dotL tab.W0 (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) := rfl
    have e2 : teB des.lam tab lr 0 = 2 * qabs des.lam * (tab.L0.2 + 2 * lr.2) := rfl
    rw [e1, e2, hW0]
    have hd := d 0
    unfold TB
    simp only [if_true]
    rw [show ∑ k ∈ Finset.range des.ws.length, wt k * (-((k + 1 : ℕ) : ℝ)) ^ 0 *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * (2 * Real.log (ρ : ℝ)))) =
        ((dotL (wTabB 0 0 des.ws) (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) : ℚ) : ℝ) from hd.symm]
    have hL' : |Real.log ((des.yb : ℝ) ^ 2 / 4) - (tab.L0.1 : ℝ)| ≤ (tab.L0.2 : ℝ) := hL
    have hr' : |Real.log (ρ : ℝ) - (lr.1 : ℝ)| ≤ (lr.2 : ℝ) := hlr
    have hq : ((qabs des.lam : ℚ) : ℝ) = |(des.lam : ℝ)| := by
      rw [CatalanMeasure.Cert.qabs_eq]; push_cast; rfl
    push_cast
    rw [hq]
    have e : 2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4) + 2 * (des.lam : ℝ) *
        (2 * Real.log (ρ : ℝ)) - 2 * ((dotL (wTabB 0 0 des.ws)
          (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) : ℚ) : ℝ) -
        (2 * (des.lam : ℝ) * ((tab.L0.1 : ℝ) + 2 * (lr.1 : ℝ)) -
          2 * ((dotL (wTabB 0 0 des.ws) (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) : ℚ) : ℝ)) =
        2 * (des.lam : ℝ) * ((Real.log ((des.yb : ℝ) ^ 2 / 4) - (tab.L0.1 : ℝ)) +
          2 * (Real.log (ρ : ℝ) - (lr.1 : ℝ))) := by ring
    rw [e, abs_mul, abs_mul, abs_two]
    have h2 : |(Real.log ((des.yb : ℝ) ^ 2 / 4) - (tab.L0.1 : ℝ)) +
        2 * (Real.log (ρ : ℝ) - (lr.1 : ℝ))| ≤ (tab.L0.2 : ℝ) + 2 * (lr.2 : ℝ) := by
      calc _ ≤ |Real.log ((des.yb : ℝ) ^ 2 / 4) - (tab.L0.1 : ℝ)| +
            |2 * (Real.log (ρ : ℝ) - (lr.1 : ℝ))| := abs_add_le _ _
        _ = |Real.log ((des.yb : ℝ) ^ 2 / 4) - (tab.L0.1 : ℝ)| +
            2 * |Real.log (ρ : ℝ) - (lr.1 : ℝ)| := by rw [abs_mul, abs_two]
        _ ≤ _ := by linarith
    calc 2 * |(des.lam : ℝ)| * |(Real.log ((des.yb : ℝ) ^ 2 / 4) - (tab.L0.1 : ℝ)) +
          2 * (Real.log (ρ : ℝ) - (lr.1 : ℝ))|
        ≤ 2 * |(des.lam : ℝ)| * ((tab.L0.2 : ℝ) + 2 * (lr.2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  · have e1 : tqB des.lam tab lr (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) 1 =
        2 * des.lam - 2 * dotL tab.W1 (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) := rfl
    have e2 : teB des.lam tab lr 1 = 0 := rfl
    rw [e1, e2, hW1]
    have hd := d 1
    unfold TB
    simp only [show (1 : ℕ) ≠ 0 by norm_num, if_true, if_false]
    rw [show ∑ k ∈ Finset.range des.ws.length, wt k * (-((k + 1 : ℕ) : ℝ)) ^ 1 *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * (2 * Real.log (ρ : ℝ)))) =
        ((dotL (wTabB 0 1 des.ws) (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) : ℚ) : ℝ) from hd.symm]
    simp
  · have e1 : tqB des.lam tab lr (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) 2 =
        -2 * dotL tab.W2 (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) := rfl
    have e2 : teB des.lam tab lr 2 = 0 := rfl
    rw [e1, e2, hW2]
    have hd := d 2
    unfold TB
    simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false]
    rw [show ∑ k ∈ Finset.range des.ws.length, wt k * (-((k + 1 : ℕ) : ℝ)) ^ 2 *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * (2 * Real.log (ρ : ℝ)))) =
        ((dotL (wTabB 0 2 des.ws) (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) : ℚ) : ℝ) from hd.symm]
    simp
  · have e1 : tqB des.lam tab lr (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) 3 =
        -2 * dotL tab.W3 (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) := rfl
    have e2 : teB des.lam tab lr 3 = 0 := rfl
    rw [e1, e2, hW3]
    have hd := d 3
    unfold TB
    simp only [show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, if_false]
    rw [show ∑ k ∈ Finset.range des.ws.length, wt k * (-((k + 1 : ℕ) : ℝ)) ^ 3 *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * (2 * Real.log (ρ : ℝ)))) =
        ((dotL (wTabB 0 3 des.ws) (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) : ℚ) : ℝ) from hd.symm]
    simp
  · have e1 : tqB des.lam tab lr (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) 4 =
        -2 * dotL tab.W4 (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) := rfl
    have e2 : teB des.lam tab lr 4 = 0 := rfl
    rw [e1, e2, hW4]
    have hd := d 4
    unfold TB
    simp only [show (4 : ℕ) ≠ 0 by norm_num, show (4 : ℕ) ≠ 1 by norm_num, if_false]
    rw [show ∑ k ∈ Finset.range des.ws.length, wt k * (-((k + 1 : ℕ) : ℝ)) ^ 4 *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * (2 * Real.log (ρ : ℝ)))) =
        ((dotL (wTabB 0 4 des.ws) (powAux des.ws.length 1 (ρ⁻¹ ^ 2)) : ℚ) : ℝ) from hd.symm]
    simp

theorem YB_centre (yb ρ : ℚ) (hρ : 0 < ρ) (j : ℕ) :
    YB (yb : ℝ) j (2 * Real.log (ρ : ℝ)) = ((yqB yb ρ j : ℚ) : ℝ) := by
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have e : 2 * Real.log (ρ : ℝ) / 2 = Real.log (ρ : ℝ) := by ring
  unfold YB yqB
  rw [e]
  by_cases hj : j % 2 = 0
  · simp only [hj, if_true]
    rw [Real.cosh_log hρR]; push_cast; ring
  · simp only [hj, if_false]
    rw [Real.sinh_log hρR]; push_cast; ring

theorem cellB_sound (des : DesB) (tab : TabB) (cell : CellB) (wt : ℕ → ℝ)
    (hdes : desOkB des = true)
    (hw : ∀ k < des.ws.length, wt k = ((des.ws.getD k 0 : ℚ) : ℝ))
    (hW0 : tab.W0 = wTabB 0 0 des.ws) (hW1 : tab.W1 = wTabB 0 1 des.ws)
    (hW2 : tab.W2 = wTabB 0 2 des.ws) (hW3 : tab.W3 = wTabB 0 3 des.ws)
    (hW4 : tab.W4 = wTabB 0 4 des.ws)
    (hL : Enc (Real.log ((des.yb : ℝ) ^ 2 / 4)) tab.L0)
    (h : cellOkB des tab cell = true) :
    ∀ x ∈ Icc (2 * Real.log (cell.ρ : ℝ) - (cell.r : ℝ)) (2 * Real.log (cell.ρ : ℝ) + (cell.r : ℝ)),
      gB (des.lam : ℝ) (des.yb : ℝ) (des.α : ℝ) wt des.ws.length x ≤ (des.M0 : ℝ) := by
  intro x hx
  simp only [desOkB, decide_eq_true_eq] at hdes
  obtain ⟨hα, hyb, hρ1, hρa, hs1, hsa⟩ := hdes
  unfold cellOkB at h
  cases hub : cellUBB des tab cell with
  | none => simp [hub] at h
  | some ub =>
    rw [hub] at h
    simp only [decide_eq_true_eq] at h
    obtain ⟨hρge, hr, hr1, hzB, hzq, hle⟩ := h
    unfold cellUBB at hub
    dsimp only at hub
    split at hub
    · rename_i lr p1 l1 l2 e0 e1 e2 e3
      simp only [Option.some.injEq] at hub
      subst hub
      have hρpos : 0 < cell.ρ := by linarith
      have hρR : (1 : ℝ) ≤ (cell.ρ : ℝ) := by exact_mod_cast hρge
      have hρR0 : (0 : ℝ) < (cell.ρ : ℝ) := by linarith
      have hybR : (0 : ℝ) < (des.yb : ℝ) := by exact_mod_cast hyb
      have hrR : (cell.r : ℝ) < 1 := by exact_mod_cast hr1
      have hr0 : (0 : ℝ) < (cell.r : ℝ) := by exact_mod_cast hr
      have hlr := (logQ_spec e0).2
      have hY0 : YB (des.yb : ℝ) 0 (2 * Real.log (cell.ρ : ℝ)) =
          ((yqB des.yb cell.ρ 0 : ℚ) : ℝ) := YB_centre des.yb cell.ρ hρpos 0
      have eV1 := V1Q_spec hα e1
      have eL1 := (logQ_spec e2).2
      have eL2 := (logQ_spec e3).2
      have hD0 : Enc (Vy (des.α : ℝ) (YB (des.yb : ℝ) 0 (2 * Real.log (cell.ρ : ℝ))))
          (VyOf des.α (yqB des.yb cell.ρ 0) p1 l1 l2) := by
        rw [hY0]; exact VyOf_spec eV1 eL1 eL2
      have hD1 : Enc (V1 (des.α : ℝ) (YB (des.yb : ℝ) 0 (2 * Real.log (cell.ρ : ℝ)))) p1 := by
        rw [hY0]; exact eV1
      have hc0 : (0 : ℝ) ≤ 2 * Real.log (cell.ρ : ℝ) := by
        have := Real.log_nonneg hρR; linarith
      have key := cell_sound (α := des.α) hα
        (T := TB (2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4)) (des.lam : ℝ) wt
          des.ws.length)
        (Y := YB (des.yb : ℝ)) (c := 2 * Real.log (cell.ρ : ℝ)) (r := (cell.r : ℝ))
        (isTower_TB _ _ _ _ _ _) (fun i _ x => hasDerivAt_YB _ i x)
        (fun i _ => continuous_YB _ i) (rq := cell.r) (TR := 2 * trSumB 0 1 cell.zB des.ws)
        (Ym := fun i => des.yb / 2 ^ i * (cell.ρ / (1 - cell.r / 2))) rfl
        (TB_enc des tab wt hw hW0 hW1 hW2 hW3 hW4 hL hρpos hlr)
        (fun j _ => YB_centre des.yb cell.ρ hρpos j)
        hD0 hD1
        (fun y hy => by
          have hz : Real.exp (-y) ≤ (cell.zB : ℝ) := by
            have h1 : -y ≤ -(2 * Real.log (cell.ρ : ℝ)) + (cell.r : ℝ) := by linarith [hy.1]
            have h2 : Real.exp (-y) ≤
                Real.exp (-(2 * Real.log (cell.ρ : ℝ))) * Real.exp (cell.r : ℝ) := by
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
            rw [exp_neg_centre hρR0] at h2
            have h3 : 1 - (cell.r : ℝ) ≤ Real.exp (-(cell.r : ℝ)) := by
              have := Real.add_one_le_exp (-(cell.r : ℝ)); linarith
            have h4 : Real.exp (cell.r : ℝ) * Real.exp (-(cell.r : ℝ)) = 1 := by
              rw [← Real.exp_add]; simp
            have h5 : ((cell.ρ : ℝ)⁻¹) ^ 2 ≤ (cell.zB : ℝ) * (1 - (cell.r : ℝ)) := by
              exact_mod_cast hzq
            have h6 : Real.exp (cell.r : ℝ) * (1 - (cell.r : ℝ)) ≤ 1 := by
              calc Real.exp (cell.r : ℝ) * (1 - (cell.r : ℝ))
                  ≤ Real.exp (cell.r : ℝ) * Real.exp (-(cell.r : ℝ)) :=
                    mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
                _ = 1 := h4
            have hzR : (0 : ℝ) < (cell.zB : ℝ) := by exact_mod_cast hzB
            calc Real.exp (-y) ≤ ((cell.ρ : ℝ)⁻¹) ^ 2 * Real.exp (cell.r : ℝ) := h2
              _ ≤ ((cell.zB : ℝ) * (1 - (cell.r : ℝ))) * Real.exp (cell.r : ℝ) :=
                  mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
              _ = (cell.zB : ℝ) * (Real.exp (cell.r : ℝ) * (1 - (cell.r : ℝ))) := by ring
              _ ≤ (cell.zB : ℝ) * 1 := mul_le_mul_of_nonneg_left h6 hzR.le
              _ = _ := mul_one _
          have := abs_TB5_le (2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4)) (des.lam : ℝ) wt
            des.ws.length hz
          have hcast : ((2 * trSumB 0 1 cell.zB des.ws : ℚ) : ℝ) =
              2 * ∑ k ∈ Finset.range des.ws.length,
                |wt k| * ((k + 1 : ℕ) : ℝ) ^ 5 * (cell.zB : ℝ) ^ (k + 1) := by
            push_cast
            rw [trSumB_cast]
            congr 1
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [hw k (Finset.mem_range.mp hk)]
            push_cast; ring
          rw [hcast]
          exact this)
        (fun y hy i _ _ => by
          have hb := abs_YB_le hybR.le i y
          refine hb.trans ?_
          have hy' : |y| ≤ 2 * Real.log (cell.ρ : ℝ) + (cell.r : ℝ) := by
            rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
          have h1 : Real.exp (|y| / 2) ≤ Real.exp (Real.log (cell.ρ : ℝ) + (cell.r : ℝ) / 2) :=
            Real.exp_le_exp.mpr (by linarith)
          rw [Real.exp_add, Real.exp_log hρR0] at h1
          have h3 : 1 - (cell.r : ℝ) / 2 ≤ Real.exp (-((cell.r : ℝ) / 2)) := by
            have := Real.add_one_le_exp (-((cell.r : ℝ) / 2)); linarith
          have h4 : Real.exp ((cell.r : ℝ) / 2) * Real.exp (-((cell.r : ℝ) / 2)) = 1 := by
            rw [← Real.exp_add]; simp
          have hpos : (0 : ℝ) < 1 - (cell.r : ℝ) / 2 := by linarith
          have h6 : Real.exp ((cell.r : ℝ) / 2) ≤ 1 / (1 - (cell.r : ℝ) / 2) := by
            rw [le_div_iff₀ hpos]
            calc Real.exp ((cell.r : ℝ) / 2) * (1 - (cell.r : ℝ) / 2)
                ≤ Real.exp ((cell.r : ℝ) / 2) * Real.exp (-((cell.r : ℝ) / 2)) :=
                  mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
              _ = 1 := h4
          have h7 : Real.exp (|y| / 2) ≤ (cell.ρ : ℝ) / (1 - (cell.r : ℝ) / 2) := by
            calc Real.exp (|y| / 2) ≤ (cell.ρ : ℝ) * Real.exp ((cell.r : ℝ) / 2) := h1
              _ ≤ (cell.ρ : ℝ) * (1 / (1 - (cell.r : ℝ) / 2)) :=
                  mul_le_mul_of_nonneg_left h6 hρR0.le
              _ = _ := by ring
          push_cast
          exact mul_le_mul_of_nonneg_left h7 (by positivity))
        hρ1 hρa
        (fun y hy => by
          have hY : YB (des.yb : ℝ) 0 y = (des.yb : ℝ) * Real.cosh (y / 2) := by simp [YB]
          have hch : 1 ≤ Real.cosh (y / 2) := Real.one_le_cosh _
          have hge : (des.yb : ℝ) ≤ (des.yb : ℝ) * Real.cosh (y / 2) := by nlinarith
          have hsq : (des.yb : ℝ) ^ 2 ≤ (YB (des.yb : ℝ) 0 y) ^ 2 := by
            rw [hY]; nlinarith
          have e1' : ((des.ρ1 : ℚ) : ℝ) ^ 2 ≤ (des.yb : ℝ) ^ 2 + 1 := by exact_mod_cast hs1
          have e2' : ((des.ρa : ℚ) : ℝ) ^ 2 ≤ (des.yb : ℝ) ^ 2 + (des.α : ℝ) ^ 2 := by
            exact_mod_cast hsa
          exact ⟨by linarith, by linarith⟩) x hx
      have hle' := (Rat.cast_le (K := ℝ)).mpr hle
      have e : gB (des.lam : ℝ) (des.yb : ℝ) (des.α : ℝ) wt des.ws.length x =
          TB (2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4)) (des.lam : ℝ) wt
            des.ws.length 0 x - Vy (des.α : ℝ) (YB (des.yb : ℝ) 0 x) := by
        simp only [gB, TB, YB]
        simp
        ring
      rw [e]
      exact key.trans hle'
    · simp at hub

end

end CatalanCore.Zeta5.Cells
