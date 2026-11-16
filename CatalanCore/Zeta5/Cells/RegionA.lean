module

public import CatalanCore.Zeta5.Cells.TrigA

@[expose] public section

/-!
# Z5-CELLS, part 6: the region-A cell checker and its soundness (ZD17, ZD19–ZD21)

Region A is `t = b cos²φ`, `y = y_b cos φ`, `y_b² = b`.  A cell is `(m, r, ρ₁, ρ_α)`:
the centre is `φ_c = 2 arctan m` (`m` rational), so `cos φ_c = u = (1−m²)/(1+m²)` and
`sin φ_c = v = 2m/(1+m²)` are exact rationals; the radius is `r`; `ρ₁, ρ_α` are rational lower
bounds of `√(y²+1)`, `√(y²+α²)` on the cell.

`cellOkA des tab cell` is the Boolean check: compute the rotation list (exact `cos 2κφ_c`,
`sin 2κφ_c`), the moments against the shared weight tables, the enclosures of `V` and `V1`
at `y_c = y_b u` (ZD21: `V1Q`, `logQ`), the rational bound `cellUB` (ZD19/ZD20) and test
`cellUB ≤ M₀` together with the side conditions.  `cellA_sound` is the one parametric
soundness theorem: the check implies `g_A ≤ M₀` on `[φ_c − r, φ_c + r]`.
-/

namespace CatalanCore.Zeta5.Cells

open Set Real CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.Cert (qabs)

noncomputable section

/-! ### the rational point on the circle -/

def uOf (m : ℚ) : ℚ := (1 - m ^ 2) / (1 + m ^ 2)
def vOf (m : ℚ) : ℚ := 2 * m / (1 + m ^ 2)

theorem cos_two_arctan (m : ℝ) : Real.cos (2 * Real.arctan m) = (1 - m ^ 2) / (1 + m ^ 2) := by
  have hs : (0 : ℝ) < 1 + m ^ 2 := by positivity
  rw [Real.cos_two_mul, Real.cos_arctan, div_pow, Real.sq_sqrt hs.le]
  field_simp
  ring

theorem sin_two_arctan (m : ℝ) : Real.sin (2 * Real.arctan m) = 2 * m / (1 + m ^ 2) := by
  have hs : (0 : ℝ) < 1 + m ^ 2 := by positivity
  have h2 : (√(1 + m ^ 2)) ^ 2 = 1 + m ^ 2 := Real.sq_sqrt hs.le
  have h3 : 0 < √(1 + m ^ 2) := Real.sqrt_pos.mpr hs
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp
  rw [h2]

theorem cos_centre (m : ℚ) : Real.cos (2 * Real.arctan (m : ℝ)) = ((uOf m : ℚ) : ℝ) := by
  rw [cos_two_arctan]; simp [uOf]

theorem sin_centre (m : ℚ) : Real.sin (2 * Real.arctan (m : ℝ)) = ((vOf m : ℚ) : ℝ) := by
  rw [sin_two_arctan]; simp [vOf]

/-! ### the change of variable `y = y_b cos φ` -/

def YA (yb : ℝ) (j : ℕ) (φ : ℝ) : ℝ := yb * Real.cos (φ + (j : ℝ) * (π / 2))

theorem hasDerivAt_YA (yb : ℝ) (j : ℕ) (φ : ℝ) : HasDerivAt (YA yb j) (YA yb (j + 1) φ) φ := by
  have h1 : HasDerivAt (fun φ => φ + (j : ℝ) * (π / 2)) 1 φ := by
    simpa using (hasDerivAt_id' φ).add_const ((j : ℝ) * (π / 2))
  have h2 := h1.cos.const_mul yb
  refine h2.congr_deriv ?_
  have : Real.cos (φ + ((j + 1 : ℕ) : ℝ) * (π / 2)) = - Real.sin (φ + (j : ℝ) * (π / 2)) := by
    rw [← Real.cos_add_pi_div_two]; congr 1; push_cast; ring
  unfold YA
  rw [this]; ring

theorem continuous_YA (yb : ℝ) (j : ℕ) : Continuous (YA yb j) := by
  unfold YA; fun_prop

theorem abs_YA_le {yb : ℝ} (hyb : 0 ≤ yb) (j : ℕ) (φ : ℝ) : |YA yb j φ| ≤ yb := by
  unfold YA
  rw [abs_mul, abs_of_nonneg hyb]
  calc yb * |Real.cos (φ + (j : ℝ) * (π / 2))| ≤ yb * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hyb
    _ = yb := mul_one _

/-- the values `Y j (φ_c) = y_b cos(φ_c + jπ/2)` for `j ≤ 5` from `cos φ_c`, `sin φ_c`. -/
def yqA (yb u v : ℚ) (j : ℕ) : ℚ :=
  yb * (if j % 4 = 0 then u else if j % 4 = 1 then -v else if j % 4 = 2 then -u else v)

theorem YA_centre (yb : ℚ) (u v : ℚ) {φ : ℝ} (hu : Real.cos φ = (u : ℝ)) (hv : Real.sin φ = (v : ℝ))
    (j : ℕ) (hj : j ≤ 5) : YA (yb : ℝ) j φ = ((yqA yb u v j : ℚ) : ℝ) := by
  have e5 : Real.cos (φ + ((5 : ℕ) : ℝ) * (π / 2)) = - Real.sin φ := by
    have : φ + ((5 : ℕ) : ℝ) * (π / 2) = (φ + π / 2) + 2 * π := by push_cast; ring
    rw [this, Real.cos_add_two_pi, Real.cos_add_pi_div_two]
  obtain ⟨c0, c1, c2, c3, c4⟩ := cos_add_quarter φ
  unfold YA yqA
  interval_cases j <;> simp_all [c0, c1, c2, c3, c4, e5]

/-! ### the traces and tables -/

/-- `Σ |w_k| (2κ)^5` (the order-5 remainder of the trigonometric part), structural. -/
def trSum : ℕ → List ℚ → ℚ
  | _, [] => 0
  | k, w :: ws => qabs w * (2 * ((k + 1 : ℕ) : ℚ)) ^ 5 + trSum (k + 1) ws

def trA (ws : List ℚ) : ℚ := 2 * trSum 0 ws

theorem trSum_cast (ws : List ℚ) : ∀ k₀ : ℕ, ((trSum k₀ ws : ℚ) : ℝ) =
    ∑ k ∈ Finset.range ws.length, |((ws.getD k 0 : ℚ) : ℝ)| *
      (2 * ((k₀ + k + 1 : ℕ) : ℝ)) ^ 5 := by
  induction ws with
  | nil => intro k₀; simp [trSum]
  | cons w ws ih =>
    intro k₀
    rw [trSum, List.length_cons, Finset.sum_range_succ']
    push_cast
    rw [ih (k₀ + 1)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    · have : ((qabs w : ℚ) : ℝ) = |(w : ℝ)| := by
        rw [CatalanMeasure.Cert.qabs_eq]; push_cast; rfl
      rw [this]

structure DesA where
  α : ℚ
  yb : ℚ
  lam : ℚ
  ws : List ℚ
  M0 : ℚ
  nA : ℕ

structure TabA where
  W0 : List ℚ
  W1 : List ℚ
  W2 : List ℚ
  W3 : List ℚ
  W4 : List ℚ
  TR : ℚ
  L0 : ℚ × ℚ

structure CellA where
  m : ℚ
  r : ℚ
  ρ1 : ℚ
  ρa : ℚ

/-- the point values `tq j` of the trigonometric tower at the centre (`j ≤ 4`) -/
def tqA (lam : ℚ) (tab : TabA) (rots : List (ℚ × ℚ)) : ℕ → ℚ
  | 0 => 2 * lam * tab.L0.1 - 2 * dotC tab.W0 rots
  | 1 => 2 * dotS tab.W1 rots
  | 2 => 2 * dotC tab.W2 rots
  | 3 => -2 * dotS tab.W3 rots
  | 4 => -2 * dotC tab.W4 rots
  | _ => 0

def teA (lam : ℚ) (tab : TabA) : ℕ → ℚ
  | 0 => 2 * qabs lam * tab.L0.2
  | _ => 0

/-- the rational bound of one cell, `none` when an enclosure tool fails -/
def cellUBA (des : DesA) (tab : TabA) (cell : CellA) : Option ℚ :=
  let u := uOf cell.m
  let v := vOf cell.m
  let rots := rotAux des.ws.length 1 0 (u ^ 2 - v ^ 2) (2 * u * v)
  let yc := des.yb * u
  match V1Q des.nA des.α yc, logQ des.nA (yc ^ 2 + 1), logQ des.nA (yc ^ 2 + des.α ^ 2) with
  | some p1, some l1, some l2 =>
      let p0 := VyOf des.α yc p1 l1 l2
      some (cellUB des.α (tqA des.lam tab rots) (teA des.lam tab) (yqA des.yb u v)
        p0.1 p0.2 p1.1 p1.2 tab.TR (fun _ => des.yb) cell.ρ1 cell.ρa cell.r)
  | _, _, _ => none

/-- the lower bound of `|y|` on the cell -/
def yloA (des : DesA) (cell : CellA) : ℚ :=
  if 0 ≤ des.yb * uOf cell.m - des.yb * cell.r then des.yb * uOf cell.m - des.yb * cell.r else 0

/-- **the cell check** -/
def cellOkA (des : DesA) (tab : TabA) (cell : CellA) : Bool :=
  match cellUBA des tab cell with
  | none => false
  | some ub => decide (0 < cell.r ∧ 0 < cell.ρ1 ∧ 0 < cell.ρa ∧
      cell.ρ1 ^ 2 ≤ yloA des cell ^ 2 + 1 ∧ cell.ρa ^ 2 ≤ yloA des cell ^ 2 + des.α ^ 2 ∧
      ub ≤ des.M0)

/-! ### soundness -/

/-- the real field of region A: `g_A(φ) = 2 c₀ log(y_b²/4) − 2 Σ w_k cos(2κφ) − V(y_b cos φ)`. -/
def gA (c0 yb α : ℝ) (w : ℕ → ℝ) (N : ℕ) (φ : ℝ) : ℝ :=
  2 * c0 * Real.log (yb ^ 2 / 4) -
    2 * ∑ k ∈ Finset.range N, w k * Real.cos (2 * ((k + 1 : ℕ) : ℝ) * φ) - Vy α (yb * Real.cos φ)

theorem dots_eq (ws : List ℚ) (w : ℕ → ℝ) (hw : ∀ k < ws.length, w k = ((ws.getD k 0 : ℚ) : ℝ))
    (m : ℚ) (j : ℕ) :
    ((dotC (wTabAux 0 j ws) (rotAux ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2) (2 * uOf m * vOf m)) : ℚ) : ℝ)
      = ∑ k ∈ Finset.range ws.length, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ j *
          Real.cos (2 * ((k + 1 : ℕ) : ℝ) * (2 * Real.arctan (m : ℝ))) ∧
    ((dotS (wTabAux 0 j ws) (rotAux ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2) (2 * uOf m * vOf m)) : ℚ) : ℝ)
      = ∑ k ∈ Finset.range ws.length, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ j *
          Real.sin (2 * ((k + 1 : ℕ) : ℝ) * (2 * Real.arctan (m : ℝ))) := by
  have hu := cos_centre m
  have hv := sin_centre m
  have hcw : (((uOf m ^ 2 - vOf m ^ 2 : ℚ)) : ℝ) = Real.cos (2 * (2 * Real.arctan (m : ℝ))) := by
    rw [Real.cos_two_mul, Rat.cast_sub, Rat.cast_pow, Rat.cast_pow, ← hu, ← hv]
    have := Real.sin_sq_add_cos_sq (2 * Real.arctan (m : ℝ))
    nlinarith
  have hsw : (((2 * uOf m * vOf m : ℚ)) : ℝ) = Real.sin (2 * (2 * Real.arctan (m : ℝ))) := by
    rw [Real.sin_two_mul]; push_cast; rw [← hu, ← hv]; ring
  have hlen : (wTabAux 0 j ws).length = ws.length := wTabAux_length 0 j ws
  have key := dot_rot (2 * (2 * Real.arctan (m : ℝ))) _ _ hcw hsw (wTabAux 0 j ws) 1 0 0
    (by simp) (by simp)
  rw [hlen] at key
  have hsumeq : ∀ f : ℝ → ℝ, ∑ k ∈ Finset.range ws.length,
      (((wTabAux 0 j ws).getD k 0 : ℚ) : ℝ) * f (0 + ((k + 1 : ℕ) : ℝ) * (2 * (2 * Real.arctan (m : ℝ)))) =
      ∑ k ∈ Finset.range ws.length, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ j *
        f (2 * ((k + 1 : ℕ) : ℝ) * (2 * Real.arctan (m : ℝ))) := by
    intro f
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have e : (0 : ℝ) + ((k + 1 : ℕ) : ℝ) * (2 * (2 * Real.arctan (m : ℝ))) =
        2 * ((k + 1 : ℕ) : ℝ) * (2 * Real.arctan (m : ℝ)) := by ring
    rw [wTabAux_getD j ws 0 k hk', hw k hk', e]
    push_cast
    ring
  exact ⟨by rw [key.1]; exact hsumeq Real.cos, by rw [key.2]; exact hsumeq Real.sin⟩

/-- the five point values of the trigonometric tower at any centre `c`, by the quarter-turn
phases -/
theorem TA_phases (K0 : ℝ) (w : ℕ → ℝ) (N : ℕ) (c : ℝ) :
    TA K0 w N 0 c = K0 - 2 * ∑ k ∈ Finset.range N, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 0 *
      Real.cos (2 * ((k + 1 : ℕ) : ℝ) * c) ∧
    TA K0 w N 1 c = 2 * ∑ k ∈ Finset.range N, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 1 *
      Real.sin (2 * ((k + 1 : ℕ) : ℝ) * c) ∧
    TA K0 w N 2 c = 2 * ∑ k ∈ Finset.range N, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 2 *
      Real.cos (2 * ((k + 1 : ℕ) : ℝ) * c) ∧
    TA K0 w N 3 c = -2 * ∑ k ∈ Finset.range N, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 3 *
      Real.sin (2 * ((k + 1 : ℕ) : ℝ) * c) ∧
    TA K0 w N 4 c = -2 * ∑ k ∈ Finset.range N, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 4 *
      Real.cos (2 * ((k + 1 : ℕ) : ℝ) * c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold TA
    simp only [if_true]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(cos_add_quarter _).1]
  · unfold TA
    have : ∀ k ∈ Finset.range N, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 1 *
        Real.cos (2 * ((k + 1 : ℕ) : ℝ) * c + ((1 : ℕ) : ℝ) * (π / 2)) =
        -(w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 1 * Real.sin (2 * ((k + 1 : ℕ) : ℝ) * c)) := by
      intro k _; rw [(cos_add_quarter _).2.1]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
    simp
  · unfold TA
    have : ∀ k ∈ Finset.range N, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 2 *
        Real.cos (2 * ((k + 1 : ℕ) : ℝ) * c + ((2 : ℕ) : ℝ) * (π / 2)) =
        -(w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 2 * Real.cos (2 * ((k + 1 : ℕ) : ℝ) * c)) := by
      intro k _; rw [(cos_add_quarter _).2.2.1]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
    simp
  · unfold TA
    have : ∀ k ∈ Finset.range N, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 3 *
        Real.cos (2 * ((k + 1 : ℕ) : ℝ) * c + ((3 : ℕ) : ℝ) * (π / 2)) =
        (w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 3 * Real.sin (2 * ((k + 1 : ℕ) : ℝ) * c)) := by
      intro k _; rw [(cos_add_quarter _).2.2.2.1]
    rw [Finset.sum_congr rfl this]
    simp
  · unfold TA
    have : ∀ k ∈ Finset.range N, w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 4 *
        Real.cos (2 * ((k + 1 : ℕ) : ℝ) * c + ((4 : ℕ) : ℝ) * (π / 2)) =
        (w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ 4 * Real.cos (2 * ((k + 1 : ℕ) : ℝ) * c)) := by
      intro k _; rw [(cos_add_quarter _).2.2.2.2]
    rw [Finset.sum_congr rfl this]
    simp

theorem TA_enc (des : DesA) (tab : TabA) (w : ℕ → ℝ)
    (hw : ∀ k < des.ws.length, w k = ((des.ws.getD k 0 : ℚ) : ℝ))
    (hW0 : tab.W0 = wTabAux 0 0 des.ws) (hW1 : tab.W1 = wTabAux 0 1 des.ws)
    (hW2 : tab.W2 = wTabAux 0 2 des.ws) (hW3 : tab.W3 = wTabAux 0 3 des.ws)
    (hW4 : tab.W4 = wTabAux 0 4 des.ws)
    (hL : Enc (Real.log ((des.yb : ℝ) ^ 2 / 4)) tab.L0) (m : ℚ) :
    ∀ j ≤ 4, Enc (TA (2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4)) w des.ws.length j
        (2 * Real.arctan (m : ℝ)))
      (tqA des.lam tab (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2) (2 * uOf m * vOf m)) j,
       teA des.lam tab j) := by
  intro j hj
  obtain ⟨p0, p1, p2, p3, p4⟩ := TA_phases (2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4)) w
    des.ws.length (2 * Real.arctan (m : ℝ))
  have d := fun j => dots_eq des.ws w hw m j
  unfold Enc
  interval_cases j
  · rw [p0, tqA, teA, hW0, ← (d 0).1]
    simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
    have := hL
    unfold Enc at this
    have e : 2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4) -
        2 * ((dotC (wTabAux 0 0 des.ws) (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
          (2 * uOf m * vOf m)) : ℚ) : ℝ) -
        (2 * (des.lam : ℝ) * (tab.L0.1 : ℝ) - 2 * ((dotC (wTabAux 0 0 des.ws) (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
          (2 * uOf m * vOf m)) : ℚ) : ℝ)) =
        2 * (des.lam : ℝ) * (Real.log ((des.yb : ℝ) ^ 2 / 4) - (tab.L0.1 : ℝ)) := by ring
    rw [e, abs_mul, abs_mul, abs_two]
    have hq : ((qabs des.lam : ℚ) : ℝ) = |(des.lam : ℝ)| := by
      rw [CatalanMeasure.Cert.qabs_eq]; push_cast; rfl
    push_cast
    rw [hq]
    calc 2 * |(des.lam : ℝ)| * |Real.log ((des.yb : ℝ) ^ 2 / 4) - (tab.L0.1 : ℝ)|
        ≤ 2 * |(des.lam : ℝ)| * (tab.L0.2 : ℝ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  · have e1 : tqA des.lam tab (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
        (2 * uOf m * vOf m)) 1 = 2 * dotS tab.W1 (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
        (2 * uOf m * vOf m)) := rfl
    have e2 : teA des.lam tab 1 = 0 := rfl
    rw [p1, e1, e2, hW1, ← (d 1).2]
    simp
  · have e1 : tqA des.lam tab (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
        (2 * uOf m * vOf m)) 2 = 2 * dotC tab.W2 (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
        (2 * uOf m * vOf m)) := rfl
    have e2 : teA des.lam tab 2 = 0 := rfl
    rw [p2, e1, e2, hW2, ← (d 2).1]
    simp
  · have e1 : tqA des.lam tab (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
        (2 * uOf m * vOf m)) 3 = -2 * dotS tab.W3 (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
        (2 * uOf m * vOf m)) := rfl
    have e2 : teA des.lam tab 3 = 0 := rfl
    rw [p3, e1, e2, hW3, ← (d 3).2]
    simp
  · have e1 : tqA des.lam tab (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
        (2 * uOf m * vOf m)) 4 = -2 * dotC tab.W4 (rotAux des.ws.length 1 0 (uOf m ^ 2 - vOf m ^ 2)
        (2 * uOf m * vOf m)) := rfl
    have e2 : teA des.lam tab 4 = 0 := rfl
    rw [p4, e1, e2, hW4, ← (d 4).1]
    simp

theorem abs_cos_sub_cos_le (x c : ℝ) : |Real.cos x - Real.cos c| ≤ |x - c| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_two]
  have h1 := Real.abs_sin_le_one ((x + c) / 2)
  have h2 : |Real.sin ((x - c) / 2)| ≤ |x - c| / 2 := by
    have := Real.abs_sin_le_abs (x := (x - c) / 2)
    rwa [abs_div, abs_two] at this
  calc 2 * |Real.sin ((x + c) / 2)| * |Real.sin ((x - c) / 2)|
      ≤ 2 * 1 * (|x - c| / 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (abs_nonneg _)
          (by norm_num)
    _ = |x - c| := by ring

theorem TR_cast (ws : List ℚ) (w : ℕ → ℝ) (hw : ∀ k < ws.length, w k = ((ws.getD k 0 : ℚ) : ℝ)) :
    ((trA ws : ℚ) : ℝ) = 2 * ∑ k ∈ Finset.range ws.length, |w k| * (2 * ((k + 1 : ℕ) : ℝ)) ^ 5 := by
  unfold trA
  push_cast
  rw [trSum_cast]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hw k (Finset.mem_range.mp hk)]
  simp

theorem cellA_sound (des : DesA) (tab : TabA) (cell : CellA) (w : ℕ → ℝ)
    (hα : 0 < des.α) (hyb : 0 < des.yb)
    (hw : ∀ k < des.ws.length, w k = ((des.ws.getD k 0 : ℚ) : ℝ))
    (hW0 : tab.W0 = wTabAux 0 0 des.ws) (hW1 : tab.W1 = wTabAux 0 1 des.ws)
    (hW2 : tab.W2 = wTabAux 0 2 des.ws) (hW3 : tab.W3 = wTabAux 0 3 des.ws)
    (hW4 : tab.W4 = wTabAux 0 4 des.ws) (hTR : tab.TR = trA des.ws)
    (hL : Enc (Real.log ((des.yb : ℝ) ^ 2 / 4)) tab.L0)
    (h : cellOkA des tab cell = true) :
    ∀ φ ∈ Icc (2 * Real.arctan (cell.m : ℝ) - (cell.r : ℝ))
        (2 * Real.arctan (cell.m : ℝ) + (cell.r : ℝ)),
      gA (des.lam : ℝ) (des.yb : ℝ) (des.α : ℝ) w des.ws.length φ ≤ (des.M0 : ℝ) := by
  intro φ hφ
  unfold cellOkA at h
  cases hub : cellUBA des tab cell with
  | none => simp [hub] at h
  | some ub =>
    rw [hub] at h
    simp only [decide_eq_true_eq] at h
    obtain ⟨hr, hρ1, hρa, hs1, hsa, hle⟩ := h
    unfold cellUBA at hub
    dsimp only at hub
    split at hub
    · rename_i p1 l1 l2 e1 e2 e3
      simp only [Option.some.injEq] at hub
      subst hub
      have hcu : Real.cos (2 * Real.arctan (cell.m : ℝ)) = ((uOf cell.m : ℚ) : ℝ) :=
        cos_centre cell.m
      have hsv : Real.sin (2 * Real.arctan (cell.m : ℝ)) = ((vOf cell.m : ℚ) : ℝ) :=
        sin_centre cell.m
      have hybR : (0 : ℝ) < (des.yb : ℝ) := by exact_mod_cast hyb
      have hY0 : YA (des.yb : ℝ) 0 (2 * Real.arctan (cell.m : ℝ)) =
          ((des.yb * uOf cell.m : ℚ) : ℝ) := by
        rw [YA_centre des.yb (uOf cell.m) (vOf cell.m) hcu hsv 0 (by norm_num)]; simp [yqA]
      have eV1 := V1Q_spec hα e1
      have eL1 := (logQ_spec e2).2
      have eL2 := (logQ_spec e3).2
      have hD0 : Enc (Vy (des.α : ℝ) (YA (des.yb : ℝ) 0 (2 * Real.arctan (cell.m : ℝ))))
          (VyOf des.α (des.yb * uOf cell.m) p1 l1 l2) := by
        rw [hY0]; exact VyOf_spec eV1 eL1 eL2
      have hD1 : Enc (V1 (des.α : ℝ) (YA (des.yb : ℝ) 0 (2 * Real.arctan (cell.m : ℝ)))) p1 := by
        rw [hY0]; exact eV1
      have hxr : ∀ x ∈ Icc (2 * Real.arctan (cell.m : ℝ) - (cell.r : ℝ))
          (2 * Real.arctan (cell.m : ℝ) + (cell.r : ℝ)),
          |x - 2 * Real.arctan (cell.m : ℝ)| ≤ (cell.r : ℝ) := fun x hx =>
        abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have key := cell_sound (α := des.α) hα
        (T := TA (2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4)) w des.ws.length)
        (Y := YA (des.yb : ℝ)) (c := 2 * Real.arctan (cell.m : ℝ)) (r := (cell.r : ℝ))
        (isTower_TA _ _ _ _ _) (fun i _ x => hasDerivAt_YA _ i x) (fun i _ => continuous_YA _ i)
        (rq := cell.r) (TR := tab.TR) rfl
        (TA_enc des tab w hw hW0 hW1 hW2 hW3 hW4 hL cell.m)
        (fun j hj => YA_centre des.yb (uOf cell.m) (vOf cell.m) hcu hsv j hj)
        hD0 hD1
        (fun x _ => by
          have := abs_TA5_le (2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4)) w
            des.ws.length x
          rw [hTR, TR_cast des.ws w hw]
          exact this)
        (fun x _ i _ _ => abs_YA_le hybR.le i x)
        hρ1 hρa
        (fun x hx => by
          have hc := abs_cos_sub_cos_le x (2 * Real.arctan (cell.m : ℝ))
          have hcx : |Real.cos x - ((uOf cell.m : ℚ) : ℝ)| ≤ (cell.r : ℝ) := by
            rw [← hcu]; exact hc.trans (hxr x hx)
          have hlo : ((yloA des cell : ℚ) : ℝ) ^ 2 ≤ (YA (des.yb : ℝ) 0 x) ^ 2 := by
            have hY : YA (des.yb : ℝ) 0 x = (des.yb : ℝ) * Real.cos x := by simp [YA]
            rw [hY]
            unfold yloA
            split_ifs with hcond
            · have hge : (des.yb : ℝ) * ((uOf cell.m : ℚ) : ℝ) - (des.yb : ℝ) * (cell.r : ℝ) ≤
                  (des.yb : ℝ) * Real.cos x := by
                have := (abs_le.mp hcx).1
                nlinarith
              have hc0 : (0 : ℝ) ≤ (des.yb : ℝ) * ((uOf cell.m : ℚ) : ℝ) -
                  (des.yb : ℝ) * (cell.r : ℝ) := by exact_mod_cast hcond
              push_cast
              nlinarith
            · push_cast; simp; positivity
          have e1' : ((cell.ρ1 : ℚ) : ℝ) ^ 2 ≤ ((yloA des cell : ℚ) : ℝ) ^ 2 + 1 := by
            exact_mod_cast hs1
          have e2' : ((cell.ρa : ℚ) : ℝ) ^ 2 ≤ ((yloA des cell : ℚ) : ℝ) ^ 2 + (des.α : ℝ) ^ 2 := by
            exact_mod_cast hsa
          exact ⟨by linarith, by linarith⟩) φ hφ
      have hle' := (Rat.cast_le (K := ℝ)).mpr hle
      have e : gA (des.lam : ℝ) (des.yb : ℝ) (des.α : ℝ) w des.ws.length φ =
          TA (2 * (des.lam : ℝ) * Real.log ((des.yb : ℝ) ^ 2 / 4)) w des.ws.length 0 φ -
            Vy (des.α : ℝ) (YA (des.yb : ℝ) 0 φ) := by
        simp [gA, TA, YA]
      rw [e]
      exact key.trans hle'
    · simp at hub

end

end CatalanCore.Zeta5.Cells
