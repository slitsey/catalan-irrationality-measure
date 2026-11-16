module

public import CatalanCore.Zeta5.Cells.Cell

@[expose] public section

/-!
# Z5-CELLS, part 5: region A, the trigonometric part and its Chebyshev/rotation recurrence (ZD20)

`g_A(φ) = 2λ log(b/4) − 2 Σ_{k=1}^N c_k cos(2kφ)/k − V(y_b cos φ)`.  With `w_k = c_{k+1}/(k+1)`
(`k < N`) and `K0 = 2 c_0 log(b/4)` the trigonometric part has the derivative tower
`TA j φ = [j = 0] K0 − 2 Σ_k w_k (2κ)^j cos(2κφ + jπ/2)`, `κ = k+1` (`hasDerivAt_TA`).

At a centre `φ_c` with rational `cos φ_c = u`, `sin φ_c = v` (`u = (1−m²)/(1+m²)`,
`v = 2m/(1+m²)`, `φ_c = 2 arctan m`) the numbers `cos(2κφ_c)`, `sin(2κφ_c)` are exact rationals
produced by the rotation recurrence `rotAux` (the Chebyshev recurrences `T_{2k}(u)`,
`v U_{2k-1}(u)` of the ledger in complex form: `(C,S) ↦ (C cos 2φ − S sin 2φ, C sin 2φ + S cos 2φ)`),
and the Taylor data are the moments `dotC`/`dotS` against the shared weight tables
`wTabAux 0 j ws = w_k (2κ)^j` (`N(M+2)` multiplications once, not per cell).
-/

namespace CatalanCore.Zeta5.Cells

open Set Real

noncomputable section

/-! ### the tower -/

/-- the trigonometric tower of region A. -/
def TA (K0 : ℝ) (w : ℕ → ℝ) (N : ℕ) (j : ℕ) (φ : ℝ) : ℝ :=
  (if j = 0 then K0 else 0) - 2 * ∑ k ∈ Finset.range N,
    w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ j * Real.cos (2 * ((k + 1 : ℕ) : ℝ) * φ + (j : ℝ) * (π / 2))

theorem hasDerivAt_TA (K0 : ℝ) (w : ℕ → ℝ) (N j : ℕ) (φ : ℝ) :
    HasDerivAt (TA K0 w N j) (TA K0 w N (j + 1) φ) φ := by
  have hk : ∀ k ∈ Finset.range N, HasDerivAt
      (fun φ => w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ j *
        Real.cos (2 * ((k + 1 : ℕ) : ℝ) * φ + (j : ℝ) * (π / 2)))
      (w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ (j + 1) *
        Real.cos (2 * ((k + 1 : ℕ) : ℝ) * φ + ((j + 1 : ℕ) : ℝ) * (π / 2))) φ := by
    intro k _
    have h1 : HasDerivAt (fun φ => 2 * ((k + 1 : ℕ) : ℝ) * φ + (j : ℝ) * (π / 2))
        (2 * ((k + 1 : ℕ) : ℝ)) φ := by
      simpa using ((hasDerivAt_id' φ).const_mul (2 * ((k + 1 : ℕ) : ℝ))).add_const
        ((j : ℝ) * (π / 2))
    have h2 := h1.cos.const_mul (w k * (2 * ((k + 1 : ℕ) : ℝ)) ^ j)
    refine h2.congr_deriv ?_
    have : Real.cos (2 * ((k + 1 : ℕ) : ℝ) * φ + ((j + 1 : ℕ) : ℝ) * (π / 2)) =
        - Real.sin (2 * ((k + 1 : ℕ) : ℝ) * φ + (j : ℝ) * (π / 2)) := by
      rw [← Real.cos_add_pi_div_two]; congr 1; push_cast; ring
    rw [this]; ring
  have hs := (HasDerivAt.fun_sum hk).const_mul 2
  have hc : HasDerivAt (fun _ : ℝ => if j = 0 then K0 else 0) 0 φ := hasDerivAt_const _ _
  have h := hc.fun_sub hs
  unfold TA
  refine h.congr_deriv ?_
  simp

theorem continuous_TA (K0 : ℝ) (w : ℕ → ℝ) (N j : ℕ) : Continuous (TA K0 w N j) := by
  unfold TA
  fun_prop

theorem isTower_TA (K0 : ℝ) (w : ℕ → ℝ) (N : ℕ) (c r : ℝ) :
    CatalanMeasure.GenD.Signed.TaylorCell.IsTower (TA K0 w N) c r 5 where
  cont j _ := (continuous_TA K0 w N j).continuousOn
  der j _ x _ := hasDerivAt_TA K0 w N j x

/-- the remainder bound `|TA 5| ≤ 2 Σ |w_k| (2κ)^5` -/
theorem abs_TA5_le (K0 : ℝ) (w : ℕ → ℝ) (N : ℕ) (φ : ℝ) :
    |TA K0 w N 5 φ| ≤ 2 * ∑ k ∈ Finset.range N, |w k| * (2 * ((k + 1 : ℕ) : ℝ)) ^ 5 := by
  unfold TA
  simp only [show (5 : ℕ) ≠ 0 by norm_num, if_false, zero_sub, abs_neg]
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ))]
  have := Real.abs_cos_le_one (2 * ((k + 1 : ℕ) : ℝ) * φ + ((5 : ℕ) : ℝ) * (π / 2))
  calc |w k| * (2 * ((k + 1 : ℕ) : ℝ)) ^ 5 * |Real.cos _|
      ≤ |w k| * (2 * ((k + 1 : ℕ) : ℝ)) ^ 5 * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := mul_one _

/-! ### the point values -/

/-- the phase table: `cos(x + jπ/2)` in terms of `C = cos x`, `S = sin x`, `j ≤ 4`. -/
theorem cos_add_quarter (x : ℝ) :
    Real.cos (x + ((0 : ℕ) : ℝ) * (π / 2)) = Real.cos x ∧
    Real.cos (x + ((1 : ℕ) : ℝ) * (π / 2)) = - Real.sin x ∧
    Real.cos (x + ((2 : ℕ) : ℝ) * (π / 2)) = - Real.cos x ∧
    Real.cos (x + ((3 : ℕ) : ℝ) * (π / 2)) = Real.sin x ∧
    Real.cos (x + ((4 : ℕ) : ℝ) * (π / 2)) = Real.cos x := by
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · rw [← Real.cos_add_pi_div_two]; congr 1; push_cast; ring
  · rw [← Real.cos_add_pi]; congr 1; push_cast; ring
  · have : x + ((3 : ℕ) : ℝ) * (π / 2) = (x + π / 2) + π := by push_cast; ring
    rw [this, Real.cos_add_pi, Real.cos_add_pi_div_two]; ring
  · have : x + ((4 : ℕ) : ℝ) * (π / 2) = x + 2 * π := by push_cast; ring
    rw [this, Real.cos_add_two_pi]

/-- weight tables: `w_k (2κ)^j`, structural in the weight list, `κ = k₀ + position + 1`. -/
def wTabAux : ℕ → ℕ → List ℚ → List ℚ
  | _, _, [] => []
  | k, j, w :: ws => (w * (2 * ((k + 1 : ℕ) : ℚ)) ^ j) :: wTabAux (k + 1) j ws

theorem wTabAux_length (k j : ℕ) (ws : List ℚ) : (wTabAux k j ws).length = ws.length := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih => simp [wTabAux, ih]

theorem wTabAux_getD (j : ℕ) (ws : List ℚ) : ∀ (k₀ k : ℕ), k < ws.length →
    (wTabAux k₀ j ws).getD k 0 = ws.getD k 0 * (2 * ((k₀ + k + 1 : ℕ) : ℚ)) ^ j := by
  induction ws with
  | nil => intro k₀ k hk; simp at hk
  | cons w ws ih =>
    intro k₀ k hk
    cases k with
    | zero => simp [wTabAux]
    | succ k =>
      simp only [wTabAux, List.getD_cons_succ]
      rw [ih (k₀ + 1) k (by simpa using hk)]
      rw [show k₀ + 1 + k + 1 = k₀ + (k + 1) + 1 by omega]

/-- the rotation recurrence: the `n` pairs `(cos(a + κβ), sin(a + κβ))`, `κ = 1..n`. -/
def rotAux : ℕ → ℚ → ℚ → ℚ → ℚ → List (ℚ × ℚ)
  | 0, _, _, _, _ => []
  | n + 1, C, S, cw, sw =>
      (C * cw - S * sw, C * sw + S * cw) :: rotAux n (C * cw - S * sw) (C * sw + S * cw) cw sw

/-- moments against the cosines / sines of the rotation list -/
def dotC : List ℚ → List (ℚ × ℚ) → ℚ
  | w :: ws, p :: rs => w * p.1 + dotC ws rs
  | _, _ => 0

def dotS : List ℚ → List (ℚ × ℚ) → ℚ
  | w :: ws, p :: rs => w * p.2 + dotS ws rs
  | _, _ => 0

theorem dot_rot (β : ℝ) (cw sw : ℚ) (hcw : (cw : ℝ) = Real.cos β) (hsw : (sw : ℝ) = Real.sin β) :
    ∀ (ws : List ℚ) (C S : ℚ) (a : ℝ), (C : ℝ) = Real.cos a → (S : ℝ) = Real.sin a →
      ((dotC ws (rotAux ws.length C S cw sw) : ℚ) : ℝ) =
        ∑ k ∈ Finset.range ws.length, (ws.getD k 0 : ℝ) * Real.cos (a + ((k + 1 : ℕ) : ℝ) * β) ∧
      ((dotS ws (rotAux ws.length C S cw sw) : ℚ) : ℝ) =
        ∑ k ∈ Finset.range ws.length, (ws.getD k 0 : ℝ) * Real.sin (a + ((k + 1 : ℕ) : ℝ) * β) := by
  intro ws
  induction ws with
  | nil => intro C S a _ _; simp [rotAux, dotC, dotS]
  | cons w ws ih =>
    intro C S a hC hS
    have hC' : (((C * cw - S * sw : ℚ)) : ℝ) = Real.cos (a + β) := by
      push_cast; rw [hC, hS, hcw, hsw, Real.cos_add]
    have hS' : (((C * sw + S * cw : ℚ)) : ℝ) = Real.sin (a + β) := by
      push_cast; rw [hC, hS, hcw, hsw, Real.sin_add]; ring
    obtain ⟨h1, h2⟩ := ih _ _ (a + β) hC' hS'
    simp only [List.length_cons, rotAux, dotC, dotS]
    constructor
    · rw [Rat.cast_add, Rat.cast_mul, hC', h1, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by congr 2; push_cast; ring
      · congr 2; push_cast; ring
    · rw [Rat.cast_add, Rat.cast_mul, hS', h2, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by congr 2; push_cast; ring
      · congr 2; push_cast; ring

end

end CatalanCore.Zeta5.Cells
