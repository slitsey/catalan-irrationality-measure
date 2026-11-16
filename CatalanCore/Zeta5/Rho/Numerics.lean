module

public import CatalanCore.Zeta5.Rho.Concave
public import CatalanCore.Zeta5.Rho.Shape
public import CatalanMeasure.GenD.Signed.LogEval
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# The certified numbers (ledger ZR08)

For `(a, b) = (10⁻⁸, 242976/10⁶)`: `sup_{[a,b]} V ≤ 30449413/10⁷` and
`sup_{α<u≤1} Φ_{a,b} ≤ 60293245/10⁷`, so `W + Pb = 9.0742658 < 907427/10⁵`
(true values `V(b) = 3.0449412257…`, `max Φ = 6.0293242993…`).

* `V(a) = V(10⁻⁸)`: crude, one logarithm (`V(a) = 1.23`).
* `V(b) ≤ V(y₀)` for the rational `y₀ ≥ √b` (monotonicity of `V` from `y = 3/20`, `Vy_mono`),
  evaluated at the rational `y₀ = 246462979/500000000`: 2 logs, 2 arctans, `π`.
* `Φ(u) ≤ Φ(u₀) + Φ'(u₀)(u - u₀)` at the rational `u₀ = 973660012/10⁹` (`Phi_tangent`, concavity),
  with `|Φ'(u₀)| ≤ 10⁻⁷` (true value `-1.64·10⁻⁸`): 4 logs, one `√` (rational bracket), and
  `arcosh Y ≤ log(Y + r)` for a rational `r ≥ √(Y²-1)`: one more log.

Every transcendental value is a rational enclosure from `CatalanMeasure.GenD.Signed.LogEval`
(`logQ`, `atanQ`, kernel-checked tables at `2^-128`), checked by one `decide +kernel` each
(10 evaluations of `logQ`/`atanQ` with `n = 12` series terms; kcost estimated < 1 s each).
No grid, no root finder.
-/

namespace CatalanCore.Zeta5.Rho

open CatalanMeasure.GenD.Signed.LogEval Set Real

/-- Checker: `logQ` encloses `log q` inside `[lo, hi]`. -/
def logChk (q lo hi : ℚ) : Bool :=
  match logQ 12 q with
  | some (v, e) => decide (lo ≤ v - e ∧ v + e ≤ hi)
  | none => false

theorem logChk_spec {q lo hi : ℚ} (h : logChk q lo hi = true) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ hi := by
  unfold logChk at h
  split at h
  · rename_i v e hv
    have := (logQ_spec hv).2
    simp only [decide_eq_true_eq] at h
    unfold Enc at this
    have h1 := abs_le.mp this
    have hlo : (lo : ℝ) ≤ (v : ℝ) - e := by exact_mod_cast h.1
    have hhi : (v : ℝ) + e ≤ hi := by exact_mod_cast h.2
    constructor <;> linarith [h1.1, h1.2]
  · simp at h

/-- Checker: `atanQ` encloses `arctan q` inside `[lo, hi]`. -/
def atanChk (q lo hi : ℚ) : Bool :=
  match atanQ 12 q with
  | some (v, e) => decide (lo ≤ v - e ∧ v + e ≤ hi)
  | none => false

theorem atanChk_spec {q lo hi : ℚ} (h : atanChk q lo hi = true) :
    (lo : ℝ) ≤ Real.arctan (q : ℝ) ∧ Real.arctan (q : ℝ) ≤ hi := by
  unfold atanChk at h
  split at h
  · rename_i v e hv
    have := atanQ_spec hv
    simp only [decide_eq_true_eq] at h
    have h1 := abs_le.mp this
    have hlo : (lo : ℝ) ≤ (v : ℝ) - e := by exact_mod_cast h.1
    have hhi : (v : ℝ) + e ≤ hi := by exact_mod_cast h.2
    constructor <;> linarith [h1.1, h1.2]
  · simp at h

/-- `u0m`: enclosure of `log 224665003/250000000` (kcost: one `logQ` evaluation, estimated < 1 s). -/
theorem lg_u0m : (-10685050069 / 100000000000 : ℝ) ≤ Real.log (224665003 / 250000000 : ℝ) ∧ Real.log (224665003 / 250000000 : ℝ) ≤ (-106850500689 / 1000000000000 : ℝ) := by
  have h := logChk_spec (q := (224665003 / 250000000 : ℚ)) (lo := (-10685050069 / 100000000000 : ℚ)) (hi := (-106850500689 / 1000000000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- `u0p`: enclosure of `log 262165003/250000000` (kcost: one `logQ` evaluation, estimated < 1 s). -/
theorem lg_u0p : (47513170111 / 1000000000000 : ℝ) ≤ Real.log (262165003 / 250000000 : ℝ) ∧ Real.log (262165003 / 250000000 : ℝ) ≤ (742393283 / 15625000000 : ℝ) := by
  have h := logChk_spec (q := (262165003 / 250000000 : ℚ)) (lo := (47513170111 / 1000000000000 : ℚ)) (hi := (742393283 / 15625000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- `one_m`: enclosure of `log 6584997/250000000` (kcost: one `logQ` evaluation, estimated < 1 s). -/
theorem lg_one_m : (-454583379781 / 125000000000 : ℝ) ≤ Real.log (6584997 / 250000000 : ℝ) ∧ Real.log (6584997 / 250000000 : ℝ) ≤ (-3636667038247 / 1000000000000 : ℝ) := by
  have h := logChk_spec (q := (6584997 / 250000000 : ℚ)) (lo := (-454583379781 / 125000000000 : ℚ)) (hi := (-3636667038247 / 1000000000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- `one_p`: enclosure of `log 493415003/250000000` (kcost: one `logQ` evaluation, estimated < 1 s). -/
theorem lg_one_p : (169972423287 / 250000000000 : ℝ) ≤ Real.log (493415003 / 250000000 : ℝ) ∧ Real.log (493415003 / 250000000 : ℝ) ≤ (679889693149 / 1000000000000 : ℝ) := by
  have h := logChk_spec (q := (493415003 / 250000000 : ℚ)) (lo := (169972423287 / 250000000000 : ℚ)) (hi := (679889693149 / 1000000000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- `Y`: enclosure of `log 133255071716740009/7592999687500000` (kcost: one `logQ` evaluation, estimated < 1 s). -/
theorem lg_q5 : (286503839491 / 100000000000 : ℝ) ≤ Real.log (133255071716740009 / 7592999687500000 : ℝ) ∧ Real.log (133255071716740009 / 7592999687500000 : ℝ) ≤ (2865038394911 / 1000000000000 : ℝ) := by
  have h := logChk_spec (q := (133255071716740009 / 7592999687500000 : ℚ)) (lo := (286503839491 / 100000000000 : ℚ)) (hi := (2865038394911 / 1000000000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- `s2p1`: enclosure of `log 310744000017554441/250000000000000000` (kcost: one `logQ` evaluation, estimated < 1 s). -/
theorem lg_s2p1 : (217508504273 / 1000000000000 : ℝ) ≤ Real.log (310744000017554441 / 250000000000000000 : ℝ) ∧ Real.log (310744000017554441 / 250000000000000000 : ℝ) ≤ (108754252137 / 500000000000 : ℝ) := by
  have h := logChk_spec (q := (310744000017554441 / 250000000000000000 : ℚ)) (lo := (217508504273 / 1000000000000 : ℚ)) (hi := (108754252137 / 500000000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- `s2pa`: enclosure of `log 62150250017554441/250000000000000000` (kcost: one `logQ` evaluation, estimated < 1 s). -/
theorem lg_s2pa : (-695953038553 / 500000000000 : ℝ) ≤ Real.log (62150250017554441 / 250000000000000000 : ℝ) ∧ Real.log (62150250017554441 / 250000000000000000 : ℝ) ≤ (-278381215421 / 200000000000 : ℝ) := by
  have h := logChk_spec (q := (62150250017554441 / 250000000000000000 : ℚ)) (lo := (-695953038553 / 500000000000 : ℚ)) (hi := (-278381215421 / 200000000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- `ya`: enclosure of `log 562501/100000000` (kcost: one `logQ` evaluation, estimated < 1 s). -/
theorem lg_ya : (-1295133138279 / 250000000000 : ℝ) ≤ Real.log (562501 / 100000000 : ℝ) ∧ Real.log (562501 / 100000000 : ℝ) ≤ (-1036106510623 / 200000000000 : ℝ) := by
  have h := logChk_spec (q := (562501 / 100000000 : ℚ)) (lo := (-1295133138279 / 250000000000 : ℚ)) (hi := (-1036106510623 / 200000000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- Enclosure of `arctan 246462979/500000000` (kcost: one `atanQ` evaluation, estimated < 1 s). -/
theorem at_s : (114493094357 / 250000000000 : ℝ) ≤ Real.arctan (246462979 / 500000000 : ℝ) ∧ Real.arctan (246462979 / 500000000 : ℝ) ≤ (457972377429 / 1000000000000 : ℝ) := by
  have h := atanChk_spec (q := (246462979 / 500000000 : ℚ)) (lo := (114493094357 / 250000000000 : ℚ)) (hi := (457972377429 / 1000000000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- Enclosure of `arctan 37500000/246462979` (kcost: one `atanQ` evaluation, estimated < 1 s). -/
theorem at_as : (18874322421 / 125000000000 : ℝ) ≤ Real.arctan (37500000 / 246462979 : ℝ) ∧ Real.arctan (37500000 / 246462979 : ℝ) ≤ (150994579369 / 1000000000000 : ℝ) := by
  have h := atanChk_spec (q := (37500000 / 246462979 : ℚ)) (lo := (18874322421 / 125000000000 : ℚ)) (hi := (150994579369 / 1000000000000 : ℚ)) (by decide +kernel)
  push_cast at h
  exact h

/-- `a = 10⁻⁸`. -/
noncomputable def aR : ℝ := 1 / 10 ^ 8
/-- `b = 242976 / 10⁶`. -/
noncomputable def bR : ℝ := 242976 / 10 ^ 6
/-- `u₀ = 973660012 / 10⁹`, the rational point of the tangent bound. -/
noncomputable def u0R : ℝ := 973660012 / 10 ^ 9

theorem aR_pos : 0 < aR := by norm_num [aR]
theorem aR_lt_bR : aR < bR := by norm_num [aR, bR]
theorem ab_le : aR * bR ≤ (3 / 40) ^ 4 := by norm_num [aR, bR]

theorem arcosh_le_log {Y r : ℝ} (hY : 1 ≤ Y) (hr : √(Y ^ 2 - 1) ≤ r) :
    Real.arcosh Y ≤ Real.log (Y + r) := by
  have h := Real.exp_arcosh hY
  have hpos : 0 < Y + √(Y ^ 2 - 1) := by
    have := Real.sqrt_nonneg (Y ^ 2 - 1); linarith
  calc Real.arcosh Y = Real.log (Y + √(Y ^ 2 - 1)) := by rw [← h, Real.log_exp]
    _ ≤ Real.log (Y + r) := Real.log_le_log hpos (by linarith)

/-- A rational bracket of `√P`, `P = (u₀² + a)(u₀² + b)`. -/
theorem sqrtP_bounds :
    (5312896617 / 5000000000 : ℝ) ≤ √((u0R ^ 2 + aR) * (u0R ^ 2 + bR)) ∧
      √((u0R ^ 2 + aR) * (u0R ^ 2 + bR)) ≤ 2125158647 / 2000000000 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num [u0R, aR, bR]
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    norm_num [u0R, aR, bR]

theorem gfun_of_pos {x : ℝ} : gfun x = x * (Real.log x - 1) := rfl

theorem Phi_u0_le : Phi aR bR u0R ≤ 60293244 / 10 ^ 7 := by
  obtain ⟨hr1, hr2⟩ := sqrtP_bounds
  have hY := Yf_gt_one (u := u0R) aR_pos aR_lt_bR
  have hba : 0 < bR - aR := by have := aR_lt_bR; linarith
  have harc : Real.arcosh (Yf aR bR u0R) ≤ Real.log (133255071716740009 / 7592999687500000 : ℝ) := by
    have h := arcosh_le_log (Y := Yf aR bR u0R) (r := 2 * (2125158647 / 2000000000) / (bR - aR))
      hY.le (by
        rw [sqrt_Y_sq aR_pos aR_lt_bR]
        exact div_le_div_of_nonneg_right (by linarith) hba.le)
    have e : Yf aR bR u0R + 2 * (2125158647 / 2000000000) / (bR - aR) =
        133255071716740009 / 7592999687500000 := by norm_num [Yf, aR, bR, u0R]
    rw [e] at h; exact h
  have g1 : gfun (3 / 40 - u0R) = -((224665003 / 250000000 : ℝ) * (Real.log (224665003 / 250000000) - 1)) := by
    rw [show (3 / 40 - u0R : ℝ) = -(224665003 / 250000000) by norm_num [u0R], gfun_neg]; rfl
  have g2 : gfun (3 / 40 + u0R) = (262165003 / 250000000 : ℝ) * (Real.log (262165003 / 250000000) - 1) := by
    rw [show (3 / 40 + u0R : ℝ) = 262165003 / 250000000 by norm_num [u0R]]; rfl
  have g3 : gfun (1 - u0R) = (6584997 / 250000000 : ℝ) * (Real.log (6584997 / 250000000) - 1) := by
    rw [show (1 - u0R : ℝ) = 6584997 / 250000000 by norm_num [u0R]]; rfl
  have g4 : gfun (1 + u0R) = (493415003 / 250000000 : ℝ) * (Real.log (493415003 / 250000000) - 1) := by
    rw [show (1 + u0R : ℝ) = 493415003 / 250000000 by norm_num [u0R]]; rfl
  obtain ⟨a1, a2⟩ := lg_u0m
  obtain ⟨b1, b2⟩ := lg_u0p
  obtain ⟨c1, c2⟩ := lg_one_m
  obtain ⟨d1, d2⟩ := lg_one_p
  obtain ⟨e1, e2⟩ := lg_q5
  unfold Phi Lg
  rw [g1, g2, g3, g4]
  nlinarith [a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, harc]


theorem dPhi_u0_abs : |dPhi aR bR u0R| ≤ 1 / 10 ^ 7 := by
  obtain ⟨hr1, hr2⟩ := sqrtP_bounds
  have hP : 0 < √((u0R ^ 2 + aR) * (u0R ^ 2 + bR)) := by
    refine lt_of_lt_of_le (by norm_num) hr1
  unfold dPhi
  have e1 : Real.log ((u0R + 3 / 40) / (u0R - 3 / 40)) =
      Real.log (262165003 / 250000000) - Real.log (224665003 / 250000000) := by
    have h1 : (u0R + 3 / 40 : ℝ) = 262165003 / 250000000 := by norm_num [u0R]
    have h2 : (u0R - 3 / 40 : ℝ) = 224665003 / 250000000 := by norm_num [u0R]
    rw [Real.log_div (by rw [h1]; norm_num) (by rw [h2]; norm_num), h1, h2]
  have e2 : Real.log ((1 - u0R) / (1 + u0R)) =
      Real.log (6584997 / 250000000) - Real.log (493415003 / 250000000) := by
    have h1 : (1 - u0R : ℝ) = 6584997 / 250000000 := by norm_num [u0R]
    have h2 : (1 + u0R : ℝ) = 493415003 / 250000000 := by norm_num [u0R]
    rw [Real.log_div (by rw [h1]; norm_num) (by rw [h2]; norm_num), h1, h2]
  have h3 : 37 / 10 * u0R / √((u0R ^ 2 + aR) * (u0R ^ 2 + bR)) ≤
      37 / 10 * u0R / (5312896617 / 5000000000) :=
    div_le_div_of_nonneg_left (by norm_num [u0R]) (by norm_num) hr1
  have h4 : 37 / 10 * u0R / (2125158647 / 2000000000) ≤
      37 / 10 * u0R / √((u0R ^ 2 + aR) * (u0R ^ 2 + bR)) :=
    div_le_div_of_nonneg_left (by norm_num [u0R]) hP hr2
  rw [e1, e2]
  obtain ⟨a1, a2⟩ := lg_u0m
  obtain ⟨b1, b2⟩ := lg_u0p
  obtain ⟨c1, c2⟩ := lg_one_m
  obtain ⟨d1, d2⟩ := lg_one_p
  have hu : u0R = 973660012 / 10 ^ 9 := rfl
  rw [hu] at h3 h4 ⊢
  rw [abs_le]
  constructor <;> norm_num at h3 h4 ⊢ <;> linarith

theorem Vf_b_le : Vf bR ≤ 30449413 / 10 ^ 7 := by
  have hb0 : (0 : ℝ) ≤ bR := by norm_num [bR]
  set s : ℝ := 246462979 / 500000000 with hs
  have hsb : √bR ≤ s := Real.sqrt_le_iff.mpr ⟨by norm_num [hs], by norm_num [bR, hs]⟩
  have hs0 : (3 / 20 : ℝ) ≤ √bR := Real.le_sqrt_of_sq_le (by norm_num [bR])
  have hmono := Vy_mono hs0 hsb
  rw [Vf_eq_Vy hb0]
  refine le_trans hmono ?_
  have hspos : 0 < s := by norm_num [hs]
  unfold Vy
  rw [Jf_sq hspos, Jf_sq hspos]
  have hinv : (1 : ℝ) / s = s⁻¹ := one_div s
  rw [hinv, Real.arctan_inv_of_pos hspos]
  have e1 : s ^ 2 + 1 ^ 2 = (310744000017554441 / 250000000000000000 : ℝ) := by norm_num [hs]
  have e2 : s ^ 2 + (3 / 40) ^ 2 = (62150250017554441 / 250000000000000000 : ℝ) := by norm_num [hs]
  have e3 : (3 / 40 : ℝ) / s = 37500000 / 246462979 := by norm_num [hs]
  rw [e1, e2, e3]
  obtain ⟨a1, a2⟩ := lg_s2p1
  obtain ⟨b1, b2⟩ := lg_s2pa
  obtain ⟨c1, c2⟩ := at_s
  obtain ⟨d1, d2⟩ := at_as
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  have hs' : s = 246462979 / 500000000 := rfl
  rw [hs'] at *
  norm_num at *
  nlinarith [a1, a2, b1, b2, c1, c2, d1, d2, hp1, hp2]

theorem Vf_a_le : Vf aR ≤ 30449413 / 10 ^ 7 := by
  have ha0 : (0 : ℝ) ≤ aR := by norm_num [aR]
  have hsq : √aR = 1 / 10 ^ 4 := by
    rw [show aR = (1 / 10 ^ 4) ^ 2 by norm_num [aR]]
    exact Real.sqrt_sq (by norm_num)
  rw [Vf_eq_Vy ha0, hsq]
  have hypos : (0 : ℝ) < 1 / 10 ^ 4 := by norm_num
  unfold Vy
  rw [Jf_sq hypos, Jf_sq hypos]
  have h1 : Real.log ((1 / 10 ^ 4 : ℝ) ^ 2 + 1 ^ 2) ≤ ((1 / 10 ^ 4 : ℝ) ^ 2 + 1 ^ 2) - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.arctan (1 / (1 / 10 ^ 4 : ℝ)) ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two _).le
  have h3 : 0 ≤ Real.arctan ((3 / 40 : ℝ) / (1 / 10 ^ 4)) :=
    Real.arctan_nonneg.mpr (by norm_num)
  have e : (1 / 10 ^ 4 : ℝ) ^ 2 + (3 / 40) ^ 2 = 562501 / 100000000 := by norm_num
  rw [e]
  obtain ⟨a1, a2⟩ := lg_ya
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  norm_num at *
  have h3' : 0 ≤ Real.arctan 750 := Real.arctan_nonneg.mpr (by norm_num)
  nlinarith [a1, a2, h1, h2, h3', hp1, hp2]

theorem rho_W : ∀ t ∈ Icc aR bR, Vf t ≤ 30449413 / 10 ^ 7 := fun t ht =>
  (Vf_le_max aR_pos ht.1 ht.2).trans (max_le Vf_a_le Vf_b_le)

theorem rho_Pb : ∀ u : ℝ, 3 / 40 < u → u ≤ 1 → Phi aR bR u ≤ 60293245 / 10 ^ 7 := by
  intro u hu hu1
  have h0 : (3 / 40 : ℝ) < u0R := by norm_num [u0R]
  have h01 : u0R < 1 := by norm_num [u0R]
  have ht := Phi_tangent aR_pos aR_lt_bR ab_le h0 h01 hu hu1
  have hP := Phi_u0_le
  have habs := dPhi_u0_abs
  have hd := abs_le.mp habs
  have hdu : |u - u0R| ≤ 1 := by
    rw [abs_le]; constructor <;> norm_num [u0R] at * <;> linarith
  have hm : dPhi aR bR u0R * (u - u0R) ≤ 1 / 10 ^ 7 := by
    calc dPhi aR bR u0R * (u - u0R) ≤ |dPhi aR bR u0R * (u - u0R)| := le_abs_self _
      _ = |dPhi aR bR u0R| * |u - u0R| := abs_mul _ _
      _ ≤ 1 / 10 ^ 7 * 1 := mul_le_mul habs hdu (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  linarith

/-- **ZR08.**  `max V + max Φ < 907427/10⁵` at `(a, b) = (10⁻⁸, 242976/10⁶)`, with certified
rational bounds `W = 30449413/10⁷`, `Pb = 60293245/10⁷` (`W + Pb = 9.0742658`). -/
theorem rho_numerics :
    (∀ t ∈ Icc aR bR, Vf t ≤ 30449413 / 10 ^ 7) ∧
      (∀ u : ℝ, 3 / 40 < u → u ≤ 1 → Phi aR bR u ≤ 60293245 / 10 ^ 7) ∧
      (30449413 / 10 ^ 7 : ℝ) + 60293245 / 10 ^ 7 < 907427 / 10 ^ 5 :=
  ⟨rho_W, rho_Pb, by norm_num⟩

end CatalanCore.Zeta5.Rho
