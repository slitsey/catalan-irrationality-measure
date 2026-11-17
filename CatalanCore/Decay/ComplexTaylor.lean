module

public import CatalanCore.Tools.Joukowski

@[expose] public section

/-!
# Complex-curve Taylor cells: the V tower and the cell soundness theorem (Lai decay, LD11, LD18)

Generic in the three-pole field `Ψ̃` (parameters `e r B K θ`), in the analytic curve `γ`, and in
the potential towers it is combined with.

* `reTower`, `isTower_reTower`, `abs_reTower5_le`: for an analytic derivative chain `D k` along a
  curve `γ`, the real parts of the Faà di Bruno towers form an `IsTower` of order 5, and
  `|f 5| ≤ fdbBound Dm Ym`.
* **W1** (`psiT`, `psiTower`, `hasDerivAt_psiT`, `hasDerivAt_psiTower_succ`, `norm_psiTower_succ_le`,
  `norm_psiTower_one_le`, `isTower_vTower`, `abs_vTower5_le`): `Ψ̃' = (e+r) log s - e log (B-s)
  - r log (s+K) + (θ - eπ) i`, `Ψ̃^{(m)}` in closed form, the pole-distance majorants and the order-4
  cell tower of `V = κ_V + Re Ψ̃` along any curve avoiding the cuts.
* Cell distances (`norm_curve_sub_le`, `norm_sub_pole_ge`, `jc_lipschitz`, `dlo_on_cell`).
* **LD18** (`wedgeTower`, `isTower_wedgeTower`, `wedgeCellUB`, `wedgeCell_sound`,
  `wedgeCellOk_sound`): the rational Taylor-model bound of a cell of the field `V - 2U₁ - 2U₂`,
  from enclosures of the point towers and a remainder bound.
-/

namespace CatalanCore.Decay.ComplexTaylor

open Complex Set Filter Topology CatalanCore.Zeta5.Cells CatalanMeasure.GenD.Signed.TaylorCell
  CatalanCore.Tools.Joukowski

noncomputable section

/-! ### 1. Real parts of complex Faà di Bruno towers -/

/-- The real tower of `Re (G ∘ γ)` where `D k = G^{(k)}`: slot `0` is the given function `U0`, and
slot `j ≥ 1` is `Re (fdb (D k ∘ γ 0) (γ i) j)`. -/
def reTower (D : ℕ → ℂ → ℂ) (U0 : ℝ → ℝ) (γ : ℕ → ℝ → ℂ) (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then U0 x else (fdb (fun k => D k (γ 0 x)) (fun i => γ i x) j).re

theorem fdb_contWithin {S : Set ℝ} {x : ℝ} {Dc Yc : ℕ → ℝ → ℂ}
    (hD : ∀ k, 1 ≤ k → k ≤ 5 → ContinuousWithinAt (Dc k) S x)
    (hY : ∀ i, 1 ≤ i → i ≤ 5 → ContinuousWithinAt (Yc i) S x) (j : ℕ) (hj1 : 1 ≤ j)
    (hj5 : j ≤ 5) :
    ContinuousWithinAt (fun y => fdb (fun k => Dc k y) (fun i => Yc i y) j) S x := by
  have h1 := hD 1 (by norm_num) (by norm_num)
  have h2 := hD 2 (by norm_num) (by norm_num)
  have h3 := hD 3 (by norm_num) (by norm_num)
  have h4 := hD 4 (by norm_num) (by norm_num)
  have h5 := hD 5 (by norm_num) (by norm_num)
  have y1 := hY 1 (by norm_num) (by norm_num)
  have y2 := hY 2 (by norm_num) (by norm_num)
  have y3 := hY 3 (by norm_num) (by norm_num)
  have y4 := hY 4 (by norm_num) (by norm_num)
  have y5 := hY 5 (by norm_num) (by norm_num)
  clear hD hY
  interval_cases j <;> simp only [fdb] <;> fun_prop

theorem isTower_reTower {D : ℕ → ℂ → ℂ} {U0 : ℝ → ℝ} {γ : ℕ → ℝ → ℂ} {a r : ℝ}
    (hγd : ∀ i < 5, ∀ x, HasDerivAt (γ i) (γ (i + 1) x) x) (hγc : Continuous (γ 5))
    (hD : ∀ x ∈ Icc (a - r) (a + r), ∀ k, 1 ≤ k → k < 5 →
      HasDerivAt (D k) (D (k + 1) (γ 0 x)) (γ 0 x))
    (hDc : ∀ x ∈ Icc (a - r) (a + r), ∀ k, 1 ≤ k → k ≤ 5 → ContinuousAt (D k) (γ 0 x))
    (hU : ∀ x ∈ Icc (a - r) (a + r), HasDerivAt U0 ((D 1 (γ 0 x) * γ 1 x).re) x) :
    IsTower (reTower D U0 γ) a r 5 := by
  have hcont : ∀ i ≤ 5, Continuous (γ i) := by
    intro i hi
    rcases Nat.lt_or_ge i 5 with h5 | h5
    · exact continuous_iff_continuousAt.2 fun x => (hγd i h5 x).continuousAt
    · have : i = 5 := le_antisymm hi h5
      subst this; exact hγc
  have hDd : ∀ x ∈ Icc (a - r) (a + r), ∀ k, 1 ≤ k → k < 5 →
      HasDerivAt (fun y => D k (γ 0 y)) (D (k + 1) (γ 0 x) * γ 1 x) x := by
    intro x hx k hk1 hk5
    have h1 : HasDerivAt (fun y => D k (γ 0 y)) (γ 1 x • D (k + 1) (γ 0 x)) x :=
      (hD x hx k hk1 hk5).scomp x (hγd 0 (by norm_num) x)
    exact h1.congr_deriv (by rw [smul_eq_mul, mul_comm])
  have e0 : reTower D U0 γ 0 = U0 := by funext y; simp [reTower]
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [e0]
      exact (hU x hx).continuousAt.continuousWithinAt
    · have hc : ∀ k, 1 ≤ k → k ≤ 5 →
          ContinuousWithinAt (fun y => D k (γ 0 y)) (Icc (a - r) (a + r)) x := by
        intro k hk1 hk5
        exact ((hDc x hx k hk1 hk5).comp (hcont 0 (by norm_num)).continuousAt).continuousWithinAt
      have hy : ∀ i, 1 ≤ i → i ≤ 5 → ContinuousWithinAt (γ i) (Icc (a - r) (a + r)) x :=
        fun i _ hi => (hcont i hi).continuousAt.continuousWithinAt
      have hne : j ≠ 0 := by omega
      have e : reTower D U0 γ j =
          fun y => (fdb (fun k => D k (γ 0 y)) (fun i => γ i y) j).re := by
        funext y; simp [reTower, hne]
      rw [e]
      exact Complex.continuous_re.continuousAt.comp_continuousWithinAt
        (fdb_contWithin (Dc := fun k y => D k (γ 0 y)) (Yc := γ) hc hy j hj0 hj)
  · intro j hj x hx
    have hx' : x ∈ Icc (a - r) (a + r) := ⟨hx.1.le, hx.2.le⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have e1 : reTower D U0 γ (0 + 1) x = (D 1 (γ 0 x) * γ 1 x).re := by
        simp [reTower, fdb]
      rw [e0, e1]
      exact hU x hx'
    · have hne : j ≠ 0 := by omega
      have hne1 : j + 1 ≠ 0 := by omega
      have hfd := hasDerivAt_fdbC (Dc := fun k y => D k (γ 0 y)) (Yc := γ) (x := x)
        (fun k hk1 hk5 => hDd x hx' k hk1 hk5) (fun i _ hi => hγd i hi x) j hj0 hj
      have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hfd
      have e : reTower D U0 γ j =
          fun y => (fdb (fun k => D k (γ 0 y)) (fun i => γ i y) j).re := by
        funext y; simp [reTower, hne]
      have e1 : reTower D U0 γ (j + 1) x =
          (fdb (fun k => D k (γ 0 x)) (fun i => γ i x) (j + 1)).re := by
        simp [reTower, hne1]
      rw [e, e1]
      exact hre

/-- The order-5 remainder of `reTower`: `|f 5 x| ≤ fdbBound Dm Ym`. -/
theorem abs_reTower5_le {D : ℕ → ℂ → ℂ} {U0 : ℝ → ℝ} {γ : ℕ → ℝ → ℂ} {x : ℝ} {Dm Ym : ℕ → ℝ}
    (hD : ∀ k, 1 ≤ k → k ≤ 5 → ‖D k (γ 0 x)‖ ≤ Dm k)
    (hY : ∀ i, 1 ≤ i → i ≤ 5 → ‖γ i x‖ ≤ Ym i) :
    |reTower D U0 γ 5 x| ≤ fdbBound Dm Ym := by
  have hne : (5 : ℕ) ≠ 0 := by norm_num
  simp only [reTower, hne, if_false]
  exact (Complex.abs_re_le_norm _).trans (norm_fdb5_le _ _ Dm Ym hD hY)

/-! ### 2. The three-pole field `Ψ̃` (W1) -/

/-- `Ψ̃ = e[s log s - s - (s - B)(log (B - s) + iπ) + (s - B)] - r[(s+K) log (s+K) - (s+K)
- s log s + s] + θ i s` with principal logarithms.  Lai: `(e, r, B, K, θ) = (3, 2, 2, 6, 2π)`. -/
def psiT (e r B K θ : ℝ) (s : ℂ) : ℂ :=
  (e : ℂ) * (s * Complex.log s - s - (s - B) * (Complex.log (B - s) + Real.pi * I) + (s - B))
  - (r : ℂ) * ((s + K) * Complex.log (s + K) - (s + K) - s * Complex.log s + s)
  + (θ : ℂ) * I * s

/-- The derivative chain `D_k = Ψ̃^{(k)}`. -/
def psiTower (e r B K θ : ℝ) : ℕ → ℂ → ℂ
  | 0 => psiT e r B K θ
  | 1 => fun s => ((e : ℂ) + r) * Complex.log s - e * Complex.log (B - s)
      - r * Complex.log (s + K) + ((θ - e * Real.pi : ℝ) : ℂ) * I
  | (n + 2) => fun s => (n.factorial : ℂ) * (((e : ℂ) + r) * (-1) ^ n / s ^ (n + 1)
      + e / ((B : ℂ) - s) ^ (n + 1) - r * (-1) ^ n / (s + K) ^ (n + 1))

/-- The analyticity domain: `s`, `B - s`, `s + K` off the closed negative axis. -/
def psiDom (B K : ℝ) (s : ℂ) : Prop :=
  s ∈ slitPlane ∧ (B : ℂ) - s ∈ slitPlane ∧ s + K ∈ slitPlane

theorem psiDom_open (B K : ℝ) : IsOpen {s : ℂ | psiDom B K s} := by
  refine IsOpen.inter isOpen_slitPlane (IsOpen.inter ?_ ?_)
  · exact isOpen_slitPlane.preimage (by fun_prop)
  · exact isOpen_slitPlane.preimage (by fun_prop)

theorem hasDerivAt_psiT (e r B K θ : ℝ) {s : ℂ} (h : psiDom B K s) :
    HasDerivAt (psiT e r B K θ) (psiTower e r B K θ 1 s) s := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : s ≠ 0 := slitPlane_ne_zero h1
  have hBs : (B : ℂ) - s ≠ 0 := slitPlane_ne_zero h2
  have hsK : s + K ≠ 0 := slitPlane_ne_zero h3
  have hid : HasDerivAt (fun s : ℂ => s) 1 s := hasDerivAt_id s
  have hl : HasDerivAt (fun s : ℂ => Complex.log s) (1 / s) s := hid.clog h1
  have hlB : HasDerivAt (fun s : ℂ => Complex.log ((B : ℂ) - s)) ((0 - 1) / ((B : ℂ) - s)) s :=
    ((hasDerivAt_const s (B : ℂ)).sub hid).clog h2
  have hlK : HasDerivAt (fun s : ℂ => Complex.log (s + K)) ((1 + 0) / (s + K)) s :=
    (hid.add (hasDerivAt_const s (K : ℂ))).clog h3
  have a1 := (hid.mul hl).sub hid
  have a2 := (hid.sub (hasDerivAt_const s (B : ℂ))).mul
    (hlB.add (hasDerivAt_const s ((Real.pi : ℂ) * I)))
  have a3 := (a1.sub a2).add (hid.sub (hasDerivAt_const s (B : ℂ)))
  have b0 := hid.add (hasDerivAt_const s (K : ℂ))
  have b1 := (((b0.mul hlK).sub b0).sub (hid.mul hl)).add hid
  have t3 := ((a3.const_mul (e : ℂ)).sub (b1.const_mul (r : ℂ))).add
    (hid.const_mul ((θ : ℂ) * I))
  refine (t3.congr_deriv ?_)
  simp only [psiTower, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_psiTower_one (e r B K θ : ℝ) {s : ℂ} (h : psiDom B K s) :
    HasDerivAt (psiTower e r B K θ 1) (psiTower e r B K θ 2 s) s := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : s ≠ 0 := slitPlane_ne_zero h1
  have hBs : (B : ℂ) - s ≠ 0 := slitPlane_ne_zero h2
  have hsK : s + K ≠ 0 := slitPlane_ne_zero h3
  have hid : HasDerivAt (fun s : ℂ => s) 1 s := hasDerivAt_id s
  have hl : HasDerivAt (fun s : ℂ => Complex.log s) (1 / s) s := hid.clog h1
  have hlB : HasDerivAt (fun s : ℂ => Complex.log ((B : ℂ) - s)) ((0 - 1) / ((B : ℂ) - s)) s :=
    ((hasDerivAt_const s (B : ℂ)).sub hid).clog h2
  have hlK : HasDerivAt (fun s : ℂ => Complex.log (s + K)) ((1 + 0) / (s + K)) s :=
    (hid.add (hasDerivAt_const s (K : ℂ))).clog h3
  have t := ((((hl.const_mul ((e : ℂ) + r))).sub (hlB.const_mul (e : ℂ))).sub
    (hlK.const_mul (r : ℂ))).add_const (((θ - e * Real.pi : ℝ) : ℂ) * I)
  refine t.congr_deriv ?_
  simp only [psiTower]
  field_simp
  simp
  ring

theorem hasDerivAt_psiTower_succ (e r B K θ : ℝ) {s : ℂ} (hs : s ≠ 0) (hBs : (B : ℂ) - s ≠ 0)
    (hsK : s + K ≠ 0) (n : ℕ) :
    HasDerivAt (psiTower e r B K θ (n + 2)) (psiTower e r B K θ (n + 3) s) s := by
  have hid : HasDerivAt (fun s : ℂ => s) 1 s := hasDerivAt_id s
  have p1 : HasDerivAt (fun s : ℂ => s ^ (n + 1)) (((n + 1 : ℕ) : ℂ) * s ^ n) s :=
    hasDerivAt_pow (n + 1) s
  have p2 : HasDerivAt (fun s : ℂ => ((B : ℂ) - s) ^ (n + 1))
      (((n + 1 : ℕ) : ℂ) * ((B : ℂ) - s) ^ n * (0 - 1)) s :=
    ((hasDerivAt_const s (B : ℂ)).sub hid).pow (n + 1)
  have p3 : HasDerivAt (fun s : ℂ => (s + K) ^ (n + 1))
      (((n + 1 : ℕ) : ℂ) * (s + K) ^ n * (1 + 0)) s :=
    (hid.add (hasDerivAt_const s (K : ℂ))).pow (n + 1)
  have q1 := (hasDerivAt_const s (((e : ℂ) + r) * (-1) ^ n)).div p1 (pow_ne_zero _ hs)
  have q2 := (hasDerivAt_const s (e : ℂ)).div p2 (pow_ne_zero _ hBs)
  have q3 := (hasDerivAt_const s ((r : ℂ) * (-1) ^ n)).div p3 (pow_ne_zero _ hsK)
  have t := ((q1.add q2).sub q3).const_mul ((n.factorial : ℂ))
  refine t.congr_deriv ?_
  simp only [psiTower, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Continuity of the whole chain at a point of the domain. -/
theorem continuousAt_psiTower (e r B K θ : ℝ) {s : ℂ} (h : psiDom B K s) {k : ℕ} (hk : 1 ≤ k) :
    ContinuousAt (psiTower e r B K θ k) s := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    exact (hasDerivAt_psiTower_one e r B K θ ⟨h1, h2, h3⟩).continuousAt
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    exact (hasDerivAt_psiTower_succ e r B K θ (slitPlane_ne_zero h1) (slitPlane_ne_zero h2)
      (slitPlane_ne_zero h3) n).continuousAt

/-! ### 3. Majorants of the chain `Ψ̃^{(k)}` -/

theorem norm_log_le (z : ℂ) : ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]
  exact add_le_add le_rfl (Complex.abs_arg_le_pi z)

theorem norm_ofReal_mul' {x : ℝ} (hx : 0 ≤ x) (w : ℂ) : ‖(x : ℂ) * w‖ = x * ‖w‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx]

theorem norm_add_ofReal {e r : ℝ} (he : 0 ≤ e) (hr : 0 ≤ r) : ‖(e : ℂ) + r‖ = e + r := by
  rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (add_nonneg he hr)]

/-- The majorant chain: `‖Ψ̃^{(k)}‖ ≤ psiDm k` for `1 ≤ k` from pole-distance lower bounds
`d_i` and bounds `L_i` of the `|log |·||`. -/
def psiDm (e r θ d1 d2 d3 L1 L2 L3 : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => (e + r) * (L1 + Real.pi) + e * (L2 + Real.pi) + r * (L3 + Real.pi)
      + |θ - e * Real.pi|
  | (n + 2) => (n.factorial : ℝ) * ((e + r) / d1 ^ (n + 1) + e / d2 ^ (n + 1) + r / d3 ^ (n + 1))

theorem norm_psiTower_one_le (e r B K θ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) {s : ℂ}
    {L1 L2 L3 : ℝ} (hL1 : |Real.log ‖s‖| ≤ L1) (hL2 : |Real.log ‖(B : ℂ) - s‖| ≤ L2)
    (hL3 : |Real.log ‖s + K‖| ≤ L3) :
    ‖psiTower e r B K θ 1 s‖ ≤ (e + r) * (L1 + Real.pi) + e * (L2 + Real.pi)
      + r * (L3 + Real.pi) + |θ - e * Real.pi| := by
  have l1 := (norm_log_le s).trans (add_le_add_left hL1 _)
  have l2 := (norm_log_le ((B : ℂ) - s)).trans (add_le_add_left hL2 _)
  have l3 := (norm_log_le (s + K)).trans (add_le_add_left hL3 _)
  simp only [psiTower]
  have n1 : ‖((e : ℂ) + r) * Complex.log s‖ ≤ (e + r) * (L1 + Real.pi) := by
    rw [norm_mul, norm_add_ofReal he hr]
    exact mul_le_mul_of_nonneg_left l1 (add_nonneg he hr)
  have n2 : ‖(e : ℂ) * Complex.log ((B : ℂ) - s)‖ ≤ e * (L2 + Real.pi) := by
    rw [norm_ofReal_mul' he]
    exact mul_le_mul_of_nonneg_left l2 he
  have n3 : ‖(r : ℂ) * Complex.log (s + K)‖ ≤ r * (L3 + Real.pi) := by
    rw [norm_ofReal_mul' hr]
    exact mul_le_mul_of_nonneg_left l3 hr
  have n4 : ‖((θ - e * Real.pi : ℝ) : ℂ) * I‖ = |θ - e * Real.pi| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ ‖((e : ℂ) + r) * Complex.log s‖ + ‖(e : ℂ) * Complex.log ((B : ℂ) - s)‖
        + ‖(r : ℂ) * Complex.log (s + K)‖ + ‖((θ - e * Real.pi : ℝ) : ℂ) * I‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by rw [n4]; linarith

theorem norm_psiTower_succ_le (e r B K θ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) {s : ℂ}
    {d1 d2 d3 : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (h1 : d1 ≤ ‖s‖)
    (h2 : d2 ≤ ‖(B : ℂ) - s‖) (h3 : d3 ≤ ‖s + K‖) (n : ℕ) :
    ‖psiTower e r B K θ (n + 2) s‖ ≤
      (n.factorial : ℝ) * ((e + r) / d1 ^ (n + 1) + e / d2 ^ (n + 1) + r / d3 ^ (n + 1)) := by
  simp only [psiTower]
  rw [norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have m1 : ‖((e : ℂ) + r) * (-1) ^ n / s ^ (n + 1)‖ ≤ (e + r) / d1 ^ (n + 1) := by
    rw [norm_div, norm_mul, norm_add_ofReal he hr, norm_pow, norm_neg, norm_one, one_pow,
      mul_one, norm_pow]
    exact div_le_div_of_nonneg_left (add_nonneg he hr) (pow_pos hd1 _)
      (pow_le_pow_left₀ hd1.le h1 _)
  have m2 : ‖(e : ℂ) / ((B : ℂ) - s) ^ (n + 1)‖ ≤ e / d2 ^ (n + 1) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg he, norm_pow]
    exact div_le_div_of_nonneg_left he (pow_pos hd2 _) (pow_le_pow_left₀ hd2.le h2 _)
  have m3 : ‖(r : ℂ) * (-1) ^ n / (s + K) ^ (n + 1)‖ ≤ r / d3 ^ (n + 1) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, norm_pow, norm_neg,
      norm_one, one_pow, mul_one, norm_pow]
    exact div_le_div_of_nonneg_left hr (pow_pos hd3 _) (pow_le_pow_left₀ hd3.le h3 _)
  calc _ ≤ ‖((e : ℂ) + r) * (-1) ^ n / s ^ (n + 1)‖ + ‖(e : ℂ) / ((B : ℂ) - s) ^ (n + 1)‖
        + ‖(r : ℂ) * (-1) ^ n / (s + K) ^ (n + 1)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

theorem norm_psiTower_le (e r B K θ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) {s : ℂ}
    {d1 d2 d3 L1 L2 L3 : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (h1 : d1 ≤ ‖s‖)
    (h2 : d2 ≤ ‖(B : ℂ) - s‖) (h3 : d3 ≤ ‖s + K‖) (hL1 : |Real.log ‖s‖| ≤ L1)
    (hL2 : |Real.log ‖(B : ℂ) - s‖| ≤ L2) (hL3 : |Real.log ‖s + K‖| ≤ L3) (k : ℕ) (hk : 1 ≤ k) :
    ‖psiTower e r B K θ k s‖ ≤ psiDm e r θ d1 d2 d3 L1 L2 L3 k := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    exact norm_psiTower_one_le e r B K θ he hr hL1 hL2 hL3
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    exact norm_psiTower_succ_le e r B K θ he hr hd1 hd2 hd3 h1 h2 h3 n

/-! ### 4. The V tower along a curve -/

/-- The derivative tower of `V ∘ γ`, `V = κ + Re Ψ̃`. -/
def vTower (e r B K θ κ : ℝ) (γ : ℕ → ℝ → ℂ) : ℕ → ℝ → ℝ :=
  reTower (psiTower e r B K θ) (fun x => κ + (psiT e r B K θ (γ 0 x)).re) γ

theorem hasDerivAt_psiTower_chain (e r B K θ : ℝ) {s : ℂ} (h : psiDom B K s) (k : ℕ)
    (hk1 : 1 ≤ k) : HasDerivAt (psiTower e r B K θ k) (psiTower e r B K θ (k + 1) s) s := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    exact hasDerivAt_psiTower_one e r B K θ ⟨h1, h2, h3⟩
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    exact hasDerivAt_psiTower_succ e r B K θ (slitPlane_ne_zero h1) (slitPlane_ne_zero h2)
      (slitPlane_ne_zero h3) n

theorem isTower_vTower (e r B K θ κ : ℝ) {γ : ℕ → ℝ → ℂ} {a rr : ℝ}
    (hγd : ∀ i < 5, ∀ x, HasDerivAt (γ i) (γ (i + 1) x) x) (hγc : Continuous (γ 5))
    (hdom : ∀ x ∈ Icc (a - rr) (a + rr), psiDom B K (γ 0 x)) :
    IsTower (vTower e r B K θ κ γ) a rr 5 := by
  refine isTower_reTower hγd hγc ?_ ?_ ?_
  · intro x hx k hk1 _
    exact hasDerivAt_psiTower_chain e r B K θ (hdom x hx) k hk1
  · intro x hx k hk1 _
    exact continuousAt_psiTower e r B K θ (hdom x hx) hk1
  · intro x hx
    have h1 : HasDerivAt (fun y => psiT e r B K θ (γ 0 y))
        (γ 1 x • psiTower e r B K θ 1 (γ 0 x)) x :=
      (hasDerivAt_psiT e r B K θ (hdom x hx)).scomp x (hγd 0 (by norm_num) x)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h1
    have h3 := h2.const_add κ
    refine h3.congr_deriv ?_
    simp [mul_comm]

theorem abs_vTower5_le (e r B K θ κ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) {γ : ℕ → ℝ → ℂ} {x : ℝ}
    {d1 d2 d3 L1 L2 L3 : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3)
    (h1 : d1 ≤ ‖γ 0 x‖) (h2 : d2 ≤ ‖(B : ℂ) - γ 0 x‖) (h3 : d3 ≤ ‖γ 0 x + K‖)
    (hL1 : |Real.log ‖γ 0 x‖| ≤ L1) (hL2 : |Real.log ‖(B : ℂ) - γ 0 x‖| ≤ L2)
    (hL3 : |Real.log ‖γ 0 x + K‖| ≤ L3) {Ym : ℕ → ℝ}
    (hY : ∀ i, 1 ≤ i → i ≤ 5 → ‖γ i x‖ ≤ Ym i) :
    |vTower e r B K θ κ γ 5 x| ≤ fdbBound (psiDm e r θ d1 d2 d3 L1 L2 L3) Ym :=
  abs_reTower5_le (fun k hk1 _ => norm_psiTower_le e r B K θ he hr hd1 hd2 hd3 h1 h2 h3 hL1 hL2
    hL3 k hk1) hY

/-! ### 5. Distances on a cell -/

theorem norm_curve_sub_le {γ γ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt γ (γ' x) x) {c r S : ℝ}
    (hS : ∀ x ∈ Icc (c - r) (c + r), ‖γ' x‖ ≤ S) {x : ℝ} (hx : x ∈ Icc (c - r) (c + r)) :
    ‖γ x - γ c‖ ≤ S * |x - c| := by
  have hc : c ∈ Icc (c - r) (c + r) := by
    have : 0 ≤ r := by linarith [hx.1, hx.2]
    exact ⟨by linarith, by linarith⟩
  have := (convex_Icc (c - r) (c + r)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hd y).hasDerivWithinAt) hS hc hx
  simpa [Real.norm_eq_abs] using this

/-- Pole distance on a cell: `‖γ c - p‖ - S r ≤ ‖γ x - p‖`. -/
theorem norm_sub_pole_ge {γ γ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt γ (γ' x) x) {c r S : ℝ}
    (hS : ∀ x ∈ Icc (c - r) (c + r), ‖γ' x‖ ≤ S) {x : ℝ} (hx : x ∈ Icc (c - r) (c + r))
    (p : ℂ) : ‖γ c - p‖ - S * r ≤ ‖γ x - p‖ := by
  have hb := norm_curve_sub_le hd hS hx
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx)
  have hxr : |x - c| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : ‖γ c - p‖ - ‖γ x - p‖ ≤ ‖γ x - γ c‖ := by
    have := norm_sub_norm_le (γ c - p) (γ x - p)
    rw [show (γ c - p) - (γ x - p) = -(γ x - γ c) by ring, norm_neg] at this
    exact this
  nlinarith [mul_le_mul_of_nonneg_left hxr hS0]

theorem jc_lipschitz (ζ ζ' : ℂ) : |jc ζ - jc ζ'| ≤ ‖ζ - ζ'‖ := by
  have h1 : |‖ζ - 1‖ - ‖ζ' - 1‖| ≤ ‖ζ - ζ'‖ := by
    have := abs_norm_sub_norm_le (ζ - 1) (ζ' - 1)
    simpa using this
  have h2 : |‖ζ + 1‖ - ‖ζ' + 1‖| ≤ ‖ζ - ζ'‖ := by
    have := abs_norm_sub_norm_le (ζ + 1) (ζ' + 1)
    simpa using this
  unfold jc
  have e : (‖ζ - 1‖ + ‖ζ + 1‖) / 2 - (‖ζ' - 1‖ + ‖ζ' + 1‖) / 2 =
      ((‖ζ - 1‖ - ‖ζ' - 1‖) + (‖ζ + 1‖ - ‖ζ' + 1‖)) / 2 := by ring
  rw [e, abs_div, abs_two]
  have := abs_add_le (‖ζ - 1‖ - ‖ζ' - 1‖) (‖ζ + 1‖ - ‖ζ' + 1‖)
  linarith

/-- The distance bound of W3(d) moves along a cell:
`|h|(c(ζ_c) - 1) - ‖s - s_c‖ ≤ |h|(c(ζ) - 1)`. -/
theorem dlo_on_cell {M h : ℂ} (hh : h ≠ 0) (s sc : ℂ) :
    ‖h‖ * (jc ((sc - M) / h) - 1) - ‖s - sc‖ ≤ ‖h‖ * (jc ((s - M) / h) - 1) := by
  have hl := jc_lipschitz ((sc - M) / h) ((s - M) / h)
  have e : (sc - M) / h - (s - M) / h = (sc - s) / h := by field_simp; ring
  rw [e, norm_div] at hl
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have h1 : ‖h‖ * |jc ((sc - M) / h) - jc ((s - M) / h)| ≤ ‖sc - s‖ := by
    calc _ ≤ ‖h‖ * (‖sc - s‖ / ‖h‖) := mul_le_mul_of_nonneg_left hl hn.le
      _ = ‖sc - s‖ := by field_simp
  rw [norm_sub_rev] at h1
  have h2 := le_abs_self (jc ((sc - M) / h) - jc ((s - M) / h))
  nlinarith [mul_le_mul_of_nonneg_left h2 hn.le]

/-- The W3(d) distance bound along a cell: if `‖γ'‖ ≤ S` on the cell and
`dlo ≤ |h|(c(ζ_c) - 1) - S r`, then `dlo ≤ |h|(c(ζ(γ x)) - 1)` for every `x` in the cell. -/
theorem dlo_cell {M h : ℂ} (hh : h ≠ 0) {γ γ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt γ (γ' x) x)
    {c r S dlo : ℝ} (hS : ∀ x ∈ Icc (c - r) (c + r), ‖γ' x‖ ≤ S)
    (hdlo : dlo ≤ ‖h‖ * (jc ((γ c - M) / h) - 1) - S * r) {x : ℝ} (hx : x ∈ Icc (c - r) (c + r)) :
    dlo ≤ ‖h‖ * (jc ((γ x - M) / h) - 1) := by
  have hb := norm_curve_sub_le hd hS hx
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx)
  have hxr : |x - c| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h2 := dlo_on_cell (M := M) hh (γ x) (γ c)
  have h3 : ‖γ x - γ c‖ ≤ S * r := hb.trans (mul_le_mul_of_nonneg_left hxr hS0)
  linarith

theorem one_lt_jc_of_dlo {M h s : ℂ} {dlo : ℝ} (hh : h ≠ 0) (hd0 : 0 < dlo)
    (hdlo : dlo ≤ ‖h‖ * (jc ((s - M) / h) - 1)) : 1 < jc ((s - M) / h) := by
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  by_contra hc
  push_neg at hc
  nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hc)]

theorem psiDom_of_im_pos (B K : ℝ) {s : ℂ} (h : 0 < s.im) : psiDom B K s :=
  ⟨Or.inr h.ne', Or.inr (by simpa using h.ne'), Or.inr (by simpa using h.ne')⟩

theorem psiDom_of_re_pos (B K : ℝ) {s : ℂ} (h1 : 0 < s.re) (h2 : 0 < B - s.re)
    (h3 : 0 < s.re + K) : psiDom B K s :=
  ⟨Or.inl h1, Or.inl (by simpa using h2), Or.inl (by simpa using h3)⟩

/-! ### 6. The wedge field and the cell soundness theorem (LD18) -/

/-- The tower of the field `V + w₁ U₁ + w₂ U₂` (Lai: `w₁ = w₂ = -2`, `U₁` the own potential of
the arm, `U₂` the cross potential). -/
def wedgeTower (fV f₁ f₂ : ℕ → ℝ → ℝ) (w₁ w₂ : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  fV j x + w₁ * f₁ j x + w₂ * f₂ j x

theorem isTower_wedgeTower {fV f₁ f₂ : ℕ → ℝ → ℝ} {c r : ℝ} (w₁ w₂ : ℝ) (hV : IsTower fV c r 5)
    (h₁ : IsTower f₁ c r 5) (h₂ : IsTower f₂ c r 5) :
    IsTower (wedgeTower fV f₁ f₂ w₁ w₂) c r 5 :=
  (hV.add (h₁.smul w₁)).add (h₂.smul w₂)

theorem abs_wedgeTower5_le {fV f₁ f₂ : ℕ → ℝ → ℝ} {w₁ w₂ x TV T1 T2 : ℝ}
    (hV : |fV 5 x| ≤ TV) (h₁ : |f₁ 5 x| ≤ T1) (h₂ : |f₂ 5 x| ≤ T2) :
    |wedgeTower fV f₁ f₂ w₁ w₂ 5 x| ≤ TV + |w₁| * T1 + |w₂| * T2 := by
  unfold wedgeTower
  have a1 : |w₁ * f₁ 5 x| ≤ |w₁| * T1 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)
  have a2 : |w₂ * f₂ 5 x| ≤ |w₂| * T2 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h₂ (abs_nonneg _)
  calc _ ≤ |fV 5 x + w₁ * f₁ 5 x| + |w₂ * f₂ 5 x| := abs_add_le _ _
    _ ≤ |fV 5 x| + |w₁ * f₁ 5 x| + |w₂ * f₂ 5 x| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith

/-- The rational Taylor-model bound of an order-5 cell: `tq j ± te j` enclose the tower at the
centre (`j ≤ 4`), and `TR` bounds `|f 5|` on the cell. -/
def wedgeCellUB (tq te : ℕ → ℚ) (TR r : ℚ) : ℚ :=
  tmUBQ (tq 0 + te 0) (tq 1 - te 1) (tq 1 + te 1) ((tq 2 + te 2) / 2) r
    [(|tq 3| + te 3) / 6, (|tq 4| + te 4) / 24] (TR / 120)

theorem wedgeCell_sound {f : ℕ → ℝ → ℝ} {c r : ℝ} (hf : IsTower f c r 5) {tq te : ℕ → ℚ}
    {TR rq : ℚ} (hrq : (rq : ℝ) = r) (hTenc : ∀ j ≤ 4, |f j c - (tq j : ℝ)| ≤ (te j : ℝ))
    (hTR : ∀ x ∈ Icc (c - r) (c + r), |f 5 x| ≤ (TR : ℝ)) :
    ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ ((wedgeCellUB tq te TR rq : ℚ) : ℝ) := by
  have hb : ∀ j, 3 ≤ j → j ≤ 4 → |f j c| ≤ |(tq j : ℝ)| + (te j : ℝ) := by
    intro j hj3 hj4
    have h := hTenc j hj4
    have := abs_sub_abs_le_abs_sub (f j c) (tq j : ℝ)
    linarith
  have key := taylor_cell_ub_rat (f := f) (c := c) (r := r)
    [(|tq 3| + te 3) / 6, (|tq 4| + te 4) / 24] hf (A0 := tq 0 + te 0) (l1 := tq 1 - te 1)
    (u1 := tq 1 + te 1) (A2 := (tq 2 + te 2) / 2) (BM := TR / 120)
    (by have := (abs_le.mp (hTenc 0 (by norm_num))).2; push_cast; linarith)
    (by have := (abs_le.mp (hTenc 1 (by norm_num))).1; push_cast; linarith)
    (by have := (abs_le.mp (hTenc 1 (by norm_num))).2; push_cast; linarith)
    (by have := (abs_le.mp (hTenc 2 (by norm_num))).2; push_cast; linarith)
    (by
      intro i hi
      have hi2 : i < 2 := by simpa using hi
      interval_cases i
      · have := hb 3 le_rfl (by norm_num)
        simp only [List.getD_cons_zero]
        push_cast
        norm_num [Nat.factorial]
        linarith
      · have := hb 4 (by norm_num) le_rfl
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        push_cast
        norm_num [Nat.factorial]
        linarith)
    (fun y hy => by
      have := hTR y hy
      simp only [List.length_cons, List.length_nil]
      norm_num [Nat.factorial]
      push_cast
      linarith)
    rq hrq
  exact key

/-- The Boolean cell check: the Taylor-model bound is at most `ℓ`. -/
def wedgeCellOk (tq te : ℕ → ℚ) (TR r ℓ : ℚ) : Bool := decide (wedgeCellUB tq te TR r ≤ ℓ)

theorem wedgeCellOk_sound {f : ℕ → ℝ → ℝ} {c r : ℝ} (hf : IsTower f c r 5) {tq te : ℕ → ℚ}
    {TR rq ℓ : ℚ} (hrq : (rq : ℝ) = r) (hTenc : ∀ j ≤ 4, |f j c - (tq j : ℝ)| ≤ (te j : ℝ))
    (hTR : ∀ x ∈ Icc (c - r) (c + r), |f 5 x| ≤ (TR : ℝ))
    (hok : wedgeCellOk tq te TR rq ℓ = true) : ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ (ℓ : ℝ) := by
  intro x hx
  have h1 := wedgeCell_sound hf hrq hTenc hTR x hx
  have h2 : wedgeCellUB tq te TR rq ≤ ℓ := by simpa [wedgeCellOk] using hok
  exact h1.trans (by exact_mod_cast h2)

/-! ### 7. The field `V` and its identification with `κ + Re Ψ̃` (W1(i)) -/

theorem log_neg_of_im_neg {z : ℂ} (h : z.im < 0) : Complex.log (-z) = Complex.log z + Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]

/-- The scaled weight field `V = κ + e ∫₀^B log |s - x| dx - r ∫₀^K log |s + x| dx - θ |Im s|`,
`κ = r (K log K - K) - e (B log B - B)`. -/
def vField (e r B K θ : ℝ) (s : ℂ) : ℝ :=
  (r * (K * Real.log K - K) - e * (B * Real.log B - B))
    + e * (∫ x in (0 : ℝ)..B, Real.log ‖s - x‖) - r * (∫ x in (0 : ℝ)..K, Real.log ‖s + x‖)
    - θ * |s.im|

theorem integral_log_norm_sub {s : ℂ} (hs : 0 < s.im) (b : ℝ) :
    ∫ x in (0 : ℝ)..b, Real.log ‖s - x‖ =
      (-((s - b) * Complex.log (s - b) - (s - b))).re
        - (-((s - 0) * Complex.log (s - 0) - (s - 0))).re := by
  have hslit : ∀ w : ℂ, w.im = s.im → w ∈ slitPlane := fun w hw => Or.inr (by rw [hw]; exact hs.ne')
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (-((s - (y : ℂ)) * Complex.log (s - (y : ℂ))
      - (s - (y : ℂ)))).re) (Real.log ‖s - x‖) x := by
    intro x
    have hsl : s - (x : ℂ) ∈ slitPlane := hslit _ (by simp)
    have hl : HasDerivAt (fun w : ℂ => Complex.log (s - w)) ((0 - 1) / (s - (x : ℂ))) (x : ℂ) :=
      ((hasDerivAt_const (x : ℂ) s).sub (hasDerivAt_id (x : ℂ))).clog hsl
    have hq : HasDerivAt (fun w : ℂ => (s - w)) (0 - 1) (x : ℂ) :=
      (hasDerivAt_const (x : ℂ) s).sub (hasDerivAt_id (x : ℂ))
    have hg := ((hq.mul hl).sub hq).neg
    have hg2 := hg.comp_ofReal
    have hg3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hg2
    refine hg3.congr_deriv ?_
    have hne : s - (x : ℂ) ≠ 0 := slitPlane_ne_zero hsl
    have : -((0 - 1) * Complex.log (s - x) + (s - x) * ((0 - 1) / (s - x)) - (0 - 1)) =
        Complex.log (s - x) := by field_simp; ring
    simp only [Complex.reCLM_apply, Pi.mul_apply] at *
    rw [show (-(((0 : ℂ) - 1) * Complex.log (s - x) + (s - x) * (((0 : ℂ) - 1) / (s - x))
      - ((0 : ℂ) - 1))) = Complex.log (s - x) from this, Complex.log_re]
  have hc : Continuous fun x : ℝ => Real.log ‖s - (x : ℂ)‖ := by
    refine Continuous.log (by fun_prop) (fun x => ?_)
    exact norm_ne_zero_iff.mpr (slitPlane_ne_zero (hslit _ (by simp)))
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := b)
    (fun x _ => hd x) (hc.intervalIntegrable _ _)
  simpa using this

theorem integral_log_norm_add {s : ℂ} (hs : 0 < s.im) (b : ℝ) :
    ∫ x in (0 : ℝ)..b, Real.log ‖s + x‖ =
      ((s + b) * Complex.log (s + b) - (s + b)).re
        - ((s + 0) * Complex.log (s + 0) - (s + 0)).re := by
  have hslit : ∀ w : ℂ, w.im = s.im → w ∈ slitPlane := fun w hw => Or.inr (by rw [hw]; exact hs.ne')
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ((s + (y : ℂ)) * Complex.log (s + (y : ℂ))
      - (s + (y : ℂ))).re) (Real.log ‖s + x‖) x := by
    intro x
    have hsl : s + (x : ℂ) ∈ slitPlane := hslit _ (by simp)
    have hq : HasDerivAt (fun w : ℂ => (s + w)) (0 + 1) (x : ℂ) :=
      (hasDerivAt_const (x : ℂ) s).add (hasDerivAt_id (x : ℂ))
    have hl : HasDerivAt (fun w : ℂ => Complex.log (s + w)) ((0 + 1) / (s + (x : ℂ))) (x : ℂ) :=
      hq.clog hsl
    have hg := (hq.mul hl).sub hq
    have hg2 := hg.comp_ofReal
    have hg3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hg2
    refine hg3.congr_deriv ?_
    have hne : s + (x : ℂ) ≠ 0 := slitPlane_ne_zero hsl
    have : ((0 + 1) * Complex.log (s + x) + (s + x) * ((0 + 1) / (s + x)) - (0 + 1)) =
        Complex.log (s + x) := by field_simp; ring
    simp only [Complex.reCLM_apply, Pi.mul_apply]
    rw [this, Complex.log_re]
  have hc : Continuous fun x : ℝ => Real.log ‖s + (x : ℂ)‖ := by
    refine Continuous.log (by fun_prop) (fun x => ?_)
    exact norm_ne_zero_iff.mpr (slitPlane_ne_zero (hslit _ (by simp)))
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := b)
    (fun x _ => hd x) (hc.intervalIntegrable _ _)
  simpa using this

/-- **W1(i)**: for `Im s > 0`, `V = κ + Re Ψ̃`. -/
theorem vField_eq_psi (e r B K θ : ℝ) {s : ℂ} (hs : 0 < s.im) :
    vField e r B K θ s =
      (r * (K * Real.log K - K) - e * (B * Real.log B - B)) + (psiT e r B K θ s).re := by
  unfold vField
  rw [integral_log_norm_sub hs B, integral_log_norm_add hs K, abs_of_pos hs]
  have hneg : s - (B : ℂ) = -((B : ℂ) - s) := by ring
  have him : ((B : ℂ) - s).im < 0 := by simpa using hs
  have hlog : Complex.log (s - B) = Complex.log ((B : ℂ) - s) + Real.pi * I := by
    rw [hneg]; exact log_neg_of_im_neg him
  have key : psiT e r B K θ s =
      (e : ℂ) * ((-((s - B) * Complex.log (s - B) - (s - B)))
        - (-(s * Complex.log s - s)))
      - (r : ℂ) * (((s + K) * Complex.log (s + K) - (s + K)) - (s * Complex.log s - s))
      + (θ : ℂ) * I * s := by
    unfold psiT
    rw [hlog]
    ring
  simp only [sub_zero, add_zero]
  rw [key]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.re_ofReal_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im,
    Complex.sub_im, Complex.neg_im, Complex.mul_im]
  ring

end

end CatalanCore.Decay.ComplexTaylor
