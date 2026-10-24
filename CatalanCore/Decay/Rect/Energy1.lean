module

public import CatalanCore.Decay.Rect.NodesB
public import CatalanCore.Decay.Rect.LemmaBG

@[expose] public section

/-!
# Two-family energy step, part 1 (WP-H2-core)

* `Esc` and `neg_log_cexpr_scaled` : `-log ‖C(z,w)‖² = Esc(z/r, w/r) + 2k log r` (scale-`r` form).
* `Esc_decomp` : the node-completion identity (legacy `Hsc_decomp`) in the form used below.
* `Usig_ge` : `U^σ_ρ(s) ≥ -(‖s‖ + R_c + ρ)` for a positive probability measure on `‖c‖ ≤ R_c`.
* `free_norm_le` : free points (atoms / rays) satisfy `‖z‖ ≤ T + xs + 2 |Im z|` (`N0 + n0off ≤ T`).
* `sumS_X_le`, `sumS_Y_le` : [R1] for free points, over all `N = r + m` nodes.
* `sumR_X_le`, `sumR_Y_le` : [R3] for a common node.
-/

open Finset
open CatalanLambda.Decay

namespace CatalanCore.Decay

variable {sl : ℝ}

/-- The energy of a point family `σ` against a node family `ω`. -/
noncomputable def Esc {k : ℕ} (σ ω : Fin k → ℂ) : ℝ :=
  ∑ l, ∑ l', elog (σ l) (σ l') + ∑ i, ∑ i', elog (ω i) (ω i')
    - 2 * ∑ l, ∑ i, elog (σ l) (ω i)

theorem neg_log_cexpr_scaled {k r : ℕ} (hr : 0 < r) (z w : Fin k → ℂ)
    (hzi : Function.Injective z) (hwi : Function.Injective w) (hzw : ∀ l i, z l ≠ w i) :
    -Real.log (‖cexpr z w‖ ^ 2)
      = Esc (fun l => z l / r) (fun i => w i / r) + 2 * k * Real.log r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h0 := neg_log_cexpr_sq z w hzi hwi hzw
  set σ : Fin k → ℂ := fun l => z l / r with hσ
  set ω : Fin k → ℂ := fun i => w i / r with hω
  have hzσ : ∀ l, z l = (r : ℂ) * σ l := fun l => by simp only [hσ]; field_simp
  have hwω : ∀ i, w i = (r : ℂ) * ω i := fun i => by simp only [hω]; field_simp
  have hσi : Function.Injective σ := fun a b h => hzi (by rw [hzσ a, hzσ b, h])
  have hωi : Function.Injective ω := fun a b h => hwi (by rw [hwω a, hwω b, h])
  have hσω : ∀ l i, σ l ≠ ω i := fun l i e => hzw l i (by rw [hzσ l, hwω i, e])
  have S1 : ∑ l, ∑ l', elog (z l) (z l')
      = ∑ l, ∑ l', elog (σ l) (σ l') - k * (k - 1) * Real.log r := by
    have : ∀ l l', elog (z l) (z l') = elog (σ l) (σ l') - (if l = l' then 0 else Real.log r) := by
      intro l l'
      rw [hzσ l, hzσ l']
      have := elog_scale (c := (r : ℝ)) hr' (σ l) (σ l')
      simp only [Complex.ofReal_natCast] at this
      rw [this]
      congr 2
      simp only [hσi.eq_iff]
    simp_rw [this, Finset.sum_sub_distrib]
    rw [CatalanCore.Decay.sum_offdiag_const]
  have S2 : ∑ i, ∑ i', elog (w i) (w i')
      = ∑ i, ∑ i', elog (ω i) (ω i') - k * (k - 1) * Real.log r := by
    have : ∀ i i', elog (w i) (w i') = elog (ω i) (ω i') - (if i = i' then 0 else Real.log r) := by
      intro i i'
      rw [hwω i, hwω i']
      have := elog_scale (c := (r : ℝ)) hr' (ω i) (ω i')
      simp only [Complex.ofReal_natCast] at this
      rw [this]
      congr 2
      simp only [hωi.eq_iff]
    simp_rw [this, Finset.sum_sub_distrib]
    rw [CatalanCore.Decay.sum_offdiag_const]
  have S3 : ∑ l, ∑ i, elog (z l) (w i) = ∑ l, ∑ i, elog (σ l) (ω i) - k * k * Real.log r := by
    have : ∀ l i, elog (z l) (w i) = elog (σ l) (ω i) - Real.log r := by
      intro l i
      rw [hzσ l, hwω i]
      have := elog_scale (c := (r : ℝ)) hr' (σ l) (ω i)
      simp only [Complex.ofReal_natCast] at this
      rw [this, if_neg (hσω _ _)]
    simp_rw [this, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [h0, S1, S2, S3]
  unfold Esc
  ring

theorem Esc_decomp {k N : ℕ} (σ : Fin k → ℂ) (τ : Fin N → ℂ) (s : Fin k → Fin N)
    (hs : Function.Injective s) :
    Esc σ (fun i => τ (s i))
      = (∑ l, ∑ l', elog (σ l) (σ l') + 2 * ∑ l, ∑ b, rmask s b * elog (σ l) (τ b)
          + ∑ b, ∑ b', rmask s b * rmask s b' * elog (τ b) (τ b'))
        + ∑ b, ∑ b', elog (τ b) (τ b')
        - 2 * ∑ l, ∑ b, elog (σ l) (τ b)
        - 2 * ∑ b, ∑ b', rmask s b * elog (τ b) (τ b') := by
  unfold Esc
  exact Hsc_decomp σ τ s hs

/-- Lower bound for `U^σ_ρ`. -/
theorem Usig_ge {K : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (c : Fin K → ℂ) (wt : Fin K → ℝ)
    (hw0 : ∀ k, 0 ≤ wt k) (hw1 : ∑ k, wt k = 1) {Rc : ℝ} (hc : ∀ k, ‖c k‖ ≤ Rc) (s : ℂ) :
    -(‖s‖ + Rc + ρ) ≤ Usig ρ c wt s := by
  have hRc : 0 ≤ Rc := by
    by_cases hK : Nonempty (Fin K)
    · obtain ⟨k⟩ := hK; exact (norm_nonneg _).trans (hc k)
    · exfalso; simp at hK; subst hK; simp at hw1
  set X : ℝ := ‖s‖ + Rc + ρ with hX
  have hX0 : 0 < X := by have := norm_nonneg s; positivity
  have key : ∀ k, -X ≤ krho ρ s (c k) := by
    intro k
    unfold krho
    have h1 : ‖s - c k‖ ≤ ‖s‖ + Rc := (norm_sub_le _ _).trans (by linarith [hc k])
    have h2 : ‖s - c k‖ ^ 2 + ρ ^ 2 ≤ X ^ 2 := by
      have := norm_nonneg (s - c k)
      nlinarith [norm_nonneg s]
    have h3 : Real.log (‖s - c k‖ ^ 2 + ρ ^ 2) ≤ Real.log (X ^ 2) :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have h4 := Real.log_le_sub_one_of_pos hX0
    push_cast at h3
    linarith
  unfold Usig
  calc -X = ∑ k, wt k * (-X) := by rw [← Finset.sum_mul, hw1]; ring
    _ ≤ _ := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (key k) (hw0 k))

/-- Free points (atoms and ray points) are controlled by their imaginary part. -/
theorem free_norm_le {Fr : Frame} (hsl : 1 ≤ sl) (hxs : (0 : ℝ) ≤ Fr.xs)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    {N0 : ℕ} {T : ℝ} (hT : (N0 : ℝ) + Fr.n0off ≤ T) {z : ℂ}
    (hz : Fr.IsAtom N0 z ∨ Fr.IsRay sl N0 z) :
    ‖z‖ ≤ T + Fr.xs + 2 * |z.im| := by
  rcases hz with ha | hr
  · obtain ⟨p, hp, rfl⟩ := ha
    have hle := Frame.atom_le hAR hp
    have hmu := Fr.mu_pos p.2
    have hm : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
    simp only [Frame.atomPos, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero,
      mul_zero, add_zero]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨u, hu, θ, hθ, rfl⟩ := hr
    have hs10 : (0 : ℝ) < Real.sqrt (1 + sl ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hs6 : Real.sqrt (1 + sl ^ 2) ≤ 2 * sl := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hsin : (1 : ℝ) / 2 ≤ |Real.sin θ| := by
      have : |Real.sin θ| = sl / Real.sqrt (1 + sl ^ 2) := by
        rcases hθ with e | e
        · rw [e, sin_phiS, abs_of_pos (div_pos (by linarith) hs10)]
        · rw [e, Real.sin_neg, abs_neg, sin_phiS, abs_of_pos (div_pos (by linarith) hs10)]
      rw [this, le_div_iff₀ hs10]
      linarith
    have him : |(rayPt (Fr.xstar N0) θ u).im| = u * |Real.sin θ| := by
      rw [CatalanLambda.Decay.rayPt_im, abs_mul, abs_of_pos hu]
    have hnorm : ‖rayPt (Fr.xstar N0) θ u‖ ≤ |Fr.xstar N0| + u := by
      unfold rayPt
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg hu.le]
    have hx : |Fr.xstar N0| ≤ T + Fr.xs := by
      unfold Frame.xstar
      rw [abs_of_nonpos (by have : (0 : ℝ) ≤ N0 := Nat.cast_nonneg _; linarith)]
      have : (0 : ℝ) ≤ Fr.n0off := Nat.cast_nonneg _
      linarith
    rw [him] at *
    have : u ≤ 2 * (u * |Real.sin θ|) := by nlinarith
    linarith

/-! ### Node sums over the whole configuration -/

section Bounds

theorem sumS_X_le {r m : ℕ} {σ : ℂ} (hσ : σ.re < 0) (hr : 0 < r) (hm : 0 < m) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : L ≤ 2 * m / r) :
    ∑ b : Fin (r + m), elog σ (nodeC r (xnode r b))
      ≤ (r : ℝ) * (Utau σ + Uex L σ) + Real.log (1 + 1 / ‖σ‖) + Real.log (1 + 2 * m / r) := by
  rw [CatalanCore.Decay.fin_sum_range (fun b => elog σ (nodeC r (xnode r b))),
    sum_range_xnode r m (fun p => elog σ (nodeC r p))]
  have hA := riemann_node_sum hr hσ
  have hB := sumX_free_le hσ hr hm hL0 hL
  linarith

theorem sumS_Y_le {r m : ℕ} {σ : ℂ} (hσ : σ.re < 0) (hr : 0 < r) (hm : 0 < m) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : L ≤ 2 * m / r) :
    ∑ b : Fin (r + m), elog σ (nodeC r (ynode r b))
      ≤ (r : ℝ) * (Utau σ + Uex L σ) + Real.log (1 + 1 / ‖σ‖) + Real.log (1 + 2 * m / r) := by
  rw [CatalanCore.Decay.fin_sum_range (fun b => elog σ (nodeC r (ynode r b))),
    sum_range_ynode r m (fun p => elog σ (nodeC r p))]
  have hA := riemann_node_sum hr hσ
  have hB := sumX_free_le hσ hr hm hL0 hL
  have hC := sumY_le_sumX (σ := σ) (by linarith) hr m
  linarith

theorem sumR_X_leW {r m b : ℕ} {w : ℝ} (hb : b < r) (hr : 0 < r) (hm : 0 < m) {L : ℝ} (hL0 : 0 < L)
    (hL : L ≤ 2 * m / r) (hL2 : 2 * (m : ℝ) / r ≤ L + 2 * w / r) :
    ∑ b' : Fin (r + m), elog (nodeC r b) (nodeC r (xnode r b'))
      ≤ (r : ℝ) * (Utau (nodeC r b) + Uex L (nodeC r b))
        + (Real.log (1 + 2 * m) + w * |Real.log L|) := by
  rw [CatalanCore.Decay.fin_sum_range (fun b' => elog (nodeC r b) (nodeC r (xnode r b'))),
    sum_range_xnode r m (fun p => elog (nodeC r b) (nodeC r p))]
  have hA := node_sum_le hr b hb
  have hB := sumX_node_leW hr hm hb hL0 hL hL2
  linarith

theorem sumR_Y_leW {r m b : ℕ} {w : ℝ} (hb : b < r) (hr : 0 < r) (hm : 0 < m) {L : ℝ} (hL0 : 0 < L)
    (hL : L ≤ 2 * m / r) (hL2 : 2 * (m : ℝ) / r ≤ L + 2 * w / r) :
    ∑ b' : Fin (r + m), elog (nodeC r b) (nodeC r (ynode r b'))
      ≤ (r : ℝ) * (Utau (nodeC r b) + Uex L (nodeC r b))
        + (Real.log (1 + 2 * m) + w * |Real.log L|) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [CatalanCore.Decay.fin_sum_range (fun b' => elog (nodeC r b) (nodeC r (ynode r b'))),
    sum_range_ynode r m (fun p => elog (nodeC r b) (nodeC r p))]
  have hA := node_sum_le hr b hb
  have hB := sumX_node_leW hr hm hb hL0 hL hL2
  have hσ1 : (nodeC r b).re < 1 := by
    have : (nodeC r b).re = (b : ℝ) / r := by simp [nodeC]
    rw [this, div_lt_one hr']; exact_mod_cast hb
  have hC := sumY_le_sumX (σ := nodeC r b) hσ1 hr m
  linarith

/-- The window-`1` case of `sumR_X_leW`. -/
theorem sumR_X_le {r m b : ℕ} (hb : b < r) (hr : 0 < r) (hm : 0 < m) {L : ℝ} (hL0 : 0 < L)
    (hL : L ≤ 2 * m / r) (hL2 : 2 * (m : ℝ) / r ≤ L + 2 / r) :
    ∑ b' : Fin (r + m), elog (nodeC r b) (nodeC r (xnode r b'))
      ≤ (r : ℝ) * (Utau (nodeC r b) + Uex L (nodeC r b))
        + (Real.log (1 + 2 * m) + |Real.log L|) := by
  simpa using sumR_X_leW (w := 1) hb hr hm hL0 hL (by simpa using hL2)

/-- The window-`1` case of `sumR_Y_leW`. -/
theorem sumR_Y_le {r m b : ℕ} (hb : b < r) (hr : 0 < r) (hm : 0 < m) {L : ℝ} (hL0 : 0 < L)
    (hL : L ≤ 2 * m / r) (hL2 : 2 * (m : ℝ) / r ≤ L + 2 / r) :
    ∑ b' : Fin (r + m), elog (nodeC r b) (nodeC r (ynode r b'))
      ≤ (r : ℝ) * (Utau (nodeC r b) + Uex L (nodeC r b))
        + (Real.log (1 + 2 * m) + |Real.log L|) := by
  simpa using sumR_Y_leW (w := 1) hb hr hm hL0 hL (by simpa using hL2)

end Bounds

end CatalanCore.Decay
