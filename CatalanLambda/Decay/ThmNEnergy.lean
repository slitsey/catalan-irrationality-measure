import CatalanLambda.Decay.ThmNLog

/-!
# Theorem N_ρ, stage 2: the `k_ρ` energy of the free points together with the removed nodes
-/

open Finset

namespace CatalanLambda.Decay

/-- `U_ρ^σ(z) = ∑_k m_k k_ρ(z, c_k)`. -/
noncomputable def Usig {K : ℕ} (ρ : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) (z : ℂ) : ℝ :=
  ∑ k, m k * krho ρ z (c k)

/-- `I_ρ(σ) = ∑ m_k m_l k_ρ(c_k, c_l)`. -/
noncomputable def Irho {K : ℕ} (ρ : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) : ℝ :=
  ∑ k, ∑ l, m k * m l * krho ρ (c k) (c l)

/-- Lemma K0 (distinct points). -/
lemma krho_le_elog {ρ : ℝ} (hρ : 0 < ρ) {x y : ℂ} (hxy : x ≠ y) : krho ρ x y ≤ elog x y := by
  unfold krho elog
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have : Real.log (‖x - y‖ ^ 2) ≤ Real.log (‖x - y‖ ^ 2 + ρ ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ρ])
  rw [Real.log_pow] at this
  push_cast at this
  linarith

/-- **Weighted Corollary K′.** -/
theorem krho_energy_w {ι : Type*} [Fintype ι] {K : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (X : ι → ℂ)
    (q : ι → ℝ) (hq : ∑ i, q i = 1) (c : Fin K → ℂ) (m : Fin K → ℝ) (hm : ∑ k, m k = 1) :
    2 * ∑ i, q i * Usig ρ c m (X i) - Irho ρ c m ≤ ∑ i, ∑ j, q i * q j * krho ρ (X i) (X j) := by
  set p : ι ⊕ Fin K → ℂ := Sum.elim X c with hp
  set w : ι ⊕ Fin K → ℝ := Sum.elim q (fun k => - m k) with hw
  have hq0 : ∑ i, w i = 0 := by
    rw [Fintype.sum_sum_type]; simp [hw, hq, hm]
  have key := krho_sum_nonneg hρ p w hq0
  simp only [Fintype.sum_sum_type, hp, hw, Sum.elim_inl, Sum.elim_inr] at key
  have hcross : ∑ k, ∑ i, -m k * q i * krho ρ (c k) (X i)
      = ∑ i, ∑ k, q i * -m k * krho ρ (X i) (c k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [krho_comm]; ring
  have e2 : ∑ i, ∑ k, q i * -m k * krho ρ (X i) (c k) = -(∑ i, q i * Usig ρ c m (X i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold Usig
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have e4 : ∑ k, ∑ l, -m k * -m l * krho ρ (c k) (c l) = Irho ρ c m := by
    unfold Irho
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at key
  rw [hcross, e2, e4] at key
  linarith

/-- Pairwise bound for the quadratic form: diagonal costs `-log ρ`. -/
lemma krho_quad_le {ι : Type*} [Fintype ι] {ρ : ℝ} (hρ : 0 < ρ) (p : ι → ℂ)
    (hp : Function.Injective p) (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    ∑ i, ∑ j, q i * q j * krho ρ (p i) (p j)
      ≤ ∑ i, ∑ j, q i * q j * elog (p i) (p j) + (-Real.log ρ) * ∑ i, q i ^ 2 := by
  classical
  have h1 : ∀ i j, q i * q j * krho ρ (p i) (p j)
      ≤ q i * q j * elog (p i) (p j) + (if i = j then (-Real.log ρ) * q i ^ 2 else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, krho_self hρ, elog_self]; nlinarith
    · rw [if_neg hij, add_zero]
      exact mul_le_mul_of_nonneg_left (krho_le_elog hρ (fun e => hij (hp e))) (mul_nonneg (hq i) (hq j))
  calc _ ≤ ∑ i, ∑ j, (q i * q j * elog (p i) (p j) + (if i = j then (-Real.log ρ) * q i ^ 2 else 0)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h1 i j))
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.mul_sum]

/-- **[B]**: the energy of the `h` support points (free points and removed nodes), through `k_ρ`. -/
theorem energy_B {k h K : ℕ} (hh : 0 < h) {ρ : ℝ} (hρ : 0 < ρ) (c : Fin K → ℂ) (m : Fin K → ℝ)
    (hm : ∑ i, m i = 1) (σ : Fin k → ℂ) (τ : Fin h → ℂ) (r : Fin h → ℝ)
    (hr : ∀ b, r b = 0 ∨ r b = 1) (hrs : ∑ b, r b = (h : ℝ) - k)
    (hp : Function.Injective (Sum.elim σ τ)) :
    2 * h * (∑ l, Usig ρ c m (σ l) + ∑ b, r b * Usig ρ c m (τ b)) - (h : ℝ) ^ 2 * Irho ρ c m
        + h * Real.log ρ
      ≤ ∑ l, ∑ l', elog (σ l) (σ l') + 2 * ∑ l, ∑ b, r b * elog (σ l) (τ b)
        + ∑ b, ∑ b', r b * r b' * elog (τ b) (τ b') := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hr0 : ∀ b, 0 ≤ r b := fun b => by rcases hr b with e | e <;> rw [e] <;> norm_num
  have hr2 : ∀ b, r b ^ 2 = r b := fun b => by rcases hr b with e | e <;> rw [e] <;> norm_num
  set q : Fin k ⊕ Fin h → ℝ := Sum.elim (fun _ => 1 / (h : ℝ)) (fun b => r b / h) with hq
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i; rcases i with l | b
    · simp [hq]
    · simp [hq]; exact div_nonneg (hr0 b) hh'.le
  have hsum : ∑ i, q i = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [hq, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.sum_div, hrs]
    field_simp; ring
  have h1 := krho_energy_w hρ (Sum.elim σ τ) q hsum c m hm
  have h2 := krho_quad_le hρ (Sum.elim σ τ) hp q hq0
  have hq2 : ∑ i, q i ^ 2 = 1 / h := by
    rw [Fintype.sum_sum_type]
    simp only [hq, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, div_pow, hr2, ← Finset.sum_div, hrs]
    field_simp; ring
  have hU : ∑ i, q i * Usig ρ c m (Sum.elim σ τ i)
      = (1 / h) * (∑ l, Usig ρ c m (σ l) + ∑ b, r b * Usig ρ c m (τ b)) := by
    rw [Fintype.sum_sum_type]
    simp only [hq, Sum.elim_inl, Sum.elim_inr, mul_add]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  have hE : ∑ i, ∑ j, q i * q j * elog (Sum.elim σ τ i) (Sum.elim σ τ j)
      = (1 / (h : ℝ)) ^ 2 * (∑ l, ∑ l', elog (σ l) (σ l') + 2 * ∑ l, ∑ b, r b * elog (σ l) (τ b)
        + ∑ b, ∑ b', r b * r b' * elog (τ b) (τ b')) := by
    simp only [Fintype.sum_sum_type, hq, Sum.elim_inl, Sum.elim_inr]
    simp only [Finset.sum_add_distrib]
    have b1 : ∑ l, ∑ l', 1 / (h : ℝ) * (1 / (h : ℝ)) * elog (σ l) (σ l')
        = (1 / (h : ℝ)) ^ 2 * ∑ l, ∑ l', elog (σ l) (σ l') := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l' _ => ?_); ring
    have b2 : ∑ l, ∑ b, 1 / (h : ℝ) * (r b / h) * elog (σ l) (τ b)
        = (1 / (h : ℝ)) ^ 2 * ∑ l, ∑ b, r b * elog (σ l) (τ b) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l' _ => ?_); ring
    have b3 : ∑ b, ∑ l, r b / h * (1 / (h : ℝ)) * elog (τ b) (σ l)
        = (1 / (h : ℝ)) ^ 2 * ∑ l, ∑ b, r b * elog (σ l) (τ b) := by
      rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [elog_comm]; ring
    have b4 : ∑ b, ∑ b', r b / h * (r b' / h) * elog (τ b) (τ b')
        = (1 / (h : ℝ)) ^ 2 * ∑ b, ∑ b', r b * r b' * elog (τ b) (τ b') := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l' _ => ?_); ring
    rw [b1, b2, b3, b4]; ring
  have hI := h1.trans h2
  rw [hU, hE, hq2] at hI
  have key : (h : ℝ) ^ 2 * (2 * (1 / h * (∑ l, Usig ρ c m (σ l) + ∑ b, r b * Usig ρ c m (τ b)))
      - Irho ρ c m) ≤ (h : ℝ) ^ 2 * ((1 / (h : ℝ)) ^ 2 * (∑ l, ∑ l', elog (σ l) (σ l')
        + 2 * ∑ l, ∑ b, r b * elog (σ l) (τ b) + ∑ b, ∑ b', r b * r b' * elog (τ b) (τ b'))
        + (-Real.log ρ) * (1 / h)) := mul_le_mul_of_nonneg_left hI (by positivity)
  have e1 : (h : ℝ) ^ 2 * (2 * (1 / h * (∑ l, Usig ρ c m (σ l) + ∑ b, r b * Usig ρ c m (τ b)))
      - Irho ρ c m) = 2 * h * (∑ l, Usig ρ c m (σ l) + ∑ b, r b * Usig ρ c m (τ b))
        - (h : ℝ) ^ 2 * Irho ρ c m := by field_simp
  have e2 : (h : ℝ) ^ 2 * ((1 / (h : ℝ)) ^ 2 * (∑ l, ∑ l', elog (σ l) (σ l')
        + 2 * ∑ l, ∑ b, r b * elog (σ l) (τ b) + ∑ b, ∑ b', r b * r b' * elog (τ b) (τ b'))
        + (-Real.log ρ) * (1 / h)) = (∑ l, ∑ l', elog (σ l) (σ l')
        + 2 * ∑ l, ∑ b, r b * elog (σ l) (τ b) + ∑ b, ∑ b', r b * r b' * elog (τ b) (τ b'))
        - h * Real.log ρ := by field_simp; ring
  rw [e1, e2] at key
  linarith

end CatalanLambda.Decay
