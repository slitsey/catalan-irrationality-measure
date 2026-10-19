module

public import CatalanCore.Decay.Rect.IntegR

@[expose] public section

/-!
# Moving one node by one unit costs `O(k)` in `RectEnergy` (MEM2D)

If the column nodes `t'` agree with `t` except at one position `p`, where `t' p + 1 = t p`, then
`RectEnergy ... T s t` implies `RectEnergy ... (T + k κ) s t'` with `κ = log (4 (1 + 1/m0))`.
The reason: the free points are at distance `≥ m0` from all nodes (so `|x - t'| ≤ (1+1/m0) |x - t|`
-type ratios), and distinct integer nodes are at distance `≥ 1` (ratio `≤ 2` per pair).
-/

open Finset
open CatalanLambda.Decay (cexpr)

namespace CatalanCore.Frame

/-- distinct naturals are at distance `≥ 1`. -/
lemma one_le_norm_nat_sub {a b : ℕ} (h : a ≠ b) : 1 ≤ ‖((a : ℂ) - (b : ℂ))‖ := by
  have : ((a : ℂ) - (b : ℂ)) = (((a : ℤ) - (b : ℤ) : ℤ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_intCast]
  have : (a : ℤ) - b ≠ 0 := by omega
  exact_mod_cast Int.one_le_abs this

/-- pairwise product comparison -/
lemma norm_prod_pairs_le {k : ℕ} (p : Fin k) (f f' : Fin k → Fin k → ℂ)
    (h : ∀ l l', l < l' → ‖f' l l'‖ ≤ (if l = p ∨ l' = p then (2 : ℝ) else 1) * ‖f l l'‖) :
    ‖∏ l, ∏ l' ∈ Ioi l, f' l l'‖ ≤ 2 ^ (2 * k) * ‖∏ l, ∏ l' ∈ Ioi l, f l l'‖ := by
  classical
  simp only [norm_prod]
  set a : Fin k → ℝ := fun l => if l = p then 2 else 1 with ha
  have ha1 : ∀ l, 1 ≤ a l := fun l => by simp only [ha]; split_ifs <;> norm_num
  have ha0 : ∀ l, 0 ≤ a l := fun l => le_trans zero_le_one (ha1 l)
  have hw : ∀ l l', (if l = p ∨ l' = p then (2 : ℝ) else 1) ≤ a l * a l' := by
    intro l l'
    simp only [ha]
    by_cases h1 : l = p <;> by_cases h2 : l' = p <;> simp [h1, h2]
  calc ∏ l, ∏ l' ∈ Ioi l, ‖f' l l'‖
      ≤ ∏ l, ∏ l' ∈ Ioi l, ((a l * a l') * ‖f l l'‖) := by
        refine Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg (fun _ _ => norm_nonneg _))
          (fun l _ => Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun l' hl' => ?_))
        exact (h l l' (Finset.mem_Ioi.1 hl')).trans
          (mul_le_mul_of_nonneg_right (hw l l') (norm_nonneg _))
    _ = (∏ l, ∏ l' ∈ Ioi l, (a l * a l')) * ∏ l, ∏ l' ∈ Ioi l, ‖f l l'‖ := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun l _ => ?_)
        rw [← Finset.prod_mul_distrib]
    _ ≤ 2 ^ (2 * k) * ∏ l, ∏ l' ∈ Ioi l, ‖f l l'‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg
          (fun _ _ => Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
        have hP : ∏ l, a l = 2 := by
          simp only [ha]
          rw [Finset.prod_ite_eq' Finset.univ p (fun _ => (2 : ℝ))]
          simp
        calc ∏ l, ∏ l' ∈ Ioi l, (a l * a l')
            ≤ ∏ l : Fin k, (a l ^ k * (∏ l', a l')) := by
              refine Finset.prod_le_prod₀ (fun l _ => Finset.prod_nonneg
                (fun _ _ => mul_nonneg (ha0 _) (ha0 _))) (fun l _ => ?_)
              rw [Finset.prod_mul_distrib, Finset.prod_const]
              refine mul_le_mul ?_ ?_ (Finset.prod_nonneg (fun _ _ => ha0 _))
                (pow_nonneg (ha0 _) _)
              · refine pow_le_pow_right₀ (ha1 l) ?_
                simpa using Finset.card_le_univ (Ioi l)
              · calc ∏ l' ∈ Ioi l, a l' = ∏ l', (if l' ∈ Ioi l then a l' else 1) := by
                      rw [Finset.prod_ite_mem]; simp
                  _ ≤ ∏ l', a l' := Finset.prod_le_prod₀
                      (fun l' _ => by split_ifs; exacts [ha0 _, zero_le_one])
                      (fun l' _ => by split_ifs; exacts [le_rfl, ha1 _])
          _ = 2 ^ (2 * k) := by
              rw [Finset.prod_mul_distrib, Finset.prod_pow, hP, Finset.prod_const]
              simp [two_mul, pow_add]

lemma ratio_aux (N N' D D' A B : ℝ) (hD : 0 < D) (hD' : 0 < D') (hN : 0 ≤ N) (h1 : N' ≤ A * N)
    (h2 : D ≤ B * D') (hA : 0 ≤ A) (hB : 0 ≤ B) : N' / D' ≤ A * B * (N / D) := by
  calc N' / D' ≤ A * N / D' := div_le_div_of_nonneg_right h1 hD'.le
    _ ≤ A * B * (N / D) := by
      rw [div_le_iff₀ hD']
      have e : A * B * (N / D) * D' = A * N * (B * D') / D := by field_simp
      rw [e, le_div_iff₀ hD]
      exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hA hN)

/-- the effect of moving one column node by one unit on `‖cexpr‖`. -/
lemma cexpr_perturb_le {k : ℕ} {m0 : ℝ} (hm0 : 0 < m0) (x : Fin k → ℂ)
    (hre : ∀ l, m0 ≤ -(x l).re) {t t' : Fin k → ℕ} (p : Fin k)
    (hne : ∀ i, i ≠ p → t' i = t i) (hp : t' p + 1 = t p) (ht : Function.Injective t) :
    ‖cexpr x (fun i => ((t' i : ℕ) : ℂ))‖
      ≤ 2 ^ (2 * k) * (1 + 1 / m0) ^ k * ‖cexpr x (fun i => ((t i : ℕ) : ℂ))‖ := by
  classical
  have hpC : ((t' p : ℕ) : ℂ) = (t p : ℂ) - 1 := by
    have : ((t' p + 1 : ℕ) : ℂ) = (t p : ℂ) := by exact_mod_cast hp
    push_cast at this; linear_combination this
  -- the denominators
  have hdist : ∀ (u : ℕ) l, m0 ≤ ‖x l - (u : ℂ)‖ := by
    intro u l
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have : (x l - (u : ℂ)).re = (x l).re - u := by simp
    rw [this]
    have := hre l
    have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg u
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hDpos : ∀ s : Fin k → ℕ, 0 < ∏ l, ∏ i, ‖x l - (s i : ℂ)‖ := fun s =>
    Finset.prod_pos (fun l _ => Finset.prod_pos (fun i _ => lt_of_lt_of_le hm0 (hdist _ _)))
  have hDle : ∏ l, ∏ i, ‖x l - (t i : ℂ)‖ ≤ (1 + 1 / m0) ^ k * ∏ l, ∏ i, ‖x l - (t' i : ℂ)‖ := by
    set v : Fin k → ℝ := fun i => if i = p then 1 + 1 / m0 else 1 with hv
    have hv1 : ∀ i, 1 ≤ v i := fun i => by
      simp only [hv]; split_ifs
      · have : 0 ≤ 1 / m0 := by positivity
        linarith
      · exact le_rfl
    have hterm : ∀ l i, ‖x l - (t i : ℂ)‖ ≤ v i * ‖x l - (t' i : ℂ)‖ := by
      intro l i
      by_cases hi : i = p
      · subst hi
        simp only [hv, if_true]
        have e1 : x l - (t i : ℂ) = (x l - (t' i : ℂ)) - 1 := by rw [hpC]; ring
        rw [e1]
        have h1 := norm_sub_le (x l - (t' i : ℂ)) 1
        have h2 := hdist (t' i) l
        simp only [norm_one] at h1
        have h3 : 1 ≤ ‖x l - (t' i : ℂ)‖ / m0 := by rw [le_div_iff₀ hm0]; linarith
        have : (1 + 1 / m0) * ‖x l - (t' i : ℂ)‖ = ‖x l - (t' i : ℂ)‖ + ‖x l - (t' i : ℂ)‖ / m0 := by
          field_simp
        linarith
      · simp only [hv, hi, if_false, one_mul]
        rw [hne i hi]
    calc ∏ l, ∏ i, ‖x l - (t i : ℂ)‖ ≤ ∏ l, ∏ i, (v i * ‖x l - (t' i : ℂ)‖) :=
          Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg (fun _ _ => norm_nonneg _))
            (fun l _ => Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hterm l i))
      _ = ∏ l : Fin k, ((∏ i, v i) * ∏ i, ‖x l - (t' i : ℂ)‖) :=
          Finset.prod_congr rfl (fun l _ => Finset.prod_mul_distrib)
      _ = (1 + 1 / m0) ^ k * ∏ l, ∏ i, ‖x l - (t' i : ℂ)‖ := by
          have hvp : ∏ i, v i = 1 + 1 / m0 := by
            simp only [hv]
            rw [Finset.prod_ite_eq' Finset.univ p (fun _ => 1 + 1 / m0)]
            simp
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hvp]
  -- the numerators
  have hnum : ‖∏ l, ∏ l' ∈ Ioi l, (((x l' - x l) * ((t' l : ℂ) - t' l')))‖
      ≤ 2 ^ (2 * k) * ‖∏ l, ∏ l' ∈ Ioi l, (((x l' - x l) * ((t l : ℂ) - t l')))‖ := by
    refine norm_prod_pairs_le p (fun l l' => (x l' - x l) * ((t l : ℂ) - t l'))
      (fun l l' => (x l' - x l) * ((t' l : ℂ) - t' l')) (fun l l' hll => ?_)
    rw [norm_mul, norm_mul, ← mul_assoc, mul_comm (if l = p ∨ l' = p then (2 : ℝ) else 1)]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    by_cases h1 : l = p
    · subst h1
      have h2 : l' ≠ l := ne_of_gt hll
      have hl' : t' l' = t l' := hne l' h2
      have hd : 1 ≤ ‖((t l : ℕ) : ℂ) - (t l' : ℂ)‖ :=
        one_le_norm_nat_sub (fun h => (ne_of_lt hll) (ht h))
      have e1 : ((t' l : ℕ) : ℂ) - (t' l' : ℂ) = (((t l : ℕ) : ℂ) - (t l' : ℂ)) - 1 := by
        rw [hl', hpC]; ring
      rw [e1]
      have := norm_sub_le (((t l : ℕ) : ℂ) - (t l' : ℂ)) 1
      simp only [norm_one] at this
      simp only [true_or, if_true]
      linarith
    · by_cases h2 : l' = p
      · subst h2
        have hl : t' l = t l := hne l h1
        have hd : 1 ≤ ‖((t l : ℕ) : ℂ) - (t l' : ℂ)‖ :=
          one_le_norm_nat_sub (fun h => (ne_of_lt hll) (ht h))
        have e1 : ((t' l : ℕ) : ℂ) - (t' l' : ℂ) = (((t l : ℕ) : ℂ) - (t l' : ℂ)) + 1 := by
          rw [hl, hpC]; ring
        rw [e1]
        have := norm_add_le (((t l : ℕ) : ℂ) - (t l' : ℂ)) 1
        simp only [norm_one] at this
        simp only [or_true, if_true]
        linarith
      · rw [hne l h1, hne l' h2]
        simp [h1, h2]
  unfold cexpr
  rw [norm_div, norm_div]
  have hD0 : 0 < ‖∏ l, ∏ i, (x l - ((t i : ℕ) : ℂ))‖ := by
    rw [norm_prod]; simp only [norm_prod]; exact hDpos t
  have hD0' : 0 < ‖∏ l, ∏ i, (x l - ((t' i : ℕ) : ℂ))‖ := by
    rw [norm_prod]; simp only [norm_prod]; exact hDpos t'
  have hDle' : ‖∏ l, ∏ i, (x l - ((t i : ℕ) : ℂ))‖
      ≤ (1 + 1 / m0) ^ k * ‖∏ l, ∏ i, (x l - ((t' i : ℕ) : ℂ))‖ := by
    simpa only [norm_prod] using hDle
  exact ratio_aux _ _ _ _ _ _ hD0 hD0' (norm_nonneg _) hnum hDle' (by positivity) (by positivity)

lemma cexpr_ne_zero {k : ℕ} (x : Fin k → ℂ) (hx : Function.Injective x) (hre : ∀ l, (x l).re < 0)
    (t : Fin k → ℕ) (ht : Function.Injective t) :
    cexpr x (fun i => ((t i : ℕ) : ℂ)) ≠ 0 := by
  unfold cexpr
  refine div_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.2 (fun l _ => Finset.prod_ne_zero_iff.2 (fun l' hl' => ?_))
    have hll : l < l' := Finset.mem_Ioi.1 hl'
    refine mul_ne_zero (sub_ne_zero.2 (fun h => (ne_of_lt hll) (hx h).symm)) ?_
    exact sub_ne_zero.2 (fun h => (ne_of_lt hll) (ht (by
      have h' : ((t l : ℕ) : ℂ) = ((t l' : ℕ) : ℂ) := h
      exact_mod_cast h')))
  · refine Finset.prod_ne_zero_iff.2 (fun l _ => Finset.prod_ne_zero_iff.2 (fun i _ => ?_))
    intro h
    have := congrArg Complex.re (sub_eq_zero.1 h)
    have h2 := hre l
    have : (x l).re = (t i : ℝ) := by simpa using this
    have : (0 : ℝ) ≤ t i := Nat.cast_nonneg _
    linarith

/-- **One node moved by one unit costs `k κ`.** -/
theorem rectEnergy_perturb {Fr : Frame} {N0 k : ℕ} {e m0 Cl T : ℝ} (hm0 : 0 < m0)
    {s t t' : Fin k → ℕ} (p : Fin k) (hne : ∀ i, i ≠ p → t' i = t i) (hp : t' p + 1 = t p)
    (ht : Function.Injective t) (ht' : Function.Injective t')
    (hE : RectEnergy Fr N0 k e m0 Cl T s t) :
    RectEnergy Fr N0 k e m0 Cl (T + k * Real.log (4 * (1 + 1 / m0))) s t' := by
  intro x hx hxa hre q hq
  have h := hE x hx hxa hre q hq
  have hre' : ∀ l, (x l).re < 0 := fun l => by have := hre l; linarith
  have hC := cexpr_ne_zero x hx hre' t ht
  have hC' := cexpr_ne_zero x hx hre' t' ht'
  have hle := cexpr_perturb_le hm0 x hre p hne hp ht
  have hpos : 0 < ‖cexpr x (fun i => ((t i : ℕ) : ℂ))‖ := norm_pos_iff.2 hC
  have hpos' : 0 < ‖cexpr x (fun i => ((t' i : ℕ) : ℂ))‖ := norm_pos_iff.2 hC'
  set K : ℝ := 2 ^ (2 * k) * (1 + 1 / m0) ^ k with hK
  have hK0 : 0 < K := by positivity
  have hsq : ‖cexpr x (fun i => ((t' i : ℕ) : ℂ))‖ ^ 2
      ≤ K ^ 2 * ‖cexpr x (fun i => ((t i : ℕ) : ℂ))‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hpos'.le hle 2
  have hlog := Real.log_le_log (by positivity) hsq
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  have hlogK : Real.log (K ^ 2) = 2 * (k * Real.log (4 * (1 + 1 / m0))) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [Real.log_pow, hK, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num) (by positivity), h4]
    push_cast
    ring
  rw [hlogK] at hlog
  nlinarith [h, hlog]

end CatalanCore.Frame
