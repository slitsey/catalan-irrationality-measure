module

public import CatalanCore.Uniform.Decay.Jet.Lattice

@[expose] public section
set_option Elab.async false

/-!
# Lemma J, the exponent on a lattice configuration (lane H, wave H2c; ledger P208)

`jetExponent_le`: for reference atoms `g` apart, other reference points `d₀` from the atoms, `J` a set of atoms and
nodes at least `s_i + a` from the polydisc, `jetExponent ≤ eJ · k · ((8/min g d₀)(1 + log k) + 1/a + log((k-1+a)/a))`,
which is `O(k log k)`.
-/

open Finset CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet

variable {k : ℕ}

/-- The two orders of a symmetric pair sum. -/
theorem pair_sum_eq (e : Fin k → ℝ) (f : Fin k → Fin k → ℝ) (hsymm : ∀ l l', f l l' = f l' l) :
    ∑ l, ∑ l' ∈ Finset.Ioi l, (e l + e l') * f l l' =
      ∑ l, ∑ l' ∈ Finset.univ.erase l, e l * f l l' := by
  have h1 : ∀ l : Fin k, ∑ l' ∈ Finset.univ.erase l, e l * f l l' =
      ∑ l' ∈ Finset.Iio l, e l * f l l' + ∑ l' ∈ Finset.Ioi l, e l * f l l' := by
    intro l
    have : Finset.univ.erase l = Finset.Iio l ∪ Finset.Ioi l := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
        Finset.mem_Ioi]
      exact ne_iff_lt_or_gt
    rw [this, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Iio, Finset.mem_Ioi] at hx hx'
    exact absurd (hx.trans hx') (lt_irrefl _)
  have h2 : ∑ l, ∑ l' ∈ Finset.Iio l, e l * f l l' = ∑ l, ∑ l' ∈ Finset.Ioi l, e l' * f l l' := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun l' => Finset.Ioi l')]
    · refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun l _ => ?_
      rw [hsymm l l']
    · intro x y
      simp [Finset.mem_Iio, Finset.mem_Ioi]
  simp only [h1, Finset.sum_add_distrib]
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  ring

/-- The harmonic number is logarithmic: `∑_{j<n} 1/(j+1) ≤ 1 + log n` for `n ≥ 1`. -/
theorem harmonic_le_log {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log n := by
  have := harmonic_shift_le (a := 1) one_pos n hn
  simpa using this

theorem card_fin_le (J : Finset (Fin k)) : (J.card : ℝ) ≤ k := by
  exact_mod_cast (calc J.card ≤ (Finset.univ : Finset (Fin k)).card :=
    Finset.card_le_card (Finset.subset_univ _)
    _ = k := by simp)

/-- **The exponent of Lemma J on a lattice configuration.** -/
theorem jetExponent_le (J : Finset (Fin k)) {eJ : ℝ} (heJ : 0 ≤ eJ) (x0 : Fin k → ℂ)
    (m : Fin k → Fin k → ℝ) (Tt : Fin k → Fin k → Prop) [DecidableRel Tt]
    (s : Fin k → ℕ) (hs : Function.Injective s) {a g d₀ : ℝ} (ha : 0 < a) (hg : 0 < g) (hd₀ : 0 < d₀)
    (hJ : ∀ l ∈ J, (x0 l).im = 0)
    (hsep : ∀ l l', l ≠ l' → (x0 l).im = 0 → (x0 l').im = 0 → g ≤ |(x0 l).re - (x0 l').re|)
    (hray : ∀ l l', (x0 l).im = 0 → (x0 l').im ≠ 0 → d₀ ≤ ‖x0 l' - x0 l‖)
    (hm : ∀ l ∈ J, ∀ i, (s i : ℝ) + a ≤ m l i) (hk : 1 ≤ k) :
    jetExponent J eJ x0 m Tt ≤ eJ * k *
      ((8 / min g d₀) * (1 + Real.log k) + (1 / a + Real.log (((k : ℝ) - 1 + a) / a))) := by
  classical
  set e : Fin k → ℝ := fun l => if l ∈ J then eJ else 0 with he
  have he0 : ∀ l, 0 ≤ e l := fun l => by simp only [he]; split_ifs <;> simp [heJ]
  have hg' : 0 < min g d₀ := lt_min hg hd₀
  have hH : ∑ j ∈ Finset.range k, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log k := harmonic_le_log hk
  have hHk : ∀ n ≤ k, ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log k := fun n hn =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hn)
      (fun j _ _ => by positivity)).trans hH
  have hH0 : 0 ≤ 1 + Real.log (k : ℝ) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have := Real.log_nonneg this
    linarith
  have hpair : (∑ l, ∑ l' ∈ Finset.Ioi l,
      if Tt l l' then 0 else (e l + e l') / ‖x0 l' - x0 l‖) ≤
      ∑ l, ∑ l' ∈ Finset.univ.erase l, e l * (1 / ‖x0 l' - x0 l‖) := by
    rw [← pair_sum_eq e (fun l l' => 1 / ‖x0 l' - x0 l‖) (fun l l' => by rw [norm_sub_rev])]
    refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun l' _ => ?_
    split_ifs
    · have := he0 l
      have := he0 l'
      positivity
    · rw [mul_one_div]
  set A : Finset (Fin k) := Finset.univ.filter (fun l => (x0 l).im = 0) with hA
  set R : Finset (Fin k) := Finset.univ.filter (fun l => (x0 l).im ≠ 0) with hR
  have hJA : ∀ l ∈ J, l ∈ A := fun l hl => by simp [hA, hJ l hl]
  have hre_le : ∀ u v : ℂ, |u.re - v.re| ≤ ‖u - v‖ := fun u v => by
    have := Complex.abs_re_le_norm (u - v)
    simpa using this
  have hm4 : (4 / g) ≤ 4 / min g d₀ :=
    div_le_div_of_nonneg_left (by norm_num) hg' (min_le_left _ _)
  have hm5 : (4 / min g d₀) ≥ 0 := by positivity
  set B : ℝ := (4 / min g d₀) * (1 + Real.log k) with hB
  have hatoms : ∀ l ∈ J, ∑ l' ∈ A.erase l, 1 / ‖x0 l' - x0 l‖ ≤ B := by
    intro l hl
    have hlA := hJA l hl
    have h := sum_inv_dist_le (g := g) (δ := g) hg hg ((x0 l).re) (A.erase l)
      (fun l' => (x0 l').re) (fun l' => ‖x0 l' - x0 l‖)
      (fun i hi j hj hne => by
        rw [Finset.mem_erase] at hi hj
        exact hsep i j hne (by simpa [hA] using hi.2) (by simpa [hA] using hj.2))
      (fun i hi => by
        rw [Finset.mem_erase] at hi
        have := hsep i l hi.1 (by simpa [hA] using hi.2) (by simpa [hA] using hlA)
        exact this.trans (hre_le _ _))
      (fun i hi => hre_le _ _)
    simp only [min_self] at h
    have hcard : (A.erase l).card ≤ k := by
      calc (A.erase l).card ≤ (Finset.univ : Finset (Fin k)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = k := by simp
    calc _ ≤ (4 / g) * ∑ j ∈ Finset.range (A.erase l).card, 1 / ((j : ℝ) + 1) := h
      _ ≤ (4 / g) * (1 + Real.log k) :=
          mul_le_mul_of_nonneg_left (hHk _ hcard) (by positivity)
      _ ≤ B := mul_le_mul_of_nonneg_right hm4 hH0
  have hrays : ∀ l' ∈ R, ∑ l ∈ J, 1 / ‖x0 l' - x0 l‖ ≤ B := by
    intro l' hl'
    have hl'R : (x0 l').im ≠ 0 := by simpa [hR] using hl'
    have h := sum_inv_dist_le (g := g) (δ := d₀) hg hd₀ ((x0 l').re) J
      (fun l => (x0 l).re) (fun l => ‖x0 l' - x0 l‖)
      (fun i hi j hj hne => hsep i j hne (hJ i hi) (hJ j hj))
      (fun i hi => hray i l' (hJ i hi) hl'R)
      (fun i hi => by
        have := hre_le (x0 l') (x0 i)
        rwa [abs_sub_comm] at this)
    have hcard : J.card ≤ k := by
      calc J.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = k := by simp
    calc _ ≤ (4 / min g d₀) * ∑ j ∈ Finset.range J.card, 1 / ((j : ℝ) + 1) := h
      _ ≤ B := mul_le_mul_of_nonneg_left (hHk _ hcard) hm5
  have hcJ := card_fin_le J
  have hcR := card_fin_le R
  have hB0 : 0 ≤ B := by positivity
  have hone : (∑ l, ∑ l' ∈ Finset.univ.erase l, e l * (1 / ‖x0 l' - x0 l‖)) ≤
      eJ * (k * B + k * B) := by
    have h1 : (∑ l, ∑ l' ∈ Finset.univ.erase l, e l * (1 / ‖x0 l' - x0 l‖)) =
        ∑ l ∈ J, eJ * ∑ l' ∈ Finset.univ.erase l, 1 / ‖x0 l' - x0 l‖ := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l ∈ J)]
      have hz : ∑ l ∈ Finset.univ.filter (fun l => l ∉ J),
          ∑ l' ∈ Finset.univ.erase l, e l * (1 / ‖x0 l' - x0 l‖) = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have : l ∉ J := (Finset.mem_filter.1 hl).2
        simp [he, this]
      rw [hz, add_zero]
      have : Finset.univ.filter (fun l => l ∈ J) = J := by ext; simp
      rw [this]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [← Finset.mul_sum]
      simp [he, hl]
    have h2 : ∀ l ∈ J, ∑ l' ∈ Finset.univ.erase l, 1 / ‖x0 l' - x0 l‖ =
        ∑ l' ∈ A.erase l, 1 / ‖x0 l' - x0 l‖ + ∑ l' ∈ R, 1 / ‖x0 l' - x0 l‖ := by
      intro l hl
      have hlA := hJA l hl
      have : Finset.univ.erase l = A.erase l ∪ R := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_univ, true_and, Finset.mem_union, hA, hR,
          Finset.mem_filter]
        have hl0 : (x0 l).im = 0 := hJ l hl
        by_cases hx : (x0 x).im = 0
        · simp [hx]
        · constructor
          · intro _; exact Or.inr hx
          · intro _; exact ⟨fun h => hx (h ▸ hl0), trivial⟩
      rw [this, Finset.sum_union]
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_erase, hA, hR, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      exact hx' hx.2
    rw [h1, ← Finset.mul_sum, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) heJ
    · calc ∑ l ∈ J, ∑ l' ∈ A.erase l, 1 / ‖x0 l' - x0 l‖ ≤ ∑ l ∈ J, B :=
            Finset.sum_le_sum hatoms
        _ = J.card * B := by simp
        _ ≤ k * B := mul_le_mul_of_nonneg_right hcJ hB0
    · rw [Finset.sum_comm]
      calc ∑ l' ∈ R, ∑ l ∈ J, 1 / ‖x0 l' - x0 l‖ ≤ ∑ l' ∈ R, B := Finset.sum_le_sum hrays
        _ = R.card * B := by simp
        _ ≤ k * B := mul_le_mul_of_nonneg_right hcR hB0
  -- the node part
  have hnode : (∑ l, ∑ i, e l / m l i) ≤
      eJ * k * (1 / a + Real.log (((k : ℝ) - 1 + a) / a)) := by
    have hharm := (sum_inv_node_le ha s hs).trans (harmonic_shift_le ha k hk)
    have hN0 : 0 ≤ 1 / a + Real.log (((k : ℝ) - 1 + a) / a) :=
      le_trans (Finset.sum_nonneg fun i _ => by positivity) hharm
    calc ∑ l, ∑ i, e l / m l i = ∑ l ∈ J, ∑ i, eJ / m l i := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l ∈ J)]
          have : Finset.univ.filter (fun l => l ∈ J) = J := by ext; simp
          rw [this]
          have hz : ∑ l ∈ Finset.univ.filter (fun l => l ∉ J), ∑ i, e l / m l i = 0 := by
            refine Finset.sum_eq_zero fun l hl => ?_
            have : l ∉ J := (Finset.mem_filter.1 hl).2
            simp [he, this]
          rw [hz, add_zero]
          refine Finset.sum_congr rfl fun l hl => ?_
          simp [he, hl]
      _ ≤ ∑ l ∈ J, eJ * ∑ i, 1 / ((s i : ℝ) + a) := by
          refine Finset.sum_le_sum fun l hl => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mul_one_div]
          have h1 := hm l hl i
          have h0 : 0 < (s i : ℝ) + a := by positivity
          exact div_le_div_of_nonneg_left heJ h0 h1
      _ ≤ ∑ l ∈ J, eJ * (1 / a + Real.log (((k : ℝ) - 1 + a) / a)) :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left hharm heJ
      _ = J.card * (eJ * (1 / a + Real.log (((k : ℝ) - 1 + a) / a))) := by simp
      _ ≤ k * (eJ * (1 / a + Real.log (((k : ℝ) - 1 + a) / a))) :=
          mul_le_mul_of_nonneg_right hcJ (mul_nonneg heJ hN0)
      _ = _ := by ring
  unfold jetExponent
  have hpair' := hpair.trans hone
  have e2 : eJ * (↑k * B + ↑k * B) = eJ * k * ((8 / min g d₀) * (1 + Real.log k)) := by
    rw [hB]; ring
  have hnode' : (∑ l, ∑ i, (if l ∈ J then eJ else 0) / m l i) ≤ _ := hnode
  have hpair'' : (∑ l, ∑ l' ∈ Finset.Ioi l,
      if Tt l l' then 0 else ((if l ∈ J then eJ else 0) + (if l' ∈ J then eJ else 0)) /
        ‖x0 l' - x0 l‖) ≤ _ := hpair'
  rw [e2] at hpair''
  linarith

end CatalanCore.Uniform.Decay.Jet

#print axioms CatalanCore.Uniform.Decay.Jet.pair_sum_eq
#print axioms CatalanCore.Uniform.Decay.Jet.jetExponent_le
