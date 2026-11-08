module

public import CatalanCore.Uniform.Decay.Jet.Reference

@[expose] public section
set_option Elab.async false

/-!
# Lemma J, the lattice sums (lane H, wave H2c; ledger P208)

`sum_inv_dist_le`: the pair sum of Lemma J.  If the points `pos i`, `i ∈ I`, of a line are pairwise at least `g`
apart, and `D i` is a distance from a fixed centre `p` that is at least `δ` and at least `|pos i - p|` (the
distance from a point of the plane to the atoms, or from an atom to the others), then
`∑_{i∈I} 1/D i ≤ (4 / min g δ) · ∑_{j<|I|} 1/(j+1)`, a harmonic sum: `O(log |I|)`.
-/

open Finset

namespace CatalanCore.Uniform.Decay.Jet

variable {ι : Type*}

/-- Indexed form of `sum_inv_sep_le`. -/
theorem sum_inv_sep_le_idx {g : ℝ} (hg : 0 < g) (a : ℝ) (I : Finset ι) (pos : ι → ℝ)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → g ≤ |pos i - pos j|) (hnear : ∀ i ∈ I, a + g ≤ pos i) :
    ∑ i ∈ I, 1 / (pos i - a) ≤ (1 / g) * ∑ j ∈ Finset.range I.card, 1 / ((j : ℝ) + 1) := by
  classical
  have hinj : Set.InjOn pos (I : Set ι) := by
    intro i hi j hj h
    by_contra hne
    have := hsep i hi j hj hne
    rw [h, sub_self, abs_zero] at this
    linarith
  have hcard : (I.image pos).card = I.card := Finset.card_image_of_injOn hinj
  have h1 := sum_inv_sep_le hg a (I.image pos)
    (by
      intro t ht t' ht' hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht'
      exact hsep i hi j hj (fun h => hne (by rw [h])))
    (by
      intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
      exact hnear i hi)
  rw [hcard, Finset.sum_image hinj] at h1
  exact h1

/-- **The pair sum of Lemma J.**  `∑_{i∈I} 1/D i ≤ (4 / min g δ) · ∑_{j<|I|} 1/(j+1)`. -/
theorem sum_inv_dist_le {g δ : ℝ} (hg : 0 < g) (hδ : 0 < δ) (p : ℝ) (I : Finset ι) (pos D : ι → ℝ)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → g ≤ |pos i - pos j|)
    (hD1 : ∀ i ∈ I, δ ≤ D i) (hD2 : ∀ i ∈ I, |pos i - p| ≤ D i) :
    ∑ i ∈ I, 1 / D i ≤ (4 / min g δ) * ∑ j ∈ Finset.range I.card, 1 / ((j : ℝ) + 1) := by
  classical
  set g' := min g δ with hg'
  have hg'0 : 0 < g' := lt_min hg hδ
  have hg'g : g' ≤ g := min_le_left _ _
  have hg'd : g' ≤ δ := min_le_right _ _
  have hpt : ∀ i ∈ I, 1 / D i ≤ 2 / (|pos i - p| + δ) := by
    intro i hi
    have h1 := hD1 i hi
    have h2 := hD2 i hi
    have hDpos : 0 < D i := lt_of_lt_of_le hδ h1
    have h3 : (|pos i - p| + δ) / 2 ≤ D i := by linarith
    have hpos : 0 < |pos i - p| + δ := by positivity
    rw [div_le_div_iff₀ hDpos hpos]
    nlinarith
  have hH : ∀ J : Finset ι, J ⊆ I →
      ∑ j ∈ Finset.range J.card, 1 / ((j : ℝ) + 1) ≤ ∑ j ∈ Finset.range I.card, 1 / ((j : ℝ) + 1) := by
    intro J hJ
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity)
    exact Finset.range_subset_range.2 (Finset.card_le_card hJ)
  have hHnn : 0 ≤ ∑ j ∈ Finset.range I.card, 1 / ((j : ℝ) + 1) :=
    Finset.sum_nonneg fun j _ => by positivity
  rw [← Finset.sum_filter_add_sum_filter_not I (fun i => p ≤ pos i)]
  have hplus : ∑ i ∈ I.filter (fun i => p ≤ pos i), 1 / D i ≤
      (2 / g') * ∑ j ∈ Finset.range I.card, 1 / ((j : ℝ) + 1) := by
    calc ∑ i ∈ I.filter (fun i => p ≤ pos i), 1 / D i
        ≤ ∑ i ∈ I.filter (fun i => p ≤ pos i), 2 * (1 / (pos i - (p - δ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_filter] at hi
          have := hpt i hi.1
          rw [abs_of_nonneg (sub_nonneg.2 hi.2)] at this
          have e : 2 / (pos i - p + δ) = 2 * (1 / (pos i - (p - δ))) := by
            have h' : pos i - p + δ = pos i - (p - δ) := by ring
            rw [h', mul_one_div]
          linarith
      _ = 2 * ∑ i ∈ I.filter (fun i => p ≤ pos i), 1 / (pos i - (p - δ)) := by rw [← Finset.mul_sum]
      _ ≤ 2 * ((1 / g') * ∑ j ∈ Finset.range (I.filter (fun i => p ≤ pos i)).card,
            1 / ((j : ℝ) + 1)) := by
          gcongr
          refine sum_inv_sep_le_idx hg'0 (p - δ) _ pos (fun i hi j hj hne => ?_) (fun i hi => ?_)
          · exact hg'g.trans (hsep i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hne)
          · have := (Finset.mem_filter.1 hi).2
            linarith
      _ ≤ 2 * ((1 / g') * ∑ j ∈ Finset.range I.card, 1 / ((j : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hH _ (Finset.filter_subset _ _)) (by positivity)) (by norm_num)
      _ = _ := by ring
  have hminus : ∑ i ∈ I.filter (fun i => ¬ p ≤ pos i), 1 / D i ≤
      (2 / g') * ∑ j ∈ Finset.range I.card, 1 / ((j : ℝ) + 1) := by
    calc ∑ i ∈ I.filter (fun i => ¬ p ≤ pos i), 1 / D i
        ≤ ∑ i ∈ I.filter (fun i => ¬ p ≤ pos i), 2 * (1 / ((-pos i) - (-p - δ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_filter] at hi
          have := hpt i hi.1
          rw [abs_of_neg (sub_neg.2 (not_le.1 hi.2))] at this
          have e : 2 / (-(pos i - p) + δ) = 2 * (1 / ((-pos i) - (-p - δ))) := by
            have h' : -(pos i - p) + δ = (-pos i) - (-p - δ) := by ring
            rw [h', mul_one_div]
          linarith
      _ = 2 * ∑ i ∈ I.filter (fun i => ¬ p ≤ pos i), 1 / ((-pos i) - (-p - δ)) := by
          rw [← Finset.mul_sum]
      _ ≤ 2 * ((1 / g') * ∑ j ∈ Finset.range (I.filter (fun i => ¬ p ≤ pos i)).card,
            1 / ((j : ℝ) + 1)) := by
          gcongr
          refine sum_inv_sep_le_idx hg'0 (-p - δ) _ (fun i => -pos i)
            (fun i hi j hj hne => ?_) (fun i hi => ?_)
          · have := hsep i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hne
            have e : |(-pos i) - (-pos j)| = |pos i - pos j| := by
              rw [← abs_neg]; congr 1; ring
            rw [e]
            exact hg'g.trans this
          · have := (Finset.mem_filter.1 hi).2
            have := not_le.1 this
            linarith
      _ ≤ 2 * ((1 / g') * ∑ j ∈ Finset.range I.card, 1 / ((j : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hH _ (Finset.filter_subset _ _)) (by positivity)) (by norm_num)
      _ = _ := by ring
  calc _ ≤ _ + _ := add_le_add hplus hminus
    _ = (4 / g') * ∑ j ∈ Finset.range I.card, 1 / ((j : ℝ) + 1) := by ring

end CatalanCore.Uniform.Decay.Jet

#print axioms CatalanCore.Uniform.Decay.Jet.sum_inv_sep_le_idx
#print axioms CatalanCore.Uniform.Decay.Jet.sum_inv_dist_le
