module

public import CatalanCore.Uniform.Decay.Jet.LatticeExp

@[expose] public section
set_option Elab.async false

/-!
# Lemma J for a configuration of labels (lane H, wave H2c; ledger P208, S15)

`jet_field`: the `jet` field of a jet source.  Labels `z : ι` carry a reference position `pos0 z`, a centre
`ctr z`, and jet coefficients `kap z`, `eps z`; the row of the label at the node `t` is
`kap · (ctr - t)⁻¹ + eps · (-(ctr - t)⁻²)`.  Labels with `eps = 0` are plain Cauchy rows at their reference
position; labels with `eps ≠ 0` are real atoms whose centre lies within `eJ - ρ` of the reference position.
Under the lattice hypotheses (atoms `g` apart, other positions `d₀` from the atoms, nodes at distance growing
like `t + a`, flagged pairs `2ρ` apart at the reference), every minor of the rows is at most
`exp (k (c1 + c2 log (k+1)))` times the Cauchy expression of the reference positions.
-/

open Finset
open CatalanLambda.Decay (cexpr)

namespace CatalanCore.Uniform.Decay.Jet

/-- The row of a label at the node `t`. -/
noncomputable def jrow {ι : Type*} (ctr kap eps : ι → ℂ) (t : ℕ) (z : ι) : ℂ :=
  kap z * (ctr z - (t : ℂ))⁻¹ + eps z * (-((ctr z - (t : ℂ))⁻¹) ^ 2)

/-- The constant `c1` of Lemma J. -/
noncomputable def jetC1 (Bk ρ a g d₀ eJ : ℝ) : ℝ :=
  Real.log (max 1 (Bk + 1 / ρ)) + eJ * (8 / min g d₀ + 1 / a + (-Real.log a))

/-- The constant `c2` of Lemma J. -/
noncomputable def jetC2 (g d₀ eJ : ℝ) : ℝ := eJ * (8 / min g d₀ + 1)

theorem jetC1_nonneg {Bk ρ a g d₀ eJ : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (ha1 : a ≤ 1) (hg : 0 < g)
    (hd₀ : 0 < d₀) (heJ : 0 ≤ eJ) (hBk : 0 ≤ Bk) : 0 ≤ jetC1 Bk ρ a g d₀ eJ := by
  unfold jetC1
  have hmin : 0 < min g d₀ := lt_min hg hd₀
  have h1 : 0 ≤ Real.log (max 1 (Bk + 1 / ρ)) := Real.log_nonneg (le_max_left _ _)
  have h2 : 0 ≤ -Real.log a := by
    have := Real.log_nonpos ha.le ha1
    linarith
  have h3 : 0 ≤ 8 / min g d₀ := by positivity
  positivity

theorem jetC2_nonneg {g d₀ eJ : ℝ} (hg : 0 < g) (hd₀ : 0 < d₀) (heJ : 0 ≤ eJ) : 0 ≤ jetC2 g d₀ eJ := by
  unfold jetC2
  have hmin : 0 < min g d₀ := lt_min hg hd₀
  have h3 : 0 ≤ 8 / min g d₀ := by positivity
  positivity

/-- **Lemma J, concrete form.** -/
theorem jet_field {ι : Type*} (pos0 ctr kap eps : ι → ℂ)
    {ρ a a0 g d₀ eJ Bk : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (ha1 : a ≤ 1) (ha0 : 0 < a0) (hg : 0 < g)
    (hd₀ : 0 < d₀) (heJ : 0 ≤ eJ) (hBk : 0 ≤ Bk)
    (hkap : ∀ z, ‖kap z‖ ≤ Bk) (heps : ∀ z, ‖eps z‖ ≤ 1)
    (hplain : ∀ z, eps z = 0 → kap z = 1 ∧ ctr z = pos0 z)
    (hJre : ∀ z, eps z ≠ 0 → (ctr z).im = 0 ∧ (pos0 z).im = 0 ∧ ρ + ‖ctr z - pos0 z‖ ≤ eJ)
    (hpos : ∀ z z', pos0 z = pos0 z' → ctr z = ctr z' ∧ kap z = kap z' ∧ eps z = eps z')
    (hsepι : ∀ z z', pos0 z ≠ pos0 z' → (pos0 z).im = 0 → (pos0 z').im = 0 →
      g ≤ |(pos0 z).re - (pos0 z').re|)
    (hrayι : ∀ z z', (pos0 z).im = 0 → (pos0 z').im ≠ 0 → d₀ ≤ ‖pos0 z' - pos0 z‖)
    (hnode0 : ∀ z (t : ℕ), a0 ≤ ‖pos0 z - (t : ℂ)‖)
    (hnodeJ : ∀ z, eps z ≠ 0 → ∀ t : ℕ, (t : ℝ) + a + ρ ≤ ‖ctr z - (t : ℂ)‖)
    (htight : ∀ z z', pos0 z ≠ pos0 z' → eps z ≠ 0 → eps z' ≠ 0 → ctr z = ctr z' →
      2 * ρ ≤ ‖pos0 z' - pos0 z‖) :
    ∀ (k : ℕ) (s : Fin k → ℕ), Function.Injective s →
      ∀ z : Fin k → ι,
        ‖(Matrix.of fun i l : Fin k => jrow ctr kap eps (s i) (z l)).det‖ ≤
          Real.exp (k * (jetC1 Bk ρ a g d₀ eJ + jetC2 g d₀ eJ * Real.log ((k : ℝ) + 1))) *
            ‖cexpr (fun l => pos0 (z l)) (fun i => (s i : ℂ))‖ := by
  classical
  set Bb : ℝ := max 1 (Bk + 1 / ρ) with hBb
  have hBb1 : 1 ≤ Bb := le_max_left _ _
  set A1 : ℝ := 8 / min g d₀ with hA1
  have hmin : 0 < min g d₀ := lt_min hg hd₀
  have hA10 : 0 ≤ A1 := by positivity
  have hloga : 0 ≤ -Real.log a := by
    have := Real.log_nonpos ha.le ha1
    linarith
  have hlogB : 0 ≤ Real.log Bb := Real.log_nonneg hBb1
  intro k s hs z
  have hc1 : jetC1 Bk ρ a g d₀ eJ = Real.log Bb + eJ * (A1 + 1 / a + (-Real.log a)) := rfl
  have hc2 : jetC2 g d₀ eJ = eJ * (A1 + 1) := rfl
  rw [hc1, hc2]
  by_cases hinj : Function.Injective (fun l => pos0 (z l))
  swap
  · -- repeated reference position: two equal columns
    have hne : ∃ l l', pos0 (z l) = pos0 (z l') ∧ l ≠ l' := by
      obtain ⟨l, l', h, hne⟩ := Function.not_injective_iff.1 hinj
      exact ⟨l, l', h, hne⟩
    obtain ⟨l, l2, hll, hne⟩ := hne
    obtain ⟨h1, h2, h3⟩ := hpos _ _ hll
    have hdet : (Matrix.of fun i l : Fin k => jrow ctr kap eps (s i) (z l)).det = 0 := by
      refine Matrix.det_zero_of_column_eq hne (fun i => ?_)
      simp [jrow, h1, h2, h3]
    rw [hdet, norm_zero]
    positivity
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    simp [cexpr]
  -- the main case
  set J : Finset (Fin k) := Finset.univ.filter (fun l => eps (z l) ≠ 0) with hJdef
  have hJmem : ∀ l, l ∈ J ↔ eps (z l) ≠ 0 := fun l => by simp [hJdef]
  set m : Fin k → Fin k → ℝ := fun l i => if l ∈ J then (s i : ℝ) + a else a0 with hm
  have hmpos : ∀ l i, 0 < m l i := fun l i => by
    simp only [hm]; split_ifs
    · positivity
    · exact ha0
  set Tt : Fin k → Fin k → Prop := fun l l2 =>
    eps (z l) ≠ 0 ∧ eps (z l2) ≠ 0 ∧ ctr (z l) = ctr (z l2) with hTt
  have hmain := lemmaJ_abstract (fun l => kap (z l)) (fun l => eps (z l)) s hs
    (fun l => ctr (z l)) (fun l => pos0 (z l)) hinj
    (fun l i h => by
      have := hnode0 (z l) (s i)
      have h2 : ‖pos0 (z l) - (s i : ℂ)‖ = 0 := by rw [h, sub_self, norm_zero]
      linarith)
    hρ heJ J
    (fun l hl i => by
      have := hnodeJ (z l) ((hJmem l).1 hl) (s i)
      have h0 : (0 : ℝ) ≤ (s i : ℝ) := Nat.cast_nonneg _
      linarith)
    (fun l hl => (hJre (z l) ((hJmem l).1 hl)).2.2)
    (fun l hl => (hplain (z l) (by simpa [hJmem] using hl)).2)
    m hmpos
    (fun x hx l i => by
      simp only [hm]
      split_ifs with hl
      · have h1 := hnodeJ (z l) ((hJmem l).1 hl) (s i)
        have h2 := hx.1 l hl
        have h3 : ‖ctr (z l) - (s i : ℂ)‖ ≤ ‖x l - (s i : ℂ)‖ + ‖x l - ctr (z l)‖ := by
          calc ‖ctr (z l) - (s i : ℂ)‖ = ‖(x l - (s i : ℂ)) - (x l - ctr (z l))‖ := by ring_nf
            _ ≤ _ := norm_sub_le _ _
        linarith
      · have h1 := hx.2 l hl
        have h2 := hnode0 (z l) (s i)
        have h3 : ctr (z l) = pos0 (z l) := (hplain (z l) (by simpa [hJmem] using hl)).2
        show a0 ≤ ‖x l - (s i : ℂ)‖
        rw [h1]
        show a0 ≤ ‖ctr (z l) - (s i : ℂ)‖
        rw [h3]
        exact h2)
    Tt
    (fun l l2 hll htt x hx => by
      have hlJ : l ∈ J := (hJmem l).2 htt.1
      have hl2J : l2 ∈ J := (hJmem l2).2 htt.2.1
      have hdl := hx.1 l hlJ
      have hdl2 := hx.1 l2 hl2J
      have hdist := htight (z l2) (z l) (fun h => absurd (hinj h) (ne_of_gt hll)) htt.2.1 htt.1
        htt.2.2.symm
      calc ‖x l2 - x l‖ = ‖(x l2 - ctr (z l2)) - (x l - ctr (z l)) + (ctr (z l2) - ctr (z l))‖ := by
            ring_nf
        _ = ‖(x l2 - ctr (z l2)) - (x l - ctr (z l))‖ := by rw [htt.2.2, sub_self, add_zero]
        _ ≤ ‖x l2 - ctr (z l2)‖ + ‖x l - ctr (z l)‖ := norm_sub_le _ _
        _ ≤ ρ + ρ := add_le_add hdl2 hdl
        _ ≤ ‖pos0 (z l2) - pos0 (z l)‖ := by rw [norm_sub_rev]; linarith)
  have hdetD : (Matrix.of fun i l : Fin k => jrow ctr kap eps (s i) (z l)).det =
      Dj (fun l => kap (z l)) (fun l => eps (z l)) s J (fun l => ctr (z l)) := by
    unfold Dj
    rw [← Matrix.det_transpose]
    congr 1
    ext l i
    by_cases hl : l ∈ J
    · simp [jrow, jr, vr, dvr, hl]
    · have h0 : eps (z l) = 0 := by simpa [hJmem] using hl
      have h1 : kap (z l) = 1 := (hplain (z l) h0).1
      simp [jrow, jr, vr, dvr, hl, h0, h1]
  have hexp := jetExponent_le J (eJ := eJ) heJ (fun l => pos0 (z l)) m Tt s hs (a := a) (g := g)
    (d₀ := d₀) ha hg hd₀
    (fun l hl => (hJre (z l) ((hJmem l).1 hl)).2.1)
    (fun l l2 hne h1 h2 => hsepι (z l) (z l2) (fun h => hne (hinj h)) h1 h2)
    (fun l l2 h1 h2 => hrayι (z l) (z l2) h1 h2)
    (fun l hl i => by simp [hm, hl]) hk1
  rw [hdetD]
  refine hmain.trans ?_
  have hprod : (∏ l ∈ J, (‖kap (z l)‖ + ‖eps (z l)‖ / ρ)) ≤ Bb ^ k := by
    calc (∏ l ∈ J, (‖kap (z l)‖ + ‖eps (z l)‖ / ρ)) ≤ ∏ l ∈ J, Bb := by
          refine Finset.prod_le_prod₀ (fun l _ => by positivity) (fun l _ => ?_)
          calc ‖kap (z l)‖ + ‖eps (z l)‖ / ρ ≤ Bk + 1 / ρ :=
                add_le_add (hkap _) (div_le_div_of_nonneg_right (heps _) hρ.le)
            _ ≤ Bb := le_max_right _ _
      _ = Bb ^ J.card := by simp
      _ ≤ Bb ^ k := pow_le_pow_right₀ hBb1 (by
          calc J.card ≤ (Finset.univ : Finset (Fin k)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = k := by simp)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hlogk : Real.log k ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log (((k : ℝ) - 1 + a) / a) ≤ Real.log ((k : ℝ) + 1) + (-Real.log a) := by
    have hle : ((k : ℝ) - 1 + a) / a ≤ ((k : ℝ) + 1) / a := by
      apply div_le_div_of_nonneg_right _ ha.le
      linarith
    have hpos' : 0 < (k : ℝ) - 1 + a := by linarith
    calc Real.log (((k : ℝ) - 1 + a) / a) ≤ Real.log (((k : ℝ) + 1) / a) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log ((k : ℝ) + 1) - Real.log a := Real.log_div (by positivity) ha.ne'
      _ = _ := by ring
  have hE : jetExponent J eJ (fun l => pos0 (z l)) m Tt ≤
      k * (eJ * (A1 + 1 / a + (-Real.log a)) + eJ * (A1 + 1) * Real.log ((k : ℝ) + 1)) := by
    refine hexp.trans ?_
    have hb : A1 * (1 + Real.log k) + (1 / a + Real.log (((k : ℝ) - 1 + a) / a)) ≤
        A1 * (1 + Real.log ((k : ℝ) + 1)) + (1 / a + (Real.log ((k : ℝ) + 1) + (-Real.log a))) := by
      have := mul_le_mul_of_nonneg_left hlogk hA10
      linarith
    calc eJ * k * (A1 * (1 + Real.log k) + (1 / a + Real.log (((k : ℝ) - 1 + a) / a)))
        ≤ eJ * k * (A1 * (1 + Real.log ((k : ℝ) + 1)) +
          (1 / a + (Real.log ((k : ℝ) + 1) + (-Real.log a)))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  have hcx := norm_nonneg (cexpr (fun l => pos0 (z l)) (fun i => (s i : ℂ)))
  have hBe : Bb ^ k = Real.exp (k * Real.log Bb) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  calc (∏ l ∈ J, (‖kap (z l)‖ + ‖eps (z l)‖ / ρ)) *
        Real.exp (jetExponent J eJ (fun l => pos0 (z l)) m Tt) *
        ‖cexpr (fun l => pos0 (z l)) (fun i => (s i : ℂ))‖
      ≤ (Real.exp (k * Real.log Bb) * Real.exp (k * (eJ * (A1 + 1 / a + (-Real.log a)) +
          eJ * (A1 + 1) * Real.log ((k : ℝ) + 1)))) *
          ‖cexpr (fun l => pos0 (z l)) (fun i => (s i : ℂ))‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hcx
        exact mul_le_mul (hprod.trans (le_of_eq hBe)) (Real.exp_le_exp.2 hE) (Real.exp_pos _).le
          (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring


theorem jetExponent_le_heads {k : ℕ} (J : Finset (Fin k)) {eJ : ℝ} (heJ : 0 ≤ eJ) (x0 : Fin k → ℂ)
    (m : Fin k → Fin k → ℝ) (Tt : Fin k → Fin k → Prop) [DecidableRel Tt]
    (s : Fin k → ℕ) (hs : Function.Injective s) {a g d₀ : ℝ} (ha : 0 < a) (hg : 0 < g) (hd₀ : 0 < d₀)
    (hJ : ∀ l ∈ J, (x0 l).im = 0)
    (hsep : ∀ l l', l ≠ l' → l ∈ J → l' ∈ J → g ≤ |(x0 l).re - (x0 l').re|)
    (hray : ∀ l l', l ∈ J → l' ∉ J → d₀ ≤ ‖x0 l' - x0 l‖)
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
  let A : Finset (Fin k) := J
  have hA : A = J := rfl
  set R : Finset (Fin k) := Finset.univ.filter (fun l => l ∉ J) with hR
  have hJA : ∀ l ∈ J, l ∈ A := fun l hl => by simpa only [hA] using hl
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
    have hl'R : l' ∉ J := by simpa [hR] using hl'
    have h := sum_inv_dist_le (g := g) (δ := d₀) hg hd₀ ((x0 l').re) J
      (fun l => (x0 l).re) (fun l => ‖x0 l' - x0 l‖)
      (fun i hi j hj hne => hsep i j hne hi hj)
      (fun i hi => hray i l' hi hl'R)
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
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, hA, hR,
          Finset.mem_filter, true_and]
        constructor
        · intro hne
          by_cases hx : x ∈ J
          · exact Or.inl ⟨hne, hx⟩
          · exact Or.inr hx
        · rintro (⟨hne, _⟩ | hx)
          · exact hne
          · intro he
            exact hx (he ▸ hl)
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

universe u

/-! ### Finite jets over a separated subset of heads -/

theorem finite_jet_field {L : Type u} (head : L → Prop) [DecidablePred head]
    (ord : ℕ) (x y : L → ℂ) (A : L → Fin (ord + 1) → ℂ)
    {ρ a g d₀ eJ H : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hg : 0 < g) (hd₀ : 0 < d₀) (heJ : 0 ≤ eJ) (hH : 0 ≤ H)
    (hA : ∀ q, head q → ∀ j, ‖A q j‖ ≤ H)
    (hplain : ∀ q, ¬head q → x q = y q)
    (hhead : ∀ q, head q → (y q).im = 0 ∧ ρ + ‖x q - y q‖ ≤ eJ)
    (hsep : ∀ q q', head q → head q' → y q ≠ y q' → g ≤ |(y q).re - (y q').re|)
    (hgap : ∀ q q', head q → ¬head q' → d₀ ≤ ‖y q - y q'‖)
    (hnode : ∀ q (t : ℕ), y q ≠ (t : ℂ))
    (hnodeJ : ∀ q, head q → ∀ t : ℕ, (t : ℝ) + a + ρ ≤ ‖x q - (t : ℂ)‖)
    (hcollision : ∀ q q', y q = y q' → ∀ t : ℕ,
      jetRowFinite head ord x y A t q = jetRowFinite head ord x y A t q') :
    ∀ (k : ℕ) (s : Fin k → ℕ), Function.Injective s → ∀ z : Fin k → L,
      ‖(Matrix.of fun i l : Fin k => jetRowFinite head ord x y A (s i) (z l)).det‖ ≤
        Real.exp ((k : ℝ) *
          ((Real.log (max 1 (∑ j : Fin (ord + 1), H * (j.val.factorial : ℝ) / ρ ^ j.val)) +
            eJ * (8 / min g d₀ + 1 / a + (-Real.log a))) +
            (eJ * (8 / min g d₀ + 1)) * Real.log ((k : ℝ) + 1))) *
          ‖cexpr (fun l => y (z l)) (fun i => (s i : ℂ))‖ := by
  classical
  set Bb : ℝ := max 1 (∑ j : Fin (ord + 1), H * (j.val.factorial : ℝ) / ρ ^ j.val) with hBb
  have hBb1 : 1 ≤ Bb := le_max_left _ _
  set A1 : ℝ := 8 / min g d₀ with hA1
  have hmin : 0 < min g d₀ := lt_min hg hd₀
  have hA10 : 0 ≤ A1 := by positivity
  intro k s hs z
  by_cases hinj : Function.Injective (fun l => y (z l))
  swap
  · obtain ⟨l, l', he, hne⟩ := Function.not_injective_iff.mp hinj
    have hz : (Matrix.of fun i l : Fin k => jetRowFinite head ord x y A (s i) (z l)).det = 0 := by
      exact Matrix.det_zero_of_column_eq hne (fun i => hcollision _ _ he (s i))
    rw [hz, norm_zero]
    positivity
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    simp [cexpr]
  set J : Finset (Fin k) := Finset.univ.filter (fun l => head (z l)) with hJdef
  have hJmem : ∀ l, l ∈ J ↔ head (z l) := fun l => by simp [hJdef]
  set m : Fin k → Fin k → ℝ := fun l i =>
    if l ∈ J then (s i : ℝ) + a else ‖y (z l) - (s i : ℂ)‖ with hm
  have hmpos : ∀ l i, 0 < m l i := by
    intro l i
    simp only [hm]
    split_ifs
    · positivity
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (hnode _ _))
  let Tt : Fin k → Fin k → Prop := fun _ _ => False
  have hmain := lemmaJ_finite_abstract ord (fun l => A (z l)) s hs
    (fun l => x (z l)) (fun l => y (z l)) hinj (fun l i => hnode _ _)
    hρ heJ J
    (fun l hl i => by
      have h := hnodeJ (z l) ((hJmem l).mp hl) (s i)
      have hn : (0 : ℝ) ≤ s i := Nat.cast_nonneg _
      linarith)
    (fun l hl => (hhead (z l) ((hJmem l).mp hl)).2)
    (fun l hl => hplain (z l) (fun h => hl ((hJmem l).mpr h)))
    m hmpos
    (fun w hw l i => by
      simp only [hm]
      split_ifs with hl
      · have h1 := hnodeJ (z l) ((hJmem l).mp hl) (s i)
        have h2 := hw.1 l hl
        have h3 : ‖x (z l) - (s i : ℂ)‖ ≤ ‖w l - (s i : ℂ)‖ + ‖w l - x (z l)‖ := by
          calc
            _ = ‖(w l - (s i : ℂ)) - (w l - x (z l))‖ := by ring_nf
            _ ≤ _ := norm_sub_le _ _
        linarith
      · rw [hw.2 l hl]
        change ‖y (z l) - (s i : ℂ)‖ ≤ ‖x (z l) - (s i : ℂ)‖
        rw [hplain (z l) (fun h => hl ((hJmem l).mpr h))])
    Tt (fun _ _ _ h => h.elim)
  have hdetD : (Matrix.of fun i l : Fin k => jetRowFinite head ord x y A (s i) (z l)).det =
      Df ord (fun l => A (z l)) s J (fun l => x (z l)) := by
    unfold Df
    rw [← Matrix.det_transpose]
    congr 1
    ext l i
    by_cases hl : l ∈ J
    · simp [jetRowFinite, jvrFinite, hl, (hJmem l).mp hl]
    · have hnot : ¬head (z l) := fun h => hl ((hJmem l).mpr h)
      simp [jetRowFinite, vr, hl, hnot, hplain _ hnot]
  have hexp := jetExponent_le_heads J (eJ := eJ) heJ (fun l => y (z l)) m Tt s hs
    (a := a) (g := g) (d₀ := d₀) ha hg hd₀
    (fun l hl => (hhead (z l) ((hJmem l).mp hl)).1)
    (fun l l' hne hl hl' => hsep _ _ ((hJmem l).mp hl) ((hJmem l').mp hl')
      (fun he => hne (hinj he)))
    (fun l l' hl hl' => by
      rw [norm_sub_rev]
      exact hgap _ _ ((hJmem l).mp hl) (fun h => hl' ((hJmem l').mpr h)))
    (fun l hl i => by simp [hm, hl]) hk1
  rw [hdetD]
  refine hmain.trans ?_
  have hprod : (∏ l ∈ J, (∑ j : Fin (ord + 1), ‖A (z l) j‖ * (j.val.factorial : ℝ) / ρ ^ j.val)) ≤ Bb ^ k := by
    calc
      _ ≤ ∏ _l ∈ J, Bb := by
        apply Finset.prod_le_prod₀ (fun l _ => Finset.sum_nonneg fun j _ => by positivity)
        intro l hl
        calc
          _ ≤ ∑ j : Fin (ord + 1), H * (j.val.factorial : ℝ) / ρ ^ j.val := by
            apply Finset.sum_le_sum
            intro j _
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hA _ ((hJmem l).mp hl) j) (Nat.cast_nonneg _))
              (pow_nonneg hρ.le _)
          _ ≤ Bb := le_max_right _ _
      _ = Bb ^ J.card := by simp
      _ ≤ Bb ^ k := pow_le_pow_right₀ hBb1 (by
        calc J.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
             _ = k := by simp)

  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hlogk : Real.log k ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log (((k : ℝ) - 1 + a) / a) ≤ Real.log ((k : ℝ) + 1) + (-Real.log a) := by
    have hle : ((k : ℝ) - 1 + a) / a ≤ ((k : ℝ) + 1) / a := by
      apply div_le_div_of_nonneg_right _ ha.le
      linarith
    have hpos' : 0 < (k : ℝ) - 1 + a := by linarith
    calc Real.log (((k : ℝ) - 1 + a) / a) ≤ Real.log (((k : ℝ) + 1) / a) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log ((k : ℝ) + 1) - Real.log a := Real.log_div (by positivity) ha.ne'
      _ = _ := by ring
  have hE : jetExponent J eJ (fun l => y (z l)) m Tt ≤
      k * (eJ * (A1 + 1 / a + (-Real.log a)) + eJ * (A1 + 1) * Real.log ((k : ℝ) + 1)) := by
    refine hexp.trans ?_
    have hb : A1 * (1 + Real.log k) + (1 / a + Real.log (((k : ℝ) - 1 + a) / a)) ≤
        A1 * (1 + Real.log ((k : ℝ) + 1)) + (1 / a + (Real.log ((k : ℝ) + 1) + (-Real.log a))) := by
      have := mul_le_mul_of_nonneg_left hlogk hA10
      linarith
    calc eJ * k * (A1 * (1 + Real.log k) + (1 / a + Real.log (((k : ℝ) - 1 + a) / a)))
        ≤ eJ * k * (A1 * (1 + Real.log ((k : ℝ) + 1)) +
          (1 / a + (Real.log ((k : ℝ) + 1) + (-Real.log a)))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  have hcx := norm_nonneg (cexpr (fun l => y (z l)) (fun i => (s i : ℂ)))
  have hBe : Bb ^ k = Real.exp (k * Real.log Bb) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  calc (∏ l ∈ J, (∑ j : Fin (ord + 1), ‖A (z l) j‖ * (j.val.factorial : ℝ) / ρ ^ j.val)) *
        Real.exp (jetExponent J eJ (fun l => y (z l)) m Tt) *
        ‖cexpr (fun l => y (z l)) (fun i => (s i : ℂ))‖
      ≤ (Real.exp (k * Real.log Bb) * Real.exp (k * (eJ * (A1 + 1 / a + (-Real.log a)) +
          eJ * (A1 + 1) * Real.log ((k : ℝ) + 1)))) *
          ‖cexpr (fun l => y (z l)) (fun i => (s i : ℂ))‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hcx
        exact mul_le_mul (hprod.trans (le_of_eq hBe)) (Real.exp_le_exp.2 hE) (Real.exp_pos _).le
          (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_add]
        congr 2
        dsimp only [Bb, A1]
        ring


/-- The maximal all-label finite-order Cauchy bound, with a fixed physical radius.
No mutual separation of contour labels, node bound, or dimension bound is assumed. -/
theorem finite_jet_cauchy_bound
    (J : ℕ) (H C0 g d0 a : ℝ)
    (hH : 0 ≤ H) (hC0 : 0 ≤ C0) (hg : 0 < g) (hd0 : 0 < d0) (ha : 0 < a) :
    ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 ≤ c2 ∧
      ∀ {L : Type u} (head : L → Prop) [DecidablePred head]
        (x y : L → ℂ) (A : L → Fin (J + 1) → ℂ),
        (∀ q, head q → (x q).im = 0 ∧ (x q).re ≤ -a) →
        (∀ q, head q → (y q).im = 0) →
        (∀ q, head q → ‖x q - y q‖ ≤ C0) →
        (∀ q, head q → ∀ j, ‖A q j‖ ≤ H) →
        (∀ q, ¬head q → x q = y q) →
        (∀ q q', head q → head q' → y q ≠ y q' → g ≤ ‖y q - y q'‖) →
        (∀ q q', head q → ¬head q' → d0 ≤ ‖y q - y q'‖) →
        (∀ q (t : ℕ), y q ≠ (t : ℂ)) →
        (∀ q q', y q = y q' → ∀ t : ℕ,
          jetRowFinite head J x y A t q = jetRowFinite head J x y A t q') →
        ∀ (k : ℕ) (s : Fin k → ℕ), Function.Injective s → ∀ z : Fin k → L,
          ‖(Matrix.of fun i l : Fin k => jetRowFinite head J x y A (s i) (z l)).det‖ ≤
            Real.exp ((k : ℝ) * (c1 + c2 * Real.log ((k : ℝ) + 1))) *
              ‖cexpr (fun l => y (z l)) (fun i => (s i : ℂ))‖ := by
  let ρ : ℝ := min a 1 / 4
  let α : ℝ := min a 1 / 2
  let eJ : ℝ := ρ + C0
  let Bb : ℝ := max 1 (∑ j : Fin (J + 1), H * (j.val.factorial : ℝ) / ρ ^ j.val)
  have hmin : 0 < min a 1 := lt_min ha one_pos
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by dsimp [α]; have := min_le_right a (1 : ℝ); linarith
  have heJ : 0 ≤ eJ := by dsimp [eJ]; positivity
  have hBb : 1 ≤ Bb := le_max_left _ _
  have hlogB : 0 ≤ Real.log Bb := Real.log_nonneg hBb
  have hloga : 0 ≤ -Real.log α := by have := Real.log_nonpos hα.le hα1; linarith
  have hmg : 0 < min g d0 := lt_min hg hd0
  refine ⟨Real.log Bb + eJ * (8 / min g d0 + 1 / α + (-Real.log α)),
    eJ * (8 / min g d0 + 1), ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro L head _ x y A hcenter hrefreal hdisp hcoef hplain hsep hgap hnode hcollision
    apply finite_jet_field head J x y A hρ hα hα1 hg hd0 heJ hH hcoef hplain
    · intro q hq
      refine ⟨hrefreal q hq, ?_⟩
      dsimp [eJ]
      linarith [hdisp q hq]
    · intro q q' hq hq' hne
      have hy : y q = ((y q).re : ℂ) := by
        apply Complex.ext <;> simp [hrefreal q hq]
      have hy' : y q' = ((y q').re : ℂ) := by
        apply Complex.ext <;> simp [hrefreal q' hq']
      have he : ‖y q - y q'‖ = |(y q).re - (y q').re| := by
        rw [hy, hy', ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simp only [Complex.ofReal_re]
      rw [← he]
      exact hsep q q' hq hq' hne
    · exact hgap
    · exact hnode
    · intro q hq t
      have hn : (0 : ℝ) ≤ t := Nat.cast_nonneg _
      have hc := (hcenter q hq).2
      have hb := Complex.abs_re_le_norm (x q - (t : ℂ))
      simp only [Complex.sub_re, Complex.natCast_re] at hb
      rw [abs_of_nonpos (by linarith)] at hb
      have hm : min a 1 ≤ a := min_le_left _ _
      dsimp [α, ρ]
      linarith
    · exact hcollision

end CatalanCore.Uniform.Decay.Jet

#print axioms CatalanCore.Uniform.Decay.Jet.jet_field
#print axioms CatalanCore.Uniform.Decay.Jet.jetC1_nonneg

#print axioms CatalanCore.Uniform.Decay.Jet.jetExponent_le_heads
#print axioms CatalanCore.Uniform.Decay.Jet.finite_jet_field
#print axioms CatalanCore.Uniform.Decay.Jet.finite_jet_cauchy_bound
