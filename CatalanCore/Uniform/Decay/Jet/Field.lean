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


end CatalanCore.Uniform.Decay.Jet

#print axioms CatalanCore.Uniform.Decay.Jet.jet_field
#print axioms CatalanCore.Uniform.Decay.Jet.jetC1_nonneg
