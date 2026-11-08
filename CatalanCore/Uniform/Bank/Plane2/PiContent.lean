module

public import CatalanCore.Uniform.Bank.Plane2.TwoTermContent
public import CatalanCore.Uniform.Bank.Plane2.PiData
public import CatalanCore.Uniform.Bank.Plane2.BoundEdge

@[expose] public section
set_option Elab.async false

/-!
# `Plane2ContentPi`: the content of `π²` on the plane 2 geometry (lane H, wave P210-PI; ledger P210, P213, Z04)

`π²` is the simple-pole datum `S = {1, 1/2}`, `a = (1, -1)`; its Löwner sequences are `4` times those of the
half-shift frame `halves` (`Mn = lw / 4`, `halves_Mn_pi`), so the content route of the two-term bank applies to
`halves` on the geometry `altGeom (6/41)` (the bank `PiData` generated at `α = 3/41`; `CatValid`, `PreValid` are the
instances `c = 6/41` of the generic `TwoTermContent.halves_catValid_gen`, `halves_preValid_gen`), and the content
transports to the family of `piDatum` (`TwoTermContent.seq_content_of_halves`).
-/

namespace CatalanCore.Uniform.Bank.Plane2.PiContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Halves
  CatalanCore.Uniform.Bank.Plane2.TwoTermContent CatalanCore.Uniform.Bank.Plane2.PiAuto
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith
  CatalanCore.Arith.Hybrid CatalanFrames.HybCommon CatalanFrames.HybGen CatalanCore.Uniform.Content.RankProducer

/-! ### The Löwner entries of `π²` and of the frame -/

theorem halves_Delta (k : ℕ) : halves.Delta (k + 1) = piDatum.delta k := by
  show (CatalanFrames.Thirds.thirdsFrame (1 / 2) 4 (1 / 4) (1 / 4) 0 (by norm_num) (by norm_num)
    (by norm_num)).Delta (k + 1) = _
  rw [CatalanFrames.Thirds.Delta_eq]
  simp only [Datum.delta, piDatum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_one, Int.cast_neg, Int.cast_zero, zero_div, sub_zero]
  push_cast
  have : (k : ℚ) + 1 - 1 + 1 / 2 = k + 1 / 2 := by ring
  rw [this]
  ring

theorem halves_Dsq (k : ℕ) : halves.Dsq (k + 1) = -piDatum.delta1 k := by
  show (CatalanFrames.Thirds.thirdsFrame (1 / 2) 4 (1 / 4) (1 / 4) 0 (by norm_num) (by norm_num)
    (by norm_num)).Dsq (k + 1) = _
  rw [CatalanFrames.Thirds.Dsq_eq]
  simp only [Datum.delta1, piDatum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_one, Int.cast_neg, Int.cast_zero, mul_zero, zero_div, add_zero]
  push_cast
  have : (k : ℚ) + 1 - 1 + 1 / 2 = k + 1 / 2 := by ring
  rw [this]
  ring

theorem sum_Delta (a : ℕ) : ∀ b, a ≤ b →
    ∑ k ∈ Finset.Ioc a b, halves.Delta k = piDatum.f b - piDatum.f a := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ioc_succ_top hb, ih, halves_Delta]
    simp only [Datum.f, Finset.sum_range_succ]
    ring

theorem sum_Dsq (a : ℕ) : ∑ k ∈ Finset.Icc 1 a, halves.Dsq k = piDatum.e a := by
  induction a with
  | zero => simp [Datum.e]
  | succ a ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, halves_Dsq]
    simp only [Datum.e, Finset.sum_range_succ]
    ring

/-- The Löwner entries of the half-shift frame are a quarter of those of the sequences of `π²`. -/
theorem halves_Mn_pi (a b : ℕ) : halves.Mn a b = (1 / 4) * lw piDatum.f piDatum.e a b := by
  have hn : halves.norm = 4 := rfl
  unfold Frame.Mn lw
  rw [hn]
  by_cases h : a = b
  · subst h
    simp only [ite_true, sum_Dsq]
    ring
  · simp only [h, ite_false]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le, sum_Delta a b hlt.le]
      have : ((b : ℚ) - a) ≠ 0 := by
        have : (a : ℚ) < b := by exact_mod_cast hlt
        linarith
      field_simp
      try ring
    · rw [min_eq_right hgt.le, max_eq_left hgt.le, sum_Delta b a hgt.le]
      have : ((a : ℚ) - b) ≠ 0 := by
        have : (b : ℚ) < a := by exact_mod_cast hgt
        linarith
      have h2 : ((b : ℚ) - a) ≠ 0 := by
        intro h0; apply this; linarith
      field_simp
      try ring

/-! ### The content -/

theorem pi_catValid (depth : ℕ) :
    CatValid (6 / 41) (by norm_num) halves depth 2 1 4
      (max (NFr (1 / halves.norm) (-1 / halves.norm) 2 14) 50) bankData.cat := by
  rw [bankData_cat]
  exact halves_catValid_c6_41 depth bankWins bankPres

theorem pi_preValid (depth : ℕ) :
    PreValid (6 / 41) (by norm_num) halves depth 2
      (SmallBudget.add (SmallBudget.sqrtLog 5 56) SmallBudget.unit) (qq 1 1000) (qq 11 5) :=
  halves_preValid_c6_41 _ _ (by norm_num [qq]) (by norm_num [qq]) depth

/-- The content of the half-shift frame on the geometry `altGeom (6/41)`: the bank `PiData`. -/
theorem halves_content_c6_41 :
    HasScaledContent (AltEven (6 / 41) (by norm_num) halves 1) (altGeom (6 / 41) (by norm_num)).scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (6 / 41) (by norm_num) (by norm_num) (by decide +kernel)
    halves 1 (by decide) cFr_halves 1 (by decide) _ _ (pi_catValid 1) (pi_preValid 1)

/-- The finite content constant of the `π²` bank at the plane 2 slope. -/
def piLam : ℚ := bankData.Λ

/-- `piLam ≤ p2LamMax`, the largest content for which the receipt gives `335.20`. -/
theorem piLam_le : piLam ≤ p2LamMax := by
  unfold piLam p2LamMax
  rw [bankData_Λ]
  decide +kernel

/-- **The content of `π²` on the plane 2 geometry**, at `Λ = piLam ≤ p2LamMax`. -/
theorem plane2ContentPi : Plane2ContentPi (piLam : ℝ) :=
  seq_content_of_halves (6 / 41) p2c_pos piDatum.f piDatum.e halves_Mn_pi piDatum.xi 1
    halves_content_c6_41

end CatalanCore.Uniform.Bank.Plane2.PiContent

#print axioms CatalanCore.Uniform.Bank.Plane2.PiContent.halves_Mn_pi
#print axioms CatalanCore.Uniform.Bank.Plane2.PiContent.plane2ContentPi
#print axioms CatalanCore.Uniform.Bank.Plane2.PiContent.piLam_le
