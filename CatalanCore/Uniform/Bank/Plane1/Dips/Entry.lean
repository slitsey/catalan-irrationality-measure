module

public import CatalanCore.Uniform.Bank.Plane1.Dips.PeriodSum
public import CatalanCore.Uniform.Content.BankShared.KTerm.TropCell

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-! # The entry lemma of the dip rows (wave R0; ledger R01-R03; Lemma 5.1' of `DIP-RANK-CLOSED-FORM-2026-11-07.md` with the
repairs A1-A4 of `DIP-RANK-AUDIT-2026-11-08.md`)

Part 1 (this section): the entries of the Löwner matrix `Fr.Mn` in terms of the levels `Vp`, `Up` of `Dips.PeriodSum`:

* `Mn_ne_split`: for nodes `U ≠ V` below `p²/3`, `Mn U V = (Vp V - Vp U) / (p (V - U)) + g`, `g` `p`-integral;
* `Mn_diag_split`: `Mn t t = Up t / p² + g`;
* `Mn_in_fibre` (refinement (R)): for `U ≡ V (mod p)`, `p ^ w0 U V * Mn U V` is `p`-integral, where
  `w0 U V = 2 · 1[Vp U ≠ Vp V]` for `U ≠ V` and `w0 t t = 2 · 1[Up t ≠ 0]`;
* `pivot_alg` (pivot entry, weight `0`): if `X = A + j p` and `l · (j · Up A) = Vp X - Vp A` then `Mn A X - l · Mn A A` is
  `p`-integral;
* `Mn_off_form` (off the fibre): each entry is `(Vp V - Vp U) / (p (Y₀ - X₀)) + g` for the reference difference `d₀ = Y₀ - X₀`; `entry_const` combines the four terms of a gauged entry into `(1-l)(1-l')(V*(y) - V*(x)) / (p d₀) + g`.

Part 2: the gauged matrix `E₁ M E₂` and the weights `Wd`. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.BankShared.KTerm

section MnSplit

variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame}

theorem Mn_comm (a b : ℕ) : Fr.Mn a b = Fr.Mn b a := by
  unfold Frame.Mn
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

theorem int_inv_mem {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) : ((d : ℚ))⁻¹ ∈ LocRing p := by
  rw [mem_locRing, Rat.inv_intCast_den]
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
  simp only [hd0, ite_false]
  intro h
  exact hd (Int.natCast_dvd.2 h)

theorem nat_pow_mem (n : ℕ) : ((p : ℚ) ^ n) ∈ LocRing p := by
  have := int_mem_locRing (ℓ := p) ((p : ℤ) ^ n)
  push_cast at this
  exact this

variable (h3 : 3 ≤ p)

include h3 in
theorem offSum_form {u v : ℕ} (huv : u < v) (hdiff : ¬ p * p ∣ v - u) :
    ∃ R : ℚ, ∑ k ∈ Ioc u v, Fr.Delta k = (Vp p Fr v - Vp p Fr u) / p + R ∧
      R / ((v : ℚ) - u) ∈ LocRing p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  by_cases hd : p ∣ v - u
  · obtain ⟨s, hs⟩ := hd
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · subst h; omega
      · exact h
    have hs0 : ¬ p ∣ s := by
      rintro ⟨t, ht⟩
      apply hdiff
      refine ⟨t, ?_⟩
      rw [hs, ht]
      ring
    obtain rfl : v = u + s * p := by rw [Nat.mul_comm] at hs; omega
    obtain ⟨D, hD1, hD2⟩ := lemmaA h3 u s
    refine ⟨D, hD1, ?_⟩
    have e : (((u + s * p : ℕ) : ℚ) - u) = (s : ℚ) * p := by push_cast; ring
    rw [e]
    have : D / ((s : ℚ) * p) = (D / p) * (s : ℚ)⁻¹ := by
      have : (s : ℚ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
      field_simp
    rw [this]
    exact (LocRing p).mul_mem hD2 (inv_natCast_mem_locRing hs0)
  · refine ⟨∑ k ∈ Ioc u v, nonpolD p Fr k, offSum_split huv.le, ?_⟩
    have hdq : ((v : ℚ) - u) = ((v - u : ℕ) : ℚ) := by push_cast [Nat.cast_sub huv.le]; ring
    rw [hdq, div_eq_mul_inv]
    exact (LocRing p).mul_mem (offSum_nonpol_mem _ _) (inv_natCast_mem_locRing hd)

include h3 in
theorem Mn_lt_split (hnorm : Fr.norm = 1) {u v : ℕ} (huv : u < v) (hdiff : ¬ p * p ∣ v - u) :
    ∃ g ∈ LocRing p, Fr.Mn u v = (Vp p Fr v - Vp p Fr u) / (p * ((v : ℚ) - u)) + g := by
  obtain ⟨R, hR1, hR2⟩ := offSum_form h3 huv hdiff
  refine ⟨R / ((v : ℚ) - u), hR2, ?_⟩
  have hne : ((v : ℚ) - u) ≠ 0 := by
    have : (u : ℚ) < v := by exact_mod_cast huv
    linarith
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold Frame.Mn
  rw [if_neg huv.ne, min_eq_left huv.le, max_eq_right huv.le, hnorm, hR1]
  push_cast
  field_simp


/-- Convert the oriented integer difference to a natural difference. -/
theorem nat_diff_not_sq {u v : ℕ} (huv : u ≤ v)
    (h : ¬ (p : ℤ) * p ∣ (v : ℤ) - u) : ¬ p * p ∣ v - u := by
  intro hd
  apply h
  have hi := Int.natCast_dvd_natCast.mpr hd
  simpa only [Nat.cast_mul, Nat.cast_sub huv] using hi

include h3 in
theorem Mn_ne_split (hnorm : Fr.norm = 1) {u v : ℕ} (huv : u ≠ v)
    (hdiff : ¬ (p : ℤ) * p ∣ (v : ℤ) - u) :
    ∃ g ∈ LocRing p, Fr.Mn u v = (Vp p Fr v - Vp p Fr u) / (p * ((v : ℚ) - u)) + g := by
  rcases lt_or_gt_of_ne huv with h | h
  · exact Mn_lt_split h3 hnorm h (nat_diff_not_sq h.le hdiff)
  · have hrev : ¬ (p : ℤ) * p ∣ (u : ℤ) - v := by
      intro hd
      apply hdiff
      convert dvd_neg.mpr hd using 1 <;> ring
    obtain ⟨g, hg, e⟩ := Mn_lt_split h3 hnorm h (nat_diff_not_sq h.le hrev)
    refine ⟨g, hg, ?_⟩
    rw [Mn_comm, e]
    have e1 : Vp p Fr u - Vp p Fr v = -(Vp p Fr v - Vp p Fr u) := by ring
    have e2 : ((u : ℚ) - v) = -((v : ℚ) - u) := by ring
    rw [e1, e2, mul_neg, neg_div_neg_eq]

theorem Mn_diag_split (hnorm : Fr.norm = 1) (t : ℕ) :
    ∃ g ∈ LocRing p, Fr.Mn t t = Up p Fr t / (p : ℚ) ^ 2 + g := by
  refine ⟨-(∑ k ∈ Ioc 0 t, nonpolS p Fr k), (LocRing p).neg_mem (diag_nonpol_mem t), ?_⟩
  unfold Frame.Mn
  rw [if_pos rfl, hnorm]
  have e : ∑ k ∈ Icc 1 t, Fr.Dsq k = ∑ k ∈ Ioc 0 t, Fr.Dsq k := by
    congr 1
  rw [e, diag_split (p := p) (Fr := Fr) t]
  ring

/-- The weight of an in-fibre entry (refinement (R)). -/
noncomputable def w0 (p : ℕ) (Fr : Frame) (U V : ℕ) : ℕ :=
  open Classical in
  if U = V then (if Up p Fr U = 0 then 0 else 2) else (if Vp p Fr U = Vp p Fr V then 0 else 2)


/-- A bounded nonzero difference cannot be divisible by a prime square. -/
theorem diff_not_sq_of_lt {U V : ℕ} (hU : U < p * p) (hV : V < p * p) (hne : U ≠ V) :
    ¬ (p : ℤ) * p ∣ (V : ℤ) - U := by
  rintro ⟨f, hf⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [mul_zero, sub_eq_zero] at hf
    exact hne (by exact_mod_cast hf.symm)
  have hbig : (p : ℤ) * p ≤ |(V : ℤ) - U| := by
    rw [hf, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (p : ℤ) * p)]
    nlinarith [Int.one_le_abs hf0]
  have hsmall : |(V : ℤ) - U| < p * p := by
    rw [abs_lt]
    constructor <;> push_cast <;> nlinarith [(by exact_mod_cast hU : (U : ℤ) < p * p),
      (by exact_mod_cast hV : (V : ℤ) < p * p)]
  linarith

/-- The quotient of a square-free congruent difference is a local unit. -/
theorem fibre_quot {U V : ℕ} (hdiff : ¬ (p : ℤ) * p ∣ (V : ℤ) - U)
    (hf : (U : ℤ) ≡ V [ZMOD p]) : ∃ e : ℤ, (V : ℤ) - U = p * e ∧ ¬ (p : ℤ) ∣ e := by
  obtain ⟨e, he⟩ := Int.ModEq.dvd hf
  refine ⟨e, he, ?_⟩
  rintro ⟨f, hf⟩
  apply hdiff
  refine ⟨f, ?_⟩
  rw [he, hf]
  ring

include h3 in
theorem Mn_in_fibre (hnorm : Fr.norm = 1) {U V : ℕ}
    (hVU : Vp p Fr U ∈ LocRing p) (hVV : Vp p Fr V ∈ LocRing p)
    (hUU : Up p Fr U ∈ LocRing p)
    (hsq : U ≠ V → ¬ (p : ℤ) * p ∣ (V : ℤ) - U)
    (hf : (U : ℤ) ≡ V [ZMOD p]) : (p : ℚ) ^ (w0 p Fr U V) * Fr.Mn U V ∈ LocRing p := by
  classical
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  by_cases hUV : U = V
  · subst hUV
    obtain ⟨g, hg, e⟩ := Mn_diag_split (p := p) hnorm U
    by_cases hu : Up p Fr U = 0
    · simp only [w0, if_true, hu, pow_zero, one_mul, e, zero_div, zero_add]
      exact hg
    · simp only [w0, if_true, hu, if_false]
      rw [e, mul_add, mul_div_cancel₀ _ (pow_ne_zero 2 hp0)]
      exact (LocRing p).add_mem hUU ((LocRing p).mul_mem (nat_pow_mem 2) hg)
  · obtain ⟨g, hg, e⟩ := Mn_ne_split h3 hnorm hUV (hsq hUV)
    by_cases hv : Vp p Fr U = Vp p Fr V
    · simp only [w0, hUV, if_false, hv, if_true, pow_zero, one_mul, e, sub_self, zero_div, zero_add]
      exact hg
    · simp only [w0, hUV, if_false, hv]
      obtain ⟨q, hq1, hq2⟩ := fibre_quot (hsq hUV) hf
      have hq1' : ((V : ℚ) - U) = (p : ℚ) * (q : ℚ) := by exact_mod_cast hq1
      have hq0 : (q : ℚ) ≠ 0 := by
        intro h0
        have : q = 0 := by exact_mod_cast h0
        exact hq2 (this ▸ dvd_zero _)
      rw [e, hq1', mul_add]
      have : (p : ℚ) ^ 2 * ((Vp p Fr V - Vp p Fr U) / (p * (p * q))) =
          (Vp p Fr V - Vp p Fr U) * (q : ℚ)⁻¹ := by field_simp
      rw [this]
      exact (LocRing p).add_mem ((LocRing p).mul_mem
        ((LocRing p).sub_mem hVV hVU) (int_inv_mem hq2))
        ((LocRing p).mul_mem (nat_pow_mem 2) hg)

include h3 in
/-- **The pivot entry** (weight `0`). -/
theorem pivot_alg (hnorm : Fr.norm = 1) {A X j : ℕ} (hX : X = A + j * p) (hj0 : 0 < j) (hsq : ¬ (p : ℤ) * p ∣ (X : ℤ) - A)
    {l : ℚ} (hl : l ∈ LocRing p) (hrel : l * (j * Up p Fr A) = Vp p Fr X - Vp p Fr A) :
    Fr.Mn A X - l * Fr.Mn A A ∈ LocRing p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hAX : A < X := by rw [hX]; nlinarith [hp.out.pos]
  obtain ⟨g1, hg1, e1⟩ := Mn_lt_split h3 hnorm hAX (nat_diff_not_sq hAX.le hsq)
  obtain ⟨g2, hg2, e2⟩ := Mn_diag_split (p := p) hnorm A
  have hj : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
  have hXA : ((X : ℚ) - A) = j * p := by rw [hX]; push_cast; ring
  have key : (Vp p Fr X - Vp p Fr A) / (p * ((X : ℚ) - A)) - l * (Up p Fr A / (p : ℚ) ^ 2) = 0 := by
    rw [hXA, ← hrel]
    field_simp
    ring
  have : Fr.Mn A X - l * Fr.Mn A A = g1 - l * g2 := by
    rw [e1, e2]
    linear_combination key
  rw [this]
  exact (LocRing p).sub_mem hg1 ((LocRing p).mul_mem hl hg2)

/-- A reciprocal of a unit changes by an integer multiple of `p` only: `V / (p d) - V / (p d₀) ∈ ℤ_(p)`. -/
theorem diff_unit {V : ℚ} (hV : V ∈ LocRing p) {d d0 : ℤ} (hd : ¬ (p : ℤ) ∣ d) (hd0 : ¬ (p : ℤ) ∣ d0)
    (hdd : (p : ℤ) ∣ d0 - d) : V / (p * d) - V / (p * d0) ∈ LocRing p := by
  obtain ⟨e, he⟩ := hdd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hdq : (d : ℚ) ≠ 0 := by
    intro h; have : d = 0 := by exact_mod_cast h
    exact hd (this ▸ dvd_zero _)
  have hd0q : (d0 : ℚ) ≠ 0 := by
    intro h; have : d0 = 0 := by exact_mod_cast h
    exact hd0 (this ▸ dvd_zero _)
  have he' : (d0 : ℚ) = d + p * e := by exact_mod_cast (by linarith : d0 = d + p * e)
  have : V / (p * d) - V / (p * d0) = V * (e : ℚ) * ((d : ℚ))⁻¹ * ((d0 : ℚ))⁻¹ := by
    field_simp
    rw [he']
    ring
  rw [this]
  exact (LocRing p).mul_mem ((LocRing p).mul_mem ((LocRing p).mul_mem hV (int_mem_locRing e))
    (int_inv_mem hd)) (int_inv_mem hd0)

include h3 in
/-- Off the fibre, with `U ≡ X₀`, `V ≡ Y₀`: the entry in terms of the reference difference `d₀ = Y₀ - X₀`. -/
theorem Mn_off_form (hnorm : Fr.norm = 1) {U V X0 Y0 : ℕ}
    (hVU : Vp p Fr U ∈ LocRing p) (hVV : Vp p Fr V ∈ LocRing p) (hUX : (U : ℤ) ≡ X0 [ZMOD p]) (hVY : (V : ℤ) ≡ Y0 [ZMOD p])
    (hoff : ¬ (X0 : ℤ) ≡ Y0 [ZMOD p]) :
    ∃ g ∈ LocRing p, Fr.Mn U V = (Vp p Fr V - Vp p Fr U) / (p * ((Y0 : ℚ) - X0)) + g := by
  have hdV : ¬ (p : ℤ) ∣ ((V : ℤ) - U) := by
    intro h
    apply hoff
    have h1 : (p : ℤ) ∣ (V : ℤ) - U := h
    have h2 := (Int.ModEq.dvd hUX.symm)    -- p ∣ U - X0
    have h3 := (Int.ModEq.dvd hVY.symm)    -- p ∣ V - Y0
    have : (p : ℤ) ∣ (Y0 : ℤ) - X0 := by
      have := dvd_sub (dvd_sub h1 h3) (dvd_neg.2 h2)
      convert this using 1; ring
    exact (Int.modEq_iff_dvd.2 this)
  have hd0 : ¬ (p : ℤ) ∣ ((Y0 : ℤ) - X0) := fun h => hoff (Int.modEq_iff_dvd.2 h)
  have hUV : U ≠ V := by
    rintro rfl; exact hdV (by simp)
  obtain ⟨g, hg, e⟩ := Mn_ne_split h3 hnorm hUV (fun hd => hdV (dvd_trans (dvd_mul_right (p : ℤ) (p : ℤ)) hd))
  have hdd : (p : ℤ) ∣ ((Y0 : ℤ) - X0) - ((V : ℤ) - U) := by
    have h2 := (Int.ModEq.dvd hUX)    -- p ∣ X0 - U
    have h3 := (Int.ModEq.dvd hVY)    -- p ∣ Y0 - V
    have := dvd_sub h3 h2
    convert this using 1; ring
  have hdiff := diff_unit (p := p) ((LocRing p).sub_mem hVV hVU) hdV hd0 hdd
  refine ⟨g + ((Vp p Fr V - Vp p Fr U) / (p * (((V : ℤ) - U : ℤ) : ℚ)) -
    (Vp p Fr V - Vp p Fr U) / (p * (((Y0 : ℤ) - X0 : ℤ) : ℚ))), ?_, ?_⟩
  · refine (LocRing p).add_mem hg hdiff
  · rw [e]
    push_cast
    ring

end MnSplit

/-! ### Part 2: the gauged matrix -/

section Gauge

variable {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The data of a gauged entry matrix: the row node and column node of each index, which indices are common nodes,
the pivots (rows and columns) and their coefficients. -/
structure GData (ι : Type) where
  rn : ι → ℕ
  cn : ι → ℕ
  isC : ι → Bool
  π : ι → Option ι
  π' : ι → Option ι
  lr : ι → ℚ
  lc : ι → ℚ

namespace GData
variable (G : GData ι)

/-- The pivot of a row (itself if it has none). -/
def aR (x : ι) : ι := match G.π x with | some a => a | none => x
/-- The coefficient of the row pivot (`0` if none). -/
def rr (x : ι) : ℚ := match G.π x with | some _ => G.lr x | none => 0
def aC (y : ι) : ι := match G.π' y with | some b => b | none => y
def cc (y : ι) : ℚ := match G.π' y with | some _ => G.lc y | none => 0

/-- Entry of the ungauged matrix, as a constant and the coefficient of the variable. -/
noncomputable def m (Fr : Frame) (u v : ι) : ℚ := Fr.Mn (G.rn u) (G.cn v)
def δ (u v : ι) : ℚ := if u = v ∧ G.isC u = true then 1 else 0

/-- The constant term of the gauged entry. -/
noncomputable def cst (Fr : Frame) (x y : ι) : ℚ :=
  G.m Fr x y - G.cc y * G.m Fr x (G.aC y) - G.rr x * G.m Fr (G.aR x) y +
    G.rr x * G.cc y * G.m Fr (G.aR x) (G.aC y)
/-- The coefficient of the variable in the gauged entry. -/
def xco (x y : ι) : ℚ :=
  G.δ x y - G.cc y * G.δ x (G.aC y) - G.rr x * G.δ (G.aR x) y + G.rr x * G.cc y * G.δ (G.aR x) (G.aC y)

end GData

/-- The matrix of the member: `Mn (row node) (column node)` with the variable on the diagonal of common nodes. -/
noncomputable def Ment (Fr : Frame) (G : GData ι) : Matrix ι ι ℚ[X] :=
  Matrix.of fun a b => C (Fr.Mn (G.rn a) (G.cn b)) + if a = b ∧ G.isC a = true then X else 0

/-- The gauged matrix `E₁ M E₂`. -/
noncomputable def Mgauge (Fr : Frame) (G : GData ι) : Matrix ι ι ℚ[X] :=
  pivotRowGauge G.π (fun x => C (G.lr x)) * Ment Fr G * pivotColGauge G.π' (fun y => C (G.lc y))

theorem Ment_apply (Fr : Frame) (G : GData ι) (a b : ι) :
    Ment Fr G a b = C (G.m Fr a b) + C (G.δ a b) * X := by
  unfold Ment GData.m GData.δ
  simp only [Matrix.of_apply]
  split_ifs <;> simp

theorem gauged_entry (Fr : Frame) (G : GData ι) (hπ : ∀ x a, G.π x = some a → a < x)
    (x y : ι) :
    Mgauge Fr G x y = C (G.cst Fr x y) + C (G.xco x y) * X := by
  have h1 : ∀ (z w : ι), (match G.π z with | some a => (fun x => C (G.lr x)) z * Ment Fr G a w | none => 0)
      = C (G.rr z) * Ment Fr G (G.aR z) w := by
    intro z w
    rcases h : G.π z with _ | a <;> simp [GData.aR, GData.rr, h]
  have hrow : ∀ z w, (pivotRowGauge G.π (fun x => C (G.lr x)) * Ment Fr G) z w =
      Ment Fr G z w - C (G.rr z) * Ment Fr G (G.aR z) w := by
    intro z w
    rw [pivotRowGauge_mul_apply _ _ hπ]
    congr 1
    exact h1 z w
  unfold Mgauge
  rw [mul_pivotColGauge_apply]
  rcases h : G.π' y with _ | b
  · have e1 : G.cc y = 0 := by simp [GData.cc, h]
    have e2 : G.aC y = y := by simp [GData.aC, h]
    simp only [e1, e2, hrow, Ment_apply, GData.cst, GData.xco, map_sub, map_add, map_mul, map_zero]
    ring
  · have e1 : G.cc y = G.lc y := by simp [GData.cc, h]
    have e2 : G.aC y = b := by simp [GData.aC, h]
    simp only [e1, e2, hrow, Ment_apply, GData.cst, GData.xco, map_sub, map_add, map_mul]
    ring

end Gauge


/-! ### Part 3: the weights and the entry lemma -/

section Weights

variable {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame}

/-- The hypotheses of the entry lemma.  `Vr`, `Vc` are the effective levels `V*` of rows and columns. -/
structure GOK (p : ℕ) [Fact p.Prime] (Fr : Frame) (G : GData ι) (Vr Vc : ι → ℚ) : Prop where
  h3 : 3 ≤ p
  hnorm : Fr.norm = 1
  v_r : ∀ u, Vp p Fr (G.rn u) ∈ LocRing p
  v_c : ∀ u, Vp p Fr (G.cn u) ∈ LocRing p
  u_r : ∀ u, Up p Fr (G.rn u) ∈ LocRing p
  u_c : ∀ u, Up p Fr (G.cn u) ∈ LocRing p
  square_free : ∀ u v, G.rn u ≠ G.cn v → ¬ (p : ℤ) * p ∣ (G.cn v : ℤ) - G.rn u
  isC_node : ∀ u, G.isC u = true → G.rn u = G.cn u
  rowPiv : ∀ x a, G.π x = some a → G.isC a = true ∧ G.isC x = false ∧ ∃ j : ℕ, 0 < j ∧
    G.rn x = G.rn a + j * p ∧ G.lr x * (j * Up p Fr (G.rn a)) = Vp p Fr (G.rn x) - Vp p Fr (G.rn a)
  colPiv : ∀ y b, G.π' y = some b → G.isC b = true ∧ G.isC y = false ∧ ∃ j : ℕ, 0 < j ∧
    G.cn y = G.cn b + j * p ∧ G.lc y * (j * Up p Fr (G.cn b)) = Vp p Fr (G.cn y) - Vp p Fr (G.cn b)
  lr_mem : ∀ x, G.lr x ∈ LocRing p
  lc_mem : ∀ y, G.lc y ∈ LocRing p
  Vr_spec : ∀ x, (1 - G.rr x) * Vr x = Vp p Fr (G.rn x) - G.rr x * Vp p Fr (G.rn (G.aR x))
  Vc_spec : ∀ y, (1 - G.cc y) * Vc y = Vp p Fr (G.cn y) - G.cc y * Vp p Fr (G.cn (G.aC y))

/-- The weight of the gauged entry `(x, y)` (Lemma 5.1' (i)-(iii)). -/
noncomputable def Wd (p : ℕ) (Fr : Frame) (G : GData ι) (Vr Vc : ι → ℚ) (x y : ι) : ℕ :=
  if (G.π x = some y ∨ G.π' y = some x) then 0
  else if ((G.rn x : ℤ) ≡ G.cn y [ZMOD p]) then
    max (max (w0 p Fr (G.rn x) (G.cn y)) (w0 p Fr (G.rn x) (G.cn (G.aC y))))
      (max (w0 p Fr (G.rn (G.aR x)) (G.cn y)) (w0 p Fr (G.rn (G.aR x)) (G.cn (G.aC y))))
  else if Vr x = Vc y then 0 else 1

variable {G : GData ι} {Vr Vc : ι → ℚ}

theorem rr_mem (hG : GOK p Fr G Vr Vc) (x : ι) : G.rr x ∈ LocRing p := by
  unfold GData.rr
  rcases G.π x with _ | a
  · exact (LocRing p).zero_mem
  · exact hG.lr_mem x

theorem cc_mem (hG : GOK p Fr G Vr Vc) (y : ι) : G.cc y ∈ LocRing p := by
  unfold GData.cc
  rcases G.π' y with _ | a
  · exact (LocRing p).zero_mem
  · exact hG.lc_mem y

theorem delta_mem (u v : ι) : G.δ u v ∈ LocRing p := by
  unfold GData.δ
  split_ifs
  · exact (LocRing p).one_mem
  · exact (LocRing p).zero_mem

theorem rn_aR_mod (hG : GOK p Fr G Vr Vc) (x : ι) : (G.rn (G.aR x) : ℤ) ≡ G.rn x [ZMOD p] := by
  rcases h : G.π x with _ | a
  · have : G.aR x = x := by simp [GData.aR, h]
    rw [this]
  · obtain ⟨-, -, j, -, hj, -⟩ := hG.rowPiv x a h
    have : G.aR x = a := by simp [GData.aR, h]
    rw [this, hj]
    exact Int.modEq_iff_dvd.2 ⟨j, by push_cast; ring⟩

theorem cn_aC_mod (hG : GOK p Fr G Vr Vc) (y : ι) : (G.cn (G.aC y) : ℤ) ≡ G.cn y [ZMOD p] := by
  rcases h : G.π' y with _ | b
  · have : G.aC y = y := by simp [GData.aC, h]
    rw [this]
  · obtain ⟨-, -, j, -, hj, -⟩ := hG.colPiv y b h
    have : G.aC y = b := by simp [GData.aC, h]
    rw [this, hj]
    exact Int.modEq_iff_dvd.2 ⟨j, by push_cast; ring⟩

theorem term_mem {W w : ℕ} (hW : w ≤ W) {c m : ℚ} (hc : c ∈ LocRing p) (hm : (p : ℚ) ^ w * m ∈ LocRing p) :
    (p : ℚ) ^ W * (c * m) ∈ LocRing p := by
  have : (p : ℚ) ^ W * (c * m) = ((p : ℚ) ^ (W - w)) * c * ((p : ℚ) ^ w * m) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hW
    rw [Nat.add_sub_cancel_left, pow_add]
    ring
  rw [this]
  exact (LocRing p).mul_mem ((LocRing p).mul_mem (nat_pow_mem _) hc) hm


theorem GOK.in_fibre (hG : GOK p Fr G Vr Vc) (u v : ι)
    (hf : (G.rn u : ℤ) ≡ G.cn v [ZMOD p]) :
    (p : ℚ) ^ (w0 p Fr (G.rn u) (G.cn v)) * Fr.Mn (G.rn u) (G.cn v) ∈ LocRing p :=
  Mn_in_fibre hG.h3 hG.hnorm (hG.v_r u) (hG.v_c v) (hG.u_r u) (hG.square_free u v) hf

/-- **The constant term of every gauged entry is `p^{Wd}`-integral.** -/
theorem entry_const (hG : GOK p Fr G Vr Vc) (x y : ι) :
    (p : ℚ) ^ (Wd p Fr G Vr Vc x y) * G.cst Fr x y ∈ LocRing p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold Wd
  by_cases hpv : (G.π x = some y ∨ G.π' y = some x)
  · rw [if_pos hpv, pow_zero, one_mul]
    rcases hpv with h | h
    · obtain ⟨hCa, hCx, j, hj0, hX, hrel⟩ := hG.rowPiv x y h
      have hπ'y : G.π' y = none := by
        rcases h' : G.π' y with _ | b
        · rfl
        · exact absurd (hG.colPiv y b h').2.1 (by simp [hCa])
      have e1 : G.aR x = y := by simp [GData.aR, h]
      have e2 : G.rr x = G.lr x := by simp [GData.rr, h]
      have e3 : G.aC y = y := by simp [GData.aC, hπ'y]
      have e4 : G.cc y = 0 := by simp [GData.cc, hπ'y]
      have hc := hG.isC_node y hCa
      have hne : G.rn x ≠ G.rn y := by rw [hX]; nlinarith [hp.out.pos]
      have hsq : ¬ (p : ℤ) * p ∣ (G.rn x : ℤ) - G.rn y := by
        intro hd
        apply hG.square_free x y (by rw [← hc]; exact hne)
        rw [← hc]
        convert dvd_neg.mpr hd using 1 <;> ring
      have key := pivot_alg hG.h3 hG.hnorm hX hj0 hsq (hG.lr_mem x) hrel
      have e5 := Mn_comm (Fr := Fr) (G.rn x) (G.rn y)
      unfold GData.cst GData.m
      rw [e1, e2, e3, e4, ← hc]
      convert key using 1
      rw [e5]
      ring
    · obtain ⟨hCa, hCy, j, hj0, hY, hrel⟩ := hG.colPiv y x h
      have hπx : G.π x = none := by
        rcases h' : G.π x with _ | b
        · rfl
        · exact absurd (hG.rowPiv x b h').2.1 (by simp [hCa])
      have e1 : G.aR x = x := by simp [GData.aR, hπx]
      have e2 : G.rr x = 0 := by simp [GData.rr, hπx]
      have e3 : G.aC y = x := by simp [GData.aC, h]
      have e4 : G.cc y = G.lc y := by simp [GData.cc, h]
      have hc := hG.isC_node x hCa
      rw [← hc] at hY hrel
      have hne : G.rn x ≠ G.cn y := by rw [hY]; nlinarith [hp.out.pos]
      have key := pivot_alg hG.h3 hG.hnorm hY hj0 (hG.square_free x y hne) (hG.lc_mem y) hrel
      unfold GData.cst GData.m
      rw [e1, e2, e3, e4, ← hc]
      convert key using 1
      ring
  · rw [if_neg hpv]
    by_cases hfi : ((G.rn x : ℤ) ≡ G.cn y [ZMOD p])
    · rw [if_pos hfi]
      have hfx : ∀ (u v : ι), (G.rn u : ℤ) ≡ G.rn x [ZMOD p] → (G.cn v : ℤ) ≡ G.cn y [ZMOD p] →
          (G.rn u : ℤ) ≡ G.cn v [ZMOD p] := fun u v hu hv => hu.trans (hfi.trans hv.symm)
      have hrefl : (G.rn x : ℤ) ≡ G.rn x [ZMOD p] := Int.ModEq.refl _
      have hrefl' : (G.cn y : ℤ) ≡ G.cn y [ZMOD p] := Int.ModEq.refl _
      have m1 := hG.in_fibre x y (hfx x y hrefl hrefl')
      have m2 := hG.in_fibre x (G.aC y) (hfx x (G.aC y) hrefl (cn_aC_mod hG y))
      have m3 := hG.in_fibre (G.aR x) y (hfx (G.aR x) y (rn_aR_mod hG x) hrefl')
      have m4 := hG.in_fibre (G.aR x) (G.aC y)
        (hfx (G.aR x) (G.aC y) (rn_aR_mod hG x) (cn_aC_mod hG y))
      set W := max (max (w0 p Fr (G.rn x) (G.cn y)) (w0 p Fr (G.rn x) (G.cn (G.aC y))))
        (max (w0 p Fr (G.rn (G.aR x)) (G.cn y)) (w0 p Fr (G.rn (G.aR x)) (G.cn (G.aC y)))) with hW
      have t1 := term_mem (W := W) (by omega) (LocRing p).one_mem m1
      have t2 := term_mem (W := W) (by omega) (cc_mem hG y) m2
      have t3 := term_mem (W := W) (by omega) (rr_mem hG x) m3
      have t4 := term_mem (W := W) (by omega) ((LocRing p).mul_mem (rr_mem hG x) (cc_mem hG y)) m4
      have : (p : ℚ) ^ W * G.cst Fr x y =
          (p : ℚ) ^ W * (1 * Fr.Mn (G.rn x) (G.cn y)) - (p : ℚ) ^ W * (G.cc y * Fr.Mn (G.rn x) (G.cn (G.aC y))) -
          (p : ℚ) ^ W * (G.rr x * Fr.Mn (G.rn (G.aR x)) (G.cn y)) +
          (p : ℚ) ^ W * (G.rr x * G.cc y * Fr.Mn (G.rn (G.aR x)) (G.cn (G.aC y))) := by
        unfold GData.cst GData.m; ring
      rw [this]
      exact (LocRing p).add_mem ((LocRing p).sub_mem ((LocRing p).sub_mem t1 t2) t3) t4
    · rw [if_neg hfi]
      set l := G.rr x with hl
      set l' := G.cc y with hl'
      have hl_mem : l ∈ LocRing p := rr_mem hG x
      have hl'_mem : l' ∈ LocRing p := cc_mem hG y
      have hd0 : ¬ (p : ℤ) ∣ ((G.cn y : ℤ) - G.rn x) := fun h => hfi (Int.modEq_iff_dvd.2 h)
      have g1 := Mn_off_form hG.h3 hG.hnorm (hG.v_r x) (hG.v_c y)
        (Int.ModEq.refl _) (Int.ModEq.refl _) hfi
      have g2 := Mn_off_form hG.h3 hG.hnorm (hG.v_r x) (hG.v_c (G.aC y))
        (Int.ModEq.refl _) (cn_aC_mod hG y) hfi
      have g3 := Mn_off_form hG.h3 hG.hnorm (hG.v_r (G.aR x)) (hG.v_c y)
        (rn_aR_mod hG x) (Int.ModEq.refl _) hfi
      have g4 := Mn_off_form hG.h3 hG.hnorm (hG.v_r (G.aR x)) (hG.v_c (G.aC y))
        (rn_aR_mod hG x) (cn_aC_mod hG y) hfi
      obtain ⟨a1, ha1, e1⟩ := g1
      obtain ⟨a2, ha2, e2⟩ := g2
      obtain ⟨a3, ha3, e3⟩ := g3
      obtain ⟨a4, ha4, e4⟩ := g4
      set B : ℚ := (1 - l) * (Vp p Fr (G.cn y) - l' * Vp p Fr (G.cn (G.aC y))) -
        (1 - l') * (Vp p Fr (G.rn x) - l * Vp p Fr (G.rn (G.aR x))) with hB
      have hcst : G.cst Fr x y = B / (p * (((G.cn y : ℕ) : ℚ) - (G.rn x : ℕ))) +
          (a1 - l' * a2 - l * a3 + l * l' * a4) := by
        unfold GData.cst GData.m
        rw [e1, e2, e3, e4]
        ring
      have hBmem : B ∈ LocRing p := by
        refine (LocRing p).sub_mem ((LocRing p).mul_mem ((LocRing p).sub_mem (LocRing p).one_mem hl_mem)
          ((LocRing p).sub_mem (hG.v_c y) ((LocRing p).mul_mem hl'_mem
            (hG.v_c _)))) ((LocRing p).mul_mem ((LocRing p).sub_mem (LocRing p).one_mem hl'_mem)
          ((LocRing p).sub_mem (hG.v_r x) ((LocRing p).mul_mem hl_mem
            (hG.v_r _))))
      have hgmem : (a1 - l' * a2 - l * a3 + l * l' * a4) ∈ LocRing p := by
        refine (LocRing p).add_mem ((LocRing p).sub_mem ((LocRing p).sub_mem ha1 ((LocRing p).mul_mem hl'_mem ha2))
          ((LocRing p).mul_mem hl_mem ha3)) ((LocRing p).mul_mem ((LocRing p).mul_mem hl_mem hl'_mem) ha4)
      have hBeq : B = (1 - l) * (1 - l') * (Vc y - Vr x) := by
        have s1 := hG.Vc_spec y
        have s2 := hG.Vr_spec x
        have : (1 - l) * (1 - l') * (Vc y - Vr x) =
          (1 - l) * ((1 - l') * Vc y) - (1 - l') * ((1 - l) * Vr x) := by ring
        rw [this, s1, s2]
      by_cases hv : Vr x = Vc y
      · rw [if_pos hv, pow_zero, one_mul, hcst]
        have : B = 0 := by rw [hBeq, hv]; ring
        rw [this, zero_div, zero_add]
        exact hgmem
      · rw [if_neg hv, pow_one, hcst, mul_add]
        have hd0q : (((G.cn y : ℕ) : ℚ) - (G.rn x : ℕ)) = ((((G.cn y : ℕ) : ℤ) - (G.rn x : ℕ) : ℤ) : ℚ) := by
          push_cast; ring
        have hne : (((G.cn y : ℕ) : ℚ) - (G.rn x : ℕ)) ≠ 0 := by
          intro h0
          apply hd0
          have h1 : ((G.cn y : ℕ) : ℤ) = ((G.rn x : ℕ) : ℤ) := by exact_mod_cast (sub_eq_zero.1 h0)
          rw [h1, sub_self]; exact dvd_zero _
        have : (p : ℚ) * (B / (p * (((G.cn y : ℕ) : ℚ) - (G.rn x : ℕ)))) =
            B * ((((G.cn y : ℕ) : ℤ) - (G.rn x : ℕ) : ℤ) : ℚ)⁻¹ := by
          rw [← hd0q]
          field_simp
        rw [this]
        refine (LocRing p).add_mem ((LocRing p).mul_mem hBmem (int_inv_mem hd0))
          ((LocRing p).mul_mem ?_ hgmem)
        have := int_mem_locRing (ℓ := p) (p : ℤ)
        simpa using this

theorem xco_mem (hG : GOK p Fr G Vr Vc) (x y : ι) : G.xco x y ∈ LocRing p := by
  unfold GData.xco
  exact (LocRing p).add_mem ((LocRing p).sub_mem ((LocRing p).sub_mem (delta_mem x y) ((LocRing p).mul_mem
    (cc_mem hG y) (delta_mem x (G.aC y)))) ((LocRing p).mul_mem (rr_mem hG x) (delta_mem (G.aR x) y)))
    ((LocRing p).mul_mem ((LocRing p).mul_mem (rr_mem hG x) (cc_mem hG y)) (delta_mem (G.aR x) (G.aC y)))

/-- **The entry lemma** (Lemma 5.1', items (i)-(iii), with the repairs A1-A4): every entry of the gauged matrix
`E₁ M E₂` has Gauss valuation at least `-Wd`. -/
theorem entry_gle (hG : GOK p Fr G Vr Vc) (hπ : ∀ x a, G.π x = some a → a < x) (x y : ι) :
    GLE p (Wd p Fr G Vr Vc x y) (Mgauge Fr G x y) := by
  rw [gauged_entry Fr G hπ x y]
  have h1 : GLE p (Wd p Fr G Vr Vc x y) (C (G.cst Fr x y)) := GLE.C_iff.2 (entry_const hG x y)
  have h2 : GLE p (Wd p Fr G Vr Vc x y) (C (G.xco x y) * X) := by
    have hc : GLE p (Wd p Fr G Vr Vc x y) (C (G.xco x y)) :=
      GLE.C_iff.2 ((LocRing p).mul_mem (nat_pow_mem _) (xco_mem hG x y))
    simpa using hc.mul (GLE.X (p := p))
  exact h1.add h2

end Weights

end CatalanCore.Uniform.Bank.Plane1.Dips

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Mn_in_fibre
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.pivot_alg
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Mn_off_form
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.gauged_entry
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.entry_const
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.entry_gle
