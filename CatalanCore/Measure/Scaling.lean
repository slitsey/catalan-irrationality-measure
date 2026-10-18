module

public import CatalanCore.Measure.Statements

@[expose] public section

/-!
# Generic rational affine scaling of irrationality measures

For real `x` and rational `a ≠ 0`, `b`: irrationality and the measure bound transfer from `x`
to `a * x + b` with the same exponent (strict slack absorbs the constants).
Replaces the legacy `double_79` (which lost one unit of exponent).
Convention: `IsCoprime p q` as in `PolyFamily.MeasureLB`; `Nat.Coprime p.natAbs q` variants below.
-/

namespace CatalanCore.Measure

/-- The measure statement for a real number (cf. `PolyFamily.MeasureLB`, which is this at
`Fam.const`). -/
def MeasureLBAt (x E : ℝ) : Prop :=
  ∀ e > 0, ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
    (q : ℝ) ^ (-(E + e)) < |x - (p : ℝ) / q|

theorem MeasureLB_iff (Fam : PolyFamily) (E : ℝ) : Fam.MeasureLB E ↔ MeasureLBAt Fam.const E :=
  Iff.rfl

theorem MeasureLBAt.mono {x E E' : ℝ} (hE : E ≤ E') (h : MeasureLBAt x E) : MeasureLBAt x E' := by
  intro e he
  obtain ⟨q₀, H⟩ := h (e + (E' - E)) (by linarith)
  refine ⟨max q₀ 1, fun p q hq hc => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  refine lt_of_le_of_lt ?_ (H p q (le_trans (le_max_left _ _) hq) hc)
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)

theorem isCoprime_iff_natCoprime (p : ℤ) (q : ℕ) :
    IsCoprime p (q : ℤ) ↔ Nat.Coprime p.natAbs q := by
  rw [Int.isCoprime_iff_gcd_eq_one]; rfl

/-- Reduction of `((p/q) - u/v) / (n/d)` to lowest terms, with denominator controls. -/
theorem reduce_affine (p u : ℤ) (q d v n : ℕ) (hq : 0 < q) (hd : 0 < d) (hv : 0 < v)
    (hn : 0 < n) (hc : IsCoprime p (q : ℤ)) :
    ∃ (p' : ℤ) (q' : ℕ), IsCoprime p' (q' : ℤ) ∧ 0 < q' ∧ q' ≤ q * v * n ∧ q ≤ d * v * q' ∧
      (((p : ℝ) / q - (u : ℝ) / v) / ((n : ℝ) / d)) = (p' : ℝ) / q' := by
  set P : ℤ := (p * v - u * q) * d with hP
  set Qn : ℕ := q * v * n with hQn
  have hQpos : 0 < Qn := by positivity
  set g : ℕ := Int.gcd P (Qn : ℤ) with hg
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hQpos.ne')
  have hgP : (g : ℤ) ∣ P := Int.gcd_dvd_left _ _
  have hgQz : (g : ℤ) ∣ (Qn : ℤ) := Int.gcd_dvd_right _ _
  have hgQ : g ∣ Qn := Int.natCast_dvd_natCast.mp hgQz
  -- g divides d * v * (v * n)
  have hgM : (g : ℤ) ∣ (q : ℤ) * (v * n) := by
    have : (Qn : ℤ) = (q : ℤ) * (v * n) := by simp [hQn]; ring
    rw [← this]; exact hgQz
  have hg2 : (g : ℤ) ∣ (d : ℤ) * v * (v * n) * p := by
    have h1 : (g : ℤ) ∣ ((v * n : ℕ) : ℤ) * P := dvd_mul_of_dvd_right hgP _
    have h2 : (g : ℤ) ∣ (d : ℤ) * u * ((q : ℤ) * (v * n)) := dvd_mul_of_dvd_right hgM _
    have h3 := dvd_add h1 h2
    convert h3 using 1
    simp only [hP]; push_cast; ring
  have hg3 : (g : ℤ) ∣ (d : ℤ) * v * (v * n) * q := by
    have : (d : ℤ) * v * (v * n) * q = (d * v) * ((q : ℤ) * (v * n)) := by ring
    rw [this]; exact dvd_mul_of_dvd_right hgM _
  obtain ⟨s, t, hst⟩ := hc
  have hgD : (g : ℤ) ∣ (d : ℤ) * v * (v * n) := by
    have := dvd_add (dvd_mul_of_dvd_right hg2 s) (dvd_mul_of_dvd_right hg3 t)
    convert this using 1
    linear_combination (-((d : ℤ) * v * (v * n))) * hst
  have hgle : g ≤ d * v * (v * n) := by
    have := Int.le_of_dvd (by positivity) hgD
    exact_mod_cast this
  obtain ⟨q', hq'⟩ := hgQ
  have hq'pos : 0 < q' := by
    rcases Nat.eq_zero_or_pos q' with h | h
    · rw [h] at hq'; omega
    · exact h
  obtain ⟨p', hp'⟩ := hgP
  have hQz : (Qn : ℤ) = g * q' := by exact_mod_cast hq'
  refine ⟨p', q', ?_, hq'pos, ?_, ?_, ?_⟩
  · have h1 := Int.gcd_div_gcd_div_gcd (i := P) (j := (Qn : ℤ)) (by
      rw [← hg]; exact_mod_cast hgpos)
    rw [← hg] at h1
    have e1 : P / (g : ℤ) = p' := by rw [hp']; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hgpos.ne')
    have e2 : (Qn : ℤ) / (g : ℤ) = q' := by
      rw [hQz]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hgpos.ne')
    rw [e1, e2] at h1
    rw [Int.isCoprime_iff_gcd_eq_one]; exact h1
  · calc q' ≤ g * q' := Nat.le_mul_of_pos_left _ hgpos
      _ = Qn := hq'.symm
  · have h1 : Qn ≤ d * v * (v * n) * q' := by
      rw [hq']; exact Nat.mul_le_mul_right _ hgle
    have h2 : q * (v * n) ≤ (d * v * q') * (v * n) := by
      calc q * (v * n) = Qn := by simp [hQn]; ring
        _ ≤ d * v * (v * n) * q' := h1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h2 (by positivity)
  · have hQr : (Qn : ℝ) = g * q' := by exact_mod_cast hq'
    have hPr : (P : ℝ) = g * p' := by exact_mod_cast hp'
    have hq'r : (0 : ℝ) < q' := by exact_mod_cast hq'pos
    have hgr : (0 : ℝ) < g := by exact_mod_cast hgpos
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hvr : (0 : ℝ) < v := by exact_mod_cast hv
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd
    have hlhs : (((p : ℝ) / q - (u : ℝ) / v) / ((n : ℝ) / d)) = (P : ℝ) / Qn := by
      simp only [hP, hQn]; push_cast; field_simp
    rw [hlhs, hQr, hPr]
    field_simp

/-- Core transfer, fixed exponents, positive slope. -/
theorem affine_pos_core {x E E' : ℝ} (hE : 0 ≤ E) (hEE : E < E') (a b : ℚ) (ha : 0 < a)
    (H : ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-E) < |x - (p : ℝ) / q|) :
    ∃ q₁ : ℕ, ∀ (p : ℤ) (q : ℕ), q₁ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-E') < |(a : ℝ) * x + b - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := H
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a.num = n := Int.eq_ofNat_of_zero_le (Rat.num_nonneg.mpr ha.le)
  have hnpos : 0 < n := by
    have := Rat.num_pos.mpr ha; omega
  have hdpos : 0 < a.den := a.den_pos
  have hvpos : 0 < b.den := b.den_pos
  set d := a.den
  set v := b.den
  have ha' : (a : ℝ) = (n : ℝ) / d := by rw [Rat.cast_def, hn]; push_cast; rfl
  have hb' : (b : ℝ) = (b.num : ℝ) / v := by rw [Rat.cast_def]
  set δ := E' - E with hδ
  have hδpos : 0 < δ := by linarith
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  set w : ℝ := ((v * n : ℕ) : ℝ) ^ E with hw
  have hwpos : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨max (max (d * v * q₀) 1) ⌈(w / a) ^ (1 / δ)⌉₊, fun p q hq hc => ?_⟩
  have hq1 : d * v * q₀ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : 1 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : ⌈(w / a) ^ (1 / δ)⌉₊ ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : 0 < q := hq2
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  obtain ⟨p', q', hc', hq'pos, hq'le, hqle, hr⟩ :=
    reduce_affine p b.num q d v n hqpos hdpos hvpos hnpos hc
  have hq0' : q₀ ≤ q' := by
    have : d * v * q₀ ≤ d * v * q' := le_trans hq1 hqle
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  have h1 := H p' q' hq0' hc'
  have hq'r : (0 : ℝ) < q' := by exact_mod_cast hq'pos
  have hid : (a : ℝ) * x + b - (p : ℝ) / q = a * (x - (p' : ℝ) / q') := by
    rw [← hr, ha', hb']
    have : (n : ℝ) ≠ 0 := by positivity
    have : (d : ℝ) ≠ 0 := by positivity
    have : (v : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos hapos]
  -- q' ≤ q * (v * n)
  have hq'le : (q' : ℝ) ≤ (q : ℝ) * ((v * n : ℕ) : ℝ) := by
    have : q' ≤ q * (v * n) := by
      calc q' ≤ q * v * n := hq'le
        _ = q * (v * n) := by ring
    exact_mod_cast this
  have h2 : ((q : ℝ) * ((v * n : ℕ) : ℝ)) ^ (-E) ≤ (q' : ℝ) ^ (-E) :=
    Real.rpow_le_rpow_of_nonpos hq'r hq'le (by linarith)
  rw [Real.mul_rpow hqr.le (by positivity)] at h2
  have hvn : ((v * n : ℕ) : ℝ) ^ (-E) = w⁻¹ := by rw [hw, Real.rpow_neg (by positivity)]
  rw [hvn] at h2
  -- q ^ δ ≥ w / a
  have hqδ : w / a ≤ (q : ℝ) ^ δ := by
    have hC : 0 ≤ w / a := by positivity
    have : (w / a) ^ (1 / δ) ≤ q := le_trans (Nat.le_ceil _) (by exact_mod_cast hq3)
    calc w / a = ((w / a) ^ (1 / δ)) ^ δ := by
            rw [← Real.rpow_mul hC, one_div_mul_cancel hδpos.ne', Real.rpow_one]
      _ ≤ (q : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) this hδpos.le
  have hA : 0 < (q : ℝ) ^ (-E) := Real.rpow_pos_of_pos hqr _
  have hsplit : (q : ℝ) ^ (-E') = (q : ℝ) ^ (-E) / (q : ℝ) ^ δ := by
    rw [hδ, show -E' = -E - (E' - E) by ring, Real.rpow_sub hqr]
  have hqδpos : 0 < (q : ℝ) ^ δ := Real.rpow_pos_of_pos hqr _
  have h3 : (q : ℝ) ^ (-E') ≤ a * ((q : ℝ) ^ (-E) * w⁻¹) := by
    rw [hsplit, div_le_iff₀ hqδpos]
    have : w ≤ a * (q : ℝ) ^ δ := by rwa [div_le_iff₀ hapos, mul_comm] at hqδ
    have h4 : (q : ℝ) ^ (-E) * w⁻¹ * (a * (q : ℝ) ^ δ) ≥ (q : ℝ) ^ (-E) * w⁻¹ * w :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have h5 : (q : ℝ) ^ (-E) * w⁻¹ * w = (q : ℝ) ^ (-E) := by field_simp
    nlinarith
  have h6 : (q : ℝ) ^ (-E) * w⁻¹ ≤ (q' : ℝ) ^ (-E) := h2
  nlinarith [mul_lt_mul_of_pos_left h1 hapos, mul_le_mul_of_nonneg_left h6 hapos.le]

theorem MeasureLBAt.neg {x E : ℝ} (h : MeasureLBAt x E) : MeasureLBAt (-x) E := by
  intro e he
  obtain ⟨q₀, H⟩ := h e he
  refine ⟨q₀, fun p q hq hc => ?_⟩
  have := H (-p) q hq hc.neg_left
  rw [show |-x - (p : ℝ) / q| = |x - ((-p : ℤ) : ℝ) / q| by
    rw [← abs_neg]; push_cast; ring_nf]
  exact this

/-- **Affine transfer of the measure bound** (same exponent). Needs `0 ≤ E`. -/
theorem MeasureLBAt.affine {x E : ℝ} (hE : 0 ≤ E) (h : MeasureLBAt x E) (a b : ℚ) (ha : a ≠ 0) :
    MeasureLBAt ((a : ℝ) * x + b) E := by
  suffices key : ∀ (y : ℝ), MeasureLBAt y E → ∀ a : ℚ, 0 < a → MeasureLBAt ((a : ℝ) * y + b) E by
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have := key (-x) h.neg (-a) (by linarith)
      convert this using 2; push_cast; ring
    · exact key x h a hpos
  intro y hy a ha e he
  obtain ⟨q₀, H⟩ := hy (e / 2) (by linarith)
  obtain ⟨q₁, H'⟩ := affine_pos_core (x := y) (E := E + e / 2) (E' := E + e) (by linarith)
    (by linarith) a b ha ⟨q₀, H⟩
  exact ⟨q₁, H'⟩

theorem irrational_affine {x : ℝ} (hx : Irrational x) (a b : ℚ) (ha : a ≠ 0) :
    Irrational ((a : ℝ) * x + b) :=
  (hx.ratCast_mul ha).add_ratCast b

/-- Strict-slack (fixed exponent) form: `E < E'` turns the `∀ e` statement into a plain bound. -/
theorem MeasureLBAt.round {x E E' : ℝ} (h : MeasureLBAt x E) (hlt : E < E') :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-E') < |x - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := h (E' - E) (by linarith)
  exact ⟨q₀, fun p q hq hc => by simpa using H p q hq hc⟩

/-- Generic replacement of `double_79`: if `x` has measure exponent `E < E'`, so does
`a * x + b`, in the plain form with `Nat.Coprime p.natAbs q`. -/
theorem affine_round {x E E' : ℝ} (hE : 0 ≤ E) (hlt : E < E') (h : MeasureLBAt x E)
    (a b : ℚ) (ha : a ≠ 0) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-E') < |(a : ℝ) * x + b - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := (h.affine hE a b ha).round hlt
  exact ⟨q₀, fun p q hc hq => H p q hq ((isCoprime_iff_natCoprime p q).2 hc)⟩

/-- `λ`-corollary: `λ = G/2 - 5π²/96` with exponent `31682445459/409965000 < 78` gives
`G - 5π²/48 = 2λ` with round exponent `78`. -/
theorem double_78 {x : ℝ} (h : MeasureLBAt x (((31682445459 / 409965000 : ℚ)) : ℝ)) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) < |2 * x - (p : ℝ) / q| := by
  have := affine_round (E' := 78) (by norm_num) (by norm_num) h 2 0 (by norm_num)
  simpa using this

theorem catalan_sub_78 {G : ℝ}
    (h : MeasureLBAt (G / 2 - 5 * Real.pi ^ 2 / 96) (((31682445459 / 409965000 : ℚ)) : ℝ)) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) < |(G - 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := double_78 h
  refine ⟨q₀, fun p q hc hq => ?_⟩
  have := H p q hc hq
  rwa [show 2 * (G / 2 - 5 * Real.pi ^ 2 / 96) = G - 5 * Real.pi ^ 2 / 48 by ring] at this

/-- Mirror: `λ' = G/2 + 5π²/96` gives `G + 5π²/48 = 2λ'` with exponent `78`. -/
theorem catalan_add_78 {G : ℝ}
    (h : MeasureLBAt (G / 2 + 5 * Real.pi ^ 2 / 96) (((31682445459 / 409965000 : ℚ)) : ℝ)) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) < |(G + 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := double_78 h
  refine ⟨q₀, fun p q hc hq => ?_⟩
  have := H p q hc hq
  rwa [show 2 * (G / 2 + 5 * Real.pi ^ 2 / 96) = G + 5 * Real.pi ^ 2 / 48 by ring] at this

end CatalanCore.Measure
