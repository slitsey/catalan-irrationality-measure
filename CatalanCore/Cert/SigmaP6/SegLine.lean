module

public import CatalanCore.Cert.SigmaP6.RayTaylor

@[expose] public section

/-!
# Real-axis cells (segment cells on `[-r0,0]` and line cells on `[-1/64,1]`)

`Utau x 0 = 1 - x log|x| - (1-x) log|1-x|`.  For a cell `[xlo,xhi]/2^40` we bound it above by
interval arithmetic on the scaled-integer log brackets (`utA` for `xhi ≤ 0`, `utB` for `0 ≤ xlo`).
-/

open Real

namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

def qmax4 (a b c d : ℚ) : ℚ := qmax (qmax a b) (qmax c d)

lemma qmax4_cast (a b c d : ℚ) :
    ((qmax4 a b c d : ℚ) : ℝ) = max (max (a : ℝ) b) (max (c : ℝ) d) := by
  unfold qmax4; rw [qmax_cast, qmax_cast, qmax_cast]

lemma prod4_le {t1 t2 l1 l2 t l : ℝ} (ht1 : t1 ≤ t) (ht2 : t ≤ t2) (hl1 : l1 ≤ l) (hl2 : l ≤ l2) :
    t * l ≤ max (max (t1 * l1) (t1 * l2)) (max (t2 * l1) (t2 * l2)) := by
  have s1 : t * l ≤ max (t1 * l) (t2 * l) := by
    rcases le_total 0 l with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right ht2 h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_right ht1 h)
  have s2 : t1 * l ≤ max (t1 * l1) (t1 * l2) := by
    rcases le_total 0 t1 with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hl2 h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_left hl1 h)
  have s3 : t2 * l ≤ max (t2 * l1) (t2 * l2) := by
    rcases le_total 0 t2 with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hl2 h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_left hl1 h)
  have s4 : max (t1 * l) (t2 * l) ≤ max (max (t1 * l1) (t1 * l2)) (max (t2 * l1) (t2 * l2)) :=
    max_le (s2.trans (le_max_left _ _)) (s3.trans (le_max_right _ _))
  exact s1.trans s4

def lloQ (N : ℕ) : ℚ := (logLoS N : ℚ) / 2 ^ 65
def lupQ (N : ℕ) : ℚ := (logUpS N : ℚ) / 2 ^ 65

lemma lloQ_cast (N : ℕ) : ((lloQ N : ℚ) : ℝ) = (logLoS N : ℝ) / 2 ^ 65 := by
  unfold lloQ; push_cast; rfl
lemma lupQ_cast (N : ℕ) : ((lupQ N : ℚ) : ℝ) = (logUpS N : ℝ) / 2 ^ 65 := by
  unfold lupQ; push_cast; rfl

lemma half_log_sq_lo {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : (N : ℝ) / 2 ^ 80 ≤ x ^ 2) :
    ((lloQ N : ℚ) : ℝ) ≤ Real.log (x ^ 2) / 2 := by
  have hpos : (0 : ℝ) < (N : ℝ) / 2 ^ 80 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have h1 := logLoS_spec hN
  have h2 := Real.log_le_log hpos hx
  rw [lloQ_cast]; linarith

lemma half_log_sq_hi {N : ℕ} (hN : 0 < N) {x : ℝ} (hx0 : 0 < x ^ 2) (hx : x ^ 2 ≤ (N : ℝ) / 2 ^ 80) :
    Real.log (x ^ 2) / 2 ≤ ((lupQ N : ℚ) : ℝ) := by
  have h1 := logUpS_spec hN
  have h2 := Real.log_le_log hx0 hx
  rw [lupQ_cast]; linarith

lemma toNat_cast_real (n : ℤ) (h : 0 ≤ n) : (((n.toNat : ℕ)) : ℝ) = (n : ℝ) := by
  have := Int.toNat_of_nonneg h
  exact_mod_cast this

lemma Utau_axis (x : ℝ) :
    Utau x 0 = 1 - x * (Real.log (x ^ 2) / 2) - (1 - x) * (Real.log ((1 - x) ^ 2) / 2) := by
  unfold Utau; simp

/-! ### case A: `xhi ≤ 0` -/

def F1A (xlo xhi : ℤ) : ℚ :=
  if xhi = 0 then 0 else
    qmax4 (((-xhi : ℤ) : ℚ) / 2 ^ 40 * lloQ (xhi * xhi).toNat)
      (((-xhi : ℤ) : ℚ) / 2 ^ 40 * lupQ (xlo * xlo).toNat)
      (((-xlo : ℤ) : ℚ) / 2 ^ 40 * lloQ (xhi * xhi).toNat)
      (((-xlo : ℤ) : ℚ) / 2 ^ 40 * lupQ (xlo * xlo).toNat)

def F2A (xhi : ℤ) : ℚ := -(((2 ^ 40 - xhi : ℤ) : ℚ) / 2 ^ 40 * lloQ ((2 ^ 40 - xhi) ^ 2).toNat)

def utA (xlo xhi : ℤ) : ℚ := 1 + F1A xlo xhi + F2A xhi

theorem utA_sound (xlo xhi : ℤ) (h0 : xhi ≤ 0) (h1 : -(2 ^ 40 : ℤ) ≤ xlo) (h2 : xlo ≤ xhi)
    (x : ℝ) (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40) :
    Utau x 0 ≤ (utA xlo xhi : ℝ) := by
  rw [Utau_axis]
  have hxhi : (xhi : ℝ) ≤ 0 := by exact_mod_cast h0
  have hxlo : (-(2 ^ 40 : ℝ)) ≤ xlo := by exact_mod_cast h1
  have hx0 : x ≤ 0 := by
    have : (xhi : ℝ) / 2 ^ 40 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hxhi (by positivity)
    linarith
  have hx1' : -1 ≤ x := by
    have : -(1 : ℝ) ≤ (xlo : ℝ) / 2 ^ 40 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  -- F1
  have hF1 : -(x * (Real.log (x ^ 2) / 2)) ≤ (F1A xlo xhi : ℝ) := by
    unfold F1A
    split_ifs with hz
    · push_cast
      have hl : Real.log (x ^ 2) ≤ 0 := Real.log_nonpos (by positivity) (by nlinarith)
      nlinarith
    · have hneg : xhi < 0 := lt_of_le_of_ne h0 hz
      have hxhiR : (xhi : ℝ) < 0 := by exact_mod_cast hneg
      have hxneg : x < 0 := by
        have : (xhi : ℝ) / 2 ^ 40 < 0 := div_neg_of_neg_of_pos hxhiR (by positivity)
        linarith
      have hN1 : 0 < (xhi * xhi).toNat := by
        have : 0 < xhi * xhi := by nlinarith
        omega
      have hN2 : 0 < (xlo * xlo).toNat := by
        have : xlo < 0 := by omega
        have : 0 < xlo * xlo := by nlinarith
        omega
      have c1 := toNat_cast_real (xhi * xhi) (by nlinarith)
      have c2 := toNat_cast_real (xlo * xlo) (by nlinarith)
      push_cast at c1 c2
      have hlo : ((lloQ (xhi * xhi).toNat : ℚ) : ℝ) ≤ Real.log (x ^ 2) / 2 := by
        apply half_log_sq_lo hN1
        rw [c1]
        have : ((xhi : ℝ) / 2 ^ 40) ^ 2 ≤ x ^ 2 := by nlinarith
        have e : ((xhi : ℝ) * xhi) / 2 ^ 80 = ((xhi : ℝ) / 2 ^ 40) ^ 2 := by ring
        linarith
      have hhi : Real.log (x ^ 2) / 2 ≤ ((lupQ (xlo * xlo).toNat : ℚ) : ℝ) := by
        apply half_log_sq_hi hN2 (by nlinarith)
        rw [c2]
        have : x ^ 2 ≤ ((xlo : ℝ) / 2 ^ 40) ^ 2 := by nlinarith
        have e : ((xlo : ℝ) * xlo) / 2 ^ 80 = ((xlo : ℝ) / 2 ^ 40) ^ 2 := by ring
        linarith
      have ht1 : ((-xhi : ℤ) : ℝ) / 2 ^ 40 ≤ -x := by push_cast; linarith [neg_div (2 ^ 40 : ℝ) (xhi : ℝ)]
      have ht2 : -x ≤ ((-xlo : ℤ) : ℝ) / 2 ^ 40 := by push_cast; linarith [neg_div (2 ^ 40 : ℝ) (xlo : ℝ)]
      have := prod4_le ht1 ht2 hlo hhi
      push_cast at this
      rw [qmax4_cast]
      push_cast
      have e : -(x * (Real.log (x ^ 2) / 2)) = -x * (Real.log (x ^ 2) / 2) := by ring
      rw [e]
      exact this
  -- F2
  have hF2 : -((1 - x) * (Real.log ((1 - x) ^ 2) / 2)) ≤ (F2A xhi : ℝ) := by
    unfold F2A
    have hpos : 0 < (2 ^ 40 - xhi : ℤ) := by omega
    have hN : 0 < ((2 ^ 40 - xhi) ^ 2).toNat := by
      have : 0 < (2 ^ 40 - xhi) ^ 2 := pow_pos hpos 2
      omega
    have c := toNat_cast_real ((2 ^ 40 - xhi) ^ 2) (by positivity)
    have c' : ((((2 ^ 40 - xhi) ^ 2).toNat : ℕ) : ℝ) = ((2 : ℝ) ^ 40 - xhi) ^ 2 := by
      rw [c]; push_cast; norm_num
    have hc1 : ((2 ^ 40 - xhi : ℤ) : ℝ) / 2 ^ 40 ≤ 1 - x := by
      have e : ((2 ^ 40 - xhi : ℤ) : ℝ) / 2 ^ 40 = 1 - (xhi : ℝ) / 2 ^ 40 := by push_cast; field_simp; norm_num
      rw [e]; linarith
    have hc0 : 0 ≤ ((2 ^ 40 - xhi : ℤ) : ℝ) / 2 ^ 40 := by
      have : (0 : ℝ) < ((2 ^ 40 - xhi : ℤ) : ℝ) := by exact_mod_cast hpos
      positivity
    have hlo : ((lloQ ((2 ^ 40 - xhi) ^ 2).toNat : ℚ) : ℝ) ≤ Real.log ((1 - x) ^ 2) / 2 := by
      apply half_log_sq_lo hN
      rw [c']
      have : (((2 ^ 40 - xhi : ℤ) : ℝ) / 2 ^ 40) ^ 2 ≤ (1 - x) ^ 2 := pow_le_pow_left₀ hc0 hc1 2
      have e : ((2 ^ 40 - (xhi : ℝ)) ^ 2) / 2 ^ 80 = (((2 ^ 40 - xhi : ℤ) : ℝ) / 2 ^ 40) ^ 2 := by
        push_cast; ring
      linarith
    have hs1 : (1 : ℝ) ≤ 1 - x := by linarith
    have hL : 0 ≤ Real.log ((1 - x) ^ 2) / 2 := by
      have : 1 ≤ (1 - x) ^ 2 := by nlinarith
      have := Real.log_nonneg this
      linarith
    simp only [Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
    set L := Real.log ((1 - x) ^ 2) / 2
    set S1 : ℝ := ((2 ^ 40 - xhi : ℤ) : ℝ) / 2 ^ 40
    have a1 : S1 * L ≤ (1 - x) * L := mul_le_mul_of_nonneg_right hc1 hL
    have a2 : S1 * ((lloQ ((2 ^ 40 - xhi) ^ 2).toNat : ℚ) : ℝ) ≤ S1 * L := mul_le_mul_of_nonneg_left hlo hc0
    linarith
  simp only [utA, Rat.cast_add, Rat.cast_one]
  linarith

/-! ### case B: `0 ≤ xlo`, `xhi ≤ 2^40` -/

def tlogUB (t1 t2 : ℤ) : ℚ :=
  if t1 = 0 then 2 * (((Nat.sqrt (t2.toNat * 2 ^ 40) + 1 : ℕ) : ℚ) / 2 ^ 40) else
    qmax4 ((t1 : ℚ) / 2 ^ 40 * (-lupQ (t2 * t2).toNat)) ((t1 : ℚ) / 2 ^ 40 * (-lloQ (t1 * t1).toNat))
      ((t2 : ℚ) / 2 ^ 40 * (-lupQ (t2 * t2).toNat)) ((t2 : ℚ) / 2 ^ 40 * (-lloQ (t1 * t1).toNat))

def utB (xlo xhi : ℤ) : ℚ := 1 + tlogUB xlo xhi + tlogUB (2 ^ 40 - xhi) (2 ^ 40 - xlo)

lemma cast_sub_div (a : ℤ) : ((2 ^ 40 - a : ℤ) : ℝ) / 2 ^ 40 = 1 - (a : ℝ) / 2 ^ 40 := by
  push_cast; field_simp; norm_num

lemma neg_mul_log_le (t : ℝ) (ht : 0 < t) : -(t * (Real.log (t ^ 2) / 2)) ≤ 2 * Real.sqrt t := by
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ t = r ^ 2 := ⟨Real.sqrt t, Real.sqrt_pos.mpr ht, (Real.sq_sqrt ht.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  have hl : Real.log ((r ^ 2) ^ 2) / 2 = 2 * Real.log r := by
    rw [← pow_mul, Real.log_pow]; push_cast; ring
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
  rw [Real.log_inv] at h2
  rw [hl]
  have h3 : r ^ 2 * (-Real.log r) ≤ r ^ 2 * (r⁻¹ - 1) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have e : r ^ 2 * (r⁻¹ - 1) = r - r ^ 2 := by field_simp
  nlinarith [sq_nonneg r]

theorem tlog_sound (t1 t2 : ℤ) (h0 : 0 ≤ t1) (h2 : t1 ≤ t2) (t : ℝ)
    (ht1 : (t1 : ℝ) / 2 ^ 40 ≤ t) (ht2 : t ≤ (t2 : ℝ) / 2 ^ 40) :
    -(t * (Real.log (t ^ 2) / 2)) ≤ (tlogUB t1 t2 : ℝ) := by
  unfold tlogUB
  split_ifs with hz
  · subst hz
    have ht0 : 0 ≤ t := by simpa using ht1
    have ht2' : 0 ≤ t2 := by omega
    have hn := toNat_cast_real t2 ht2'
    have hsq : t ≤ (((Nat.sqrt (t2.toNat * 2 ^ 40) + 1 : ℕ) : ℝ) / 2 ^ 40) ^ 2 := by
      have h := Nat.lt_succ_sqrt (t2.toNat * 2 ^ 40)
      have h' : ((t2.toNat * 2 ^ 40 : ℕ) : ℝ) < (((Nat.sqrt (t2.toNat * 2 ^ 40) + 1 : ℕ) : ℝ)) ^ 2 := by
        have : t2.toNat * 2 ^ 40 < (Nat.sqrt (t2.toNat * 2 ^ 40) + 1) ^ 2 := by
          rw [pow_two]; exact h
        exact_mod_cast this
      push_cast at h'
      rw [hn] at h'
      rw [div_pow]
      rw [le_div_iff₀ (by positivity)]
      have : t * 2 ^ 80 ≤ (t2 : ℝ) / 2 ^ 40 * 2 ^ 80 := by
        apply mul_le_mul_of_nonneg_right ht2 (by positivity)
      have e : (t2 : ℝ) / 2 ^ 40 * 2 ^ 80 = t2 * 2 ^ 40 := by ring
      push_cast
      nlinarith
    rcases ht0.eq_or_lt with h | h
    · rw [← h]; simp; positivity
    · have h1 := neg_mul_log_le t h
      have h2' : Real.sqrt t ≤ (((Nat.sqrt (t2.toNat * 2 ^ 40) + 1 : ℕ) : ℝ) / 2 ^ 40) :=
        Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
      push_cast at h2' ⊢
      linarith
  · have hpos : 0 < t1 := lt_of_le_of_ne h0 (Ne.symm hz)
    have hposR : (0 : ℝ) < t1 := by exact_mod_cast hpos
    have htp : 0 < t := lt_of_lt_of_le (by positivity) ht1
    have hN1 : 0 < (t1 * t1).toNat := by
      have : 0 < t1 * t1 := by nlinarith
      omega
    have hN2 : 0 < (t2 * t2).toNat := by
      have : 0 < t1 * t1 := by nlinarith
      have : t1 * t1 ≤ t2 * t2 := by nlinarith
      omega
    have c1 := toNat_cast_real (t1 * t1) (by nlinarith)
    have c2 := toNat_cast_real (t2 * t2) (by nlinarith)
    push_cast at c1 c2
    have hlo : ((lloQ (t1 * t1).toNat : ℚ) : ℝ) ≤ Real.log (t ^ 2) / 2 := by
      apply half_log_sq_lo hN1
      rw [c1]
      have : ((t1 : ℝ) / 2 ^ 40) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) ht1 2
      have e : ((t1 : ℝ) * t1) / 2 ^ 80 = ((t1 : ℝ) / 2 ^ 40) ^ 2 := by ring
      linarith
    have hhi : Real.log (t ^ 2) / 2 ≤ ((lupQ (t2 * t2).toNat : ℚ) : ℝ) := by
      apply half_log_sq_hi hN2 (by positivity)
      rw [c2]
      have : t ^ 2 ≤ ((t2 : ℝ) / 2 ^ 40) ^ 2 := pow_le_pow_left₀ htp.le ht2 2
      have e : ((t2 : ℝ) * t2) / 2 ^ 80 = ((t2 : ℝ) / 2 ^ 40) ^ 2 := by ring
      linarith
    have := prod4_le ht1 ht2 (neg_le_neg hhi) (neg_le_neg hlo)
    push_cast at this
    rw [qmax4_cast]
    push_cast
    have e : -(t * (Real.log (t ^ 2) / 2)) = t * -(Real.log (t ^ 2) / 2) := by ring
    rw [e]
    exact this

theorem utB_sound (xlo xhi : ℤ) (h0 : 0 ≤ xlo) (h2 : xlo ≤ xhi) (h1 : xhi ≤ 2 ^ 40)
    (x : ℝ) (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40) :
    Utau x 0 ≤ (utB xlo xhi : ℝ) := by
  rw [Utau_axis]
  have a := tlog_sound xlo xhi h0 h2 x hx1 hx2
  have b := tlog_sound (2 ^ 40 - xhi) (2 ^ 40 - xlo) (by omega) (by omega) (1 - x)
    (by rw [cast_sub_div]; linarith) (by rw [cast_sub_div]; linarith)
  simp only [utB, Rat.cast_add, Rat.cast_one]
  linarith

end CatalanCore.Cert.SigmaP6
