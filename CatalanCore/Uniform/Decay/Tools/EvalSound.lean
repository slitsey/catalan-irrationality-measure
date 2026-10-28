import CatalanCore.Uniform.Decay.Tools.SeriesBridge
set_option Elab.async false

/-!
# Soundness of the accepted checker input evaluator `SignedPilot.evalInput`

`evalInput (kind, n, d, m) = some (v, e)` implies `|v - scale * f| ≤ e`, where `f` is
`π` (kind 0), `log (n/d)` (kind 1, `n>0`), `arctan (n/d)` (kind 2).
-/

namespace CatalanCore.Uniform.Decay.Tools

open CatalanCore.Uniform.Decay.SignedPilot

theorem tail3 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 3) :
    (scale : ℝ) * (u ^ (2 * 64 + 1) / (1 - u ^ 2)) ≤ 1 / 2 := by
  have hp : u ^ (2 * 64 + 1) ≤ (1 / 3 : ℝ) ^ (2 * 64 + 1) := pow_le_pow_left₀ h0 h1 _
  have hd : (8 / 9 : ℝ) ≤ 1 - u ^ 2 := by nlinarith
  have : u ^ (2 * 64 + 1) / (1 - u ^ 2) ≤ (1 / 3 : ℝ) ^ (2 * 64 + 1) / (8 / 9) :=
    div_le_div₀ (by positivity) hp (by norm_num) hd
  calc (scale : ℝ) * (u ^ (2 * 64 + 1) / (1 - u ^ 2))
      ≤ (scale : ℝ) * ((1 / 3 : ℝ) ^ (2 * 64 + 1) / (8 / 9)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ ≤ 1 / 2 := by unfold scale; norm_num

theorem tail_atan (u : ℝ) (h0 : 0 ≤ u) (c : ℝ) (hc : u ≤ c) (hc3 : c ≤ 1 / 2) :
    (scale : ℝ) * (u ^ (2 * (2 * 32) + 1) / (2 * ((2 * 32 : ℕ) : ℝ) + 1)) ≤ 1 := by
  have hp : u ^ (2 * (2 * 32) + 1) ≤ (1 / 2 : ℝ) ^ (2 * (2 * 32) + 1) :=
    pow_le_pow_left₀ h0 (hc.trans hc3) _
  calc (scale : ℝ) * (u ^ (2 * (2 * 32) + 1) / (2 * ((2 * 32 : ℕ) : ℝ) + 1))
      ≤ (scale : ℝ) * ((1 / 2 : ℝ) ^ (2 * (2 * 32) + 1) / (2 * ((2 * 32 : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp (by positivity)) (by positivity)
    _ ≤ 1 := by unfold scale; norm_num

theorem int_div_bound (P : ℤ) (c : ℕ) (hc : 0 < c) :
    |((P / (c : ℤ) : ℤ) : ℝ) - (P : ℝ) / c| ≤ 1 := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have h1 : (c : ℤ) * (P / (c : ℤ)) + P % (c : ℤ) = P := by rw [Int.emod_def]; ring
  have h2 := Int.emod_nonneg P (by exact_mod_cast hc.ne' : (c : ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos P (by exact_mod_cast hc : (0 : ℤ) < c)
  have h1R : (c : ℝ) * ((P / (c : ℤ) : ℤ) : ℝ) + ((P % (c : ℤ) : ℤ) : ℝ) = P := by exact_mod_cast h1
  have h2R : (0 : ℝ) ≤ ((P % (c : ℤ) : ℤ) : ℝ) := by exact_mod_cast h2
  have h3R : ((P % (c : ℤ) : ℤ) : ℝ) < c := by exact_mod_cast h3
  have : (P : ℝ) / c = ((P / (c : ℤ) : ℤ) : ℝ) + ((P % (c : ℤ) : ℤ) : ℝ) / c := by
    field_simp; linarith
  rw [this, abs_le]
  have : ((P % (c : ℤ) : ℤ) : ℝ) / c ≤ 1 := by rw [div_le_one hcR]; exact h3R.le
  have : 0 ≤ ((P % (c : ℤ) : ℤ) : ℝ) / c := div_nonneg h2R hcR.le
  constructor <;> linarith

theorem log_case (a b : ℕ) (hb : 0 < b) (hba : b ≤ a) (ha2 : a ≤ 2 * b) :
    |((2 * series false (a - b) (a + b) : ℤ) : ℝ) - (scale : ℝ) * Real.log ((a : ℝ) / b)| ≤ 129 := by
  have h := scLog_enclosure scale a b 64 hb hba
  have hs : ((2 * series false (a - b) (a + b) : ℤ) : ℝ) = ((scLog scale a b 64 : ℕ) : ℝ) := by
    rw [series_false]; unfold scLog
    generalize scAtanh scale (a - b) (a + b) 64 = X
    push_cast; ring
  rw [hs]
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hu0 : (0 : ℝ) ≤ ((a - b : ℕ) : ℝ) / ((a + b : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hu1 : ((a - b : ℕ) : ℝ) / ((a + b : ℕ) : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    push_cast [Nat.cast_sub hba]
    have : (a : ℝ) ≤ 2 * b := by exact_mod_cast ha2
    linarith
  have := tail3 _ hu0 hu1
  linarith

theorem atan_small (a b : ℕ) (hb : 0 < b) (h : 2 * a ≤ b) :
    |((series true a b : ℤ) : ℝ) - (scale : ℝ) * Real.arctan ((a : ℝ) / b)| ≤ 70 := by
  have hab : a < b := by omega
  have h1 := series_true_enclosure a b hb hab
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hu0 : (0 : ℝ) ≤ (a : ℝ) / b := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hu1 : (a : ℝ) / b ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hbR (by norm_num)]
    have : (2 : ℝ) * a ≤ b := by exact_mod_cast h
    linarith
  have := tail_atan _ hu0 _ hu1 le_rfl
  push_cast at h1 this ⊢
  linarith

theorem arctan_shift (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    Real.arctan ((a : ℝ) / b) =
      Real.pi / 4 - Real.arctan (((b - a : ℕ) : ℝ) / ((b + a : ℕ) : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := lt_of_lt_of_le haR (by exact_mod_cast hab)
  have haR' : (a : ℝ) ≤ b := by exact_mod_cast hab
  push_cast [Nat.cast_sub hab]
  have key : Real.arctan (((b : ℝ) - a) / (b + a)) + Real.arctan ((a : ℝ) / b) = Real.pi / 4 := by
    rw [← Real.arctan_one]
    have hxy : ((b : ℝ) - a) / (b + a) * ((a : ℝ) / b) < 1 := by
      rw [← mul_div_mul_comm, div_lt_one (by positivity)]
      nlinarith
    rw [Real.arctan_add hxy]
    congr 1
    rw [div_eq_one_iff_eq (sub_pos.2 hxy).ne']
    field_simp
    ring
  linarith

theorem atan_shift (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (hb2 : b < 2 * a) :
    |(((piLiteral / 4 - series true (b - a) (b + a) : ℤ)) : ℝ) -
        (scale : ℝ) * Real.arctan ((a : ℝ) / b)| ≤ 600 := by
  have hbpos : 0 < b := by omega
  have hlt : b - a < b + a := by omega
  have h1 := series_true_enclosure (b - a) (b + a) (by omega) hlt
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hu0 : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) / ((b + a : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hu1 : ((b - a : ℕ) : ℝ) / ((b + a : ℕ) : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    push_cast [Nat.cast_sub hab]
    have : (b : ℝ) ≤ 2 * a := by exact_mod_cast hb2.le
    linarith
  have h2 := tail_atan _ hu0 _ hu1 (by norm_num)
  have h3 := int_div_bound piLiteral 4 (by norm_num)
  have h4 := piLiteral_enclosure
  rw [arctan_shift a b ha hab]
  push_cast at h1 h2 h3 ⊢
  rw [abs_le] at h1 h3 h4 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h3.1, h3.2, h4.1, h4.2]

/-- The inner `(a,b)` block of `evalInput` kind 2. -/
def pairVal (a b : ℕ) : Int × Nat :=
  if b < 2 * a then (piLiteral / 4 - series true (b - a) (b + a), 600) else (series true a b, 70)

theorem pairVal_sound (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    |((pairVal a b).1 : ℝ) - (scale : ℝ) * Real.arctan ((a : ℝ) / b)| ≤ (pairVal a b).2 := by
  unfold pairVal
  by_cases h : b < 2 * a
  · simp only [h, if_true]
    have := atan_shift a b (by omega) hab h
    exact_mod_cast this
  · simp only [h, if_false]
    have := atan_small a b hb (by omega)
    exact_mod_cast this

/-- Mirror of the kind-2 branch (`d ≠ 0`). -/
def atanVal (n : Int) (d : Nat) : Int × Nat :=
  let neg := n < 0
  let inv := d < n.natAbs
  let (a, b) := if inv then (d, n.natAbs) else (n.natAbs, d)
  let (v, e) : Int × Nat := pairVal a b
  let (v, e) := if inv then (piLiteral / 2 - v, e + 1100) else (v, e)
  ((if neg then -v else v), e)

theorem atanVal_sound (n : Int) (d : Nat) (hd : 0 < d) :
    |((atanVal n d).1 : ℝ) - (scale : ℝ) * Real.arctan ((n : ℝ) / d)| ≤ (atanVal n d).2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hN : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hpi2 := int_div_bound piLiteral 2 (by norm_num)
  have hpi := piLiteral_enclosure
  -- sign handling
  have hsign : Real.arctan ((n : ℝ) / d) =
      (if n < 0 then -1 else 1) * Real.arctan (((n.natAbs : ℕ) : ℝ) / d) := by
    by_cases hn : n < 0
    · have : (n : ℝ) = -((n.natAbs : ℕ) : ℝ) := by
        rw [hN, abs_of_neg (by exact_mod_cast hn)]; ring
      rw [if_pos hn, this, neg_div, Real.arctan_neg]; ring
    · have : (n : ℝ) = ((n.natAbs : ℕ) : ℝ) := by
        rw [hN, abs_of_nonneg (by exact_mod_cast not_lt.1 hn)]
      rw [if_neg hn, this]; ring
  unfold atanVal
  by_cases hinv : d < n.natAbs
  · have hNpos : 0 < n.natAbs := by omega
    have hNR : (0 : ℝ) < ((n.natAbs : ℕ) : ℝ) := by exact_mod_cast hNpos
    have hp := pairVal_sound d n.natAbs hNpos hinv.le
    have hinvx : Real.arctan (((n.natAbs : ℕ) : ℝ) / d) =
        Real.pi / 2 - Real.arctan ((d : ℝ) / ((n.natAbs : ℕ) : ℝ)) := by
      have := Real.arctan_inv_of_pos (x := (d : ℝ) / ((n.natAbs : ℕ) : ℝ)) (by positivity)
      rw [inv_div] at this
      exact this
    simp only [hinv, if_true]
    rw [hsign, hinvx]
    by_cases hn : n < 0
    · simp only [hn, if_true]
      push_cast at hp hpi2 ⊢
      rw [abs_le] at hp hpi2 hpi ⊢
      constructor <;> nlinarith [hp.1, hp.2, hpi2.1, hpi2.2, hpi.1, hpi.2]
    · simp only [hn, if_false]
      push_cast at hp hpi2 ⊢
      rw [abs_le] at hp hpi2 hpi ⊢
      constructor <;> nlinarith [hp.1, hp.2, hpi2.1, hpi2.2, hpi.1, hpi.2]
  · have hp := pairVal_sound n.natAbs d hd (not_lt.1 hinv)
    simp only [hinv, if_false]
    rw [hsign]
    by_cases hn : n < 0
    · simp only [hn, if_true]
      push_cast at hp ⊢
      rw [abs_le] at hp ⊢
      constructor <;> nlinarith [hp.1, hp.2]
    · simp only [hn, if_false]
      push_cast at hp ⊢
      rw [abs_le] at hp ⊢
      constructor <;> nlinarith [hp.1, hp.2]

/-- **Soundness of `evalInput`, kind 2:** value of `arctan (n/d)` (scaled). -/
theorem evalInput_atan {n : Int} {d : Nat} {m : Int} {v : Int} {e : Nat}
    (h : evalInput (2, n, d, m) = some (v, e)) :
    |(v : ℝ) - (scale : ℝ) * Real.arctan ((n : ℝ) / d)| ≤ e := by
  have hd : d ≠ 0 := by
    rintro rfl; simp [evalInput] at h
  have : evalInput (2, n, d, m) = some (atanVal n d) := by
    unfold evalInput atanVal pairVal
    simp [hd]
  rw [this] at h
  have h' : atanVal n d = (v, e) := Option.some.inj h
  have := atanVal_sound n d (Nat.pos_of_ne_zero hd)
  rw [h'] at this
  exact this

/-- **Soundness of `evalInput`, kind 0:** `π`. -/
theorem evalInput_pi {n : Int} {d : Nat} {m : Int} {v : Int} {e : Nat}
    (h : evalInput (0, n, d, m) = some (v, e)) :
    |(v : ℝ) - (scale : ℝ) * Real.pi| ≤ e := by
  have hd : d ≠ 0 := by
    rintro rfl; simp [evalInput] at h
  simp [evalInput, hd] at h
  obtain ⟨rfl, rfl⟩ := h
  have := piLiteral_enclosure
  push_cast
  linarith

/-- Mirror of the kind-1 branch (`d ≠ 0`). -/
def logVal (n : Int) (d : Nat) (m : Int) : Option (Int × Nat) :=
  let (a, b) := if 0 ≤ m then (n.natAbs, d * 2 ^ m.toNat) else (n.natAbs * 2 ^ (-m).toNat, d)
  if 0 < n && b ≤ a && a ≤ 2 * b then
    some (2 * series false (a - b) (a + b) + m * log2Literal, 130 * (1 + m.natAbs))
  else none

theorem log2_bound_m (m : Int) : |((m * log2Literal : ℤ) : ℝ) - (scale : ℝ) * (m * Real.log 2)|
    ≤ 129 * (m.natAbs : ℝ) := by
  have h := log2Literal_enclosure
  have : ((m * log2Literal : ℤ) : ℝ) - (scale : ℝ) * (m * Real.log 2)
      = (m : ℝ) * ((log2Literal : ℝ) - (scale : ℝ) * Real.log 2) := by push_cast; ring
  rw [this, abs_mul, Nat.cast_natAbs, Int.cast_abs]
  have := mul_le_mul_of_nonneg_left h (abs_nonneg (m : ℝ))
  linarith

theorem logVal_sound {n : Int} {d : Nat} {m : Int} {v : Int} {e : Nat} (hd : 0 < d)
    (h : logVal n d m = some (v, e)) :
    |(v : ℝ) - (scale : ℝ) * Real.log ((n : ℝ) / d)| ≤ e := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold logVal at h
  have hlog2 := log2_bound_m m
  by_cases hm : 0 ≤ m
  · simp only [hm, if_true] at h
    split_ifs at h with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hn, hba⟩, ha2⟩ := hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hbpos : 0 < d * 2 ^ m.toNat := by positivity
      have hl := log_case n.natAbs (d * 2 ^ m.toNat) hbpos hba ha2
      have hnR : (n : ℝ) = ((n.natAbs : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hn)]
      have hmR : (m : ℝ) = ((m.toNat : ℕ) : ℝ) := by
        have := Int.toNat_of_nonneg hm
        exact_mod_cast this.symm
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hsplit : Real.log ((n : ℝ) / d) =
          Real.log (((n.natAbs : ℕ) : ℝ) / ((d * 2 ^ m.toNat : ℕ) : ℝ)) + m * Real.log 2 := by
        have e1 : (n : ℝ) / d = (((n.natAbs : ℕ) : ℝ) / ((d * 2 ^ m.toNat : ℕ) : ℝ)) *
            (2 : ℝ) ^ m.toNat := by
          push_cast; rw [← hnR]; field_simp
        have hN : (0 : ℝ) < ((n.natAbs : ℕ) : ℝ) := by rw [← hnR]; exact hnpos
        have hB : (0 : ℝ) < ((d * 2 ^ m.toNat : ℕ) : ℝ) := by exact_mod_cast hbpos
        rw [e1, Real.log_mul (by positivity) (by positivity), Real.log_pow, hmR]
      rw [hsplit]
      push_cast at hl hlog2 ⊢
      rw [abs_le] at hl hlog2 ⊢
      have h0 : (0 : ℝ) ≤ (m.natAbs : ℝ) := Nat.cast_nonneg _
      constructor <;> linarith [hl.1, hl.2, hlog2.1, hlog2.2]
  · simp only [hm, if_false] at h
    split_ifs at h with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hn, hba⟩, ha2⟩ := hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hbpos : 0 < d := hd
      have hl := log_case (n.natAbs * 2 ^ (-m).toNat) d hbpos hba ha2
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hnR : (n : ℝ) = ((n.natAbs : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hnpos]
      have hmR : (-(m : ℝ)) = (((-m).toNat : ℕ) : ℝ) := by
        have := Int.toNat_of_nonneg (by omega : 0 ≤ -m)
        have h2 : (((-m).toNat : ℕ) : ℤ) = -m := this
        have h3 : ((((-m).toNat : ℕ) : ℤ) : ℝ) = ((-m : ℤ) : ℝ) := by rw [h2]
        push_cast at h3
        linarith
      have hsplit : Real.log ((n : ℝ) / d) =
          Real.log (((n.natAbs * 2 ^ (-m).toNat : ℕ) : ℝ) / (d : ℝ)) + m * Real.log 2 := by
        have hN : (0 : ℝ) < ((n.natAbs : ℕ) : ℝ) := by rw [← hnR]; exact hnpos
        have e1 : (n : ℝ) / d = (((n.natAbs * 2 ^ (-m).toNat : ℕ) : ℝ) / (d : ℝ)) /
            (2 : ℝ) ^ (-m).toNat := by
          push_cast; rw [← hnR]; field_simp
        have hB : (0 : ℝ) < (((n.natAbs * 2 ^ (-m).toNat : ℕ) : ℝ) / (d : ℝ)) := by
          have : (0 : ℝ) < ((n.natAbs * 2 ^ (-m).toNat : ℕ) : ℝ) := by
            push_cast; positivity
          positivity
        rw [e1, Real.log_div hB.ne' (by positivity), Real.log_pow]
        have : (m : ℝ) = -(((-m).toNat : ℕ) : ℝ) := by linarith
        rw [this]; ring
      rw [hsplit]
      push_cast at hl hlog2 ⊢
      rw [abs_le] at hl hlog2 ⊢
      have h0 : (0 : ℝ) ≤ (m.natAbs : ℝ) := Nat.cast_nonneg _
      constructor <;> linarith [hl.1, hl.2, hlog2.1, hlog2.2]

/-- **Soundness of `evalInput`, kind 1:** `log (n/d)`. -/
theorem evalInput_log {n : Int} {d : Nat} {m : Int} {v : Int} {e : Nat}
    (h : evalInput (1, n, d, m) = some (v, e)) :
    |(v : ℝ) - (scale : ℝ) * Real.log ((n : ℝ) / d)| ≤ e := by
  have hd : d ≠ 0 := by
    rintro rfl; simp [evalInput] at h
  have : evalInput (1, n, d, m) = logVal n d m := by
    unfold evalInput logVal
    simp [hd]
  rw [this] at h
  exact logVal_sound (Nat.pos_of_ne_zero hd) h

end CatalanCore.Uniform.Decay.Tools
