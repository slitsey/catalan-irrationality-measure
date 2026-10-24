module
public import CatalanArchive.CatalanMeasure.G728.LogFix
@[expose] public section
/-!
# Integer complex logarithm enclosures

`cLog1I c d a b` approximates `Re ((c + d i) log (a + b i))` with integer arithmetic only:
`A + B i = L (a + b i)` with `L = den a · den b`, so `log |z|² = log N - 2 log L`
(`N = A² + B²`), both by `logI` (binary exponent `Nat.log2` and the fixed-point log series);
the argument is that of `A + B i`, after OAI's octant reduction on the integer pair.
-/
namespace CatalanMeasure.G728
open CatalanMeasure.Cert OAI.InternalCatalan

/-- the fixed-point log series at a mantissa `y ∈ [1,2]`, given the floor `Q` of `q·2^80` -/
theorem logY_spec {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ 2) {Q : ℤ}
    (hQ1 : (Q : ℝ) ≤ ((y - 1) / (y + 1)) * (S80 : ℝ))
    (hQ2 : ((y - 1) / (y + 1)) * (S80 : ℝ) < (Q : ℝ) + 1) :
    |Real.log y - ((logSerF Q : ℤ) : ℝ) / (S80 : ℝ)| ≤ barrierLogHError + 23 / (S80 : ℝ) := by
  have hS := S80_pos
  set qq := (y - 1) / (y + 1) with hqq
  have hq0 : 0 ≤ qq := by rw [hqq]; apply div_nonneg <;> linarith
  have hq3 : qq ≤ 1 / 3 := by rw [hqq, div_le_iff₀ (by linarith)]; linarith
  set q' : ℝ := (Q : ℝ) / (S80 : ℝ) with hq'def
  have hq'le : q' ≤ qq := by rw [hq'def, div_le_iff₀ hS]; linarith
  have hq'gt : qq - q' < 1 / (S80 : ℝ) := by
    have : qq < ((Q : ℝ) + 1) / (S80 : ℝ) := by rw [lt_div_iff₀ hS]; linarith
    have h2 : ((Q : ℝ) + 1) / (S80 : ℝ) = q' + 1 / (S80 : ℝ) := by rw [hq'def]; ring
    linarith
  have hq'0 : 0 ≤ q' := by
    have hQ0 : (0 : ℤ) ≤ Q := by
      have : (-1 : ℝ) < (Q : ℝ) := by nlinarith
      have : (-1 : ℤ) < Q := by exact_mod_cast this
      omega
    rw [hq'def]; exact div_nonneg (by exact_mod_cast hQ0) hS.le
  set y2 : ℝ := (1 + q') / (1 - q') with hy2def
  have h1q : 0 < 1 - q' := by linarith
  have hy2q : (y2 - 1) / (y2 + 1) = q' := by rw [hy2def]; field_simp; ring
  have hy21 : 1 ≤ y2 := by rw [hy2def, le_div_iff₀ h1q]; linarith
  have hy22 : y2 ≤ 2 := by rw [hy2def, div_le_iff₀ h1q]; linarith
  have hyform : y = (1 + qq) / (1 - qq) := by rw [hqq]; field_simp; ring
  have hy2le : y2 ≤ y := by
    rw [hyform, hy2def, div_le_div_iff₀ h1q (by linarith)]; nlinarith
  have hydiff : y - y2 ≤ 9 / 2 * (qq - q') := by
    have h1qq : 0 < 1 - qq := by linarith
    have : y - y2 = 2 * (qq - q') / ((1 - qq) * (1 - q')) := by
      rw [hyform, hy2def]; field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    have hprod : 4 / 9 ≤ (1 - qq) * (1 - q') := by nlinarith
    nlinarith
  have hser : barrierLogH y2 = 2 * ∑ j ∈ Finset.range 18, q' ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) := by
    unfold barrierLogH; rw [hy2q]
  have hLF := logSerF_spec Q
  simp only at hLF
  rw [← hq'def, ← hser] at hLF
  have hrem := barrier_logH_remainder_uniform (y := y2) ⟨hy21, hy22⟩
  have hly := log_sub_le_of_le hy21 hy2le
  have hB := abs_sub_fl_le (by norm_num) hLF.1 hLF.2
  have hC : |Real.log y - Real.log y2| ≤ 5 / (S80 : ℝ) := by
    have h0 : y - y2 ≤ 9 / 2 * (1 / (S80 : ℝ)) := by nlinarith
    have h3 : 9 / 2 * (1 / (S80 : ℝ)) ≤ 5 / (S80 : ℝ) := by
      have : 0 < 1 / (S80 : ℝ) := by positivity
      rw [show (5 : ℝ) / (S80 : ℝ) = 5 * (1 / (S80 : ℝ)) by ring]; nlinarith
    linarith
  have hsplit : Real.log y - ((logSerF Q : ℤ) : ℝ) / (S80 : ℝ) =
      (Real.log y - Real.log y2) + (Real.log y2 - barrierLogH y2) +
        (barrierLogH y2 - ((logSerF Q : ℤ) : ℝ) / (S80 : ℝ)) := by ring
  rw [hsplit]
  have hrem' : |Real.log y2 - barrierLogH y2| ≤ barrierLogHError := by
    rw [abs_of_nonneg hrem.1]; exact hrem.2
  have t1 := abs_add_le ((Real.log y - Real.log y2) + (Real.log y2 - barrierLogH y2))
    (barrierLogH y2 - ((logSerF Q : ℤ) : ℝ) / (S80 : ℝ))
  have t2 := abs_add_le (Real.log y - Real.log y2) (Real.log y2 - barrierLogH y2)
  have e1 : (23 : ℝ) / (S80 : ℝ) = 5 / (S80 : ℝ) + 18 / (S80 : ℝ) := by ring
  rw [e1]
  linarith

/-- fixed-point `log n · 2^80` -/
def logI (n : ℕ) : ℤ :=
  (n.log2 : ℤ) * L2F + logSerF ((((n : ℤ) - 2 ^ n.log2) * S80) / ((n : ℤ) + 2 ^ n.log2))

theorem logI_spec {n : ℕ} (hn : n ≠ 0) :
    |Real.log n - ((logI n : ℤ) : ℝ) / (S80 : ℝ)| ≤
      ((n.log2 : ℝ) + 1) * (barrierLogHError + 23 / (S80 : ℝ)) := by
  have hS := S80_pos
  set m := n.log2
  have hP1 : 2 ^ m ≤ n := Nat.log2_self_le hn
  have hP2 : n < 2 ^ (m + 1) := Nat.lt_log2_self
  set P : ℝ := (2 : ℝ) ^ m with hPdef
  have hPpos : 0 < P := by positivity
  have hnR : P ≤ (n : ℝ) := by rw [hPdef]; exact_mod_cast hP1
  have hnR2 : (n : ℝ) < 2 * P := by
    rw [hPdef, ← pow_succ']; exact_mod_cast hP2
  set y : ℝ := (n : ℝ) / P with hydef
  have hy1 : 1 ≤ y := by rw [hydef, le_div_iff₀ hPpos]; linarith
  have hy2 : y ≤ 2 := by rw [hydef, div_le_iff₀ hPpos]; linarith
  set Q : ℤ := (((n : ℤ) - 2 ^ m) * S80) / ((n : ℤ) + 2 ^ m)
  have hD : (0 : ℤ) < (n : ℤ) + 2 ^ m := by positivity
  have hQ := ediv_spec (((n : ℤ) - 2 ^ m) * S80) hD
  have hqform : ((y - 1) / (y + 1)) * (S80 : ℝ) =
      ((((n : ℤ) - 2 ^ m) * S80 : ℤ) : ℝ) / (((n : ℤ) + 2 ^ m : ℤ) : ℝ) := by
    rw [hydef]; push_cast; rw [← hPdef]; field_simp
  have hY := logY_spec hy1 hy2 (Q := Q) (by rw [hqform]; exact hQ.1) (by rw [hqform]; exact hQ.2)
  have hlogn : Real.log (n : ℝ) = (m : ℝ) * Real.log 2 + Real.log y := by
    have : (n : ℝ) = P * y := by rw [hydef]; field_simp
    rw [this, Real.log_mul hPpos.ne' (by linarith), hPdef, Real.log_pow]
  have hrem2 := barrier_logH_remainder_uniform (y := 2) ⟨by norm_num, le_rfl⟩
  have hL2 := L2F_spec
  have hlog2 : |Real.log 2 - (L2F : ℝ) / (S80 : ℝ)| ≤ barrierLogHError + 1 / (S80 : ℝ) := by
    have h0 := abs_sub_fl_le (by norm_num) hL2.1 hL2.2.le
    have hsp : Real.log 2 - (L2F : ℝ) / (S80 : ℝ) =
        (Real.log 2 - barrierLogH 2) + (barrierLogH 2 - (L2F : ℝ) / (S80 : ℝ)) := by ring
    rw [hsp]
    have := abs_add_le (Real.log 2 - barrierLogH 2) (barrierLogH 2 - (L2F : ℝ) / (S80 : ℝ))
    rw [abs_of_nonneg hrem2.1] at this
    linarith [hrem2.2]
  have hval : ((logI n : ℤ) : ℝ) / (S80 : ℝ) =
      (m : ℝ) * ((L2F : ℝ) / (S80 : ℝ)) + ((logSerF Q : ℤ) : ℝ) / (S80 : ℝ) := by
    unfold logI; push_cast; ring
  rw [hlogn, hval]
  have hsplit : (m : ℝ) * Real.log 2 + Real.log y -
      ((m : ℝ) * ((L2F : ℝ) / (S80 : ℝ)) + ((logSerF Q : ℤ) : ℝ) / (S80 : ℝ)) =
      (m : ℝ) * (Real.log 2 - (L2F : ℝ) / (S80 : ℝ)) +
        (Real.log y - ((logSerF Q : ℤ) : ℝ) / (S80 : ℝ)) := by ring
  rw [hsplit]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have t1 := abs_add_le ((m : ℝ) * (Real.log 2 - (L2F : ℝ) / (S80 : ℝ)))
    (Real.log y - ((logSerF Q : ℤ) : ℝ) / (S80 : ℝ))
  have t2 : |(m : ℝ) * (Real.log 2 - (L2F : ℝ) / (S80 : ℝ))| ≤
      (m : ℝ) * (barrierLogHError + 23 / (S80 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hm0]
    apply mul_le_mul_of_nonneg_left _ hm0
    have : 1 / (S80 : ℝ) ≤ 23 / (S80 : ℝ) := by
      apply div_le_div_of_nonneg_right (by norm_num) hS.le
    linarith
  nlinarith

def cLog1I (c d a b : ℚ) : Option ℚ :=
  let A : ℤ := a.num * b.den
  let B : ℤ := b.num * a.den
  let L : ℕ := a.den * b.den
  let N : ℕ := (A * A + B * B).toNat
  match findOct ((A : ℚ), (B : ℚ)) with
  | some k =>
    if qabs c ≤ 1 ∧ qabs d ≤ 1 ∧ N ≠ 0 ∧ N.log2 ≤ 1000 ∧ L.log2 ≤ 1000 then
      some (c * (((logI N - 2 * logI L : ℤ) : ℚ) / (2 * S80)) -
        d * (((k * AF + atanSerF (flQ ((octRot k ((A : ℚ), (B : ℚ))).2 /
          (octRot k ((A : ℚ), (B : ℚ))).1)) : ℤ) : ℚ) / S80))
    else none
  | none => none

theorem errI_allowance :
    1502 * (barrierLogHError + 23 / (S80 : ℝ)) + 9 * barrierAtanJ0 + 29 / (S80 : ℝ) <
      1 / 1000000000000 := by
  unfold barrierLogHError barrierAtanJ0 S80; norm_num

set_option maxHeartbeats 4000000 in
theorem cLog1I_spec {c d a b q : ℚ} (h : cLog1I c d a b = some q) :
    |(barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re - (q : ℝ)| < 1 / 1000000000000 := by
  unfold cLog1I at h
  simp only at h
  split at h
  · rename_i k hk
    split_ifs at h with hw
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hc, hd, hN0, hNm, hLm⟩ := hw
    rw [qabs_eq] at hc hd
    set A : ℤ := a.num * b.den with hA
    set B : ℤ := b.num * a.den with hB
    set L : ℕ := a.den * b.den with hL
    set N : ℕ := (A * A + B * B).toNat with hN
    unfold findOct at hk
    have hk' := List.find?_some hk
    have hkmem := List.mem_of_find?_eq_some hk
    unfold octOK at hk'
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hk'
    obtain ⟨⟨⟨hr, hs⟩, h4⟩, hm4⟩ := hk'
    set r := (octRot k ((A : ℚ), (B : ℚ))).1
    set s := (octRot k ((A : ℚ), (B : ℚ))).2
    have hkabs : |k| ≤ 4 := by
      simp only [octCandidates, List.mem_cons, List.not_mem_nil, or_false] at hkmem
      rcases hkmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hrot := octRot_spec k ((A : ℚ), (B : ℚ))
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    have hsR : |(s : ℝ)| ≤ (r : ℝ) / 2 := by
      have : 2 * |s| ≤ r := by rw [← qabs_eq]; exact hs
      have h' : ((2 * |s| : ℚ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith
    have hpos : k = 4 → (s : ℝ) ≤ 0 := by
      intro hk4; rcases h4 with h4 | h4
      · exact absurd hk4 h4
      · exact_mod_cast h4
    have hneg : k = -4 → (0 : ℝ) < (s : ℝ) := by
      intro hk4; rcases hm4 with h4 | h4
      · exact absurd hk4 h4
      · exact_mod_cast h4
    have hS := S80_pos
    -- the scaling
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      have : 0 < L := Nat.mul_pos a.den_pos b.den_pos
      exact_mod_cast this
    have hAa : (A : ℝ) = (L : ℝ) * (a : ℝ) := by
      rw [hA, hL, Rat.cast_def a]; push_cast
      have : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_nz
      field_simp
      try ring
    have hBb : (B : ℝ) = (L : ℝ) * (b : ℝ) := by
      rw [hB, hL, Rat.cast_def b]; push_cast
      have : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_nz
      field_simp
      try ring
    have hNR : (N : ℝ) = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 := by
      have h0 : 0 ≤ A * A + B * B := by nlinarith [mul_self_nonneg A, mul_self_nonneg B]
      rw [hN]
      have : ((A * A + B * B).toNat : ℤ) = A * A + B * B := Int.toNat_of_nonneg h0
      have : (((A * A + B * B).toNat : ℕ) : ℝ) = ((A * A + B * B : ℤ) : ℝ) := by exact_mod_cast this
      rw [this]; push_cast; ring
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := Nat.pos_of_ne_zero hN0
      exact_mod_cast this
    have hz : (⟨(A : ℝ), (B : ℝ)⟩ : ℂ) = ((L : ℝ) : ℂ) * ⟨(a : ℝ), (b : ℝ)⟩ := by
      apply Complex.ext <;> simp [hAa, hBb]
    -- the log of the modulus
    have hre := barrierComplexLog_re (⟨(a : ℝ), (b : ℝ)⟩ : ℂ)
    have hmod : (⟨(a : ℝ), (b : ℝ)⟩ : ℂ).re ^ 2 + (⟨(a : ℝ), (b : ℝ)⟩ : ℂ).im ^ 2 =
        (N : ℝ) / (L : ℝ) ^ 2 := by
      simp only
      rw [hNR, hAa, hBb]; field_simp
      try ring
    rw [hmod, Real.log_div hNpos.ne' (by positivity), Real.log_pow] at hre
    have hlN := logI_spec hN0
    have hlL := logI_spec (n := L) (Nat.pos_iff_ne_zero.mp (Nat.mul_pos a.den_pos b.den_pos))
    -- the argument
    have hargz' := barrierComplexArg_octant_rational k ⟨((A : ℚ) : ℝ), ((B : ℚ) : ℝ)⟩ (r : ℝ) (s : ℝ)
      hrot hrR hsR hkabs hpos hneg
    have hargeq : Complex.arg ⟨(a : ℝ), (b : ℝ)⟩ = Complex.arg ⟨((A : ℚ) : ℝ), ((B : ℚ) : ℝ)⟩ := by
      have hcast : (⟨((A : ℚ) : ℝ), ((B : ℚ) : ℝ)⟩ : ℂ) = ⟨(A : ℝ), (B : ℝ)⟩ := by push_cast; rfl
      rw [hcast, hz, Complex.arg_real_mul _ hLpos]
    set tt : ℚ := s / r with httdef
    have httR : (tt : ℝ) = (s : ℝ) / (r : ℝ) := by rw [httdef]; push_cast; rfl
    have htabs : |(tt : ℝ)| ≤ 1 / 2 := by
      rw [httR, abs_div, abs_of_pos hrR, div_le_iff₀ hrR]; linarith
    set T := flQ tt
    have hT := flQ_spec tt
    set t' : ℝ := (T : ℝ) / (S80 : ℝ) with ht'def
    have ht'le : t' ≤ (tt : ℝ) := by rw [ht'def, div_le_iff₀ hS]; linarith [hT.1]
    have ht'gt : (tt : ℝ) - t' < 1 / (S80 : ℝ) := by
      have : (tt : ℝ) < ((T : ℝ) + 1) / (S80 : ℝ) := by rw [lt_div_iff₀ hS]; linarith [hT.2]
      have h2 : ((T : ℝ) + 1) / (S80 : ℝ) = t' + 1 / (S80 : ℝ) := by rw [ht'def]; ring
      linarith
    have ht'ge : -(1 / 2 : ℝ) ≤ t' := by
      have hS2 : (S80 : ℤ) = 2 * 604462909807314587353088 := by unfold S80; norm_num
      have hc2 : (S80 : ℝ) = 2 * 604462909807314587353088 := by exact_mod_cast hS2
      have hTlo : -(S80 : ℝ) / 2 - 1 < (T : ℝ) := by nlinarith [hT.2, (abs_le.mp htabs).1]
      have hTZ : -(604462909807314587353088 : ℤ) ≤ T := by
        have : ((-(604462909807314587353088 : ℤ) - 1 : ℤ) : ℝ) < (T : ℝ) := by
          push_cast; rw [hc2] at hTlo; linarith
        have := (Int.cast_lt (R := ℝ)).mp this
        omega
      rw [ht'def, le_div_iff₀ hS]
      have : ((-(604462909807314587353088 : ℤ) : ℤ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTZ
      push_cast at this; rw [hc2]; linarith
    have ht'abs : |t'| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp htabs).2]
    have harg := barrierArgApprox_error k t' hkabs ht'abs
    have hTF := atanSerF_spec T
    simp only at hTF
    rw [← ht'def] at hTF
    have hAF := AF_spec
    have hat : |Real.arctan (tt : ℝ) - Real.arctan t'| ≤ (tt : ℝ) - t' := by
      have := arctan_sub_abs_le (tt : ℝ) t'
      rw [abs_of_nonneg (show (0 : ℝ) ≤ (tt : ℝ) - t' by linarith)] at this
      exact this
    -- assemble
    have hcre : (barrierComplex c d).re = (c : ℝ) := by simp [barrierComplex]
    have hcim : (barrierComplex c d).im = (d : ℝ) := by simp [barrierComplex]
    rw [Complex.mul_re, Complex.log_im, hre, hargeq, hargz', ← httR, hcre, hcim]
    have hcR : |(c : ℝ)| ≤ 1 := by exact_mod_cast hc
    have hdR : |(d : ℝ)| ≤ 1 := by exact_mod_cast hd
    have hkR : |(k : ℝ)| ≤ 4 := by exact_mod_cast hkabs
    have he : 0 ≤ barrierLogHError := by unfold barrierLogHError; positivity
    have hj : 0 ≤ barrierAtanJ0 := by unfold barrierAtanJ0; positivity
    have hNm' : (N.log2 : ℝ) ≤ 1000 := by exact_mod_cast hNm
    have hLm' : (L.log2 : ℝ) ≤ 1000 := by exact_mod_cast hLm
    have hEp : 0 ≤ barrierLogHError + 23 / (S80 : ℝ) := by positivity
    set LN := logI N
    set LL := logI L
    set TF := atanSerF T
    have hval : ((c * (((LN - 2 * LL : ℤ) : ℚ) / (2 * S80)) -
        d * (((k * AF + TF : ℤ) : ℚ) / S80) : ℚ) : ℝ) =
        (c : ℝ) * (((LN : ℝ) - 2 * (LL : ℝ)) / (2 * (S80 : ℝ))) -
          (d : ℝ) * (((k : ℝ) * (AF : ℝ) + (TF : ℝ)) / (S80 : ℝ)) := by
      push_cast; ring
    rw [hval]
    set L1 := (Real.log (N : ℝ) - 2 * Real.log (L : ℝ)) / 2 -
      ((LN : ℝ) - 2 * (LL : ℝ)) / (2 * (S80 : ℝ))
    have hL1 : |L1| ≤ 1502 * (barrierLogHError + 23 / (S80 : ℝ)) := by
      have hsp : L1 = ((Real.log (N : ℝ) - (LN : ℝ) / (S80 : ℝ)) -
          2 * (Real.log (L : ℝ) - (LL : ℝ) / (S80 : ℝ))) / 2 := by
        simp only [L1]; field_simp; ring
      rw [hsp, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have t1 := abs_sub (Real.log (N : ℝ) - (LN : ℝ) / (S80 : ℝ))
        (2 * (Real.log (L : ℝ) - (LL : ℝ) / (S80 : ℝ)))
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at t1
      have b1 : ((N.log2 : ℝ) + 1) * (barrierLogHError + 23 / (S80 : ℝ)) ≤
          1001 * (barrierLogHError + 23 / (S80 : ℝ)) := by nlinarith
      have b2 : ((L.log2 : ℝ) + 1) * (barrierLogHError + 23 / (S80 : ℝ)) ≤
          1001 * (barrierLogHError + 23 / (S80 : ℝ)) := by nlinarith
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    set A1 := (k : ℝ) * (Real.pi / 4) + Real.arctan (tt : ℝ) -
      ((k : ℝ) * (AF : ℝ) + (TF : ℝ)) / (S80 : ℝ)
    have hA1 : |A1| ≤ 9 * barrierAtanJ0 + 29 / (S80 : ℝ) := by
      have hsplit : A1 = (Real.arctan (tt : ℝ) - Real.arctan t') +
          ((k : ℝ) * (Real.pi / 4) + Real.arctan t' - barrierArgApprox k t') +
          (k : ℝ) * ((barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)) - (AF : ℝ) / (S80 : ℝ)) +
          (barrierAtanJ t' - (TF : ℝ) / (S80 : ℝ)) := by
        simp only [A1, barrierArgApprox]; field_simp; ring
      have hK : |(k : ℝ) * ((barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)) - (AF : ℝ) / (S80 : ℝ))| ≤
          4 / (S80 : ℝ) := by
        rw [abs_mul]
        have h0 : |(barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)) - (AF : ℝ) / (S80 : ℝ)| ≤
            1 / (S80 : ℝ) := abs_sub_fl_le (by norm_num) hAF.1 hAF.2.le
        calc |(k : ℝ)| * _ ≤ 4 * (1 / (S80 : ℝ)) := mul_le_mul hkR h0 (abs_nonneg _) (by norm_num)
          _ = 4 / (S80 : ℝ) := by ring
      have hJ : |barrierAtanJ t' - (TF : ℝ) / (S80 : ℝ)| ≤ 24 / (S80 : ℝ) :=
        abs_sub_fl_le (by norm_num) hTF.1 hTF.2
      rw [hsplit]
      have := abs_add_le ((Real.arctan (tt : ℝ) - Real.arctan t') +
          ((k : ℝ) * (Real.pi / 4) + Real.arctan t' - barrierArgApprox k t') +
          (k : ℝ) * ((barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)) - (AF : ℝ) / (S80 : ℝ)))
          (barrierAtanJ t' - (TF : ℝ) / (S80 : ℝ))
      have := abs_add_le ((Real.arctan (tt : ℝ) - Real.arctan t') +
          ((k : ℝ) * (Real.pi / 4) + Real.arctan t' - barrierArgApprox k t'))
          ((k : ℝ) * ((barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)) - (AF : ℝ) / (S80 : ℝ)))
      have := abs_add_le (Real.arctan (tt : ℝ) - Real.arctan t')
          ((k : ℝ) * (Real.pi / 4) + Real.arctan t' - barrierArgApprox k t')
      have e1 : (29 : ℝ) / (S80 : ℝ) = 1 / (S80 : ℝ) + 4 / (S80 : ℝ) + 24 / (S80 : ℝ) := by ring
      rw [e1]
      linarith
    have hkey : (c : ℝ) * ((Real.log (N : ℝ) - 2 * Real.log (L : ℝ)) / 2) -
        (d : ℝ) * ((k : ℝ) * (Real.pi / 4) + Real.arctan (tt : ℝ)) -
        ((c : ℝ) * (((LN : ℝ) - 2 * (LL : ℝ)) / (2 * (S80 : ℝ))) -
          (d : ℝ) * (((k : ℝ) * (AF : ℝ) + (TF : ℝ)) / (S80 : ℝ))) = (c : ℝ) * L1 - (d : ℝ) * A1 := by
      simp only [L1, A1]; ring
    have hcL : |(c : ℝ) * L1| ≤ 1502 * (barrierLogHError + 23 / (S80 : ℝ)) := by
      rw [abs_mul]
      calc |(c : ℝ)| * |L1| ≤ 1 * |L1| := mul_le_mul_of_nonneg_right hcR (abs_nonneg _)
        _ ≤ _ := by linarith
    have hdA : |(d : ℝ) * A1| ≤ 9 * barrierAtanJ0 + 29 / (S80 : ℝ) := by
      rw [abs_mul]
      calc |(d : ℝ)| * |A1| ≤ 1 * |A1| := mul_le_mul_of_nonneg_right hdR (abs_nonneg _)
        _ ≤ _ := by linarith
    have htot := abs_sub ((c : ℝ) * L1) ((d : ℝ) * A1)
    have hall := errI_allowance
    calc |_| = |(c : ℝ) * L1 - (d : ℝ) * A1| := by
          first | (congr 1; done) | (congr 1; simp only [L1, A1]; push_cast; ring)
      _ < _ := by linarith
  · simp at h

def cLogI (c d a b : ℚ) : Option ℚ :=
  let n := wPieces c d
  (cLog1I (c / n) (d / n) a b).map (fun q => n * q)

theorem cLogI_spec {c d a b q : ℚ} (h : cLogI c d a b = some q) :
    |(barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re - (q : ℝ)| ≤
      (wPieces c d : ℝ) / 1000000000000 := by
  unfold cLogI at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨q1, h1, rfl⟩ := h
  have hs := cLog1I_spec h1
  set n := wPieces c d
  have hn : (0 : ℝ) < n := by
    have : 1 ≤ n := le_max_left _ _
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hsplit : (barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re =
      n * (barrierComplex (c / n) (d / n) * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re := by
    simp only [barrierComplex, Complex.mul_re]
    push_cast
    field_simp
  rw [hsplit]
  push_cast
  rw [← mul_sub, abs_mul, abs_of_pos hn]
  calc (n : ℝ) * |_| ≤ n * (1 / 1000000000000) := mul_le_mul_of_nonneg_left hs.le hn.le
    _ = _ := by ring

end CatalanMeasure.G728
