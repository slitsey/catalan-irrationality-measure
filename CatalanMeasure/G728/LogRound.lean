module
public import CatalanMeasure.Cert.LogApprox
@[expose] public section
/-!
# Complex logarithm enclosures with rounded series inputs

`cLog1` feeds the series of `barrierWeightedComplexLogRat` with the exact rational inputs
`y = |z|²/2^m ∈ [1,2]` and `t = s/r`, whose denominators (≈2^160 for the 728 fields) make the
kernel's rational arithmetic in the 18 + 24 series terms expensive.  `cLog1R` first rounds
`y` and `t` down to the grid `2^-48`.  Since `log` and `arctan` are 1-Lipschitz on the relevant
ranges, the rounding adds at most `3/2 · 2^-48` to the error.
-/
namespace CatalanMeasure.G728
open CatalanMeasure.Cert OAI.InternalCatalan

def S48 : ℤ := 281474976710656

theorem S48_pos : (0 : ℝ) < (S48 : ℝ) := by unfold S48; norm_num

/-- `⌊q · 2^48⌋` -/
def rk48 (q : ℚ) : ℤ := q.num * S48 / (q.den : ℤ)

/-- `q` rounded down to the grid `2^-48` -/
def rnd48 (q : ℚ) : ℚ := ((rk48 q : ℤ) : ℚ) / (S48 : ℚ)

theorem rk48_spec (q : ℚ) :
    ((rk48 q : ℤ) : ℝ) ≤ (q : ℝ) * (S48 : ℝ) ∧ (q : ℝ) * (S48 : ℝ) < ((rk48 q : ℤ) : ℝ) + 1 := by
  have hbpos : 0 < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have h1 : (q.den : ℤ) * (q.num * S48 / (q.den : ℤ)) ≤ q.num * S48 :=
    Int.mul_ediv_self_le hbpos.ne'
  have h2 : q.num * S48 < (q.den : ℤ) * (q.num * S48 / (q.den : ℤ) + 1) := by
    have := Int.emod_lt_of_pos (q.num * S48) hbpos
    have h3 := Int.mul_ediv_add_emod (q.num * S48) (q.den : ℤ)
    nlinarith [this]
  have hbR : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have h1R : (q.den : ℝ) * ((rk48 q : ℤ) : ℝ) ≤ (q.num : ℝ) * (S48 : ℝ) := by
    unfold rk48; exact_mod_cast h1
  have h2R : (q.num : ℝ) * (S48 : ℝ) < (q.den : ℝ) * (((rk48 q : ℤ) : ℝ) + 1) := by
    unfold rk48; exact_mod_cast h2
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by rw [Rat.cast_def]
  rw [hq]
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hbR]; linarith
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hbR]; linarith

theorem rnd48_cast (q : ℚ) : ((rnd48 q : ℚ) : ℝ) = ((rk48 q : ℤ) : ℝ) / (S48 : ℝ) := by
  unfold rnd48; push_cast; rfl

theorem rnd48_le (q : ℚ) : ((rnd48 q : ℚ) : ℝ) ≤ (q : ℝ) := by
  rw [rnd48_cast, div_le_iff₀ S48_pos]; exact (rk48_spec q).1

theorem rnd48_sub_lt (q : ℚ) : (q : ℝ) - ((rnd48 q : ℚ) : ℝ) < 1 / (S48 : ℝ) := by
  have h := (rk48_spec q).2
  rw [rnd48_cast]
  have hS := S48_pos
  have hq : (q : ℝ) < (((rk48 q : ℤ) : ℝ) + 1) / (S48 : ℝ) := by
    rw [lt_div_iff₀ hS]; linarith
  calc (q : ℝ) - ((rk48 q : ℤ) : ℝ) / (S48 : ℝ)
      < (((rk48 q : ℤ) : ℝ) + 1) / (S48 : ℝ) - ((rk48 q : ℤ) : ℝ) / (S48 : ℝ) := by linarith
    _ = 1 / (S48 : ℝ) := by ring

/-- grid points below `q` stay below the rounded value -/
theorem rnd48_ge {q : ℚ} {z : ℤ} (h : (z : ℝ) ≤ (q : ℝ) * (S48 : ℝ)) :
    (z : ℝ) / (S48 : ℝ) ≤ ((rnd48 q : ℚ) : ℝ) := by
  have h2 := (rk48_spec q).2
  have hlt : (z : ℝ) < ((rk48 q : ℤ) : ℝ) + 1 := lt_of_le_of_lt h h2
  have hz : z ≤ rk48 q := by
    have : (z : ℝ) < ((rk48 q + 1 : ℤ) : ℝ) := by push_cast; exact hlt
    have := (Int.cast_lt (R := ℝ)).mp this
    omega
  rw [rnd48_cast]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hz) S48_pos.le

theorem arctan_sub_abs_le (a b : ℝ) : |Real.arctan a - Real.arctan b| ≤ |a - b| := by
  have hL : LipschitzWith 1 Real.arctan := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun x => Real.differentiableAt_arctan x) ?_
    intro x
    rw [Real.deriv_arctan]
    have hpos : 0 < 1 + x ^ 2 := by positivity
    have hle : 1 / (1 + x ^ 2) ≤ 1 := by
      rw [div_le_one hpos]; nlinarith [sq_nonneg x]
    have hnn : 0 ≤ 1 / (1 + x ^ 2) := by positivity
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hnn]
    simpa using hle
  have := hL.dist_le_mul a b
  simpa [Real.dist_eq] using this

theorem log_sub_le_of_le {y y' : ℝ} (h1 : 1 ≤ y') (h2 : y' ≤ y) :
    |Real.log y - Real.log y'| ≤ y - y' := by
  have hy'pos : 0 < y' := by linarith
  have hypos : 0 < y := by linarith
  have hnn : 0 ≤ Real.log y - Real.log y' := by
    have := Real.log_le_log hy'pos h2; linarith
  rw [abs_of_nonneg hnn, ← Real.log_div hypos.ne' hy'pos.ne']
  have hq : 0 < y / y' := div_pos hypos hy'pos
  have := Real.log_le_sub_one_of_pos hq
  have hdiv : y / y' - 1 ≤ y - y' := by
    rw [div_sub_one hy'pos.ne', div_le_iff₀ hy'pos]
    nlinarith
  linarith

def cLog1R (c d a b : ℚ) : Option ℚ :=
  match findExp (a * a + b * b), findOct (a, b) with
  | some m, some k =>
    if qabs c ≤ 1 ∧ qabs d ≤ 1 ∧ qabs m ≤ 100 then
      some (barrierWeightedComplexLogRat c d m k (rnd48 ((a * a + b * b) / 2 ^ m))
        (rnd48 ((octRot k (a, b)).2 / (octRot k (a, b)).1)))
    else none
  | _, _ => none

/-- error budget of one rounded piece -/
def errR : ℚ := 1 / 1000000000000 + 1 / 140737488355328

theorem cLog1R_spec {c d a b q : ℚ} (h : cLog1R c d a b = some q) :
    |(barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re - (q : ℝ)| < (errR : ℝ) := by
  unfold cLog1R at h
  split at h
  · rename_i m k hm hk
    split_ifs at h with hw
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hc, hd, hmm⟩ := hw
    rw [qabs_eq] at hc hd hmm
    unfold findExp at hm
    have hm' := List.find?_some hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm'
    obtain ⟨hy1, hy2⟩ := hm'
    unfold findOct at hk
    have hk' := List.find?_some hk
    have hkmem := List.mem_of_find?_eq_some hk
    unfold octOK at hk'
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hk'
    obtain ⟨⟨⟨hr, hs⟩, h4⟩, hm4⟩ := hk'
    set r := (octRot k (a, b)).1
    set s := (octRot k (a, b)).2
    set y : ℚ := (a * a + b * b) / 2 ^ m with hydef
    have hn2 : a * a + b * b = 2 ^ m * y := by
      have : (2 : ℚ) ^ m ≠ 0 := zpow_ne_zero _ (by norm_num)
      rw [hydef]; field_simp
    have hnorm : (⟨(a : ℝ), (b : ℝ)⟩ : ℂ).re ^ 2 + (⟨(a : ℝ), (b : ℝ)⟩ : ℂ).im ^ 2 =
        (2 : ℝ) ^ m * (y : ℝ) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) hn2
      simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_zpow, Rat.cast_ofNat] at this
      simp only [pow_two]
      rw [this]
    have hkabs : |k| ≤ 4 := by
      simp only [octCandidates, List.mem_cons, List.not_mem_nil, or_false] at hkmem
      rcases hkmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hrot := octRot_spec k (a, b)
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
    have hS := S48_pos
    -- the rounded inputs
    set y' := rnd48 y
    set t : ℚ := s / r with htdef
    set t' := rnd48 t
    have hy1R : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
    have hy2R : (y : ℝ) ≤ 2 := by exact_mod_cast hy2
    have hy'le : (y' : ℝ) ≤ (y : ℝ) := rnd48_le y
    have hy'sub : (y : ℝ) - (y' : ℝ) < 1 / (S48 : ℝ) := rnd48_sub_lt y
    have hy'1 : (1 : ℝ) ≤ (y' : ℝ) := by
      have := rnd48_ge (q := y) (z := S48) (by nlinarith)
      rwa [div_self hS.ne'] at this
    have htR : (t : ℝ) = (s : ℝ) / (r : ℝ) := by rw [htdef]; push_cast; rfl
    have htabs : |(t : ℝ)| ≤ 1 / 2 := by
      rw [htR, abs_div, abs_of_pos hrR, div_le_iff₀ hrR]; linarith
    have ht'le : (t' : ℝ) ≤ (t : ℝ) := rnd48_le t
    have ht'sub : (t : ℝ) - (t' : ℝ) < 1 / (S48 : ℝ) := rnd48_sub_lt t
    have ht'ge : -(1 / 2 : ℝ) ≤ (t' : ℝ) := by
      have h0 : ((-140737488355328 : ℤ) : ℝ) ≤ (t : ℝ) * (S48 : ℝ) := by
        have := (abs_le.mp htabs).1
        unfold S48; push_cast; nlinarith
      have := rnd48_ge (q := t) h0
      unfold S48 at this; push_cast at this; linarith
    have ht'abs : |(t' : ℝ)| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp htabs).2]
    -- the two OAI error estimates at the rounded inputs
    have hlog := barrier_scaled_log_abs_error m (y := (y' : ℝ)) ⟨hy'1, by linarith⟩
    have harg := barrierArgApprox_error k (t' : ℝ) hkabs ht'abs
    have hargz := barrierComplexArg_octant_rational k ⟨(a : ℝ), (b : ℝ)⟩ (r : ℝ) (s : ℝ)
      hrot hrR hsR hkabs hpos hneg
    have hre := barrierComplexLog_re (⟨(a : ℝ), (b : ℝ)⟩ : ℂ)
    rw [hnorm] at hre
    -- the rounding errors
    have hly : |Real.log ((2 : ℝ) ^ m * (y : ℝ)) - Real.log ((2 : ℝ) ^ m * (y' : ℝ))| ≤
        (y : ℝ) - (y' : ℝ) := by
      have h2m : (0 : ℝ) < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
      rw [Real.log_mul h2m.ne' (by linarith), Real.log_mul h2m.ne' (by linarith)]
      have := log_sub_le_of_le hy'1 hy'le
      calc _ = |Real.log (y : ℝ) - Real.log (y' : ℝ)| := by congr 1; ring
        _ ≤ _ := this
    have hat : |Real.arctan (t : ℝ) - Real.arctan (t' : ℝ)| ≤ (t : ℝ) - (t' : ℝ) := by
      have := arctan_sub_abs_le (t : ℝ) (t' : ℝ)
      rw [abs_of_nonneg (show (0 : ℝ) ≤ (t : ℝ) - (t' : ℝ) by linarith)] at this
      exact this
    -- assemble
    rw [barrierWeightedComplexLogRat_cast]
    unfold barrierWeightedComplexLogApprox
    rw [Complex.mul_re, Complex.log_im, hre, hargz, ← htR]
    have hcre : (barrierComplex c d).re = (c : ℝ) := by simp [barrierComplex]
    have hcim : (barrierComplex c d).im = (d : ℝ) := by simp [barrierComplex]
    rw [hcre, hcim]
    have hcR : |(c : ℝ)| ≤ 1 := by exact_mod_cast hc
    have hdR : |(d : ℝ)| ≤ 1 := by exact_mod_cast hd
    have hmR : |(m : ℝ)| ≤ 100 := by
      have : ((|m| : ℤ) : ℚ) ≤ 100 := by exact_mod_cast hmm
      rw [← Int.cast_abs]; exact_mod_cast this
    have he : 0 ≤ barrierLogHError := by unfold barrierLogHError; positivity
    have hj : 0 ≤ barrierAtanJ0 := by unfold barrierAtanJ0; positivity
    have hallow := barrier_weighted_log_error_allowance
    set L1 := Real.log ((2 : ℝ) ^ m * (y : ℝ)) / 2 - barrierScaledLogApprox m (y' : ℝ) / 2
    set A1 := (k : ℝ) * (Real.pi / 4) + Real.arctan (t : ℝ) - barrierArgApprox k (t' : ℝ)
    have hL1 : |L1| ≤ (1 / (S48 : ℝ) + (|(m : ℝ)| + 1) * barrierLogHError) / 2 := by
      have : L1 = ((Real.log ((2 : ℝ) ^ m * (y : ℝ)) - Real.log ((2 : ℝ) ^ m * (y' : ℝ))) +
          (Real.log ((2 : ℝ) ^ m * (y' : ℝ)) - barrierScaledLogApprox m (y' : ℝ))) / 2 := by
        simp only [L1]; ring
      rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc _ ≤ |Real.log ((2 : ℝ) ^ m * (y : ℝ)) - Real.log ((2 : ℝ) ^ m * (y' : ℝ))| +
            |Real.log ((2 : ℝ) ^ m * (y' : ℝ)) - barrierScaledLogApprox m (y' : ℝ)| :=
          abs_add_le _ _
        _ ≤ _ := by linarith
    have hA1 : |A1| ≤ 1 / (S48 : ℝ) + 9 * barrierAtanJ0 := by
      have : A1 = (Real.arctan (t : ℝ) - Real.arctan (t' : ℝ)) +
          ((k : ℝ) * (Real.pi / 4) + Real.arctan (t' : ℝ) - barrierArgApprox k (t' : ℝ)) := by
        simp only [A1]; ring
      rw [this]
      calc _ ≤ |Real.arctan (t : ℝ) - Real.arctan (t' : ℝ)| +
            |(k : ℝ) * (Real.pi / 4) + Real.arctan (t' : ℝ) - barrierArgApprox k (t' : ℝ)| :=
          abs_add_le _ _
        _ ≤ _ := by linarith
    have hkey : (c : ℝ) * (Real.log ((2 : ℝ) ^ m * (y : ℝ)) / 2) -
        (d : ℝ) * ((k : ℝ) * (Real.pi / 4) + Real.arctan (t : ℝ)) -
        ((c : ℝ) * (barrierScaledLogApprox m (y' : ℝ) / 2) - (d : ℝ) * barrierArgApprox k (t' : ℝ)) =
        (c : ℝ) * L1 - (d : ℝ) * A1 := by
      simp only [L1, A1]; ring
    rw [hkey]
    have hcL : |(c : ℝ) * L1| ≤ (1 / (S48 : ℝ) + 101 * barrierLogHError) / 2 := by
      rw [abs_mul]
      have h0 : |L1| ≤ (1 / (S48 : ℝ) + 101 * barrierLogHError) / 2 := by
        refine hL1.trans ?_
        apply div_le_div_of_nonneg_right _ (by norm_num)
        nlinarith
      calc |(c : ℝ)| * |L1| ≤ 1 * |L1| := mul_le_mul_of_nonneg_right hcR (abs_nonneg _)
        _ ≤ _ := by linarith
    have hdA : |(d : ℝ) * A1| ≤ 1 / (S48 : ℝ) + 9 * barrierAtanJ0 := by
      rw [abs_mul]
      calc |(d : ℝ)| * |A1| ≤ 1 * |A1| := mul_le_mul_of_nonneg_right hdR (abs_nonneg _)
        _ ≤ _ := by linarith
    have htot := abs_sub ((c : ℝ) * L1) ((d : ℝ) * A1)
    have hS' : 1 / (S48 : ℝ) = 1 / 281474976710656 := by unfold S48; norm_num
    unfold errR
    push_cast
    rw [hS'] at hcL hdA
    linarith
  · simp at h

def cLogR (c d a b : ℚ) : Option ℚ :=
  let n := wPieces c d
  (cLog1R (c / n) (d / n) a b).map (fun q => n * q)

theorem cLogR_spec {c d a b q : ℚ} (h : cLogR c d a b = some q) :
    |(barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re - (q : ℝ)| ≤
      (wPieces c d : ℝ) * (errR : ℝ) := by
  unfold cLogR at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨q1, h1, rfl⟩ := h
  have hs := cLog1R_spec h1
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
  exact mul_le_mul_of_nonneg_left hs.le hn.le

end CatalanMeasure.G728
