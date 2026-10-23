module
public import CatalanMeasure.G728.LogRound
@[expose] public section
/-!
# Fixed-point complex logarithm enclosures

`cLog1F` computes the same approximation as `cLog1` (OAI's 18-term log series and 24-term
arctan series after octant reduction), but in integer fixed point at scale `S = 2^80`:
the series inputs `q = (y-1)/(y+1)` and `t = s/r` are floored to `Q/S`, `T/S`, and each series
term is an integer floor.  This avoids exact rational series with growing denominators.
Error: `1e-12` (OAI's series bound) plus at most `91/S` per piece.
-/
namespace CatalanMeasure.G728
open CatalanMeasure.Cert OAI.InternalCatalan

def S80 : ℤ := 1208925819614629174706176

theorem S80_pos : (0 : ℝ) < (S80 : ℝ) := by unfold S80; norm_num

/-- `⌊x · 2^80⌋` -/
def flQ (x : ℚ) : ℤ := x.num * S80 / (x.den : ℤ)

theorem ediv_spec (N : ℤ) {D : ℤ} (hD : 0 < D) :
    ((N / D : ℤ) : ℝ) ≤ (N : ℝ) / (D : ℝ) ∧ (N : ℝ) / (D : ℝ) < ((N / D : ℤ) : ℝ) + 1 := by
  have h1 : D * (N / D) ≤ N := Int.mul_ediv_self_le hD.ne'
  have h2 : N < D * (N / D + 1) := by
    have := Int.emod_lt_of_pos N hD
    have h3 := Int.mul_ediv_add_emod N D
    nlinarith [this]
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have h1R : (D : ℝ) * ((N / D : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
  have h2R : (N : ℝ) < (D : ℝ) * (((N / D : ℤ) : ℝ) + 1) := by exact_mod_cast h2
  constructor
  · rw [le_div_iff₀ hDR]; linarith
  · rw [div_lt_iff₀ hDR]; linarith

theorem flQ_spec (x : ℚ) :
    ((flQ x : ℤ) : ℝ) ≤ (x : ℝ) * (S80 : ℝ) ∧ (x : ℝ) * (S80 : ℝ) < ((flQ x : ℤ) : ℝ) + 1 := by
  have hb : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
  have h := ediv_spec (x.num * S80) hb
  have hx : (x : ℝ) * (S80 : ℝ) = ((x.num * S80 : ℤ) : ℝ) / ((x.den : ℤ) : ℝ) := by
    rw [Rat.cast_def]; push_cast; ring
  rw [hx]; exact h

/-- floors of a list of terms -/
theorem sum_floor_bounds (n : ℕ) (g : ℕ → ℤ) (f : ℕ → ℝ)
    (h : ∀ j, ((g j : ℤ) : ℝ) ≤ f j ∧ f j < ((g j : ℤ) : ℝ) + 1) :
    ((((List.range n).map g).sum : ℤ) : ℝ) ≤ ∑ j ∈ Finset.range n, f j ∧
      ∑ j ∈ Finset.range n, f j ≤ ((((List.range n).map g).sum : ℤ) : ℝ) + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Int.cast_add,
      Nat.cast_succ]
    have := h n
    constructor <;> linarith [ih.1, ih.2, this.1, this.2]

def logSerF (Q : ℤ) : ℤ :=
  ((List.range 18).map (fun j => (2 * Q ^ (2 * j + 1)) / (((2 * j + 1 : ℕ) : ℤ) * S80 ^ (2 * j)))).sum

def atanSerF (T : ℤ) : ℤ :=
  ((List.range 24).map (fun j => ((-1) ^ j * T ^ (2 * j + 1)) / (((2 * j + 1 : ℕ) : ℤ) * S80 ^ (2 * j)))).sum

theorem term_spec (A : ℤ) (j : ℕ) (X : ℝ) (hX : X = (A : ℝ) / (S80 : ℝ)) (c : ℤ) :
    let g := (c * A ^ (2 * j + 1)) / (((2 * j + 1 : ℕ) : ℤ) * S80 ^ (2 * j))
    ((g : ℤ) : ℝ) ≤ (c : ℝ) * X ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) * (S80 : ℝ) ∧
      (c : ℝ) * X ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) * (S80 : ℝ) < ((g : ℤ) : ℝ) + 1 := by
  intro g
  have hS := S80_pos
  have hD : (0 : ℤ) < ((2 * j + 1 : ℕ) : ℤ) * S80 ^ (2 * j) := by
    have : (0 : ℤ) < S80 := by unfold S80; norm_num
    positivity
  have h := ediv_spec (c * A ^ (2 * j + 1)) hD
  have heq : (c : ℝ) * X ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) * (S80 : ℝ) =
      ((c * A ^ (2 * j + 1) : ℤ) : ℝ) / ((((2 * j + 1 : ℕ) : ℤ) * S80 ^ (2 * j) : ℤ) : ℝ) := by
    rw [hX, div_pow]; push_cast
    have hS0 : (S80 : ℝ) ≠ 0 := hS.ne'
    rw [pow_succ]
    field_simp
    ring
  rw [heq]; exact h

theorem logSerF_spec (Q : ℤ) :
    let q : ℝ := (Q : ℝ) / (S80 : ℝ)
    ((logSerF Q : ℤ) : ℝ) ≤ (2 * ∑ j ∈ Finset.range 18, q ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)) * S80 ∧
      (2 * ∑ j ∈ Finset.range 18, q ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)) * S80 ≤
        ((logSerF Q : ℤ) : ℝ) + 18 := by
  intro q
  have h := sum_floor_bounds 18 (fun j => (2 * Q ^ (2 * j + 1)) / (((2 * j + 1 : ℕ) : ℤ) * S80 ^ (2 * j)))
    (fun j => ((2 : ℤ) : ℝ) * q ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) * (S80 : ℝ))
    (fun j => term_spec Q j q rfl 2)
  have hsum : (2 * ∑ j ∈ Finset.range 18, q ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)) * S80 =
      ∑ j ∈ Finset.range 18, ((2 : ℤ) : ℝ) * q ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) * (S80 : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; push_cast; ring
  unfold logSerF
  rw [hsum]
  exact_mod_cast h

theorem atanSerF_spec (T : ℤ) :
    let t : ℝ := (T : ℝ) / (S80 : ℝ)
    ((atanSerF T : ℤ) : ℝ) ≤ barrierAtanJ t * S80 ∧ barrierAtanJ t * S80 ≤ ((atanSerF T : ℤ) : ℝ) + 24 := by
  intro t
  have h := sum_floor_bounds 24 (fun j => ((-1) ^ j * T ^ (2 * j + 1)) / (((2 * j + 1 : ℕ) : ℤ) * S80 ^ (2 * j)))
    (fun j => (((-1) ^ j : ℤ) : ℝ) * t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) * (S80 : ℝ))
    (fun j => term_spec T j t rfl ((-1) ^ j))
  have hsum : barrierAtanJ t * S80 =
      ∑ j ∈ Finset.range 24, (((-1) ^ j : ℤ) : ℝ) * t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) * (S80 : ℝ) := by
    unfold barrierAtanJ
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; push_cast; ring
  unfold atanSerF
  rw [hsum]
  exact_mod_cast h

def L2F : ℤ := flQ (5796068539909855793494541848 / 8361959339180483840538659925)

def AF : ℤ := flQ (82070093885243869609160349250891 / 177009634670845858814825909452800 +
  112400876852048123008581938124204001832 / 349341672659511491372281601118448876275)

theorem L2F_spec : ((L2F : ℤ) : ℝ) ≤ barrierLogH 2 * S80 ∧ barrierLogH 2 * S80 < ((L2F : ℤ) : ℝ) + 1 := by
  have h := flQ_spec (5796068539909855793494541848 / 8361959339180483840538659925)
  have hc : (((5796068539909855793494541848 / 8361959339180483840538659925 : ℚ)) : ℝ) = barrierLogH 2 := by
    rw [← barrierLogHRat_two_eq, barrierLogHRat_cast]; norm_num
  rw [hc] at h; exact h

theorem AF_spec : ((AF : ℤ) : ℝ) ≤ (barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)) * S80 ∧
    (barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)) * S80 < ((AF : ℤ) : ℝ) + 1 := by
  have h := flQ_spec (82070093885243869609160349250891 / 177009634670845858814825909452800 +
    112400876852048123008581938124204001832 / 349341672659511491372281601118448876275)
  have hc : (((82070093885243869609160349250891 / 177009634670845858814825909452800 +
      112400876852048123008581938124204001832 / 349341672659511491372281601118448876275 : ℚ)) : ℝ) =
      barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3) := by
    rw [← barrierAtanJRat_half_eq, ← barrierAtanJRat_third_eq]
    push_cast
    rw [barrierAtanJRat_cast, barrierAtanJRat_cast]; norm_num
  rw [hc] at h; exact h

theorem abs_sub_fl_le {X : ℝ} {F : ℤ} {n : ℝ} (hn : 0 ≤ n) (h1 : (F : ℝ) ≤ X * (S80 : ℝ))
    (h2 : X * (S80 : ℝ) ≤ (F : ℝ) + n) : |X - (F : ℝ) / (S80 : ℝ)| ≤ n / (S80 : ℝ) := by
  have hS := S80_pos
  have hlo : (F : ℝ) / (S80 : ℝ) ≤ X := by rw [div_le_iff₀ hS]; linarith
  have hhi : X ≤ ((F : ℝ) + n) / (S80 : ℝ) := by rw [le_div_iff₀ hS]; linarith
  have hsplit : ((F : ℝ) + n) / (S80 : ℝ) = (F : ℝ) / (S80 : ℝ) + n / (S80 : ℝ) := by ring
  have hn' : 0 ≤ n / (S80 : ℝ) := div_nonneg hn hS.le
  rw [abs_le]; constructor <;> linarith

def cLog1F (c d a b : ℚ) : Option ℚ :=
  match findExp (a * a + b * b), findOct (a, b) with
  | some m, some k =>
    if qabs c ≤ 1 ∧ qabs d ≤ 1 ∧ qabs m ≤ 100 then
      some (c * (((m * L2F + logSerF (flQ (((a * a + b * b) / 2 ^ m - 1) /
          ((a * a + b * b) / 2 ^ m + 1))) : ℤ) : ℚ) / (2 * S80)) -
        d * (((k * AF + atanSerF (flQ ((octRot k (a, b)).2 / (octRot k (a, b)).1)) : ℤ) : ℚ) / S80))
    else none
  | _, _ => none

/-- error budget of one fixed-point piece -/
def errF : ℚ := 1 / 1000000000000 + 1 / 9444732965739290427392

set_option maxHeartbeats 4000000 in
theorem cLog1F_spec {c d a b q : ℚ} (h : cLog1F c d a b = some q) :
    |(barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re - (q : ℝ)| < (errF : ℝ) := by
  unfold cLog1F at h
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
    have hS := S80_pos
    -- the log input
    have hy1R : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
    have hy2R : (y : ℝ) ≤ 2 := by exact_mod_cast hy2
    set qq : ℚ := (y - 1) / (y + 1) with hqqdef
    have hqqR : (qq : ℝ) = ((y : ℝ) - 1) / ((y : ℝ) + 1) := by rw [hqqdef]; push_cast; ring
    have hq0 : (0 : ℝ) ≤ (qq : ℝ) := by rw [hqqR]; apply div_nonneg <;> linarith
    have hq3 : (qq : ℝ) ≤ 1 / 3 := by
      rw [hqqR, div_le_iff₀ (by linarith)]; linarith
    set Q := flQ qq
    have hQ := flQ_spec qq
    set q' : ℝ := (Q : ℝ) / (S80 : ℝ) with hq'def
    have hq'le : q' ≤ (qq : ℝ) := by rw [hq'def, div_le_iff₀ hS]; linarith [hQ.1]
    have hq'gt : (qq : ℝ) - q' < 1 / (S80 : ℝ) := by
      have : (qq : ℝ) < ((Q : ℝ) + 1) / (S80 : ℝ) := by rw [lt_div_iff₀ hS]; linarith [hQ.2]
      have h2 : ((Q : ℝ) + 1) / (S80 : ℝ) = q' + 1 / (S80 : ℝ) := by rw [hq'def]; ring
      linarith
    have hq'0 : 0 ≤ q' := by
      have hQ0 : (0 : ℤ) ≤ Q := by
        have : (-1 : ℝ) < (Q : ℝ) := by nlinarith [hQ.2]
        have : (-1 : ℤ) < Q := by exact_mod_cast this
        omega
      rw [hq'def]; exact div_nonneg (by exact_mod_cast hQ0) hS.le
    -- y'' with parameter q'
    set y2 : ℝ := (1 + q') / (1 - q') with hy2def
    have h1q : 0 < 1 - q' := by linarith
    have hy2q : (y2 - 1) / (y2 + 1) = q' := by
      rw [hy2def]; field_simp; ring
    have hy21 : 1 ≤ y2 := by rw [hy2def, le_div_iff₀ h1q]; linarith
    have hy22 : y2 ≤ 2 := by rw [hy2def, div_le_iff₀ h1q]; linarith
    have hyform : (y : ℝ) = (1 + (qq : ℝ)) / (1 - (qq : ℝ)) := by
      rw [hqqR]; field_simp; ring
    have hy2le : y2 ≤ (y : ℝ) := by
      rw [hyform, hy2def, div_le_div_iff₀ h1q (by linarith)]; nlinarith
    have hydiff : (y : ℝ) - y2 ≤ 9 / 2 * ((qq : ℝ) - q') := by
      have h1qq : 0 < 1 - (qq : ℝ) := by linarith
      have : (y : ℝ) - y2 = 2 * ((qq : ℝ) - q') / ((1 - (qq : ℝ)) * (1 - q')) := by
        rw [hyform, hy2def]; field_simp; ring
      rw [this, div_le_iff₀ (by positivity)]
      have hprod : 4 / 9 ≤ (1 - (qq : ℝ)) * (1 - q') := by nlinarith
      nlinarith [hq'le]
    -- the series value of log at y2
    have hser : barrierLogH y2 = 2 * ∑ j ∈ Finset.range 18, q' ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) := by
      unfold barrierLogH; rw [hy2q]
    have hLF := logSerF_spec Q
    simp only at hLF
    rw [← hq'def, ← hser] at hLF
    have hscaled := barrier_scaled_log_abs_error m (y := y2) ⟨hy21, hy22⟩
    have hL2 := L2F_spec
    -- the arg input
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
      have hlo : (-(S80 : ℝ)) / 2 ≤ (tt : ℝ) * (S80 : ℝ) := by
        nlinarith [(abs_le.mp htabs).1]
      have hTlo : -(S80 : ℝ) / 2 - 1 < (T : ℝ) := by linarith [hT.2]
      have hS2 : (S80 : ℤ) = 2 * 604462909807314587353088 := by unfold S80; norm_num
      have hTZ : -(604462909807314587353088 : ℤ) ≤ T := by
        have : ((-(604462909807314587353088 : ℤ) - 1 : ℤ) : ℝ) < (T : ℝ) := by
          have hc : (S80 : ℝ) = 2 * 604462909807314587353088 := by exact_mod_cast hS2
          push_cast; rw [hc] at hTlo; linarith
        have := (Int.cast_lt (R := ℝ)).mp this
        omega
      rw [ht'def, le_div_iff₀ hS]
      have hc : (S80 : ℝ) = 2 * 604462909807314587353088 := by exact_mod_cast hS2
      have : ((-(604462909807314587353088 : ℤ) : ℤ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTZ
      push_cast at this; rw [hc]; linarith
    have ht'abs : |t'| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp htabs).2]
    have harg := barrierArgApprox_error k t' hkabs ht'abs
    have hTF := atanSerF_spec T
    simp only at hTF
    rw [← ht'def] at hTF
    have hAF := AF_spec
    have hargz := barrierComplexArg_octant_rational k ⟨(a : ℝ), (b : ℝ)⟩ (r : ℝ) (s : ℝ)
      hrot hrR hsR hkabs hpos hneg
    have hre := barrierComplexLog_re (⟨(a : ℝ), (b : ℝ)⟩ : ℂ)
    rw [hnorm] at hre
    -- rounding errors of the inputs
    have hly : |Real.log ((2 : ℝ) ^ m * (y : ℝ)) - Real.log ((2 : ℝ) ^ m * y2)| ≤ (y : ℝ) - y2 := by
      have h2m : (0 : ℝ) < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
      rw [Real.log_mul h2m.ne' (by linarith), Real.log_mul h2m.ne' (by linarith)]
      have := log_sub_le_of_le hy21 hy2le
      calc _ = |Real.log (y : ℝ) - Real.log y2| := by congr 1; ring
        _ ≤ _ := this
    have hat : |Real.arctan (tt : ℝ) - Real.arctan t'| ≤ (tt : ℝ) - t' := by
      have := arctan_sub_abs_le (tt : ℝ) t'
      rw [abs_of_nonneg (show (0 : ℝ) ≤ (tt : ℝ) - t' by linarith)] at this
      exact this
    -- assemble
    have hcre : (barrierComplex c d).re = (c : ℝ) := by simp [barrierComplex]
    have hcim : (barrierComplex c d).im = (d : ℝ) := by simp [barrierComplex]
    rw [Complex.mul_re, Complex.log_im, hre, hargz, ← httR, hcre, hcim]
    have hcR : |(c : ℝ)| ≤ 1 := by exact_mod_cast hc
    have hdR : |(d : ℝ)| ≤ 1 := by exact_mod_cast hd
    have hmR : |(m : ℝ)| ≤ 100 := by
      have : ((|m| : ℤ) : ℚ) ≤ 100 := by exact_mod_cast hmm
      rw [← Int.cast_abs]; exact_mod_cast this
    have hkR : |(k : ℝ)| ≤ 4 := by exact_mod_cast hkabs
    have he : 0 ≤ barrierLogHError := by unfold barrierLogHError; positivity
    have hj : 0 ≤ barrierAtanJ0 := by unfold barrierAtanJ0; positivity
    have hallow := barrier_weighted_log_error_allowance
    set LF := logSerF Q
    set TF := atanSerF T
    -- the computed real value
    have hval : ((c * (((m * L2F + LF : ℤ) : ℚ) / (2 * S80)) -
        d * (((k * AF + TF : ℤ) : ℚ) / S80) : ℚ) : ℝ) =
        (c : ℝ) * (((m : ℝ) * (L2F : ℝ) + (LF : ℝ)) / (2 * (S80 : ℝ))) -
          (d : ℝ) * (((k : ℝ) * (AF : ℝ) + (TF : ℝ)) / (S80 : ℝ)) := by
      push_cast; ring
    rw [hval]
    -- log part
    set L1 := Real.log ((2 : ℝ) ^ m * (y : ℝ)) / 2 -
      ((m : ℝ) * (L2F : ℝ) + (LF : ℝ)) / (2 * (S80 : ℝ))
    have hL1 : |L1| ≤ ((|(m : ℝ)| + 1) * barrierLogHError + 123 / (S80 : ℝ)) / 2 := by
      have hsplit : L1 = ((Real.log ((2 : ℝ) ^ m * (y : ℝ)) - Real.log ((2 : ℝ) ^ m * y2)) +
          (Real.log ((2 : ℝ) ^ m * y2) - barrierScaledLogApprox m y2) +
          (m : ℝ) * (barrierLogH 2 - (L2F : ℝ) / (S80 : ℝ)) +
          (barrierLogH y2 - (LF : ℝ) / (S80 : ℝ))) / 2 := by
        simp only [L1, barrierScaledLogApprox]; field_simp; ring
      have hA : |(m : ℝ) * (barrierLogH 2 - (L2F : ℝ) / (S80 : ℝ))| ≤ 100 / (S80 : ℝ) := by
        rw [abs_mul]
        have h0 : |barrierLogH 2 - (L2F : ℝ) / (S80 : ℝ)| ≤ 1 / (S80 : ℝ) :=
          abs_sub_fl_le (by norm_num) hL2.1 hL2.2.le
        calc |(m : ℝ)| * |barrierLogH 2 - (L2F : ℝ) / (S80 : ℝ)| ≤ 100 * (1 / (S80 : ℝ)) :=
            mul_le_mul hmR h0 (abs_nonneg _) (by norm_num)
          _ = 100 / (S80 : ℝ) := by ring
      have hB : |barrierLogH y2 - (LF : ℝ) / (S80 : ℝ)| ≤ 18 / (S80 : ℝ) :=
        abs_sub_fl_le (by norm_num) hLF.1 hLF.2
      have hC : |Real.log ((2 : ℝ) ^ m * (y : ℝ)) - Real.log ((2 : ℝ) ^ m * y2)| ≤ 5 / (S80 : ℝ) := by
        have : (y : ℝ) - y2 ≤ 9 / 2 * (1 / (S80 : ℝ)) := by nlinarith [hydiff, hq'gt]
        have h3 : 9 / 2 * (1 / (S80 : ℝ)) ≤ 5 / (S80 : ℝ) := by
          have : 0 < 1 / (S80 : ℝ) := by positivity
          rw [show (5 : ℝ) / (S80 : ℝ) = 5 * (1 / (S80 : ℝ)) by ring]; nlinarith
        linarith [hly]
      rw [hsplit, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have := abs_add_le (Real.log ((2 : ℝ) ^ m * (y : ℝ)) - Real.log ((2 : ℝ) ^ m * y2) +
          (Real.log ((2 : ℝ) ^ m * y2) - barrierScaledLogApprox m y2) +
          (m : ℝ) * (barrierLogH 2 - (L2F : ℝ) / (S80 : ℝ))) (barrierLogH y2 - (LF : ℝ) / (S80 : ℝ))
      have := abs_add_le (Real.log ((2 : ℝ) ^ m * (y : ℝ)) - Real.log ((2 : ℝ) ^ m * y2) +
          (Real.log ((2 : ℝ) ^ m * y2) - barrierScaledLogApprox m y2))
          ((m : ℝ) * (barrierLogH 2 - (L2F : ℝ) / (S80 : ℝ)))
      have := abs_add_le (Real.log ((2 : ℝ) ^ m * (y : ℝ)) - Real.log ((2 : ℝ) ^ m * y2))
          (Real.log ((2 : ℝ) ^ m * y2) - barrierScaledLogApprox m y2)
      have hS' : 0 < 1 / (S80 : ℝ) := by positivity
      have e1 : (123 : ℝ) / (S80 : ℝ) = 5 / (S80 : ℝ) + 100 / (S80 : ℝ) + 18 / (S80 : ℝ) := by ring
      rw [e1]
      linarith
    -- arg part
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
        have h0 : |(barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)) - (AF : ℝ) / (S80 : ℝ)| ≤ 1 / (S80 : ℝ) :=
          abs_sub_fl_le (by norm_num) hAF.1 hAF.2.le
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
    have hkey : (c : ℝ) * (Real.log ((2 : ℝ) ^ m * (y : ℝ)) / 2) -
        (d : ℝ) * ((k : ℝ) * (Real.pi / 4) + Real.arctan (tt : ℝ)) -
        ((c : ℝ) * (((m : ℝ) * (L2F : ℝ) + (LF : ℝ)) / (2 * (S80 : ℝ))) -
          (d : ℝ) * (((k : ℝ) * (AF : ℝ) + (TF : ℝ)) / (S80 : ℝ))) = (c : ℝ) * L1 - (d : ℝ) * A1 := by
      simp only [L1, A1]; ring
    rw [hkey]
    have hcL : |(c : ℝ) * L1| ≤ (101 * barrierLogHError + 123 / (S80 : ℝ)) / 2 := by
      rw [abs_mul]
      have h0 : |L1| ≤ (101 * barrierLogHError + 123 / (S80 : ℝ)) / 2 := by
        refine hL1.trans ?_
        apply div_le_div_of_nonneg_right _ (by norm_num)
        nlinarith
      calc |(c : ℝ)| * |L1| ≤ 1 * |L1| := mul_le_mul_of_nonneg_right hcR (abs_nonneg _)
        _ ≤ _ := by linarith
    have hdA : |(d : ℝ) * A1| ≤ 9 * barrierAtanJ0 + 29 / (S80 : ℝ) := by
      rw [abs_mul]
      calc |(d : ℝ)| * |A1| ≤ 1 * |A1| := mul_le_mul_of_nonneg_right hdR (abs_nonneg _)
        _ ≤ _ := by linarith
    have htot := abs_sub ((c : ℝ) * L1) ((d : ℝ) * A1)
    have hSv : (1 : ℝ) / (S80 : ℝ) = 1 / 1208925819614629174706176 := by unfold S80; norm_num
    have h123 : (123 : ℝ) / (S80 : ℝ) = 123 * (1 / 1208925819614629174706176) := by
      rw [← hSv]; ring
    have h29 : (29 : ℝ) / (S80 : ℝ) = 29 * (1 / 1208925819614629174706176) := by
      rw [← hSv]; ring
    rw [h123] at hcL; rw [h29] at hdA
    unfold errF
    push_cast
    linarith
  · simp at h

def cLogF (c d a b : ℚ) : Option ℚ :=
  let n := wPieces c d
  (cLog1F (c / n) (d / n) a b).map (fun q => n * q)

theorem cLogF_spec {c d a b q : ℚ} (h : cLogF c d a b = some q) :
    |(barrierComplex c d * Complex.log ⟨(a : ℝ), (b : ℝ)⟩).re - (q : ℝ)| ≤
      (wPieces c d : ℝ) * (errF : ℝ) := by
  unfold cLogF at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨q1, h1, rfl⟩ := h
  have hs := cLog1F_spec h1
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
