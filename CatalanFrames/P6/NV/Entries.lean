module

public import CatalanFrames.P6.Frame
public import CatalanFrames.P6.NV.Tel

/-!
# P6 NV: entries of the Loewner matrix modulo `ℓ = 6t+1` (WP11)

Nodes `a ≤ 2t` are *low* (`K = 2t+1` of them), nodes `2t+1 ≤ b ≤ 3t` are *middle*.  The singular
terms are `Δ_K` (`3K - 2 = ℓ`).  Everything is stated as `Good` (reduction of `ℓ`-integral
rationals), so that it feeds `reduce_det_eq_zero`:

* `low_good`    : `M_{ab} ≡ (Gw_{ab} - δ_{ab} c)/36` for `a, b ≤ 2t`,
* `lowmid_good` : `ℓ M_{ab} ≡ 1/(6 (b - a))` for `a ≤ 2t < b ≤ 3t`,
* `midmid_diag_good`, `midmid_off_good` : `ℓ² M_{ab} ≡ -δ_{ab}/2` for `2t < a, b ≤ 3t`.
-/

@[expose] public section

open Finset CatalanCore

namespace CatalanFrames.P6.NV

/-- `1/x` in `ZMod ℓ` for a natural `x`. -/
noncomputable def finv (ℓ x : ℕ) : ZMod ℓ := (x : ZMod ℓ)⁻¹

/-- `1/x²` in `ZMod ℓ` for a natural `x`. -/
noncomputable def finv2 (ℓ x : ℕ) : ZMod ℓ := ((x : ZMod ℓ) ^ 2)⁻¹

/-- the two-weight Gram entry `∑_y w_y / ((a+y)(b+y))`. -/
noncomputable def Gw (ℓ t a b : ℕ) : ZMod ℓ :=
  ∑ j ∈ range (3 * t), finv ℓ (a + 1 + j) * finv ℓ (b + 1 + j) -
    2 * ∑ j ∈ range t, finv ℓ (a + 3 * t + 1 + j) * finv ℓ (b + 3 * t + 1 + j)

/-- the diagonal constant `c = ∑_y w_y / y²`. -/
noncomputable def cc (ℓ t : ℕ) : ZMod ℓ := Pot (finv2 ℓ) t 0

lemma Gw_comm (ℓ t a b : ℕ) : Gw ℓ t a b = Gw ℓ t b a := by
  simp only [Gw, mul_comm]

section FrameEntries
open CatalanFrames.P6

lemma norm_eq : p6Frame.norm = 36 := rfl

lemma Mn_diag (a : ℕ) :
    p6Frame.Mn a a = -(1 / 36) * ∑ k ∈ Icc 1 a, p6Frame.Dsq k := by
  simp only [Frame.Mn, eq_self_iff_true, if_true, norm_eq]

lemma Mn_off {a b : ℕ} (hab : a < b) :
    p6Frame.Mn a b = (1 / 36) * (1 / ((b : ℚ) - a)) * ∑ k ∈ Ioc a b, p6Frame.Delta k := by
  simp only [Frame.Mn, if_neg hab.ne, max_eq_right hab.le, min_eq_left hab.le, norm_eq]

lemma Mn_comm (a b : ℕ) : p6Frame.Mn a b = p6Frame.Mn b a := by
  unfold Frame.Mn
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm b a, min_comm b a]

end FrameEntries

section Mod
variable {ℓ t : ℕ} [Fact ℓ.Prime]

lemma not_dvd_of_lt {n : ℕ} (h0 : 0 < n) (h2 : n < 2 * ℓ) (hne : n ≠ ℓ) : ¬ ℓ ∣ n := by
  rintro ⟨c, hc⟩
  have hc2 : c = 0 ∨ c = 1 ∨ 2 ≤ c := by omega
  rcases hc2 with rfl | rfl | h
  · omega
  · omega
  · have := Nat.mul_le_mul_left ℓ h
    omega

lemma zne {n : ℕ} (h0 : 0 < n) (h2 : n < 2 * ℓ) (hne : n ≠ ℓ) : (n : ZMod ℓ) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact not_dvd_of_lt h0 h2 hne

variable (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t)
include hl ht

lemma two_ne : (2 : ZMod ℓ) ≠ 0 := by
  simpa using zne (ℓ := ℓ) (n := 2) (by norm_num) (by omega) (by omega)
lemma three_ne : (3 : ZMod ℓ) ≠ 0 := by
  simpa using zne (ℓ := ℓ) (n := 3) (by norm_num) (by omega) (by omega)
lemma six_ne : (6 : ZMod ℓ) ≠ 0 := by
  simpa using zne (ℓ := ℓ) (n := 6) (by norm_num) (by omega) (by omega)
lemma n36_ne : (36 : ZMod ℓ) ≠ 0 := by
  have := mul_ne_zero (six_ne hl ht) (six_ne hl ht)
  rwa [show (6 : ZMod ℓ) * 6 = 36 by norm_num] at this

lemma six_t : 6 * (t : ZMod ℓ) + 1 = 0 := by
  have : ((6 * t + 1 : ℕ) : ZMod ℓ) = 0 := by rw [← hl]; simp
  simpa using this

lemma ell_q : (ℓ : ℚ) = 6 * t + 1 := by exact_mod_cast hl

omit hl ht in
lemma alg1 {F : Type*} [Field F] (x T : F) (h6 : 6 * T + 1 = 0) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h32 : 3 * x - 2 ≠ 0) (h21 : 2 * x - 1 ≠ 0) (hx : x ≠ 0) :
    1 / x + 6 / (3 * x - 2) - 6 / (2 * x - 1) =
      1 / x - 3 * (1 / (x + 3 * T)) + 2 * (1 / (x + 4 * T)) := by
  have e1 : 2 * x - 1 = 2 * (x + 3 * T) := by linear_combination (-1) * h6
  have e2 : 3 * x - 2 = 3 * (x + 4 * T) := by linear_combination (-2) * h6
  rw [e1] at h21 ⊢
  rw [e2] at h32 ⊢
  have ha : x + 3 * T ≠ 0 := right_ne_zero_of_mul h21
  have hb : x + 4 * T ≠ 0 := right_ne_zero_of_mul h32
  field_simp
  ring

omit hl ht in
lemma alg2 {F : Type*} [Field F] (x T : F) (h6 : 6 * T + 1 = 0) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h32 : 3 * x - 2 ≠ 0) (h21 : 2 * x - 1 ≠ 0) (hx : x ≠ 0) :
    1 / x ^ 2 + 18 / (3 * x - 2) ^ 2 - 12 / (2 * x - 1) ^ 2 =
      1 / x ^ 2 - 3 * (1 / (x + 3 * T) ^ 2) + 2 * (1 / (x + 4 * T) ^ 2) := by
  have e1 : 2 * x - 1 = 2 * (x + 3 * T) := by linear_combination (-1) * h6
  have e2 : 3 * x - 2 = 3 * (x + 4 * T) := by linear_combination (-2) * h6
  rw [e1] at h21 ⊢
  rw [e2] at h32 ⊢
  have ha : x + 3 * T ≠ 0 := right_ne_zero_of_mul h21
  have hb : x + 4 * T ≠ 0 := right_ne_zero_of_mul h32
  field_simp
  ring

/-- nonvanishing of `k`, `3k-2`, `2k-1` for `1 ≤ k ≤ 3t`, `k ≠ 2t+1`. -/
lemma k_ne {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 3 * t) (hkK : k ≠ 2 * t + 1) :
    (k : ZMod ℓ) ≠ 0 ∧ 3 * (k : ZMod ℓ) - 2 ≠ 0 ∧ 2 * (k : ZMod ℓ) - 1 ≠ 0 := by
  refine ⟨zne (by omega) (by omega) (by omega), ?_, ?_⟩
  · have := zne (ℓ := ℓ) (n := 3 * k - 2) (by omega) (by omega) (by omega)
    have e : ((3 * k - 2 : ℕ) : ZMod ℓ) = 3 * (k : ZMod ℓ) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rwa [e] at this
  · have := zne (ℓ := ℓ) (n := 2 * k - 1) (by omega) (by omega) (by omega)
    have e : ((2 * k - 1 : ℕ) : ZMod ℓ) = 2 * (k : ZMod ℓ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rwa [e] at this

lemma delta_good {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 3 * t) (hkK : k ≠ 2 * t + 1) :
    Good ℓ (CatalanFrames.P6.p6Frame.Delta k) (Tri (finv ℓ) t k) := by
  obtain ⟨hx, h32, h21⟩ := k_ne hl ht hk1 hk2 hkK
  rw [CatalanFrames.P6.Delta_eq k hk1]
  have g32 : Good ℓ (3 * (k : ℚ) - 2) (3 * (k : ZMod ℓ) - 2) :=
    (Good.mul (Good.ofNat 3) (Good.natCast k)).sub (Good.ofNat 2)
  have g21 : Good ℓ (2 * (k : ℚ) - 1) (2 * (k : ZMod ℓ) - 1) :=
    (Good.mul (Good.ofNat 2) (Good.natCast k)).sub Good.one
  have g := ((Good.one.div (Good.natCast k) hx).add
    ((Good.ofNat 6).div g32 h32)).sub ((Good.ofNat 6).div g21 h21)
  refine g.congr ?_
  have := alg1 (k : ZMod ℓ) (t : ZMod ℓ) (six_t hl ht) (two_ne hl ht) (three_ne hl ht) h32 h21 hx
  rw [this]
  simp only [Tri, finv, one_div, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

lemma dsq_good {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 3 * t) (hkK : k ≠ 2 * t + 1) :
    Good ℓ (CatalanFrames.P6.p6Frame.Dsq k) (Tri (finv2 ℓ) t k) := by
  obtain ⟨hx, h32, h21⟩ := k_ne hl ht hk1 hk2 hkK
  rw [CatalanFrames.P6.Dsq_eq k hk1]
  have g32 : Good ℓ (3 * (k : ℚ) - 2) (3 * (k : ZMod ℓ) - 2) :=
    (Good.mul (Good.ofNat 3) (Good.natCast k)).sub (Good.ofNat 2)
  have g21 : Good ℓ (2 * (k : ℚ) - 1) (2 * (k : ZMod ℓ) - 1) :=
    (Good.mul (Good.ofNat 2) (Good.natCast k)).sub Good.one
  have g := ((Good.one.div ((Good.natCast k).pow' 2) (pow_ne_zero 2 hx)).add
    ((Good.ofNat 18).div (g32.pow' 2) (pow_ne_zero 2 h32))).sub
      ((Good.ofNat 12).div (g21.pow' 2) (pow_ne_zero 2 h21))
  refine g.congr ?_
  have := alg2 (k : ZMod ℓ) (t : ZMod ℓ) (six_t hl ht) (two_ne hl ht) (three_ne hl ht) h32 h21 hx
  rw [this]
  simp only [Tri, finv2, one_div, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

omit hl ht in
lemma tel_term {u v : ℕ} (hu : (u : ZMod ℓ) ≠ 0) (hv : (v : ZMod ℓ) ≠ 0) :
    ((v : ZMod ℓ) - u) * (finv ℓ u * finv ℓ v) = finv ℓ u - finv ℓ v := by
  simp only [finv]
  field_simp

lemma Gw_off {a b : ℕ} (ha : a ≤ 2 * t) (hb : b ≤ 2 * t) :
    ((b : ZMod ℓ) - a) * Gw ℓ t a b = Pot (finv ℓ) t a - Pot (finv ℓ) t b := by
  have e1 : ((b : ZMod ℓ) - a) * ∑ j ∈ range (3 * t), finv ℓ (a + 1 + j) * finv ℓ (b + 1 + j) =
      ∑ j ∈ range (3 * t), (finv ℓ (a + 1 + j) - finv ℓ (b + 1 + j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.1 hj
    have := tel_term (ℓ := ℓ) (u := a + 1 + j) (v := b + 1 + j)
      (zne (by omega) (by omega) (by omega)) (zne (by omega) (by omega) (by omega))
    rw [← this]; push_cast; ring
  have e2 : ((b : ZMod ℓ) - a) *
      ∑ j ∈ range t, finv ℓ (a + 3 * t + 1 + j) * finv ℓ (b + 3 * t + 1 + j) =
      ∑ j ∈ range t, (finv ℓ (a + 3 * t + 1 + j) - finv ℓ (b + 3 * t + 1 + j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.1 hj
    have := tel_term (ℓ := ℓ) (u := a + 3 * t + 1 + j) (v := b + 3 * t + 1 + j)
      (zne (by omega) (by omega) (by omega)) (zne (by omega) (by omega) (by omega))
    rw [← this]; push_cast; ring
  unfold Gw Pot
  rw [mul_sub, e1, mul_left_comm, e2, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

omit hl ht in
lemma Gw_diag (a : ℕ) : Gw ℓ t a a = Pot (finv2 ℓ) t a := by
  have h : ∀ x : ℕ, finv ℓ x * finv ℓ x = finv2 ℓ x := fun x => by
    simp only [finv, finv2]; rw [sq]; field_simp
  unfold Gw Pot
  simp only [h]

lemma low_good {a b : ℕ} (ha : a ≤ 2 * t) (hb : b ≤ 2 * t) :
    Good ℓ (CatalanFrames.P6.p6Frame.Mn a b)
      ((Gw ℓ t a b - if a = b then cc ℓ t else 0) / 36) := by
  have g36 : Good ℓ (1 / 36 : ℚ) (1 / 36) := Good.one.div (Good.ofNat 36) (n36_ne hl ht)
  by_cases hab : a = b
  · subst hab
    rw [Mn_diag, if_pos rfl]
    have gs := Good.sum (ℓ := ℓ) (Icc 1 a) (fun k => CatalanFrames.P6.p6Frame.Dsq k)
      (fun k => Tri (finv2 ℓ) t k) fun k hk => by
        have := Finset.mem_Icc.1 hk
        exact dsq_good hl ht this.1 (by omega) (by omega)
    have hI : Icc 1 a = Ioc 0 a := by ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hI, sum_Ioc_Tri _ _ _ _ (Nat.zero_le a)] at gs
    refine (g36.neg.mul gs).congr ?_
    rw [Gw_diag, cc]
    have := n36_ne hl ht
    field_simp
    ring
  · rcases lt_or_gt_of_ne hab with h | h
    · rw [Mn_off h, if_neg hab]
      have gs := Good.sum (ℓ := ℓ) (Ioc a b) (fun k => CatalanFrames.P6.p6Frame.Delta k)
        (fun k => Tri (finv ℓ) t k) fun k hk => by
          have := Finset.mem_Ioc.1 hk
          exact delta_good hl ht (by omega) (by omega) (by omega)
      rw [sum_Ioc_Tri _ _ _ _ h.le] at gs
      have hne : (b : ZMod ℓ) - a ≠ 0 :=
        sub_ne_zero.2 (natCast_ne_natCast (p := ℓ) (by omega) (by omega) h.ne')
      have gd : Good ℓ (1 / ((b : ℚ) - a)) (1 / ((b : ZMod ℓ) - a)) :=
        Good.one.div ((Good.natCast b).sub (Good.natCast a)) hne
      refine ((g36.mul gd).mul gs).congr ?_
      have key := Gw_off hl ht ha hb (a := a) (b := b)
      have h36 := n36_ne hl ht
      rw [sub_zero, ← key]
      field_simp
    · rw [Mn_comm a b, Mn_off h, if_neg hab]
      have gs := Good.sum (ℓ := ℓ) (Ioc b a) (fun k => CatalanFrames.P6.p6Frame.Delta k)
        (fun k => Tri (finv ℓ) t k) fun k hk => by
          have := Finset.mem_Ioc.1 hk
          exact delta_good hl ht (by omega) (by omega) (by omega)
      rw [sum_Ioc_Tri _ _ _ _ h.le] at gs
      have hne : (a : ZMod ℓ) - b ≠ 0 :=
        sub_ne_zero.2 (natCast_ne_natCast (p := ℓ) (by omega) (by omega) h.ne')
      have gd : Good ℓ (1 / ((a : ℚ) - b)) (1 / ((a : ZMod ℓ) - b)) :=
        Good.one.div ((Good.natCast a).sub (Good.natCast b)) hne
      refine ((g36.mul gd).mul gs).congr ?_
      have key := Gw_off hl ht hb ha (a := b) (b := a)
      have h36 := n36_ne hl ht
      rw [sub_zero, Gw_comm, ← key]
      field_simp

end Mod
end CatalanFrames.P6.NV
