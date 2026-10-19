module

public import CatalanCore.Basic.ZModGood
public import CatalanCore.Frame.Spec
public import CatalanCore.Arith.Hybrid.DefBHarm

@[expose] public section

/-!
# `ℤ_(p)`-reductions of the entries of a λ-like frame

For a frame with `Δ_t = 1/t - 4/(4t-1)`, `D_t = 1/t² - 16/(4t-1)²`, `norm = 16` (`LamData`), and a
prime `p ≥ 5`, the entries `Mn A B` are `p`-adic numbers with a controlled pole at the *singular*
indices (`p ∣ t(4t-1)`).  Here: `Good p x y` (`x ∈ ℤ_(p)` reducing to `y ∈ 𝔽_p`) statements for
* `Δ_t`, `D_t` at regular `t`, and `p Δ_t`, `p² D_t` at `t = k` where `4k = j p + 1`, and `p Δ_p`;
* sums of these over finite sets (`sum_good_p`, `sum_good_0`).
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

/-- The λ-like formulas of the frame. -/
structure LamData (Fr : Frame) (o : ℕ) : Prop where
  norm_eq : Fr.norm = 16
  o_pos : 0 < o
  o_le : o ≤ 3
  delta_eq : ∀ t : ℕ, 1 ≤ t → Fr.Delta t = 1 / (t : ℚ) - 4 / (4 * (t : ℚ) - (o : ℚ))
  dsq_eq : ∀ t : ℕ, 1 ≤ t → Fr.Dsq t = 1 / (t : ℚ) ^ 2 - 16 / (4 * (t : ℚ) - (o : ℚ)) ^ 2

section Prime

variable (p : ℕ) [Fact p.Prime]

lemma four_ne_zmod (hp5 : 5 ≤ p) : (4 : ZMod p) ≠ 0 := by
  have : ((4 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
  simpa using this

lemma LamData.delta_eq_one {Fr : Frame} (hL : LamData Fr 1) (t : ℕ) (ht : 1 ≤ t) :
    Fr.Delta t = 1 / (t : ℚ) - 4 / (4 * (t : ℚ) - 1) := by simpa using hL.delta_eq t ht

lemma LamData.dsq_eq_one {Fr : Frame} (hL : LamData Fr 1) (t : ℕ) (ht : 1 ≤ t) :
    Fr.Dsq t = 1 / (t : ℚ) ^ 2 - 16 / (4 * (t : ℚ) - 1) ^ 2 := by simpa using hL.dsq_eq t ht

lemma o_ne_zmod {o : ℕ} (h0 : 0 < o) (h3 : o ≤ 3) (hp5 : 5 ≤ p) : ((o : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd h0 hd) (by omega)

/-- Regular index: `p ∤ t(t-k)`, where `k` is the singular index (`4k ≡ o`). -/
def Reg (k t : ℕ) : Prop := ((t : ℕ) : ZMod p) ≠ 0 ∧ (((t : ℕ) : ZMod p) - (k : ZMod p)) ≠ 0

variable {p}

lemma four_sub_eq {o k : ℕ} (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p)) (t : ZMod p) :
    4 * t - (o : ZMod p) = 4 * (t - (k : ZMod p)) := by linear_combination hk4

lemma four_sub_ne {o k : ℕ} (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p))
    {t : ℕ} (hr : Reg p k t) : (4 * ((t : ℕ) : ZMod p) - (o : ZMod p)) ≠ 0 := by
  rw [four_sub_eq hk4]; exact mul_ne_zero (four_ne_zmod p hp5) hr.2

lemma conv4 {o k : ℕ} (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p))
    (t : ZMod p) : 4 * (4 * t - (o : ZMod p))⁻¹ = (t - (k : ZMod p))⁻¹ := by
  have h4 := four_ne_zmod p hp5
  rw [four_sub_eq hk4, mul_inv]
  field_simp

lemma conv4sq {o k : ℕ} (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p))
    (t : ZMod p) : 16 * ((4 * t - (o : ZMod p))⁻¹) ^ 2 = ((t - (k : ZMod p))⁻¹) ^ 2 := by
  have h4 := four_ne_zmod p hp5
  rw [four_sub_eq hk4, mul_inv]
  field_simp
  ring

/-- `Δ_t` at a regular index. -/
lemma good_Delta_reg {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) {k : ℕ}
    (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p)) {t : ℕ} (ht1 : 1 ≤ t)
    (hr : Reg p k t) :
    Good p (Fr.Delta t) (((t : ℕ) : ZMod p)⁻¹ - (((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹) := by
  rw [hL.delta_eq t ht1]
  have := (Good.one (ℓ := p)).div (Good.natCast (ℓ := p) t) hr.1 |>.sub
    ((Good.ofNat (ℓ := p) 4).div (((Good.ofNat (ℓ := p) 4).mul (Good.natCast t)).sub
      (Good.natCast (ℓ := p) o)) (four_sub_ne hp5 hk4 hr))
  refine this.congr ?_
  rw [← conv4 hp5 hk4]
  simp [div_eq_mul_inv]

/-- `D_t` at a regular index. -/
lemma good_Dsq_reg {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) {k : ℕ}
    (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p)) {t : ℕ} (ht1 : 1 ≤ t)
    (hr : Reg p k t) :
    Good p (Fr.Dsq t) ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - ((((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹) ^ 2) := by
  rw [hL.dsq_eq t ht1]
  have := (Good.one (ℓ := p)).div ((Good.natCast (ℓ := p) t).pow' 2) (pow_ne_zero 2 hr.1) |>.sub
    ((Good.ofNat (ℓ := p) 16).div ((((Good.ofNat (ℓ := p) 4).mul (Good.natCast t)).sub
      (Good.natCast (ℓ := p) o)).pow' 2) (pow_ne_zero 2 (four_sub_ne hp5 hk4 hr)))
  refine this.congr ?_
  rw [← conv4sq hp5 hk4]
  simp [div_eq_mul_inv]

/-- Sum of `Δ_t` over a set of regular indices. -/
lemma sum_good_0 {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) {k : ℕ}
    (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p)) (s : Finset ℕ)
    (h1 : ∀ t ∈ s, 1 ≤ t) (hr : ∀ t ∈ s, Reg p k t) :
    Good p (∑ t ∈ s, Fr.Delta t)
      (∑ t ∈ s, (((t : ℕ) : ZMod p)⁻¹ - (((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹)) :=
  Good.sum s _ _ fun t ht => good_Delta_reg hL hp5 hk4 (h1 t ht) (hr t ht)

lemma dsum_good_0 {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) {k : ℕ}
    (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p)) (s : Finset ℕ)
    (h1 : ∀ t ∈ s, 1 ≤ t) (hr : ∀ t ∈ s, Reg p k t) :
    Good p (∑ t ∈ s, Fr.Dsq t)
      (∑ t ∈ s, ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - ((((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹) ^ 2)) :=
  Good.sum s _ _ fun t ht => good_Dsq_reg hL hp5 hk4 (h1 t ht) (hr t ht)

/-- `p ∑_{t ∈ s} Δ_t` when `s` contains a set `S0` of singular indices (residues `res`) and
otherwise regular ones. -/
lemma sum_good_p {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) {k : ℕ}
    (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p)) (s S0 : Finset ℕ) (hS0 : S0 ⊆ s)
    (h1 : ∀ t ∈ s \ S0, 1 ≤ t) (res : ℕ → ZMod p)
    (hsing : ∀ t ∈ S0, Good p ((p : ℚ) * Fr.Delta t) (res t)) (hr : ∀ t ∈ s \ S0, Reg p k t) :
    Good p ((p : ℚ) * ∑ t ∈ s, Fr.Delta t) (∑ t ∈ S0, res t) := by
  have hsplit : ∑ t ∈ s, Fr.Delta t = ∑ t ∈ S0, Fr.Delta t + ∑ t ∈ s \ S0, Fr.Delta t := by
    rw [← Finset.sum_sdiff hS0]; ring
  rw [hsplit, mul_add]
  have g1 : Good p (∑ t ∈ S0, (p : ℚ) * Fr.Delta t) (∑ t ∈ S0, res t) := Good.sum S0 _ _ hsing
  have g2 : Good p ((p : ℚ) * ∑ t ∈ s \ S0, Fr.Delta t) 0 :=
    (sum_good_0 hL hp5 hk4 (s \ S0) h1 hr).ell_mul
  have := g1.add g2
  rw [← Finset.mul_sum] at this
  simpa using this

lemma dsum_good_p2 {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) {k : ℕ}
    (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p)) (s S0 : Finset ℕ) (hS0 : S0 ⊆ s)
    (h1 : ∀ t ∈ s \ S0, 1 ≤ t) (res : ℕ → ZMod p)
    (hsing : ∀ t ∈ S0, Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (res t)) (hr : ∀ t ∈ s \ S0, Reg p k t) :
    Good p ((p : ℚ) ^ 2 * ∑ t ∈ s, Fr.Dsq t) (∑ t ∈ S0, res t) := by
  have hsplit : ∑ t ∈ s, Fr.Dsq t = ∑ t ∈ S0, Fr.Dsq t + ∑ t ∈ s \ S0, Fr.Dsq t := by
    rw [← Finset.sum_sdiff hS0]; ring
  rw [hsplit, mul_add]
  have g1 : Good p (∑ t ∈ S0, (p : ℚ) ^ 2 * Fr.Dsq t) (∑ t ∈ S0, res t) := Good.sum S0 _ _ hsing
  have g2 : Good p ((p : ℚ) ^ 2 * ∑ t ∈ s \ S0, Fr.Dsq t) 0 := by
    have := ((dsum_good_0 hL hp5 hk4 (s \ S0) h1 hr).ell_mul).ell_mul
    refine this.congr' ?_
    ring
  have := g1.add g2
  rw [← Finset.mul_sum] at this
  simpa using this

/-! ### Singular indices -/

section Singular

variable {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (_hp5 : 5 ≤ p) {j k : ℕ} (hk : 4 * k = j * p + o)
  (hj0 : 0 < j) (hjp : j < p) (hk0 : 0 < k) (hkp : k < p)

include hL hk hj0 hjp hk0 hkp

lemma good_Delta_k : Good p ((p : ℚ) * Fr.Delta k) (-(4 * ((j : ℕ) : ZMod p)⁻¹)) := by
  rw [hL.delta_eq k hk0]
  have hjz : ((j : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
  have hkz : ((k : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hk0 hd) (by omega)
  have hkQ : 4 * (k : ℚ) - (o : ℚ) = (j : ℚ) * p := by
    have : (4 * k : ℚ) = j * p + o := by exact_mod_cast hk
    linarith
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
  have hk0Q : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  have g1 : Good p ((p : ℚ) * (1 / (k : ℚ))) 0 :=
    ((Good.one (ℓ := p)).div (Good.natCast (ℓ := p) k) hkz).ell_mul
  have g2 : Good p (4 / (j : ℚ)) (4 * ((j : ℕ) : ZMod p)⁻¹) :=
    ((Good.ofNat (ℓ := p) 4).div (Good.natCast (ℓ := p) j) hjz).congr (by simp [div_eq_mul_inv])
  have := g1.sub g2
  refine this.congr' ?_ |>.congr (by ring)
  rw [hkQ]
  field_simp

lemma good_Dsq_k : Good p ((p : ℚ) ^ 2 * Fr.Dsq k) (-(16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2)) := by
  rw [hL.dsq_eq k hk0]
  have hjz : ((j : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
  have hkz : ((k : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hk0 hd) (by omega)
  have hkQ : 4 * (k : ℚ) - (o : ℚ) = (j : ℚ) * p := by
    have : (4 * k : ℚ) = j * p + o := by exact_mod_cast hk
    linarith
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
  have hk0Q : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  have g1 : Good p ((p : ℚ) ^ 2 * (1 / (k : ℚ) ^ 2)) 0 := by
    have := ((Good.one (ℓ := p)).div ((Good.natCast (ℓ := p) k).pow' 2) (pow_ne_zero 2 hkz)).ell_mul.ell_mul
    refine this.congr' ?_
    ring
  have g2 : Good p (16 / (j : ℚ) ^ 2) (16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2) :=
    ((Good.ofNat (ℓ := p) 16).div ((Good.natCast (ℓ := p) j).pow' 2) (pow_ne_zero 2 hjz)).congr
      (by simp [div_eq_mul_inv])
  have := g1.sub g2
  refine this.congr' ?_ |>.congr (by ring)
  rw [hkQ]
  field_simp

end Singular

lemma good_Delta_p {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) :
    Good p ((p : ℚ) * Fr.Delta p) 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [hL.delta_eq p hp1]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h4 : (4 * (p : ℚ) - (o : ℚ)) ≠ 0 := by
    have : (5 : ℚ) ≤ p := by exact_mod_cast hp5
    have : (o : ℚ) ≤ 3 := by exact_mod_cast hL.o_le
    linarith
  have hl0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hz : (4 * ((p : ℕ) : ZMod p) - (o : ZMod p)) ≠ 0 := by
    rw [hl0]; simpa using o_ne_zmod p hL.o_pos hL.o_le hp5
  have g2 : Good p ((p : ℚ) * (4 / (4 * (p : ℚ) - (o : ℚ)))) 0 :=
    ((Good.ofNat (ℓ := p) 4).div (((Good.ofNat (ℓ := p) 4).mul (Good.natCast (ℓ := p) p)).sub
      (Good.natCast (ℓ := p) o)) hz).ell_mul
  have := (Good.one (ℓ := p)).sub g2
  refine this.congr' ?_ |>.congr (by simp)
  field_simp

lemma good_Dsq_p {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) :
    Good p ((p : ℚ) ^ 2 * Fr.Dsq p) 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [hL.dsq_eq p hp1]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h4 : (4 * (p : ℚ) - (o : ℚ)) ≠ 0 := by
    have : (5 : ℚ) ≤ p := by exact_mod_cast hp5
    have : (o : ℚ) ≤ 3 := by exact_mod_cast hL.o_le
    linarith
  have hl0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hz : (4 * ((p : ℕ) : ZMod p) - (o : ZMod p)) ≠ 0 := by
    rw [hl0]; simpa using o_ne_zmod p hL.o_pos hL.o_le hp5
  have g2 : Good p ((p : ℚ) * ((p : ℚ) * (16 / (4 * (p : ℚ) - (o : ℚ)) ^ 2))) 0 :=
    ((((Good.ofNat (ℓ := p) 16).div ((((Good.ofNat (ℓ := p) 4).mul (Good.natCast (ℓ := p) p)).sub
      (Good.natCast (ℓ := p) o)).pow' 2) (pow_ne_zero 2 hz)).ell_mul).ell_mul)
  have := (Good.one (ℓ := p)).sub g2
  refine this.congr' ?_ |>.congr (by simp)
  field_simp

end Prime

/-! ### The entries `Mn` -/

lemma Mn_lt {Fr : Frame} {o : ℕ} (hL : LamData Fr o) {A B : ℕ} (h : A < B) :
    Fr.Mn A B = 1 / (16 * ((B : ℚ) - A)) * ∑ t ∈ Ioc A B, Fr.Delta t := by
  unfold Frame.Mn
  rw [if_neg h.ne, hL.norm_eq, min_eq_left h.le, max_eq_right h.le]
  have : ((B : ℚ) - A) ≠ 0 := by
    have : (A : ℚ) < B := by exact_mod_cast h
    linarith
  field_simp

lemma Mn_symm {Fr : Frame} (A B : ℕ) : Fr.Mn A B = Fr.Mn B A := by
  by_cases h : A = B
  · rw [h]
  · unfold Frame.Mn
    rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

lemma Mn_diag {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (A : ℕ) :
    Fr.Mn A A = -(1 / 16) * ∑ t ∈ Icc 1 A, Fr.Dsq t := by
  unfold Frame.Mn
  rw [if_pos rfl, hL.norm_eq]

section Entry

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) {k : ℕ}
  (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p))

include hL hp5 hk4

/-- Entry with all `t ∈ (A, B]` regular. -/
lemma Mn_good0 {A B : ℕ} (h : A < B) (h1 : ∀ t ∈ Ioc A B, 1 ≤ t)
    (hr : ∀ t ∈ Ioc A B, Reg p k t) (hd : ((B : ZMod p) - A) ≠ 0) :
    Good p (Fr.Mn A B) ((16 * ((B : ZMod p) - A))⁻¹ *
      ∑ t ∈ Ioc A B, (((t : ℕ) : ZMod p)⁻¹ - (((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹)) := by
  rw [Mn_lt hL h]
  have h16 : (16 : ZMod p) * ((B : ZMod p) - A) ≠ 0 := by
    have : (16 : ZMod p) ≠ 0 := by
      have : (16 : ZMod p) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
    exact mul_ne_zero this hd
  have g1 : Good p (1 / (16 * ((B : ℚ) - A))) ((16 * ((B : ZMod p) - A))⁻¹) :=
    ((Good.one (ℓ := p)).div ((Good.ofNat (ℓ := p) 16).mul
      ((Good.natCast (ℓ := p) B).sub (Good.natCast A))) h16).congr (by simp)
  exact g1.mul (sum_good_0 hL hp5 hk4 _ h1 hr)

/-- `p ·` entry, with a set `S0` of singular indices in `(A, B]`. -/
lemma Mn_goodP {A B : ℕ} (h : A < B) (S0 : Finset ℕ) (hS0 : S0 ⊆ Ioc A B)
    (h1 : ∀ t ∈ Ioc A B \ S0, 1 ≤ t) (res : ℕ → ZMod p)
    (hsing : ∀ t ∈ S0, Good p ((p : ℚ) * Fr.Delta t) (res t))
    (hr : ∀ t ∈ Ioc A B \ S0, Reg p k t) (hd : ((B : ZMod p) - A) ≠ 0) :
    Good p ((p : ℚ) * Fr.Mn A B) ((16 * ((B : ZMod p) - A))⁻¹ * ∑ t ∈ S0, res t) := by
  rw [Mn_lt hL h]
  have h16 : (16 : ZMod p) * ((B : ZMod p) - A) ≠ 0 := by
    have : (16 : ZMod p) ≠ 0 := by
      have : (16 : ZMod p) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
    exact mul_ne_zero this hd
  have g1 : Good p (1 / (16 * ((B : ℚ) - A))) ((16 * ((B : ZMod p) - A))⁻¹) :=
    ((Good.one (ℓ := p)).div ((Good.ofNat (ℓ := p) 16).mul
      ((Good.natCast (ℓ := p) B).sub (Good.natCast A))) h16).congr (by simp)
  have := g1.mul (sum_good_p hL hp5 hk4 (Ioc A B) S0 hS0 h1 res hsing hr)
  exact this.congr' (by ring)

/-- `p² ·` entry with `B - A = p`. -/
lemma Mn_goodPP {A B : ℕ} (h : A < B) (hBA : B - A = p) (S0 : Finset ℕ) (hS0 : S0 ⊆ Ioc A B)
    (h1 : ∀ t ∈ Ioc A B \ S0, 1 ≤ t) (res : ℕ → ZMod p)
    (hsing : ∀ t ∈ S0, Good p ((p : ℚ) * Fr.Delta t) (res t))
    (hr : ∀ t ∈ Ioc A B \ S0, Reg p k t) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) ((16 : ZMod p)⁻¹ * ∑ t ∈ S0, res t) := by
  rw [Mn_lt hL h]
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
  have hBQ : (B : ℚ) - A = p := by
    have : B = A + p := by omega
    rw [this]; push_cast; ring
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have g1 : Good p (1 / (16 : ℚ)) ((16 : ZMod p)⁻¹) :=
    ((Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 16) h16).congr (by simp)
  have := g1.mul (sum_good_p hL hp5 hk4 (Ioc A B) S0 hS0 h1 res hsing hr)
  refine this.congr' ?_
  rw [hBQ]
  field_simp

/-- Diagonal entry with all indices regular. -/
lemma Mn_diag_good0 {A : ℕ} (hr : ∀ t ∈ Icc 1 A, Reg p k t) :
    Good p (Fr.Mn A A) (-(1 / 16) * ∑ t ∈ Icc 1 A,
      ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - ((((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹) ^ 2)) := by
  rw [Mn_diag hL]
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
  have g1 : Good p (-(1 / 16 : ℚ)) (-(1 / 16)) :=
    Good.neg ((Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 16) h16)
  exact g1.mul (dsum_good_0 hL hp5 hk4 _ (fun t ht => (Finset.mem_Icc.1 ht).1) hr)

/-- `p² ·` diagonal entry with singular set `S0`. -/
lemma Mn_diag_goodP2 {A : ℕ} (S0 : Finset ℕ) (hS0 : S0 ⊆ Icc 1 A)
    (res : ℕ → ZMod p) (hsing : ∀ t ∈ S0, Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (res t))
    (hr : ∀ t ∈ Icc 1 A \ S0, Reg p k t) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A A) (-(1 / 16) * ∑ t ∈ S0, res t) := by
  rw [Mn_diag hL]
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
  have g1 : Good p (-(1 / 16 : ℚ)) (-(1 / 16)) :=
    Good.neg ((Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 16) h16)
  have := g1.mul (dsum_good_p2 hL hp5 hk4 (Icc 1 A) S0 hS0
    (fun t ht => (Finset.mem_Icc.1 (Finset.mem_sdiff.1 ht).1).1) res hsing hr)
  exact this.congr' (by ring)

end Entry

/-! ### Theorem B: the label-level table -/

section TableB

variable {p : ℕ} [Fact p.Prime] {Fr : Frame}

/-- The D4 potential of a label (`r < p`, singular block starts at `k`). -/
def uPot (p r k : ℕ) (A : ℕ) : ℕ :=
  if A < r then (if k ≤ A then 1 else 0) else 1 + (if p ≤ A then 1 else 0)

/-- The residue `p^{u A + u B} Mn A B mod p` for `A < B`. -/
noncomputable def TB (p j k : ℕ) [Fact p.Prime] (A B : ℕ) : ZMod p :=
  if B < k then (16 * ((B : ZMod p) - A))⁻¹ *
      ∑ t ∈ Ioc A B, (((t : ℕ) : ZMod p)⁻¹ - (((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹)
  else if A < k then
    (if B < p then (16 * ((B : ZMod p) - A))⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹))
     else if B - A = p then (16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1) else 0)
  else 0

/-- The diagonal residue (`A < r`). -/
noncomputable def TD (p j k : ℕ) [Fact p.Prime] (A : ℕ) : ZMod p :=
  if A < k then -(1 / 16 : ZMod p) * ∑ t ∈ Icc 1 A,
      ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - ((((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹) ^ 2)
  else (((j : ℕ) : ZMod p)⁻¹) ^ 2

lemma natCast_ne_zero_of_lt {x : ℕ} (h0 : 0 < x) (hx : x < p) : ((x : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd; exact absurd (Nat.le_of_dvd h0 hd) (by omega)

lemma sub_ne_zero_of_lt {A B : ℕ} (hAB : A < B) (hB : B - A < p) : ((B : ZMod p) - A) ≠ 0 := by
  rw [← Nat.cast_sub hAB.le]; exact natCast_ne_zero_of_lt (by omega) hB

lemma sub_ne_zero_of_ne {A B : ℕ} (hAB : A < B) (hB : B - A < 2 * p) (hne : B - A ≠ p) :
    ((B : ZMod p) - A) ≠ 0 := by
  rw [← Nat.cast_sub hAB.le, Ne, ZMod.natCast_eq_zero_iff]
  rintro ⟨c, hc⟩
  have hp0 := (Fact.out : p.Prime).pos
  rcases c with _ | _ | c
  · omega
  · omega
  · have : p * (c + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
    omega

/-- Regular indices below `2p`. -/
lemma reg_of {o j k : ℕ} (_hk : 4 * k = j * p + o) (_hp5 : 5 ≤ p) (hkp : k < p) {t : ℕ} (h1 : 1 ≤ t)
    (ht2 : t < 2 * p) (htk : t < k + p) (hnk : t ≠ k) (hnp : t ≠ p) : Reg p k t := by
  have hp0 := (Fact.out : p.Prime).pos
  refine ⟨?_, ?_⟩
  · rw [Ne, ZMod.natCast_eq_zero_iff]
    rintro ⟨c, hc⟩
    rcases c with _ | _ | c
    · omega
    · omega
    · have : p * (c + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
      omega
  · intro h0
    have : (t : ZMod p) = (k : ZMod p) := sub_eq_zero.1 h0
    rw [ZMod.natCast_eq_natCast_iff'] at this
    by_cases htp : t < p
    · rw [Nat.mod_eq_of_lt htp, Nat.mod_eq_of_lt hkp] at this; exact hnk this
    · have : t % p = t - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt hkp] at *
      omega

lemma good_pow_mul_zero {x : ℚ} {y : ZMod p} (h : Good p x y) {n : ℕ} (hn : 1 ≤ n) :
    Good p ((p : ℚ) ^ n * x) 0 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have h1 : Good p ((p : ℚ) ^ n') ((p : ZMod p) ^ n') := (Good.natCast (ℓ := p) p).pow' n'
  have := h1.mul (h.ell_mul)
  refine this.congr' (by ring) |>.congr (by simp)

/-- The hypotheses of the Theorem B setting. -/
structure BSetup (o p r m j k : ℕ) : Prop where
  p5 : 5 ≤ p
  hk : 4 * k = j * p + o
  hj0 : 0 < j
  hjp : j < p
  hk0 : 0 < k
  hkp : k < p
  hrp : r < p
  hkr : k ≤ r
  h2mk : 2 * m < k
  hmr : 2 * m ≤ r

variable {o r m j k : ℕ}

lemma BSetup.reg (S : BSetup o p r m j k) {t : ℕ} (h1 : 1 ≤ t) (hN : t < r + 2 * m)
    (hnk : t ≠ k) (hnp : t ≠ p) : Reg p k t :=
  reg_of S.hk S.p5 S.hkp h1 (by have := S.hrp; have := S.hmr; omega)
    (by have := S.hrp; have := S.h2mk; omega) hnk hnp

lemma hk4_of {p o j k : ℕ} (hk : 4 * k = j * p + o) :
    (4 : ZMod p) * (k : ZMod p) = (o : ZMod p) := by
  have : ((4 * k : ℕ) : ZMod p) = ((j * p + o : ℕ) : ZMod p) := by rw [hk]
  push_cast at this
  simpa [ZMod.natCast_self] using this

section TableThm

variable {o : ℕ} (hL : LamData Fr o) (S : BSetup o p r m j k)

include hL S

/-- **The label-level table of Theorem B.**  For labels `A < B < r + 2m`, the scaled entry
`p^{u A + u B} Mn A B` is `p`-integral with reduction `TB A B`. -/
theorem good_TB {A B : ℕ} (hAB : A < B) (hBN : B < r + 2 * m) :
    Good p ((p : ℚ) ^ (uPot p r k A + uPot p r k B) * Fr.Mn A B) (TB p j k A B) := by
  have hp5 := S.p5
  have hkr := S.hkr
  have hrp := S.hrp
  have hkp := S.hkp
  have h2mk := S.h2mk
  have hmr := S.hmr
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  by_cases hBk : B < k
  · -- both below the singular block
    have hw : uPot p r k A + uPot p r k B = 0 := by unfold uPot; split_ifs <;> omega
    rw [hw, pow_zero, one_mul]
    unfold TB; rw [if_pos hBk]
    exact Mn_good0 hL hp5 (hk4_of S.hk) hAB (fun t ht => by have := Finset.mem_Ioc.1 ht; omega)
      (fun t ht => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 ht
        exact S.reg (by omega) (by omega) (by omega) (by omega))
      (sub_ne_zero_of_lt hAB (by omega))
  by_cases hAk : A < k
  · by_cases hBp : B < p
    · -- weight 1, singular index k
      have hw : uPot p r k A + uPot p r k B = 1 := by unfold uPot; split_ifs <;> omega
      rw [hw, pow_one]
      unfold TB; rw [if_neg hBk, if_pos hAk, if_pos hBp]
      have := Mn_goodP hL hp5 (hk4_of S.hk) hAB {k} (by intro t ht; rw [Finset.mem_singleton.1 ht]; simp; omega)
        (fun t ht => by have := Finset.mem_Ioc.1 (Finset.mem_sdiff.1 ht).1; omega)
        (fun _ => -(4 * ((j : ℕ) : ZMod p)⁻¹))
        (fun t ht => by
          rw [Finset.mem_singleton.1 ht]
          exact good_Delta_k hL S.hk S.hj0 S.hjp S.hk0 S.hkp)
        (fun t ht => by
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ht
          have h1' := Finset.mem_Ioc.1 h1
          have h2' : t ≠ k := fun e => h2 (by simp [e])
          exact S.reg (by omega) (by omega) h2' (by omega))
        (sub_ne_zero_of_lt hAB (by omega))
      simpa using this
    · -- weight 2, singular indices k and p
      have hw : uPot p r k A + uPot p r k B = 2 := by unfold uPot; split_ifs <;> omega
      rw [hw]
      unfold TB; rw [if_neg hBk, if_pos hAk, if_neg hBp]
      have hkne : k ≠ p := by omega
      have hsub : ({k, p} : Finset ℕ) ⊆ Ioc A B := by
        intro t ht
        rcases Finset.mem_insert.1 ht with e | e
        · rw [e]; simp; omega
        · rw [Finset.mem_singleton.1 e]; simp; omega
      have h1 : ∀ t ∈ Ioc A B \ {k, p}, 1 ≤ t := fun t ht => by
        have := Finset.mem_Ioc.1 (Finset.mem_sdiff.1 ht).1; omega
      have hsing : ∀ t ∈ ({k, p} : Finset ℕ), Good p ((p : ℚ) * Fr.Delta t)
          ((fun t => if t = k then -(4 * ((j : ℕ) : ZMod p)⁻¹) else (1 : ZMod p)) t) := by
        intro t ht
        rcases Finset.mem_insert.1 ht with e | e
        · rw [e]; simp only [if_true]
          exact good_Delta_k hL S.hk S.hj0 S.hjp S.hk0 S.hkp
        · rw [Finset.mem_singleton.1 e]; simp only [if_neg hkne.symm]
          exact good_Delta_p hL hp5
      have hr : ∀ t ∈ Ioc A B \ {k, p}, Reg p k t := fun t ht => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ht
        have h1' := Finset.mem_Ioc.1 h1
        have h2k : t ≠ k := fun e => h2 (by simp [e])
        have h2p : t ≠ p := fun e => h2 (by simp [e])
        exact S.reg (by omega) (by omega) h2k h2p
      have hsum : ∑ t ∈ ({k, p} : Finset ℕ),
          (fun t => if t = k then -(4 * ((j : ℕ) : ZMod p)⁻¹) else (1 : ZMod p)) t =
          -(4 * ((j : ℕ) : ZMod p)⁻¹) + 1 := by
        rw [Finset.sum_pair hkne]; simp [hkne.symm]
      by_cases hBA : B - A = p
      · rw [if_pos hBA]
        have := Mn_goodPP hL hp5 (hk4_of S.hk) hAB hBA {k, p} hsub h1 _ hsing hr
        rw [hsum] at this
        exact this
      · rw [if_neg hBA]
        have := Mn_goodP hL hp5 (hk4_of S.hk) hAB {k, p} hsub h1 _ hsing hr
          (sub_ne_zero_of_ne hAB (by omega) hBA)
        exact ((good_pow_mul_zero this (n := 1) le_rfl).congr' (by ring))
  · -- A ≥ k: the entry vanishes mod p at its weight
    have hw2 : 2 ≤ uPot p r k A + uPot p r k B := by unfold uPot; split_ifs <;> omega
    unfold TB; rw [if_neg hBk, if_neg hAk]
    by_cases hBp : B < p
    · have := Mn_good0 hL hp5 (hk4_of S.hk) hAB (fun t ht => by have := Finset.mem_Ioc.1 ht; omega)
        (fun t ht => by
          obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 ht
          exact S.reg (by omega) (by omega) (by omega) (by omega))
        (sub_ne_zero_of_lt hAB (by omega))
      exact good_pow_mul_zero this (by omega)
    · by_cases hAp : A < p
      · have hBA : B - A ≠ p := by omega
        have := Mn_goodP hL hp5 (hk4_of S.hk) hAB {p} (by intro t ht; rw [Finset.mem_singleton.1 ht]; simp; omega)
          (fun t ht => by have := Finset.mem_Ioc.1 (Finset.mem_sdiff.1 ht).1; omega)
          (fun _ => (1 : ZMod p))
          (fun t ht => by rw [Finset.mem_singleton.1 ht]; exact good_Delta_p hL hp5)
          (fun t ht => by
            obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ht
            have h1' := Finset.mem_Ioc.1 h1
            have h2p : t ≠ p := fun e => h2 (by simp [e])
            exact S.reg (by omega) (by omega) (by omega) h2p)
          (sub_ne_zero_of_ne hAB (by omega) hBA)
        obtain ⟨w', hw'⟩ : ∃ w', uPot p r k A + uPot p r k B = w' + 1 :=
          ⟨uPot p r k A + uPot p r k B - 1, by omega⟩
        rw [hw', pow_succ]
        exact ((good_pow_mul_zero this (n := w') (by omega)).congr' (by ring))
      · have := Mn_good0 hL hp5 (hk4_of S.hk) hAB (fun t ht => by have := Finset.mem_Ioc.1 ht; omega)
          (fun t ht => by
            obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 ht
            exact S.reg (by omega) (by omega) (by omega) (by omega))
          (sub_ne_zero_of_lt hAB (by omega))
        exact good_pow_mul_zero this (by omega)

/-- The diagonal entries of `C`. -/
theorem good_TD {A : ℕ} (hA : A < r) :
    Good p ((p : ℚ) ^ (uPot p r k A + uPot p r k A) * Fr.Mn A A) (TD p j k A) := by
  have hp5 := S.p5
  have hkr := S.hkr
  have hrp := S.hrp
  have hkp := S.hkp
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  by_cases hAk : A < k
  · have hw : uPot p r k A + uPot p r k A = 0 := by unfold uPot; split_ifs <;> omega
    rw [hw, pow_zero, one_mul]
    unfold TD; rw [if_pos hAk]
    exact Mn_diag_good0 hL hp5 (hk4_of S.hk) (fun t ht => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht
      exact S.reg h1 (by omega) (by omega) (by omega))
  · have hw : uPot p r k A + uPot p r k A = 2 := by unfold uPot; split_ifs <;> omega
    rw [hw]
    unfold TD; rw [if_neg hAk]
    have h16 : (16 : ZMod p) ≠ 0 := by
      have : (16 : ZMod p) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
    have := Mn_diag_goodP2 hL hp5 (hk4_of S.hk) (A := A) {k} (by intro t ht; rw [Finset.mem_singleton.1 ht]; simp; have := S.hk0; omega)
      (fun _ => -(16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2))
      (fun t ht => by
        rw [Finset.mem_singleton.1 ht]
        exact good_Dsq_k hL S.hk S.hj0 S.hjp S.hk0 S.hkp)
      (fun t ht => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ht
        have h1' := Finset.mem_Icc.1 h1
        have h2' : t ≠ k := fun e => h2 (by simp [e])
        exact S.reg h1'.1 (by omega) h2' (by omega))
    refine this.congr ?_
    rw [Finset.sum_singleton]
    field_simp

end TableThm

end TableB

end CatalanCore.Arith.Hybrid
