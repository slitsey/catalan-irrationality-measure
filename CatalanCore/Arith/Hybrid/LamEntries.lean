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
structure LamData (Fr : Frame) : Prop where
  norm_eq : Fr.norm = 16
  delta_eq : ∀ t : ℕ, 1 ≤ t → Fr.Delta t = 1 / (t : ℚ) - 4 / (4 * (t : ℚ) - 1)
  dsq_eq : ∀ t : ℕ, 1 ≤ t → Fr.Dsq t = 1 / (t : ℚ) ^ 2 - 16 / (4 * (t : ℚ) - 1) ^ 2

section Prime

variable (p : ℕ) [Fact p.Prime]

lemma four_ne_zmod (hp5 : 5 ≤ p) : (4 : ZMod p) ≠ 0 := by
  have : ((4 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
  simpa using this

/-- Regular index: `p ∤ t(4t-1)`. -/
def Reg (t : ℕ) : Prop := ((t : ℕ) : ZMod p) ≠ 0 ∧ (4 * ((t : ℕ) : ZMod p) - 1) ≠ 0

variable {p}

/-- `Δ_t` at a regular index. -/
lemma good_Delta_reg {Fr : Frame} (hL : LamData Fr) (hp5 : 5 ≤ p) {t : ℕ} (ht1 : 1 ≤ t)
    (hr : Reg p t) :
    Good p (Fr.Delta t) (((t : ℕ) : ZMod p)⁻¹ - 4 * (4 * ((t : ℕ) : ZMod p) - 1)⁻¹) := by
  rw [hL.delta_eq t ht1]
  have := (Good.one (ℓ := p)).div (Good.natCast (ℓ := p) t) hr.1 |>.sub
    ((Good.ofNat (ℓ := p) 4).div (((Good.ofNat (ℓ := p) 4).mul (Good.natCast t)).sub Good.one) hr.2)
  refine this.congr ?_
  simp [div_eq_mul_inv]

/-- `D_t` at a regular index. -/
lemma good_Dsq_reg {Fr : Frame} (hL : LamData Fr) (hp5 : 5 ≤ p) {t : ℕ} (ht1 : 1 ≤ t)
    (hr : Reg p t) :
    Good p (Fr.Dsq t) ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - 16 * ((4 * ((t : ℕ) : ZMod p) - 1)⁻¹) ^ 2) := by
  rw [hL.dsq_eq t ht1]
  have := (Good.one (ℓ := p)).div ((Good.natCast (ℓ := p) t).pow' 2) (pow_ne_zero 2 hr.1) |>.sub
    ((Good.ofNat (ℓ := p) 16).div ((((Good.ofNat (ℓ := p) 4).mul (Good.natCast t)).sub Good.one).pow' 2)
      (pow_ne_zero 2 hr.2))
  refine this.congr ?_
  simp [div_eq_mul_inv]

/-- Sum of `Δ_t` over a set of regular indices. -/
lemma sum_good_0 {Fr : Frame} (hL : LamData Fr) (hp5 : 5 ≤ p) (s : Finset ℕ)
    (h1 : ∀ t ∈ s, 1 ≤ t) (hr : ∀ t ∈ s, Reg p t) :
    Good p (∑ t ∈ s, Fr.Delta t) (∑ t ∈ s, (((t : ℕ) : ZMod p)⁻¹ - 4 * (4 * ((t : ℕ) : ZMod p) - 1)⁻¹)) :=
  Good.sum s _ _ fun t ht => good_Delta_reg hL hp5 (h1 t ht) (hr t ht)

lemma dsum_good_0 {Fr : Frame} (hL : LamData Fr) (hp5 : 5 ≤ p) (s : Finset ℕ)
    (h1 : ∀ t ∈ s, 1 ≤ t) (hr : ∀ t ∈ s, Reg p t) :
    Good p (∑ t ∈ s, Fr.Dsq t)
      (∑ t ∈ s, ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - 16 * ((4 * ((t : ℕ) : ZMod p) - 1)⁻¹) ^ 2)) :=
  Good.sum s _ _ fun t ht => good_Dsq_reg hL hp5 (h1 t ht) (hr t ht)

/-- `p ∑_{t ∈ s} Δ_t` when `s` contains a set `S0` of singular indices (residues `res`) and
otherwise regular ones. -/
lemma sum_good_p {Fr : Frame} (hL : LamData Fr) (hp5 : 5 ≤ p) (s S0 : Finset ℕ) (hS0 : S0 ⊆ s)
    (h1 : ∀ t ∈ s \ S0, 1 ≤ t) (res : ℕ → ZMod p)
    (hsing : ∀ t ∈ S0, Good p ((p : ℚ) * Fr.Delta t) (res t)) (hr : ∀ t ∈ s \ S0, Reg p t) :
    Good p ((p : ℚ) * ∑ t ∈ s, Fr.Delta t) (∑ t ∈ S0, res t) := by
  have hsplit : ∑ t ∈ s, Fr.Delta t = ∑ t ∈ S0, Fr.Delta t + ∑ t ∈ s \ S0, Fr.Delta t := by
    rw [← Finset.sum_sdiff hS0]; ring
  rw [hsplit, mul_add]
  have g1 : Good p (∑ t ∈ S0, (p : ℚ) * Fr.Delta t) (∑ t ∈ S0, res t) := Good.sum S0 _ _ hsing
  have g2 : Good p ((p : ℚ) * ∑ t ∈ s \ S0, Fr.Delta t) 0 :=
    (sum_good_0 hL hp5 (s \ S0) h1 hr).ell_mul
  have := g1.add g2
  rw [← Finset.mul_sum] at this
  simpa using this

lemma dsum_good_p2 {Fr : Frame} (hL : LamData Fr) (hp5 : 5 ≤ p) (s S0 : Finset ℕ) (hS0 : S0 ⊆ s)
    (h1 : ∀ t ∈ s \ S0, 1 ≤ t) (res : ℕ → ZMod p)
    (hsing : ∀ t ∈ S0, Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (res t)) (hr : ∀ t ∈ s \ S0, Reg p t) :
    Good p ((p : ℚ) ^ 2 * ∑ t ∈ s, Fr.Dsq t) (∑ t ∈ S0, res t) := by
  have hsplit : ∑ t ∈ s, Fr.Dsq t = ∑ t ∈ S0, Fr.Dsq t + ∑ t ∈ s \ S0, Fr.Dsq t := by
    rw [← Finset.sum_sdiff hS0]; ring
  rw [hsplit, mul_add]
  have g1 : Good p (∑ t ∈ S0, (p : ℚ) ^ 2 * Fr.Dsq t) (∑ t ∈ S0, res t) := Good.sum S0 _ _ hsing
  have g2 : Good p ((p : ℚ) ^ 2 * ∑ t ∈ s \ S0, Fr.Dsq t) 0 := by
    have := ((dsum_good_0 hL hp5 (s \ S0) h1 hr).ell_mul).ell_mul
    refine this.congr' ?_
    ring
  have := g1.add g2
  rw [← Finset.mul_sum] at this
  simpa using this

/-! ### Singular indices -/

section Singular

variable {Fr : Frame} (hL : LamData Fr) (_hp5 : 5 ≤ p) {j k : ℕ} (hk : 4 * k = j * p + 1)
  (hj0 : 0 < j) (hjp : j < p) (hk0 : 0 < k) (hkp : k < p)

include hL hk hj0 hjp hk0 hkp

lemma good_Delta_k : Good p ((p : ℚ) * Fr.Delta k) (-(4 * ((j : ℕ) : ZMod p)⁻¹)) := by
  rw [hL.delta_eq k hk0]
  have hjz : ((j : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
  have hkz : ((k : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hk0 hd) (by omega)
  have hkQ : 4 * (k : ℚ) - 1 = (j : ℚ) * p := by
    have : (4 * k : ℚ) = j * p + 1 := by exact_mod_cast hk
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
  have hkQ : 4 * (k : ℚ) - 1 = (j : ℚ) * p := by
    have : (4 * k : ℚ) = j * p + 1 := by exact_mod_cast hk
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

lemma good_Delta_p {Fr : Frame} (hL : LamData Fr) (hp5 : 5 ≤ p) :
    Good p ((p : ℚ) * Fr.Delta p) 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [hL.delta_eq p hp1]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h4 : (4 * (p : ℚ) - 1) ≠ 0 := by
    have : (5 : ℚ) ≤ p := by exact_mod_cast hp5
    linarith
  have hl0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hz : (4 * ((p : ℕ) : ZMod p) - 1) ≠ 0 := by rw [hl0]; simp
  have g2 : Good p ((p : ℚ) * (4 / (4 * (p : ℚ) - 1))) 0 :=
    ((Good.ofNat (ℓ := p) 4).div (((Good.ofNat (ℓ := p) 4).mul (Good.natCast (ℓ := p) p)).sub Good.one) hz).ell_mul
  have := (Good.one (ℓ := p)).sub g2
  refine this.congr' ?_ |>.congr (by simp)
  field_simp

end Prime

/-! ### The entries `Mn` -/

lemma Mn_lt {Fr : Frame} (hL : LamData Fr) {A B : ℕ} (h : A < B) :
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

lemma Mn_diag {Fr : Frame} (hL : LamData Fr) (A : ℕ) :
    Fr.Mn A A = -(1 / 16) * ∑ t ∈ Icc 1 A, Fr.Dsq t := by
  unfold Frame.Mn
  rw [if_pos rfl, hL.norm_eq]

section Entry

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} (hL : LamData Fr) (hp5 : 5 ≤ p)

include hL hp5

/-- Entry with all `t ∈ (A, B]` regular. -/
lemma Mn_good0 {A B : ℕ} (h : A < B) (h1 : ∀ t ∈ Ioc A B, 1 ≤ t)
    (hr : ∀ t ∈ Ioc A B, Reg p t) (hd : ((B : ZMod p) - A) ≠ 0) :
    Good p (Fr.Mn A B) ((16 * ((B : ZMod p) - A))⁻¹ *
      ∑ t ∈ Ioc A B, (((t : ℕ) : ZMod p)⁻¹ - 4 * (4 * ((t : ℕ) : ZMod p) - 1)⁻¹)) := by
  rw [Mn_lt hL h]
  have h16 : (16 : ZMod p) * ((B : ZMod p) - A) ≠ 0 := by
    have : (16 : ZMod p) ≠ 0 := by
      have : (16 : ZMod p) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
    exact mul_ne_zero this hd
  have g1 : Good p (1 / (16 * ((B : ℚ) - A))) ((16 * ((B : ZMod p) - A))⁻¹) :=
    ((Good.one (ℓ := p)).div ((Good.ofNat (ℓ := p) 16).mul
      ((Good.natCast (ℓ := p) B).sub (Good.natCast A))) h16).congr (by simp)
  exact g1.mul (sum_good_0 hL hp5 _ h1 hr)

/-- `p ·` entry, with a set `S0` of singular indices in `(A, B]`. -/
lemma Mn_goodP {A B : ℕ} (h : A < B) (S0 : Finset ℕ) (hS0 : S0 ⊆ Ioc A B)
    (h1 : ∀ t ∈ Ioc A B \ S0, 1 ≤ t) (res : ℕ → ZMod p)
    (hsing : ∀ t ∈ S0, Good p ((p : ℚ) * Fr.Delta t) (res t))
    (hr : ∀ t ∈ Ioc A B \ S0, Reg p t) (hd : ((B : ZMod p) - A) ≠ 0) :
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
  have := g1.mul (sum_good_p hL hp5 (Ioc A B) S0 hS0 h1 res hsing hr)
  exact this.congr' (by ring)

/-- `p² ·` entry with `B - A = p`. -/
lemma Mn_goodPP {A B : ℕ} (h : A < B) (hBA : B - A = p) (S0 : Finset ℕ) (hS0 : S0 ⊆ Ioc A B)
    (h1 : ∀ t ∈ Ioc A B \ S0, 1 ≤ t) (res : ℕ → ZMod p)
    (hsing : ∀ t ∈ S0, Good p ((p : ℚ) * Fr.Delta t) (res t))
    (hr : ∀ t ∈ Ioc A B \ S0, Reg p t) :
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
  have := g1.mul (sum_good_p hL hp5 (Ioc A B) S0 hS0 h1 res hsing hr)
  refine this.congr' ?_
  rw [hBQ]
  field_simp

/-- Diagonal entry with all indices regular. -/
lemma Mn_diag_good0 {A : ℕ} (hr : ∀ t ∈ Icc 1 A, Reg p t) :
    Good p (Fr.Mn A A) (-(1 / 16) * ∑ t ∈ Icc 1 A,
      ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - 16 * ((4 * ((t : ℕ) : ZMod p) - 1)⁻¹) ^ 2)) := by
  rw [Mn_diag hL]
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
  have g1 : Good p (-(1 / 16 : ℚ)) (-(1 / 16)) :=
    Good.neg ((Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 16) h16)
  exact g1.mul (dsum_good_0 hL hp5 _ (fun t ht => (Finset.mem_Icc.1 ht).1) hr)

/-- `p² ·` diagonal entry with singular set `S0`. -/
lemma Mn_diag_goodP2 {A : ℕ} (S0 : Finset ℕ) (hS0 : S0 ⊆ Icc 1 A)
    (res : ℕ → ZMod p) (hsing : ∀ t ∈ S0, Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (res t))
    (hr : ∀ t ∈ Icc 1 A \ S0, Reg p t) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A A) (-(1 / 16) * ∑ t ∈ S0, res t) := by
  rw [Mn_diag hL]
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
  have g1 : Good p (-(1 / 16 : ℚ)) (-(1 / 16)) :=
    Good.neg ((Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 16) h16)
  have := g1.mul (dsum_good_p2 hL hp5 (Icc 1 A) S0 hS0
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
      ∑ t ∈ Ioc A B, (((t : ℕ) : ZMod p)⁻¹ - 4 * (4 * ((t : ℕ) : ZMod p) - 1)⁻¹)
  else if A < k then
    (if B < p then (16 * ((B : ZMod p) - A))⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹))
     else if B - A = p then (16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1) else 0)
  else 0

/-- The diagonal residue (`A < r`). -/
noncomputable def TD (p j k : ℕ) [Fact p.Prime] (A : ℕ) : ZMod p :=
  if A < k then -(1 / 16 : ZMod p) * ∑ t ∈ Icc 1 A,
      ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - 16 * ((4 * ((t : ℕ) : ZMod p) - 1)⁻¹) ^ 2)
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
lemma reg_of {j k : ℕ} (hk : 4 * k = j * p + 1) (hp5 : 5 ≤ p) (hkp : k < p) {t : ℕ} (h1 : 1 ≤ t)
    (ht2 : t < 2 * p) (htk : t < k + p) (hnk : t ≠ k) (hnp : t ≠ p) : Reg p t := by
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
    have h4k : (4 : ZMod p) * (k : ZMod p) = 1 := by
      have : ((4 * k : ℕ) : ZMod p) = ((j * p + 1 : ℕ) : ZMod p) := by rw [hk]
      push_cast at this
      simpa [ZMod.natCast_self] using this
    have h4 : (4 : ZMod p) ≠ 0 := four_ne_zmod p hp5
    have : (t : ZMod p) = (k : ZMod p) := by
      have : (4 : ZMod p) * ((t : ZMod p) - k) = 0 := by linear_combination h0 - h4k
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h h4
      · exact sub_eq_zero.1 h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    by_cases htp : t < p
    · rw [Nat.mod_eq_of_lt htp, Nat.mod_eq_of_lt hkp] at this; exact hnk this
    · have : t % p = t - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt hkp] at *
      omega

end TableB

end CatalanCore.Arith.Hybrid
