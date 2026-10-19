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

variable {Fr : Frame} (hL : LamData Fr) (hp5 : 5 ≤ p) {j k : ℕ} (hk : 4 * k = j * p + 1)
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

end CatalanCore.Arith.Hybrid
