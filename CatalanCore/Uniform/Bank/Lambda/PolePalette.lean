import CatalanCore.Uniform.Bank.Chi3Rank.Closed
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open Finset CatalanCore CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Bank.Chi3Rank (lf_term e_term)

/-- Positive two-term increment convention of the q4 rank pipeline, norm one. -/
noncomputable def D4 (a : ℕ) : DigammaFrame (Fin 2) where
  u := ![a, 1]
  q := ![4, 1]
  c := ![-1, 1]

def poleL (j z d : ℕ) : ℚ :=
  (∑ m ∈ range d, 1 / ((1 + m : ℕ) : ℚ)) -
    ∑ m ∈ range (d + z), 4 / ((j + 4 * m : ℕ) : ℚ)

def poleE (j z d : ℕ) : ℚ :=
  (∑ m ∈ range d, 1 / ((1 + m : ℕ) : ℚ) ^ 2) -
    ∑ m ∈ range (d + z), 16 / ((j + 4 * m : ℕ) : ℚ) ^ 2

/-- Exact physical pole palette, not merely an equality after reduction. -/
theorem D4_pole_node (a p : ℕ) [hp : Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (k j x d : ℕ) (hk : k < p) (hw : 4 * k + a = p * j) (hx : x < p) :
    (D4 a).Lf p (x + p * d) = poleL j (if k < x then 1 else 0) d ∧
    (D4 a).E p (x + p * d) = poleE j (if k < x then 1 else 0) d := by
  have hi : 1 * (p - 1) + 1 = p * 1 := by have := hp.out.pos; omega
  have hik : p - 1 < p := by have := hp.out.pos; omega
  have hix : ¬ p - 1 < x := by omega
  have hp1 : ¬ p ∣ 1 := hp.out.not_dvd_one
  have f0 := lf_term p (-1) 4 a k j x d (by norm_num) hp4 hk hw hx
  have f1 := lf_term p 1 1 1 (p - 1) 1 x d (by norm_num) hp1 hik hi hx
  have e0 := e_term p (-1) 4 a k j x d (by norm_num) hp4 hk hw hx
  have e1 := e_term p 1 1 1 (p - 1) 1 x d (by norm_num) hp1 hik hi hx
  rw [if_neg hix, add_zero] at f1 e1
  norm_num only [Nat.cast_ofNat, Nat.cast_one] at f0 f1 e0 e1
  constructor
  · unfold DigammaFrame.Lf
    rw [Fin.sum_univ_two]
    change (∑ t ∈ range (x + p * d),
        if p ∣ 4 * t + a then (-1 : ℚ) * 4 * p / ((4 * t + a : ℕ) : ℚ) else 0) +
      (∑ t ∈ range (x + p * d),
        if p ∣ 1 * t + 1 then (1 : ℚ) * 1 * p / ((1 * t + 1 : ℕ) : ℚ) else 0) = _
    norm_num only
    rw [f0, f1]
    simp only [poleL, one_mul, mul_one, neg_mul, one_mul, neg_div, sum_neg_distrib]
    ring
  · unfold DigammaFrame.E
    rw [Fin.sum_univ_two]
    change (∑ t ∈ range (x + p * d),
        if p ∣ 4 * t + a then (-1 : ℚ) * (4 : ℚ) ^ 2 * (p : ℚ) ^ 2 /
          ((4 * t + a : ℕ) : ℚ) ^ 2 else 0) +
      (∑ t ∈ range (x + p * d),
        if p ∣ 1 * t + 1 then (1 : ℚ) * (1 : ℚ) ^ 2 * (p : ℚ) ^ 2 /
          ((1 * t + 1 : ℕ) : ℚ) ^ 2 else 0) = _
    norm_num only
    rw [e0, e1]
    norm_num only [poleE, one_pow, one_mul, mul_one, neg_mul, neg_div, sum_neg_distrib]
    ring

#print axioms D4_pole_node
end CatalanCore.Uniform.Bank.Lambda

