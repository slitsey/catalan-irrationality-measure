module

public import CatalanCore.Arith.Hybrid.DefGKTab

@[expose] public section

/-!
# A uniform singular-node dictionary below the square-prime threshold

No chain-type determinant or exceptional-prime list is used here.  The residues
are defined by the quotient of a singular denominator by `p`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

variable {p : ℕ} [Fact p.Prime]

/-- Residue of `p/n` when `0<n<p²`. -/
noncomputable def invResidue (p n : ℕ) : ZMod p :=
  if p ∣ n then ((n / p : ℕ) : ZMod p)⁻¹ else 0

theorem good_scaled_inverse {n : ℕ} (hn : 0 < n) (hn2 : n < p * p) :
    Good p ((p : ℚ) / n) (invResidue p n) := by
  have hp := (Fact.out : p.Prime)
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases hd : p ∣ n
  · obtain ⟨j, hj⟩ := hd
    have hj0 : 0 < j := by nlinarith
    have hjp : j < p := by nlinarith [hp.pos]
    have hjz : (j : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd hj0 h
      omega
    have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
    have hq : (n : ℚ) = p * j := by exact_mod_cast hj
    have hd' : p ∣ n := ⟨j, hj⟩
    have hdiv : n / p = j := by rw [hj, Nat.mul_div_right _ hp.pos]
    have g := (Good.one (ℓ := p)).div (Good.natCast (ℓ := p) j) hjz
    refine (g.congr' ?_).congr ?_
    · rw [hq]; field_simp
    · simp [invResidue, hd', hdiv, div_eq_mul_inv]
  · have hnz : (n : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    have g := ((Good.one (ℓ := p)).div (Good.natCast (ℓ := p) n) hnz).ell_mul
    simpa [invResidue, hd, div_eq_mul_inv] using g

noncomputable def deltaResidue (p o t : ℕ) : ZMod p :=
  invResidue p t - 4 * invResidue p (4 * t - o)

noncomputable def dsqResidue (p o t : ℕ) : ZMod p :=
  (invResidue p t) ^ 2 - 16 * (invResidue p (4 * t - o)) ^ 2

theorem good_Delta_uniform {Fr : Frame} {o N t : ℕ} (hL : LamData Fr o)
    (hN : 4 * N < p * p) (ht : 1 ≤ t) (htN : t < N) :
    Good p ((p : ℚ) * Fr.Delta t) (deltaResidue p o t) := by
  have ho := hL.o_le
  have ht2 : t < p * p := by omega
  have hd0 : 0 < 4 * t - o := by omega
  have hd2 : 4 * t - o < p * p := by omega
  have hcast : ((4 * t - o : ℕ) : ℚ) = 4 * (t : ℚ) - o := by
    rw [Nat.cast_sub (by omega : o ≤ 4 * t)]; push_cast; ring
  have g := (good_scaled_inverse (p := p) ht ht2).sub
    ((Good.ofNat (ℓ := p) 4).mul (good_scaled_inverse hd0 hd2))
  refine (g.congr' ?_)
  rw [hL.delta_eq t ht, hcast]
  ring

theorem good_Dsq_uniform {Fr : Frame} {o N t : ℕ} (hL : LamData Fr o)
    (hN : 4 * N < p * p) (ht : 1 ≤ t) (htN : t < N) :
    Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (dsqResidue p o t) := by
  have ho := hL.o_le
  have ht2 : t < p * p := by omega
  have hd0 : 0 < 4 * t - o := by omega
  have hd2 : 4 * t - o < p * p := by omega
  have hcast : ((4 * t - o : ℕ) : ℚ) = 4 * (t : ℚ) - o := by
    rw [Nat.cast_sub (by omega : o ≤ 4 * t)]; push_cast; ring
  have g := ((good_scaled_inverse (p := p) ht ht2).pow' 2).sub
    ((Good.ofNat (ℓ := p) 16).mul ((good_scaled_inverse hd0 hd2).pow' 2))
  refine g.congr' ?_
  rw [hL.dsq_eq t ht, hcast]
  simp only [div_pow, one_pow, mul_pow]
  ring

/-- All singular indices in the physical range, with no case enumeration. -/
def singularNodes (p o N : ℕ) : Finset ℕ :=
  (Ico 1 N).filter (fun t => p ∣ t ∨ p ∣ 4 * t - o)

theorem uniform_sgData {Fr : Frame} {o N k : ℕ} (hL : LamData Fr o)
    (hN : 4 * N < p * p) (hk4 : (4 : ZMod p) * k = (o : ZMod p)) :
    SgData Fr o p N k (singularNodes p o N) (deltaResidue p o) (dsqResidue p o) := by
  refine ⟨?_, ?_, ?_, ?_, hk4⟩
  · intro t ht
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp ht).1).1
  · intro t ht
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    exact good_Delta_uniform hL hN (Finset.mem_Ico.mp ht).1 (Finset.mem_Ico.mp ht).2
  · intro t ht
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    exact good_Dsq_uniform hL hN (Finset.mem_Ico.mp ht).1 (Finset.mem_Ico.mp ht).2
  · intro t ht htN hn
    have ho := hL.o_le
    have hn' : ¬ (p ∣ t ∨ p ∣ 4 * t - o) := by
      intro hd
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ht, htN⟩, hd⟩)
    refine ⟨?_, ?_⟩
    · rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => hn' (Or.inl hd)
    · intro he
      have hzero : (4 : ZMod p) * t - o = 0 := by rw [four_sub_eq hk4, he, mul_zero]
      have hcast : ((4 * t - o : ℕ) : ZMod p) = 4 * (t : ZMod p) - o := by
        rw [Nat.cast_sub (by omega : o ≤ 4 * t)]; push_cast; ring
      exact hn' (Or.inr ((ZMod.natCast_eq_zero_iff _ _).mp (hcast.trans hzero)))

end CatalanCore.Arith.Hybrid
