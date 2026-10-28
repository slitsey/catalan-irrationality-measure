module

public import CatalanCore.Arith.Hybrid.PeriodicEntries
public import CatalanCore.Arith.Hybrid.SingularData
public import CatalanFrames.P6.Content

@[expose] public section

/-!
# `PoleData` for the chi_{-3} frame (lane B, B3c)

The singular classes of `Delta k = 1/k + 6/(3k-2) - 6/(2k-1)` modulo `p` are `p | k`, `p | 3k-2`,
`p | 2k-1` (three distinct classes for `p >= 5`).  For `3 N < p^2` the entries are `S p`-integral
after one factor `p`, and off the singular classes they are `S p`-integral.
-/

open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic
  CatalanFrames.P6

namespace CatalanCore.Uniform.Bank.Chi3Content

/-- The periodic singular set of the chi_{-3} frame. -/
def chi3Sing (p : ℕ) (t : ℤ) : Prop := (p : ℤ) ∣ t ∨ (p : ℤ) ∣ 3 * t - 2 ∨ (p : ℤ) ∣ 2 * t - 1

theorem chi3Sing_periodic (p : ℕ) (t j : ℤ) : chi3Sing p (t + j * p) ↔ chi3Sing p t := by
  unfold chi3Sing
  have e1 : 3 * (t + j * p) - 2 = (3 * t - 2) + (3 * j) * p := by ring
  have e2 : 2 * (t + j * p) - 1 = (2 * t - 1) + (2 * j) * p := by ring
  rw [e1, e2, dvd_add_left (dvd_mul_left (p : ℤ) j),
    dvd_add_left (dvd_mul_left (p : ℤ) (3 * j)), dvd_add_left (dvd_mul_left (p : ℤ) (2 * j))]

variable {p N : ℕ} [Fact p.Prime]

theorem chi3_delta_form (k : ℕ) (hk : 1 ≤ k) :
    p6Frame.Delta k = 1 / (k : ℚ) + 6 / ((3 * k - 2 : ℕ) : ℚ) - 6 / ((2 * k - 1 : ℕ) : ℚ) := by
  rw [Delta_eq k hk, c3 (by omega), c2 (by omega)]

theorem chi3_dsq_form (k : ℕ) (hk : 1 ≤ k) :
    p6Frame.Dsq k = 1 / (k : ℚ) ^ 2 + 18 / ((3 * k - 2 : ℕ) : ℚ) ^ 2 -
      12 / ((2 * k - 1 : ℕ) : ℚ) ^ 2 := by
  rw [Dsq_eq k hk, c3 (by omega), c2 (by omega)]

theorem chi3_good_delta (hN : 3 * N < p * p) {k : ℕ} (hk : 1 ≤ k) (hkN : k < N) :
    ((p : ℚ) * p6Frame.Delta k) ∈ S p := by
  have g1 := good_scaled_inverse (p := p) (n := k) (by omega) (by omega)
  have g2 := good_scaled_inverse (p := p) (n := 3 * k - 2) (by omega) (by omega)
  have g3 := good_scaled_inverse (p := p) (n := 2 * k - 1) (by omega) (by omega)
  have g := (g1.add ((Good.ofNat (ℓ := p) 6).mul g2)).sub ((Good.ofNat (ℓ := p) 6).mul g3)
  refine (g.congr' ?_).mem
  rw [chi3_delta_form k hk]
  push_cast
  ring

theorem chi3_good_dsq (hN : 3 * N < p * p) {k : ℕ} (hk : 1 ≤ k) (hkN : k < N) :
    ((p : ℚ) ^ 2 * p6Frame.Dsq k) ∈ S p := by
  have g1 := good_scaled_inverse (p := p) (n := k) (by omega) (by omega)
  have g2 := good_scaled_inverse (p := p) (n := 3 * k - 2) (by omega) (by omega)
  have g3 := good_scaled_inverse (p := p) (n := 2 * k - 1) (by omega) (by omega)
  have g := ((g1.pow' 2).add ((Good.ofNat (ℓ := p) 18).mul (g2.pow' 2))).sub
    ((Good.ofNat (ℓ := p) 12).mul (g3.pow' 2))
  refine (g.congr' ?_).mem
  rw [chi3_dsq_form k hk]
  simp only [div_pow, one_pow]
  ring

theorem chi3_regular {t : ℕ} (ht : 1 ≤ t) (hs : ¬ chi3Sing p (t : ℤ)) :
    p6Frame.Delta t ∈ S p ∧ p6Frame.Dsq t ∈ S p := by
  unfold chi3Sing at hs
  push Not at hs
  obtain ⟨h1, h2, h3⟩ := hs
  have hn : (((t : ℤ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h1
  have hm : ((3 * (t : ℤ) - 2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h2
  have hl : ((2 * (t : ℤ) - 1 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h3
  have gt := (Good.intCast (ℓ := p) (t : ℤ)).inv hn
  have gm := (Good.intCast (ℓ := p) (3 * (t : ℤ) - 2)).inv hm
  have gl := (Good.intCast (ℓ := p) (2 * (t : ℤ) - 1)).inv hl
  have e3 : ((3 * t - 2 : ℕ) : ℚ) = ((3 * (t : ℤ) - 2 : ℤ) : ℚ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : ((2 * t - 1 : ℕ) : ℚ) = ((2 * (t : ℤ) - 1 : ℤ) : ℚ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  constructor
  · have g := (gt.add ((Good.ofNat (ℓ := p) 6).mul gm)).sub ((Good.ofNat (ℓ := p) 6).mul gl)
    refine (g.congr' ?_).mem
    rw [chi3_delta_form t ht, e3, e2]
    push_cast
    simp [div_eq_mul_inv]
  · have g := ((gt.pow' 2).add ((Good.ofNat (ℓ := p) 18).mul (gm.pow' 2))).sub
      ((Good.ofNat (ℓ := p) 12).mul (gl.pow' 2))
    refine (g.congr' ?_).mem
    rw [chi3_dsq_form t ht, e3, e2]
    push_cast
    simp [div_eq_mul_inv, inv_pow]

/-- `PoleData` of the chi_{-3} frame for `p ≥ 5` and `3 N < p²`. -/
noncomputable def chi3PoleData (hp : 5 ≤ p) (hN : 3 * N < p * p) : PoleData p6Frame p N where
  singular := chi3Sing p
  periodic := chi3Sing_periodic p
  norm_mem := by
    show (36 : ℚ) ∈ S p
    simpa using (Good.ofNat (ℓ := p) 36).mem
  norm_ne := by
    show red p (36 : ℚ) ≠ 0
    have h6 : (6 : ZMod p) ≠ 0 := by
      have : ((6 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
        have h23 : p ∣ 2 * 3 := by simpa using hd
        rcases (Fact.out : p.Prime).dvd_mul.mp h23 with h | h
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      simpa using this
    have h36 : (36 : ZMod p) ≠ 0 := by
      have : (36 : ZMod p) = 6 * 6 := by norm_num
      rw [this]; exact mul_ne_zero h6 h6
    simpa [red] using h36
  delta_mem := fun k hk hkN => chi3_good_delta hN hk hkN
  dsq_mem := fun k hk hkN => chi3_good_dsq hN hk hkN
  regular_delta := fun k hk _ hs => (chi3_regular hk hs).1
  regular_dsq := fun k hk _ hs => (chi3_regular hk hs).2

end CatalanCore.Uniform.Bank.Chi3Content
