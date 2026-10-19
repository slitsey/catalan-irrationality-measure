module

public import CatalanCore.Arith.Hybrid.LemmaE.EntriesG
public import CatalanCore.Arith.Hybrid.LemmaE.EntriesE
public import CatalanCore.Arith.Hybrid.LemmaE.PairRankG

@[expose] public section

/-!
# Lemma E, class `p ≡ 3 (4)`: the setting and the singular data

`k₁ = (p+1)/4` (`4k₁ - 1 = p`), `p`, `k₂ = p + k₁` (`4k₂ - 1 = 5p`).  The labels are `< N = r+2m <
2p`, so these are the only singular indices (DQ §2).  Residues of `pΔ`: `-4, 1, -4/5`; of `p²D`:
`-16, 1, -16/25`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {Fr : Frame}

lemma good_Delta_kz {o : ℕ} (hL : LamData Fr o) {j k : ℕ} (hk : 4 * k = j * p + o) (hj0 : 0 < j)
    (hjp : j < p) (hk0 : 0 < k) (hkz : ((k : ℕ) : ZMod p) ≠ 0) :
    Good p ((p : ℚ) * Fr.Delta k) (-(4 * ((j : ℕ) : ZMod p)⁻¹)) := by
  rw [hL.delta_eq k hk0]
  have hjz : ((j : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
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

lemma good_Dsq_kz {o : ℕ} (hL : LamData Fr o) {j k : ℕ} (hk : 4 * k = j * p + o) (hj0 : 0 < j)
    (hjp : j < p) (hk0 : 0 < k) (hkz : ((k : ℕ) : ZMod p) ≠ 0) :
    Good p ((p : ℚ) ^ 2 * Fr.Dsq k) (-(16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2)) := by
  rw [hL.dsq_eq k hk0]
  have hjz : ((j : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
  have hkQ : 4 * (k : ℚ) - (o : ℚ) = (j : ℚ) * p := by
    have : (4 * k : ℚ) = j * p + o := by exact_mod_cast hk
    linarith
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
  have hk0Q : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  have g1 : Good p ((p : ℚ) ^ 2 * (1 / (k : ℚ) ^ 2)) 0 := by
    have := ((Good.one (ℓ := p)).div ((Good.natCast (ℓ := p) k).pow' 2)
      (pow_ne_zero 2 hkz)).ell_mul.ell_mul
    refine this.congr' ?_
    ring
  have g2 : Good p (16 / (j : ℚ) ^ 2) (16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2) :=
    ((Good.ofNat (ℓ := p) 16).div ((Good.natCast (ℓ := p) j).pow' 2) (pow_ne_zero 2 hjz)).congr
      (by simp [div_eq_mul_inv])
  have := g1.sub g2
  refine this.congr' ?_ |>.congr (by ring)
  rw [hkQ]
  field_simp

/-- The setting of Lemma E, class 3. -/
structure ESetup3 (o p r m k1 : ℕ) : Prop where
  p5 : 5 ≤ p
  hp6 : 6 ≤ p
  ho0 : 0 < o
  ho3 : o ≤ 3
  hk1 : 4 * k1 = p + o
  hpr : p < r
  hk2r : p + k1 < r
  hN : r + 2 * m < 2 * p

variable {o r m k1 : ℕ}

lemma ESetup3.hk4 {p : ℕ} [Fact p.Prime] (S : ESetup3 o p r m k1) :
    (4 : ZMod p) * (k1 : ZMod p) = (o : ZMod p) := hk4_of (j := 1) (by rw [one_mul]; exact S.hk1)

lemma ESetup3.hk1o (S : ESetup3 o p r m k1) : 4 * k1 = p + o ∧ 0 < o ∧ o ≤ 3 ∧ 6 ≤ p :=
  ⟨S.hk1, S.ho0, S.ho3, S.hp6⟩

lemma ESetup3.reg (S : ESetup3 o p r m k1) {t : ℕ} (h1 : 1 ≤ t) (hN : t < r + 2 * m)
    (h2 : t ≠ k1) (h3 : t ≠ p) (h4 : t ≠ p + k1) : Reg p k1 t := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hk1 := S.hk1o
  have hSN := S.hN
  refine ⟨?_, ?_⟩
  · rw [Ne, ZMod.natCast_eq_zero_iff]
    rintro ⟨c, hc⟩
    rcases c with _ | _ | c
    · omega
    · omega
    · have : p * (c + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
      omega
  · intro h0
    have hk1p : k1 < p := by omega
    have : (t : ZMod p) = (k1 : ZMod p) := sub_eq_zero.1 h0
    rw [ZMod.natCast_eq_natCast_iff'] at this
    by_cases htp : t < p
    · rw [Nat.mod_eq_of_lt htp, Nat.mod_eq_of_lt hk1p] at this; exact h2 this
    · have : t % p = t - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt hk1p] at *
      omega

/-- The singular data of class 3. -/
noncomputable def sd3 (S : ESetup3 o p r m k1) : SingData p (r + 2 * m) k1 where
  Sg := {k1, p, p + k1}
  ρ := fun t => if t = k1 then -(4 * (((1 : ℕ) : ZMod p))⁻¹)
    else if t = p then 1 else -(4 * (((5 : ℕ) : ZMod p))⁻¹)
  ρ2 := fun t => if t = k1 then -(16 * ((((1 : ℕ) : ZMod p))⁻¹) ^ 2)
    else if t = p then 1 else -(16 * ((((5 : ℕ) : ZMod p))⁻¹) ^ 2)
  pos := by
    intro t ht
    have hk1 := S.hk1o
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with h | h | h <;> omega
  reg := by
    intro t h1 hN hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    exact S.reg h1 hN hn.1 hn.2.1 hn.2.2

theorem sd3_good {o : ℕ} (hL : LamData Fr o) (S : ESetup3 o p r m k1) : SingGood Fr (sd3 S) where
  hΔ := by
    intro t ht
    have hk1 := S.hk1o
    have hp5 := S.p5
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    simp only [sd3, Finset.mem_insert, Finset.mem_singleton] at ht
    have hk1z : ((k1 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    rcases ht with h | h | h
    · subst h
      simp only [sd3, if_true]
      exact good_Delta_kz hL (j := 1) (by omega) (by omega) (by omega) (by omega) hk1z
    · subst h
      have hne : t ≠ k1 := by omega
      simp only [sd3, if_neg hne, if_true]
      exact good_Delta_p hL hp5
    · subst h
      have hne : p + k1 ≠ k1 := by omega
      have hne2 : p + k1 ≠ p := by omega
      simp only [sd3, if_neg hne, if_neg hne2]
      refine good_Delta_kz hL (j := 5) (by omega) (by omega) (by omega) (by omega) ?_
      push_cast
      rw [ZMod.natCast_self, zero_add]; exact hk1z
  hD := by
    intro t ht
    have hk1 := S.hk1o
    have hp5 := S.p5
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    simp only [sd3, Finset.mem_insert, Finset.mem_singleton] at ht
    have hk1z : ((k1 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    rcases ht with h | h | h
    · subst h
      simp only [sd3, if_true]
      exact good_Dsq_kz hL (j := 1) (by omega) (by omega) (by omega) (by omega) hk1z
    · subst h
      have hne : t ≠ k1 := by omega
      simp only [sd3, if_neg hne, if_true]
      exact good_Dsq_p hL hp5
    · subst h
      have hne : p + k1 ≠ k1 := by omega
      have hne2 : p + k1 ≠ p := by omega
      simp only [sd3, if_neg hne, if_neg hne2]
      refine good_Dsq_kz hL (j := 5) (by omega) (by omega) (by omega) (by omega) ?_
      push_cast
      rw [ZMod.natCast_self, zero_add]; exact hk1z

end

end CatalanCore.Arith.Hybrid
