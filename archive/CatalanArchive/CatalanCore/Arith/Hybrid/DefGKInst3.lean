module

public import CatalanCore.Arith.Hybrid.GKConditions
public import CatalanCore.Arith.Hybrid.DefGKTab
public import CatalanCore.Arith.Hybrid.DefC7Entries

@[expose] public section

/-!
# GK, class `p ≡ 3 (mod 4)`: the singular set `{k, p, p+k, 2p, 2p+k}` (`4k = p+1`)

`GKS3 o p r m k` : `13 ≤ p`, `4k = p+1`, `2p + k < r`, `r + 2m ≤ 3p`, `0 < m`.
`sgData3`: the `SgData` of the singular set with the residues of `p Δ_t` and `p² D_t`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section Inst3

variable {o p : ℕ} [Fact p.Prime]

/-- `p² D_t` at a singular `4t = jp + 1`, `p ∤ j`, `p ∤ t` (no `t < p` needed). -/
lemma good_Dsq_gen7 {Fr : Frame} (hL : LamData Fr o) {j k : ℕ} (hk : 4 * k = j * p + o ∧ 0 < o ∧ o ≤ 3)
    (hj0 : 0 < j) (hjz : ((j : ℕ) : ZMod p) ≠ 0) (hk0 : 0 < k) (hkz : ((k : ℕ) : ZMod p) ≠ 0) :
    Good p ((p : ℚ) ^ 2 * Fr.Dsq k) (-(16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2)) := by
  rw [hL.dsq_eq k hk0]
  have hkQ : 4 * (k : ℚ) - (o : ℚ) = (j : ℚ) * p := by
    have : (4 * k : ℚ) = j * p + o := by exact_mod_cast hk.1
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

lemma two_ne_zmod (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  have : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
    have := Nat.le_of_dvd (by norm_num) hd; omega
  simpa using this

lemma good_Delta_2p {Fr : Frame} (hL : LamData Fr o) (hp5 : 5 ≤ p) :
    Good p ((p : ℚ) * Fr.Delta (2 * p)) (2 : ZMod p)⁻¹ := by
  have hp1 : 1 ≤ 2 * p := by have := (Fact.out : p.Prime).pos; omega
  rw [hL.delta_eq (2 * p) hp1]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h4 : (4 * ((2 * p : ℕ) : ℚ) - (o : ℚ)) ≠ 0 := by
    have : (5 : ℚ) ≤ p := by exact_mod_cast hp5
    have : (o : ℚ) ≤ 3 := by exact_mod_cast hL.o_le
    push_cast; linarith
  have hz : (4 * (((2 * p : ℕ)) : ZMod p) - (o : ZMod p)) ≠ 0 := by
    have : (((2 * p : ℕ)) : ZMod p) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
    rw [this]; simpa using o_ne_zmod p hL.o_pos hL.o_le hp5
  have h2 := two_ne_zmod hp5
  have g1 : Good p ((p : ℚ) * (1 / ((2 * p : ℕ) : ℚ))) (2 : ZMod p)⁻¹ := by
    have := ((Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 2) h2)
    refine (this.congr' ?_).congr (by simp)
    push_cast; field_simp
  have g2 : Good p ((p : ℚ) * (4 / (4 * ((2 * p : ℕ) : ℚ) - (o : ℚ)))) 0 :=
    ((Good.ofNat (ℓ := p) 4).div (((Good.ofNat (ℓ := p) 4).mul (Good.natCast (ℓ := p) (2 * p))).sub
      (Good.natCast (ℓ := p) o)) hz).ell_mul
  have := g1.sub g2
  refine this.congr' ?_ |>.congr (by simp)
  push_cast
  ring

lemma good_Dsq_2p {Fr : Frame} (hL : LamData Fr o) (hp5 : 5 ≤ p) :
    Good p ((p : ℚ) ^ 2 * Fr.Dsq (2 * p)) (4 : ZMod p)⁻¹ := by
  have hp1 : 1 ≤ 2 * p := by have := (Fact.out : p.Prime).pos; omega
  rw [hL.dsq_eq (2 * p) hp1]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hz : (4 * (((2 * p : ℕ)) : ZMod p) - (o : ZMod p)) ≠ 0 := by
    have : (((2 * p : ℕ)) : ZMod p) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
    rw [this]; simpa using o_ne_zmod p hL.o_pos hL.o_le hp5
  have h4 := four_ne_zmod p hp5
  have g1 : Good p ((p : ℚ) ^ 2 * (1 / ((2 * p : ℕ) : ℚ) ^ 2)) (4 : ZMod p)⁻¹ := by
    have := ((Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 4) h4)
    refine (this.congr' ?_).congr (by simp)
    push_cast; field_simp; norm_num
  have g2 : Good p ((p : ℚ) ^ 2 * (16 / (4 * ((2 * p : ℕ) : ℚ) - (o : ℚ)) ^ 2)) 0 :=
    ((((Good.ofNat (ℓ := p) 16).div ((((Good.ofNat (ℓ := p) 4).mul
      (Good.natCast (ℓ := p) (2 * p))).sub (Good.natCast (ℓ := p) o)).pow' 2) (pow_ne_zero 2 hz)).ell_mul).ell_mul).congr'
      (by ring)
  have := g1.sub g2
  refine this.congr' ?_ |>.congr (by simp)
  ring

/-! ### The data -/

/-- The singular set of class 3. -/
def Sg3 (p k : ℕ) : Finset ℕ := {k, p, p + k, 2 * p, 2 * p + k}

/-- Residues of `p Δ_t`. -/
noncomputable def res3 (p k : ℕ) (t : ℕ) : ZMod p :=
  if t = k then -4 else if t = p then 1 else if t = p + k then -(4 * (5 : ZMod p)⁻¹)
  else if t = 2 * p then (2 : ZMod p)⁻¹ else -(4 * (9 : ZMod p)⁻¹)

/-- Residues of `p² D_t`. -/
noncomputable def resD3 (p k : ℕ) (t : ℕ) : ZMod p :=
  if t = k then -16 else if t = p then 1 else if t = p + k then -(16 * ((5 : ZMod p)⁻¹) ^ 2)
  else if t = 2 * p then (4 : ZMod p)⁻¹ else -(16 * ((9 : ZMod p)⁻¹) ^ 2)

lemma reg3 {r m k : ℕ} (S : GKS3 o p r m k) {t : ℕ} (h1 : 1 ≤ t) (ht : t < 3 * p)
    (hn : t ∉ Sg3 p k) : Reg p k t := by
  have hp0 := (Fact.out : p.Prime).pos
  have hkp := S.kp
  have h13 := S.p13
  have hk := S.hk
  refine ⟨?_, ?_⟩
  · rw [Ne, ZMod.natCast_eq_zero_iff]
    rintro ⟨c, hc⟩
    rcases c with _ | _ | _ | c
    · omega
    · exact hn (by simp [Sg3]; omega)
    · exact hn (by simp [Sg3]; omega)
    · have : p * (c + 1 + 1 + 1) ≥ p * 3 := Nat.mul_le_mul_left p (by omega)
      omega
  · intro h0
    have : (t : ZMod p) = (k : ZMod p) := sub_eq_zero.1 h0
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rw [Nat.mod_eq_of_lt hkp] at this
    by_cases htp : t < p
    · rw [Nat.mod_eq_of_lt htp] at this; exact hn (by simp [Sg3]; omega)
    · by_cases ht2 : t < 2 * p
      · have : t % p = t - p := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        exact hn (by simp [Sg3]; omega)
      · have : t % p = t - 2 * p := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)]
          omega
        exact hn (by simp [Sg3]; omega)

theorem sgData3 {Fr : Frame} (hL : LamData Fr o) {r m k : ℕ} (S : GKS3 o p r m k) :
    SgData Fr o p (r + 2 * m) k (Sg3 p k) (res3 p k) (resD3 p k) := by
  have hp0 := (Fact.out : p.Prime).pos
  have hkp := S.kp
  have hk0 := S.k0
  have h13 := S.p13
  have hk := S.hk
  have hp5 : 5 ≤ p := by omega
  have hkz : ((k : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt hk0 hkp
  have hz1 : ((1 : ℕ) : ZMod p) ≠ 0 := by simp
  have hj5 : (((5 : ℕ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
    have := Nat.le_of_dvd (by norm_num) hd; omega
  have hj9 : (((9 : ℕ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
    have := Nat.le_of_dvd (by norm_num) hd; omega
  have hpk : (((p + k : ℕ)) : ZMod p) ≠ 0 := by
    rw [Nat.cast_add, ZMod.natCast_self, zero_add]; exact hkz
  have h2pk : (((2 * p + k : ℕ)) : ZMod p) ≠ 0 := by
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]; exact hkz
  have np : p ≠ 0 := by omega
  have nk : k ≠ 0 := by omega
  have e1 : k ≠ p := by omega
  have e2 : k ≠ p + k := by omega
  have e3 : p ≠ p + k := by omega
  have e4 : k ≠ 2 * p := by omega
  have e5 : p ≠ 2 * p := by omega
  have e6 : p + k ≠ 2 * p := by omega
  have e7 : 2 * p + k ≠ k := by omega
  have e8 : 2 * p + k ≠ p := by omega
  have e9 : 2 * p + k ≠ p + k := by omega
  have e10 : 2 * p + k ≠ 2 * p := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [Sg3, Finset.mem_insert, Finset.mem_singleton] at ht
    omega
  · intro t ht
    simp only [Sg3, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · have := good_Delta_gen7 hL (j := 1) (k := t) (by omega) (by omega) hz1 hkz
      refine this.congr ?_
      simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
    · refine (good_Delta_p hL hp5).congr ?_
      simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
    · have := good_Delta_gen7 hL (j := 5) (k := p + k) (by omega) (by omega) hj5 hpk
      refine this.congr ?_
      simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
    · refine (good_Delta_2p hL hp5).congr ?_
      simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
    · have := good_Delta_gen7 hL (j := 9) (k := 2 * p + k) (by omega) (by omega) hj9 h2pk
      refine this.congr ?_
      simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
  · intro t ht
    simp only [Sg3, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · have := good_Dsq_gen7 hL (j := 1) (k := t) (by omega) (by omega) hz1 hk0 hkz
      refine this.congr ?_
      simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
    · refine (good_Dsq_p hL hp5).congr ?_
      simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
    · have := good_Dsq_gen7 hL (j := 5) (k := p + k) (by omega) (by omega) hj5 (by omega) hpk
      refine this.congr ?_
      simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
    · refine (good_Dsq_2p hL hp5).congr ?_
      simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
    · have := good_Dsq_gen7 hL (j := 9) (k := 2 * p + k) (by omega) (by omega) hj9 (by omega) h2pk
      refine this.congr ?_
      simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]
  · intro t h1 ht hn
    exact reg3 S h1 (by have := S.hN; omega) hn
  · exact hk4_of (j := 1) (o := o) (by rw [one_mul]; exact S.hk.1)

end Inst3

end CatalanCore.Arith.Hybrid
