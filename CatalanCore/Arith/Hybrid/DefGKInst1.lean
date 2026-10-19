module

public import CatalanCore.Arith.Hybrid.DefGKTab
public import CatalanCore.Arith.Hybrid.DefGKInst3

@[expose] public section

/-!
# GK, class `p ≡ 1 (mod 4)`: the singular set `{K, p, p+K, 2p}` (`4K = 3p+1`)

`GKS1 p r m k` : `13 ≤ p`, `4k = 3p+1`, `2p < r`, `4(r + 2m) ≤ 11p+1`, `0 < m`, `p ≠ 1009`.
`sgData1`: the `SgData` of the singular set with the residues of `p Δ_t` and `p² D_t`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid.GK1

open CatalanCore.Arith.Hybrid

section Inst1

variable {p : ℕ} [Fact p.Prime]

/-! ### The data -/

/-- The singular set of class 1. -/
def Sg1 (p k : ℕ) : Finset ℕ := {k, p, p + k, 2 * p}

/-- Residues of `p Δ_t`. -/
noncomputable def res1 (p k : ℕ) (t : ℕ) : ZMod p :=
  if t = k then -(4 * (3 : ZMod p)⁻¹) else if t = p then 1
  else if t = p + k then -(4 * (7 : ZMod p)⁻¹) else (2 : ZMod p)⁻¹

/-- Residues of `p² D_t`. -/
noncomputable def resD1 (p k : ℕ) (t : ℕ) : ZMod p :=
  if t = k then -(16 * ((3 : ZMod p)⁻¹) ^ 2) else if t = p then 1
  else if t = p + k then -(16 * ((7 : ZMod p)⁻¹) ^ 2) else (4 : ZMod p)⁻¹

/-- Hypotheses of the class-1 GK setting. -/
structure GKS1 (p r m k : ℕ) : Prop where
  p13 : 13 ≤ p
  hk : 4 * k = 3 * p + 1
  hr : 2 * p < r
  hN : 4 * (r + 2 * m) ≤ 11 * p + 1
  hm : 0 < m
  h1009 : p ≠ 1009

lemma GKS1.kp {r m k : ℕ} (S : GKS1 p r m k) : k < p := by have := S.p13; have := S.hk; omega
lemma GKS1.k0 {r m k : ℕ} (S : GKS1 p r m k) : 0 < k := by have := S.hk; omega

lemma reg1 {r m k : ℕ} (S : GKS1 p r m k) {t : ℕ} (h1 : 1 ≤ t) (ht : t < 2 * p + k)
    (hn : t ∉ Sg1 p k) : Reg p t := by
  have hp0 := (Fact.out : p.Prime).pos
  have hkp := S.kp
  have h13 := S.p13
  have hk := S.hk
  refine ⟨?_, ?_⟩
  · rw [Ne, ZMod.natCast_eq_zero_iff]
    rintro ⟨c, hc⟩
    rcases c with _ | _ | _ | c
    · omega
    · exact hn (by simp [Sg1]; omega)
    · exact hn (by simp [Sg1]; omega)
    · have : p * (c + 1 + 1 + 1) ≥ p * 3 := Nat.mul_le_mul_left p (by omega)
      omega
  · intro h0
    have h4k : (4 : ZMod p) * (k : ZMod p) = 1 := by
      have : ((4 * k : ℕ) : ZMod p) = ((3 * p + 1 : ℕ) : ZMod p) := by rw [hk]
      push_cast at this
      simpa [ZMod.natCast_self] using this
    have h4 : (4 : ZMod p) ≠ 0 := four_ne_zmod p (by omega)
    have : (t : ZMod p) = (k : ZMod p) := by
      have : (4 : ZMod p) * ((t : ZMod p) - k) = 0 := by linear_combination h0 - h4k
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h h4
      · exact sub_eq_zero.1 h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rw [Nat.mod_eq_of_lt hkp] at this
    by_cases htp : t < p
    · rw [Nat.mod_eq_of_lt htp] at this; exact hn (by simp [Sg1]; omega)
    · by_cases ht2 : t < 2 * p
      · have : t % p = t - p := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        exact hn (by simp [Sg1]; omega)
      · have : t % p = t - 2 * p := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)]
          omega
        omega

theorem sgData1 {Fr : Frame} (hL : LamData Fr) {r m k : ℕ} (S : GKS1 p r m k) :
    SgData Fr p (r + 2 * m) (Sg1 p k) (res1 p k) (resD1 p k) := by
  have hp0 := (Fact.out : p.Prime).pos
  have hkp := S.kp
  have hk0 := S.k0
  have h13 := S.p13
  have hk := S.hk
  have hp5 : 5 ≤ p := by omega
  have hkz : ((k : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt hk0 hkp
  have hj3 : (((3 : ℕ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
    have := Nat.le_of_dvd (by norm_num) hd; omega
  have hj7 : (((7 : ℕ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
    have := Nat.le_of_dvd (by norm_num) hd; omega
  have hpk : (((p + k : ℕ)) : ZMod p) ≠ 0 := by
    rw [Nat.cast_add, ZMod.natCast_self, zero_add]; exact hkz
  have np : p ≠ 0 := by omega
  have nk : k ≠ 0 := by omega
  have e1 : k ≠ p := by omega
  have e2 : k ≠ p + k := by omega
  have e3 : p ≠ p + k := by omega
  have e4 : k ≠ 2 * p := by omega
  have e5 : p ≠ 2 * p := by omega
  have e6 : p + k ≠ 2 * p := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [Sg1, Finset.mem_insert, Finset.mem_singleton] at ht
    omega
  · intro t ht
    simp only [Sg1, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · have := good_Delta_gen7 hL (j := 3) (k := t) (by omega) (by omega) hj3 hkz
      refine this.congr ?_
      simp [res1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
        e6.symm]
    · refine (good_Delta_p hL hp5).congr ?_
      simp [res1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
        e6.symm]
    · have := good_Delta_gen7 hL (j := 7) (k := p + k) (by omega) (by omega) hj7 hpk
      refine this.congr ?_
      simp [res1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
        e6.symm]
    · refine (good_Delta_2p hL hp5).congr ?_
      simp [res1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
        e6.symm]
  · intro t ht
    simp only [Sg1, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · have := good_Dsq_gen7 hL (j := 3) (k := t) (by omega) (by omega) hj3 hk0 hkz
      refine this.congr ?_
      simp [resD1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
        e6.symm]
    · refine (good_Dsq_p hL hp5).congr ?_
      simp [resD1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
        e6.symm]
    · have := good_Dsq_gen7 hL (j := 7) (k := p + k) (by omega) (by omega) hj7 (by omega) hpk
      refine this.congr ?_
      simp [resD1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
        e6.symm]
    · refine (good_Dsq_2p hL hp5).congr ?_
      simp [resD1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
        e6.symm]
  · intro t h1 ht hn
    exact reg1 S h1 (by have := S.hN; omega) hn

end Inst1

end CatalanCore.Arith.Hybrid.GK1
