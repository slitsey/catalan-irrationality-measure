module

public import CatalanCore.Arith.Hybrid.DefGKLz3

@[expose] public section

/-!
# GK, class 3: the table `Qz3` is the `p²`-level residue of `Mn`
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section Qz3

variable {p : ℕ} [Fact p.Prime] {k : ℕ}

lemma Pv_eq_Pz {r m : ℕ} (S : GKS3 p r m k) (n : ℕ) :
    Lv (Sg3 p k) (resD3 p k) n = (Pz3 p k n : ZMod p) * 8100⁻¹ := by
  have h13 := S.p13
  have hkp := S.kp; have hk0 := S.k0
  have n8100' := n8100 (p := p) h13
  have n5' := n5 (p := p) h13
  have n9' := n9 (p := p) h13
  have n2' := n2 (p := p) h13
  have n4' := n4 (p := p) h13
  have n25' := n25 (p := p) h13
  have n81' := n81 (p := p) h13
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
  have np : p ≠ 0 := by omega
  have nk : k ≠ 0 := by omega
  rw [Pv_Sg3 S]
  unfold Pz3
  have r1 : resD3 p k k = ((-129600 : ℤ) : ZMod p) * 8100⁻¹ := by
    simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm,
      e4.symm, e5.symm, e6.symm]
    field_simp; norm_num
  have r2 : resD3 p k p = ((8100 : ℤ) : ZMod p) * 8100⁻¹ := by
    simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm,
      e4.symm, e5.symm, e6.symm]
    field_simp
  have r3 : resD3 p k (p + k) = ((-5184 : ℤ) : ZMod p) * 8100⁻¹ := by
    simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm,
      e4.symm, e5.symm, e6.symm]
    field_simp; norm_num
  have r4 : resD3 p k (2 * p) = ((2025 : ℤ) : ZMod p) * 8100⁻¹ := by
    simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm,
      e4.symm, e5.symm, e6.symm]
    field_simp; norm_num
  have r5 : resD3 p k (2 * p + k) = ((-1600 : ℤ) : ZMod p) * 8100⁻¹ := by
    simp [resD3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm,
      e4.symm, e5.symm, e6.symm]
    field_simp; norm_num
  rw [ite_cast_mul _ _ _ _ r1, ite_cast_mul _ _ _ _ r2, ite_cast_mul _ _ _ _ r3,
    ite_cast_mul _ _ _ _ r4, ite_cast_mul _ _ _ _ r5]
  push_cast
  ring

lemma sub_ne3 {A B : ℕ} (hAB : A < B) (hB : B < 3 * p) (h1 : B - A ≠ p) (h2 : B - A ≠ 2 * p) :
    ((B : ZMod p) - A) ≠ 0 := by
  have hp0 := (Fact.out : p.Prime).pos
  have : (((B - A : ℕ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    rintro ⟨c, hc⟩
    rcases c with _ | _ | _ | c
    · omega
    · omega
    · omega
    · have : p * (c + 1 + 1 + 1) ≥ p * 3 := Nat.mul_le_mul_left p (by omega)
      omega
  rwa [Nat.cast_sub hAB.le] at this

variable {Fr : Frame}

theorem good_Qz3_lt (hL : LamData Fr) {r m : ℕ} (S : GKS3 p r m k) {A B : ℕ} (hAB : A < B)
    (hB : B < r + 2 * m) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) ((Qz3 p k A B : ZMod p) * 129600⁻¹) := by
  have h13 := S.p13
  have hp5 : 5 ≤ p := by omega
  have hN := S.hN
  have D := sgData3 hL S
  have n129600' := n129600 (p := p) h13
  have n90' := n90 (p := p) h13
  have n16' := n16 (p := p) h13
  have n32' := n32 (p := p) h13
  by_cases h1 : B - A = p
  · have := tab_PP hL hp5 D hAB hB h1
    refine this.congr ?_
    rw [Lv_eq_Lz S, Lv_eq_Lz S]
    unfold Qz3
    rw [if_pos hAB, if_pos h1]
    push_cast
    field_simp
    ring
  by_cases h2 : B - A = 2 * p
  · have := tab_P2P hL hp5 D hAB hB h2
    refine this.congr ?_
    rw [Lv_eq_Lz S, Lv_eq_Lz S]
    unfold Qz3
    rw [if_pos hAB, if_neg h1, if_pos h2]
    push_cast
    field_simp
    ring
  · have := tab_P0 hL hp5 D hAB hB (sub_ne3 hAB (by omega) h1 h2)
    refine this.congr ?_
    unfold Qz3
    rw [if_pos hAB, if_neg h1, if_neg h2]
    simp

theorem good_Qz3 (hL : LamData Fr) {r m : ℕ} (S : GKS3 p r m k) {A B : ℕ}
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) (hd : A = B → A < r) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) ((Qz3 p k A B : ZMod p) * 129600⁻¹) := by
  have h13 := S.p13
  have hp5 : 5 ≤ p := by omega
  rcases lt_trichotomy A B with h | h | h
  · exact good_Qz3_lt hL S h hB
  · subst h
    have hAr := hd rfl
    have D := sgData3 hL S
    have n8100' := n8100 (p := p) h13
    have n129600' := n129600 (p := p) h13
    have n16' := n16 (p := p) h13
    have := tab_D hL hp5 D hA
    refine this.congr ?_
    rw [Pv_eq_Pz S, Qz3_diag]
    push_cast
    field_simp
    ring
  · rw [Mn_symm, Qz3_symm]
    exact good_Qz3_lt hL S h hA

end Qz3

end CatalanCore.Arith.Hybrid
