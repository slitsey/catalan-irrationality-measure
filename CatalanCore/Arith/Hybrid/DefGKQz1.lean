module

public import CatalanCore.Arith.Hybrid.DefGKLz1
public import CatalanCore.Arith.Hybrid.DefGKQz3

@[expose] public section

/-!
# GK, class 1: the table `Qz1` is the `p²`-level residue of `Mn`
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid.GK1

open CatalanCore.Arith.Hybrid

section Qz1

variable {o p : ℕ} [Fact p.Prime] {k : ℕ}

lemma Pv_eq_Pz {r m : ℕ} (S : GKS1 o p r m k) (n : ℕ) :
    Lv (Sg1 p k) (resD1 p k) n = (Pz1 p k n : ZMod p) * 1764⁻¹ := by
  have h13 := S.p13
  have hkp := S.kp; have hk0 := S.k0
  have n1764' := n1764 (p := p) h13
  have n3' := n3 (p := p) h13
  have n7' := n7 (p := p) h13
  have n2' := n2 (p := p) h13
  have n4' := n4 (p := p) h13
  have n9' := n9 (p := p) h13
  have n49' := n49 (p := p) h13
  have e1 : k ≠ p := by omega
  have e2 : k ≠ p + k := by omega
  have e3 : p ≠ p + k := by omega
  have e4 : k ≠ 2 * p := by omega
  have e5 : p ≠ 2 * p := by omega
  have e6 : p + k ≠ 2 * p := by omega
  have np : p ≠ 0 := by omega
  have nk : k ≠ 0 := by omega
  rw [Pv_Sg1 S]
  unfold Pz1
  have r1 : resD1 p k k = ((-3136 : ℤ) : ZMod p) * 1764⁻¹ := by
    simp [resD1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
      e6.symm]
    field_simp; norm_num
  have r2 : resD1 p k p = ((1764 : ℤ) : ZMod p) * 1764⁻¹ := by
    simp [resD1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
      e6.symm]
    field_simp
  have r3 : resD1 p k (p + k) = ((-576 : ℤ) : ZMod p) * 1764⁻¹ := by
    simp [resD1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
      e6.symm]
    field_simp; norm_num
  have r4 : resD1 p k (2 * p) = ((441 : ℤ) : ZMod p) * 1764⁻¹ := by
    simp [resD1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
      e6.symm]
    field_simp; norm_num
  rw [ite_cast_mul _ _ _ _ r1, ite_cast_mul _ _ _ _ r2, ite_cast_mul _ _ _ _ r3,
    ite_cast_mul _ _ _ _ r4]
  push_cast
  ring

variable {Fr : Frame}

theorem good_Qz1_lt (hL : LamData Fr o) {r m : ℕ} (S : GKS1 o p r m k) {A B : ℕ} (hAB : A < B)
    (hB : B < r + 2 * m) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) ((Qz1 p k A B : ZMod p) * 56448⁻¹) := by
  have h13 := S.p13
  have hp5 : 5 ≤ p := by omega
  have hN := S.hN; have hkk := S.hk
  have hk := S.hk
  have D := sgData1 hL S
  have n56448' := n56448 (p := p) h13
  have n84' := n84 (p := p) h13
  have n16' := n16 (p := p) h13
  have n32' := n32 (p := p) h13
  by_cases h1 : B - A = p
  · have := tab_PP hL hp5 D hAB hB h1
    refine this.congr ?_
    rw [Lv_eq_Lz S, Lv_eq_Lz S]
    unfold Qz1
    rw [if_pos hAB, if_pos h1]
    push_cast
    field_simp
    ring
  by_cases h2 : B - A = 2 * p
  · have := tab_P2P hL hp5 D hAB hB h2
    refine this.congr ?_
    rw [Lv_eq_Lz S, Lv_eq_Lz S]
    unfold Qz1
    rw [if_pos hAB, if_neg h1, if_pos h2]
    push_cast
    field_simp
    ring
  · have := tab_P0 hL hp5 D hAB hB (sub_ne3 hAB (by omega) h1 h2)
    refine this.congr ?_
    unfold Qz1
    rw [if_pos hAB, if_neg h1, if_neg h2]
    simp

theorem good_Qz1 (hL : LamData Fr o) {r m : ℕ} (S : GKS1 o p r m k) {A B : ℕ}
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) (hd : A = B → A < r) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) ((Qz1 p k A B : ZMod p) * 56448⁻¹) := by
  have h13 := S.p13
  have hp5 : 5 ≤ p := by omega
  rcases lt_trichotomy A B with h | h | h
  · exact good_Qz1_lt hL S h hB
  · subst h
    have hAr := hd rfl
    have D := sgData1 hL S
    have n1764' := n1764 (p := p) h13
    have n56448' := n56448 (p := p) h13
    have n16' := n16 (p := p) h13
    have := tab_D hL hp5 D hA
    refine this.congr ?_
    rw [Pv_eq_Pz S, Qz1_diag]
    push_cast
    field_simp
    ring
  · rw [Mn_symm, Qz1_symm]
    exact good_Qz1_lt hL S h hA

end Qz1

end CatalanCore.Arith.Hybrid.GK1
