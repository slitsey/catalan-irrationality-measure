module
public import CatalanCore.Li2.NV.ReductionData
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Prod.Lex
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped BigOperators
noncomputable section
namespace CatalanCore.Li2.NV
private theorem parity_block_det {F : Type*} [CommRing F] {ℓ : ℕ} (m : Fin ℓ → ℕ)
    (even : Fin ℓ → Prop) [DecidablePred even]
    (M : Matrix (Σ s, Fin (m s)) (Σ s, Fin (m s)) F)
    (hSame : ∀ P Q, (even P.1 ↔ even Q.1) → P.1 ≠ Q.1 → M P Q = 0)
    (hBA : ∀ P Q, ¬even P.1 → even Q.1 → M P Q = 0) :
    M.det = ∏ s : Fin ℓ, (Matrix.of fun i j : Fin (m s) => M ⟨s,i⟩ ⟨s,j⟩).det := by
  classical
  let key : Fin ℓ → Lex (ℕ × ℕ) := fun s => toLex (if even s then 0 else 1,s.val)
  have hinj : Function.Injective key := by
    intro s t h
    exact Fin.ext (congrArg (fun p : Lex (ℕ × ℕ) => (ofLex p).2) h)
  letI : LinearOrder (Fin ℓ) := LinearOrder.lift' key hinj
  letI : LT (Fin ℓ) := (LinearOrder.lift' key hinj).toLT
  letI : LE (Fin ℓ) := (LinearOrder.lift' key hinj).toLE
  have htri : M.BlockTriangular Sigma.fst := by
    intro P Q hlt
    have hne : P.1 ≠ Q.1 := by
      intro he
      have hh : key Q.1 < key P.1 := hlt
      rw [he] at hh
      exact lt_irrefl _ hh
    by_cases hP : even P.1 <;> by_cases hQ : even Q.1
    · exact hSame P Q (iff_of_true hP hQ) hne
    · change key Q.1 < key P.1 at hlt
      simp only [key,if_neg hQ,if_pos hP,Prod.Lex.toLex_lt_toLex] at hlt
      omega
    · exact hBA P Q hP hQ
    · exact hSame P Q (iff_of_false hP hQ) hne
  rw [htri.det_fintype]
  apply Finset.prod_congr rfl
  intro s hs
  let e : {P : Σ t, Fin (m t) // P.1 = s} ≃ Fin (m s) :=
    { toFun := fun ⟨⟨t,i⟩,ht⟩ => by dsimp at ht; subst t; exact i
      invFun := fun i => ⟨⟨s,i⟩,rfl⟩
      left_inv := by rintro ⟨⟨t,i⟩,ht⟩; dsimp at ht; subst t; rfl
      right_inv := by intro i; rfl }
  exact
    (Matrix.det_submatrix_equiv_self e.symm (M.toSquareBlock Sigma.fst s)).symm

open NVMod
private theorem reduction_det_tiefree_eq (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hR : Range n ℓ) (ht : ¬tied n ℓ) (R : ReductionData z n ℓ)
    (upper : Matrix (Ix n ℓ) (Ix n ℓ) (ZMod ℓ)) :
    (expectedReduction R upper).det =
      ∏ s : Fin ℓ, redU R s^(m n ℓ s)*redK R (classKey n ℓ s) := by
  classical
  have hC : Cset n ℓ=∅ := Finset.not_nonempty_iff_eq_empty.mp
    (fun h => ht ((class_table n ℓ hR).2.2.mpr h))
  have hS : S0red R=0 := by simp [S0red,hC]
  have hdiag : ∀ P Q : Ix n ℓ, expectedDiagonal R P Q =
      if P.1=Q.1 then redU R P.1*redMoment R (classKey n ℓ P.1) (P.2.val+Q.2.val) else 0 := by
    intro P Q
    simp [expectedDiagonal,hC,hS]
  have hfactor := parity_block_det (F := ZMod ℓ) (ℓ := ℓ)
    (fun s : Fin ℓ => m n ℓ s) (fun s => nu n ℓ s%2=0)
    (expectedReduction R upper) (by
      intro P Q hpq hne
      change expectedReduction R upper P Q=0
      have hp := Int.emod_nonneg (nu n ℓ P.1) (by norm_num : (2:ℤ)≠0)
      have hq := Int.emod_nonneg (nu n ℓ Q.1) (by norm_num : (2:ℤ)≠0)
      have hp2 := Int.emod_lt_of_pos (nu n ℓ P.1) (by norm_num : (0:ℤ)<2)
      have hq2 := Int.emod_lt_of_pos (nu n ℓ Q.1) (by norm_num : (0:ℤ)<2)
      have he : nu n ℓ P.1%2=nu n ℓ Q.1%2 := by omega
      simp [expectedReduction,he,hdiag,hne]) (by
      intro P Q hp hq
      change expectedReduction R upper P Q=0
      have he : nu n ℓ P.1%2≠nu n ℓ Q.1%2 := by omega
      simp [expectedReduction,he,hp])
  rw [hfactor]
  apply Finset.prod_congr rfl
  intro s hs
  have he : (Matrix.of fun i j : Fin (m n ℓ s) =>
      expectedReduction R upper ⟨s,i⟩ ⟨s,j⟩) =
      redU R s • (Matrix.of fun i j : Fin (m n ℓ s) =>
        redMoment R (classKey n ℓ s) (i.val+j.val)) := by
    ext i j
    simp [expectedReduction,hdiag]
  rw [he,Matrix.det_smul,Fintype.card_fin]
  rfl
private theorem class_parameters_valid (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) :
    k n ℓ < 4 ∧ (1 ≤ n/ℓ ∨ k n ℓ = 3) := by
  have hp := (Fact.out : ℓ.Prime).pos
  have hr := Nat.mod_lt n hp
  have hd := Nat.mod_add_div (4*(n%ℓ)) ℓ
  have he := Nat.mod_add_div n ℓ
  have hk : k n ℓ < 4 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  refine ⟨hk,?_⟩
  by_cases hq : 1 ≤ n/ℓ
  · exact Or.inl hq
  · right
    have hq0 : n/ℓ=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (lt_of_not_ge hq))
    have hn : n<ℓ := (Nat.div_eq_zero_iff.mp hq0).resolve_left (by omega)
    have hlarge : 3*ℓ<4*n := (hR.2.resolve_left (by omega)).2
    have hk3 : 3 ≤ k n ℓ := by
      unfold k
      rw [Nat.mod_eq_of_lt hn]
      exact (Nat.le_div_iff_mul_le hp).mpr (by omega)
    omega
private theorem class_key_mem (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s : Fin ℓ) : classKey n ℓ s ∈ neededAtValid (n/ℓ) (k n ℓ) := by
  classical
  rw [neededAtValid_eq _ _ (class_parameters_valid n ℓ hR)]
  have hp := (Fact.out : ℓ.Prime).pos
  have hr := Nat.mod_lt n hp
  have hr' := Nat.mod_lt (4*(n%ℓ)) hp
  have hd := Nat.mod_add_div (4*(n%ℓ)) ℓ
  have hv := class_parameters_valid n ℓ hR
  change r' n ℓ + ℓ*k n ℓ = 4*r n ℓ at hd
  have ht := (class_counts n ℓ hR).2.2 s
  have ha := congrArg Prod.fst ht
  have hc := congrArg Prod.snd ht
  dsimp only [typeAC] at ha hc
  by_cases h0 : s.val=0
  · simp only [h0,ne_eq,not_true_eq_false,false_and,ite_false,Nat.add_zero] at ha hc
    have hm : m n ℓ 0=2*(n/ℓ)+k n ℓ := by unfold m; rw [ha,hc]; omega
    simp only [classKey,h0,ite_true,ha,hc,hm,neededAt]
    by_cases hk : 1 ≤ k n ℓ
    · simp [hk]
    · have hq : 1 ≤ n/ℓ := by omega
      have hk2 : k n ℓ ≤ 2 := by omega
      simp [hk,hq,hk2]
  · by_cases hs : s.val≤r n ℓ <;> by_cases hs' : s.val≤r' n ℓ
    · simp only [h0,ne_eq,not_false_eq_true,true_and,hs,hs',ite_true] at ha hc
      have hm : m n ℓ s=2*(n/ℓ)+k n ℓ-1 := by unfold m; rw [ha,hc]; omega
      simp [classKey,h0,ha,hc,hm,neededAt]
    · simp only [h0,ne_eq,not_false_eq_true,true_and,hs,hs',ite_true,ite_false,Nat.add_zero] at ha hc
      have hm : m n ℓ s=2*(n/ℓ)+k n ℓ-2 := by unfold m; rw [ha,hc]; omega
      have hk : 1 ≤ k n ℓ := by
        by_contra h
        have hk0 : k n ℓ=0 := by omega
        rw [hk0,mul_zero,add_zero] at hd
        omega
      simp [classKey,h0,ha,hc,hm,neededAt,hk]
    · simp only [h0,ne_eq,not_false_eq_true,true_and,hs,hs',ite_true,ite_false,Nat.add_zero] at ha hc
      have hm : m n ℓ s=2*(n/ℓ)+k n ℓ+1 := by unfold m; rw [ha,hc]; omega
      have hk : k n ℓ ≤ 2 := by
        have hr0 : r n ℓ < ℓ := hr
        have hr1 : r' n ℓ < ℓ := hr'
        by_contra h
        have hk3 : k n ℓ=3 := by omega
        rw [hk3] at hd
        omega
      have hq : 1 ≤ n/ℓ := by omega
      simp [classKey,h0,ha,hc,hm,neededAt,hq,hk]
    · simp only [h0,ne_eq,not_false_eq_true,true_and,hs,hs',ite_false,Nat.add_zero] at ha hc
      have hm : m n ℓ s=2*(n/ℓ)+k n ℓ := by unfold m; rw [ha,hc]; omega
      simp [classKey,h0,ha,hc,hm,neededAt]

def AllConstantsUnit (z : ℚ) (q k ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ A ∈ neededAtValid q k, Unit ℓ (K A z:Padic ℓ)
theorem reduction_det_tiefree (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (ht : ¬tied n ℓ)
    (hK : AllConstantsUnit z (n/ℓ) (k n ℓ) ℓ)
    (R : ReductionData z n ℓ) (upper : Matrix (Ix n ℓ) (Ix n ℓ) (ZMod ℓ)) :
  (expectedReduction R upper).det=
    ∏ s : Fin ℓ, redU R s^(m n ℓ s)*redK R (classKey n ℓ s) ∧
      (expectedReduction R upper).det≠0 := by
  classical
  have he := reduction_det_tiefree_eq z n ℓ hR ht R upper
  refine ⟨he,?_⟩
  rw [he]
  apply Finset.prod_ne_zero_iff.mpr
  intro s hs
  apply mul_ne_zero (pow_ne_zero _ (redU_ne_zero z n ℓ hz R s))
  have hc := (class_counts n ℓ hR).1 s
  have hp := (Fact.out : ℓ.Prime).pos
  apply redK_ne_zero z n ℓ R (classKey n ℓ s)
  · change a n ℓ s ≤ c n ℓ s
    omega
  · change c n ℓ s < ℓ
    omega
  · exact hK _ (class_key_mem n ℓ hR s)
#print axioms reduction_det_tiefree
end CatalanCore.Li2.NV
