module

public import CatalanCore.Arith.Hybrid.DefGKVec3

@[expose] public section

/-!
# GK, class 3: the defect rows and columns `L = C - αA`, `L' = B - Aβ` (`hL`, `hL'` of `tcore_vec`)
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid

section Fin3

variable {p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

/-- Row partners (zone rows `r + 2i`). -/
noncomputable def alphaM (Fr : Frame) (p r m : ℕ) : Matrix (Fin m) (Fin r) ℚ[X] :=
  Matrix.of fun i c => C (avec p r (r + 2 * (i : ℕ)) c)

/-- Column partners (zone columns `r + 2j + 1`). -/
noncomputable def betaM (Fr : Frame) (p r m : ℕ) : Matrix (Fin r) (Fin m) ℚ[X] :=
  Matrix.of fun c j => C (avec p r (r + 2 * (j : ℕ) + 1) c)

lemma avec_int (h13 : 13 ≤ p) (hp : p ≠ 139) (u : ℕ) (c : Fin r) : Int1 p (C (avec p r u c)) :=
  int1_C_of_good (good_avec h13 hp u c)

lemma gn_C_mul_X_le (h13 : 13 ≤ p) (hp : p ≠ 139) (u : ℕ) (c : Fin r) :
    gn p (C (avec p r u c) * X) ≤ 1 := by
  rw [gn_mul, gn_X, mul_one]; exact avec_int h13 hp u c

lemma entL (i : Fin m) (c : Fin r) :
    ((Matrix.of (fullEntry Fr r m)).toBlocks₂₁ - alphaM Fr p r m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) i c =
      C (Fr.Mn (r + 2 * (i : ℕ)) (c : ℕ) -
        ∑ c' : Fin r, avec p r (r + 2 * (i : ℕ)) c' * Fr.Mn (c' : ℕ) (c : ℕ)) -
        C (avec p r (r + 2 * (i : ℕ)) c) * X := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, alphaM, Matrix.of_apply, Matrix.toBlocks₂₁,
    Matrix.toBlocks₁₁, fullEntry, Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← C_mul, ← map_sum, map_sub, zero_add]
  ring

lemma entL' (c : Fin r) (j : Fin m) :
    ((Matrix.of (fullEntry Fr r m)).toBlocks₁₂ - (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ *
        betaM Fr p r m) c j =
      C (Fr.Mn (c : ℕ) (r + 2 * (j : ℕ) + 1) -
        ∑ c' : Fin r, Fr.Mn (c : ℕ) (c' : ℕ) * avec p r (r + 2 * (j : ℕ) + 1) c') -
        C (avec p r (r + 2 * (j : ℕ) + 1) c) * X := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, betaM, Matrix.of_apply, Matrix.toBlocks₁₂,
    Matrix.toBlocks₁₁, fullEntry, Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, ← C_mul, ← map_sum, map_sub, zero_add]
  ring

theorem hL_bound (hL : LamData Fr 1) (S : GKS3 p r m k) (i : Fin m) (c : Fin r) :
    gn p (((Matrix.of (fullEntry Fr r m)).toBlocks₂₁ - alphaM Fr p r m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) i c) ≤ p := by
  have h13 := S.p13
  have hi := i.2
  rw [entL]
  refine (gn_sub_le _ _).trans (max_le ?_ ?_)
  · exact lbnd hL S (u := r + 2 * (i : ℕ)) (by omega) (by omega) c
  · refine (gn_C_mul_X_le h13 S.h139 _ c).trans ?_
    have : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    exact this

theorem hL'_bound (hL : LamData Fr 1) (S : GKS3 p r m k) (c : Fin r) (j : Fin m) :
    gn p (((Matrix.of (fullEntry Fr r m)).toBlocks₁₂ - (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ *
        betaM Fr p r m) c j) ≤ p := by
  have h13 := S.p13
  have hj := j.2
  rw [entL']
  refine (gn_sub_le _ _).trans (max_le ?_ ?_)
  · have := lbnd hL S (u := r + 2 * (j : ℕ) + 1) (by omega) (by omega) c
    have e : Fr.Mn (c : ℕ) (r + 2 * (j : ℕ) + 1) -
        ∑ c' : Fin r, Fr.Mn (c : ℕ) (c' : ℕ) * avec p r (r + 2 * (j : ℕ) + 1) c' =
        Fr.Mn (r + 2 * (j : ℕ) + 1) (c : ℕ) -
        ∑ c' : Fin r, avec p r (r + 2 * (j : ℕ) + 1) c' * Fr.Mn (c' : ℕ) (c : ℕ) := by
      rw [Mn_symm (c : ℕ)]
      congr 1
      refine Finset.sum_congr rfl (fun c' _ => ?_)
      rw [mul_comm, Mn_symm (c : ℕ)]
    rw [e]; exact this
  · refine (gn_C_mul_X_le h13 S.h139 _ c).trans ?_
    have : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    exact this

lemma alphaA_entry (i : Fin m) (c : Fin r) :
    (alphaM Fr p r m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) i c =
      C (∑ c' : Fin r, avec p r (r + 2 * (i : ℕ)) c' * Fr.Mn (c' : ℕ) (c : ℕ)) +
        C (avec p r (r + 2 * (i : ℕ)) c) * X := by
  simp only [Matrix.mul_apply, alphaM, Matrix.of_apply, Matrix.toBlocks₁₁, fullEntry,
    Frame.hybRow, Frame.hybCol, Sum.elim_inl]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← C_mul, ← map_sum, zero_add]
  ring

lemma alphaB_entry (i j : Fin m) :
    (alphaM Fr p r m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₂) i j =
      C (∑ c : Fin r, avec p r (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (r + 2 * (j : ℕ) + 1)) := by
  simp only [Matrix.mul_apply, alphaM, Matrix.of_apply, Matrix.toBlocks₁₂, fullEntry,
    Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr, zero_add, ← C_mul, ← map_sum]

lemma Cbeta_entry (i j : Fin m) :
    ((Matrix.of (fullEntry Fr r m)).toBlocks₂₁ * betaM Fr p r m) i j =
      C (∑ c : Fin r, Fr.Mn (r + 2 * (i : ℕ)) (c : ℕ) * avec p r (r + 2 * (j : ℕ) + 1) c) := by
  simp only [Matrix.mul_apply, betaM, Matrix.of_apply, Matrix.toBlocks₂₁, fullEntry,
    Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr, zero_add, ← C_mul, ← map_sum]

lemma alphaAbeta_entry (i j : Fin m) :
    (alphaM Fr p r m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ * betaM Fr p r m) i j =
      C (∑ c' : Fin r, (∑ c : Fin r, avec p r (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (c' : ℕ)) *
          avec p r (r + 2 * (j : ℕ) + 1) c') +
        C (∑ c : Fin r, avec p r (r + 2 * (i : ℕ)) c * avec p r (r + 2 * (j : ℕ) + 1) c) * X := by
  rw [Matrix.mul_apply]
  have h : ∀ c' : Fin r, (alphaM Fr p r m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) i c' *
      betaM Fr p r m c' j =
      C ((∑ c : Fin r, avec p r (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (c' : ℕ)) *
        avec p r (r + 2 * (j : ℕ) + 1) c') +
      C (avec p r (r + 2 * (i : ℕ)) c' * avec p r (r + 2 * (j : ℕ) + 1) c') * X := by
    intro c'
    rw [alphaA_entry]
    simp only [betaM, Matrix.of_apply]
    rw [C_mul, C_mul]; ring
  rw [Finset.sum_congr rfl (fun c' _ => h c'), Finset.sum_add_distrib, ← map_sum,
    ← Finset.sum_mul, ← map_sum]

lemma entDelta (i j : Fin m) :
    ((Matrix.of (fullEntry Fr r m)).toBlocks₂₂ - alphaM Fr p r m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₂ -
      (Matrix.of (fullEntry Fr r m)).toBlocks₂₁ * betaM Fr p r m +
      alphaM Fr p r m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ * betaM Fr p r m) i j =
    C (Fr.Mn (r + 2 * (i : ℕ)) (r + 2 * (j : ℕ) + 1) -
        ∑ c : Fin r, avec p r (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (r + 2 * (j : ℕ) + 1) -
        ∑ c : Fin r, Fr.Mn (r + 2 * (i : ℕ)) (c : ℕ) * avec p r (r + 2 * (j : ℕ) + 1) c +
        ∑ c' : Fin r, (∑ c : Fin r, avec p r (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (c' : ℕ)) *
          avec p r (r + 2 * (j : ℕ) + 1) c') +
      C (∑ c : Fin r, avec p r (r + 2 * (i : ℕ)) c * avec p r (r + 2 * (j : ℕ) + 1) c) * X := by
  simp only [Matrix.add_apply, Matrix.sub_apply, alphaB_entry, Cbeta_entry, alphaAbeta_entry,
    Matrix.toBlocks₂₂, Matrix.of_apply, fullEntry, Frame.hybRow, Frame.hybCol, Sum.elim_inr,
    zero_add, map_sub, map_add]
  ring

end Fin3

end CatalanCore.Arith.Hybrid
