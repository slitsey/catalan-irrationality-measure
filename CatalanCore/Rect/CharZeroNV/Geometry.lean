module

public import CatalanCore.Rect.CharZeroNV.Space

@[expose] public section

/-! # Node geometry for the characteristic-zero selector

The rows and columns may partition the consecutive tail arbitrarily, provided
their common nodes are the initial interval and the square indexing aligns
those common nodes.
-/

open Polynomial Finset

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

structure NodeGeometry (r m : ℕ) where
  rows : Finset K
  cols : Finset K
  equiv : rows ≃ cols
  card_rows : rows.card = r + m
  union_eq : rows ∪ cols = natNodes (r + 2 * m)
  inter_eq : rows ∩ cols = natNodes r
  align : ∀ (i : Fin r) (hi : (i.val : K) ∈ rows),
    (equiv ⟨(i.val : K), hi⟩).val = (i.val : K)

namespace NodeGeometry

variable {r m : ℕ} (G : NodeGeometry (K := K) r m)

lemma card_cols : G.cols.card = r + m := by
  have h := Fintype.card_congr G.equiv
  simpa [G.card_rows] using h.symm

lemma common_mem (i : Fin r) : (i.val : K) ∈ G.rows ∧ (i.val : K) ∈ G.cols := by
  apply Finset.mem_inter.mp
  rw [G.inter_eq]
  exact mem_natNodes.mpr ⟨i.val, i.isLt, rfl⟩

def common (i : Fin r) : G.rows := ⟨(i.val : K), (G.common_mem i).1⟩

lemma common_injective : Function.Injective G.common := by
  intro i j h
  apply Fin.ext
  exact Nat.cast_injective (congrArg Subtype.val h)

lemma mem_union {i : ℕ} (hi : i < r + 2 * m) :
    (i : K) ∈ G.rows ∨ (i : K) ∈ G.cols := by
  apply Finset.mem_union.mp
  rw [G.union_eq]
  exact mem_natNodes.mpr ⟨i, hi, rfl⟩

lemma mem_inter {x : K} (hx : x ∈ G.rows ∧ x ∈ G.cols) :
    ∃ i < r, (i : K) = x := by
  apply mem_natNodes.mp
  rw [← G.inter_eq]
  exact Finset.mem_inter.mpr hx

end NodeGeometry

/-- Symmetric divided difference, with a prescribed diagonal jet. -/
noncomputable def loewnerEntry (f tau : K → K) (a b : K) : K :=
  if a = b then tau a else (f a - f b) / (a - b)

lemma loewnerEntry_symm (f tau : K → K) (a b : K) :
    loewnerEntry f tau a b = loewnerEntry f tau b a := by
  unfold loewnerEntry
  by_cases h : a = b
  · subst b; simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    field_simp
    ring

noncomputable def loewnerMatrix {r m : ℕ} (G : NodeGeometry (K := K) r m)
    (f tau : K → K) : Matrix G.rows G.rows K :=
  fun i j => loewnerEntry f tau i.val (G.equiv j).val

end CatalanCore.Rect.CharZeroNV
