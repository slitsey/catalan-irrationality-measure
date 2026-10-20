module

public import CatalanCore.Rect.CharZeroNV.Geometry

@[expose] public section

/-! # Consecutive common nodes and alternating border nodes -/

open Finset

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

def afterNodeNat (r m ε : ℕ) : Fin r ⊕ Fin m → ℕ :=
  Sum.elim (fun i => i.val) (fun j => r + 2 * j.val + ε)

lemma afterNodeNat_injective (r m ε : ℕ) (hε : ε ≤ 1) :
    Function.Injective (afterNodeNat r m ε) := by
  intro i j h
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (Fin.ext h)
  · have := i.isLt; simp [afterNodeNat] at h; omega
  · have := j.isLt; simp [afterNodeNat] at h; omega
  · apply congrArg Sum.inr; apply Fin.ext
    simp [afterNodeNat] at h; omega

noncomputable def afterNodes (r m ε : ℕ) : Finset K :=
  univ.image (fun i => (afterNodeNat r m ε i : K))

omit [CharZero K] in
lemma mem_afterNodes (r m ε : ℕ) (x : K) :
    x ∈ (afterNodes r m ε : Finset K) ↔
      ∃ i : Fin r ⊕ Fin m, (afterNodeNat r m ε i : K) = x := by
  simp [afterNodes]

noncomputable def afterIndexEquiv (r m ε : ℕ) (hε : ε ≤ 1) :
    (Fin r ⊕ Fin m) ≃ (afterNodes r m ε : Finset K) :=
  Equiv.ofBijective
    (fun i => ⟨(afterNodeNat r m ε i : K), (mem_afterNodes r m ε _).mpr ⟨i, rfl⟩⟩)
    ⟨by
      intro i j h
      apply afterNodeNat_injective r m ε hε
      exact Nat.cast_injective (congrArg Subtype.val h), by
      intro x
      obtain ⟨i, hi⟩ := (mem_afterNodes r m ε x.val).mp x.property
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp] lemma afterIndexEquiv_val (r m ε : ℕ) (hε : ε ≤ 1) (i : Fin r ⊕ Fin m) :
    (afterIndexEquiv (K := K) r m ε hε i).val = (afterNodeNat r m ε i : K) := rfl

lemma afterNodes_union (r m : ℕ) :
    (afterNodes r m 0 : Finset K) ∪ afterNodes r m 1 = natNodes (r + 2 * m) := by
  ext x
  constructor
  · intro hx
    rcases mem_union.mp hx with hx | hx
    all_goals
      obtain ⟨i, rfl⟩ := (mem_afterNodes _ _ _ _).mp hx
      apply mem_natNodes.mpr
      refine ⟨_, ?_, rfl⟩
      rcases i with i | i <;> simp only [afterNodeNat, Sum.elim_inl, Sum.elim_inr]
      all_goals omega
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
    by_cases hir : i < r
    · exact mem_union.mpr (Or.inl ((mem_afterNodes r m 0 _).mpr ⟨Sum.inl ⟨i, hir⟩, by simp [afterNodeNat]⟩))
    · have hmod : (i - r) % 2 = 0 ∨ (i - r) % 2 = 1 := by omega
      rcases hmod with hmod | hmod
      · apply mem_union.mpr; left
        apply (mem_afterNodes r m 0 _).mpr
        refine ⟨Sum.inr ⟨(i-r)/2, by omega⟩, ?_⟩
        have he : r + 2 * ((i-r)/2) + 0 = i := by omega
        change ((r + 2 * ((i-r)/2) + 0 : ℕ) : K) = (i : K)
        exact congrArg (fun n : ℕ => (n : K)) he
      · apply mem_union.mpr; right
        apply (mem_afterNodes r m 1 _).mpr
        refine ⟨Sum.inr ⟨(i-r)/2, by omega⟩, ?_⟩
        have he : r + 2 * ((i-r)/2) + 1 = i := by omega
        change ((r + 2 * ((i-r)/2) + 1 : ℕ) : K) = (i : K)
        exact congrArg (fun n : ℕ => (n : K)) he

lemma afterNodes_inter (r m : ℕ) :
    (afterNodes r m 0 : Finset K) ∩ afterNodes r m 1 = natNodes r := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hy⟩ := mem_inter.mp hx
    obtain ⟨i, rfl⟩ := (mem_afterNodes _ _ _ _).mp hx
    obtain ⟨j, hj⟩ := (mem_afterNodes _ _ _ _).mp hy
    have he := Nat.cast_injective (R := K) hj
    rcases i with i | i
    · exact mem_natNodes.mpr ⟨i.val, i.isLt, rfl⟩
    · rcases j with j | j <;> simp [afterNodeNat] at he
      all_goals omega
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
    apply mem_inter.mpr
    constructor
    all_goals exact (mem_afterNodes _ _ _ _).mpr ⟨Sum.inl ⟨i, hi⟩, by simp [afterNodeNat]⟩

noncomputable def after (r m : ℕ) : NodeGeometry (K := K) r m where
  rows := afterNodes r m 0
  cols := afterNodes r m 1
  equiv := (afterIndexEquiv r m 0 (by omega)).symm.trans (afterIndexEquiv r m 1 (by omega))
  card_rows := by
    have h := Fintype.card_congr (afterIndexEquiv (K := K) r m 0 (by omega))
    simpa using h.symm
  union_eq := afterNodes_union r m
  inter_eq := afterNodes_inter r m
  align := by
    intro i hi
    have he : (⟨(i.val : K), hi⟩ : (afterNodes r m 0 : Finset K)) =
        afterIndexEquiv r m 0 (by omega) (Sum.inl i) := rfl
    rw [he]
    simp [afterNodeNat]

noncomputable abbrev afterRowEquiv (r m : ℕ) : (Fin r ⊕ Fin m) ≃ (after (K := K) r m).rows :=
  afterIndexEquiv r m 0 (by omega)

noncomputable abbrev afterColEquiv (r m : ℕ) : (Fin r ⊕ Fin m) ≃ (after (K := K) r m).cols :=
  afterIndexEquiv r m 1 (by omega)

@[simp] lemma after_equiv_row (r m : ℕ) (i : Fin r ⊕ Fin m) :
    (after (K := K) r m).equiv (afterRowEquiv r m i) = afterColEquiv r m i := by
  change afterIndexEquiv r m 1 (by omega)
    ((afterIndexEquiv r m 0 (by omega)).symm (afterIndexEquiv r m 0 (by omega) i)) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] lemma afterRowEquiv_common (r m : ℕ) (i : Fin r) :
    afterRowEquiv (K := K) r m (Sum.inl i) = (after r m).common i := rfl

@[simp] lemma afterRowEquiv_val (r m : ℕ) (i : Fin r ⊕ Fin m) :
    (afterRowEquiv (K := K) r m i).val = (afterNodeNat r m 0 i : K) := rfl

@[simp] lemma afterColEquiv_val (r m : ℕ) (i : Fin r ⊕ Fin m) :
    (afterColEquiv (K := K) r m i).val = (afterNodeNat r m 1 i : K) := rfl

end CatalanCore.Rect.CharZeroNV
