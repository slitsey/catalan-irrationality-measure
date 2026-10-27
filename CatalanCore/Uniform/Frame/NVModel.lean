module
public import CatalanCore.Uniform.Frame.Family
public import CatalanCore.Uniform.NV.KernelCoordinates
public import CatalanCore.Uniform.NV.StepGeometry
public import CatalanCore.Rect.CharZeroNV.Complement
@[expose] public section

namespace CatalanCore.Uniform.NVAdapter
open Finset Matrix
open CatalanCore.Arith.Hybrid.FiniteFieldCorank CatalanCore.Rect.CharZeroNV

abbrev Index (G : Rect.Geometry) := G.C ⊕ Fin G.k

noncomputable def rowEquiv (G : Rect.Geometry) : Index G ≃ G.rows :=
  (Equiv.sumCongr (Equiv.refl G.C) (G.X'.orderIsoOfFin rfl).toEquiv).trans
    (Equiv.Finset.union G.C G.X' G.disjCX)
noncomputable def colEquiv (G : Rect.Geometry) : Index G ≃ G.cols :=
  (Equiv.sumCongr (Equiv.refl G.C) (G.Y'.orderIsoOfFin G.card_eq.symm).toEquiv).trans
    (Equiv.Finset.union G.C G.Y' G.disjCY)

@[simp] theorem rowEquiv_inl (G : Rect.Geometry) (a : G.C) :
    (rowEquiv G (.inl a) : ℕ) = a := rfl
@[simp] theorem rowEquiv_inr (G : Rect.Geometry) (i : Fin G.k) :
    (rowEquiv G (.inr i) : ℕ) = G.xs i := rfl
@[simp] theorem colEquiv_inl (G : Rect.Geometry) (a : G.C) :
    (colEquiv G (.inl a) : ℕ) = a := rfl
@[simp] theorem colEquiv_inr (G : Rect.Geometry) (i : Fin G.k) :
    (colEquiv G (.inr i) : ℕ) = G.ys i := rfl

noncomputable def castEquiv (s : Finset ℕ) : s ≃ (NV.fieldNodes s : Finset ℚ) :=
  Equiv.ofBijective (fun a => ⟨(a.val : ℚ), Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩⟩) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact Nat.cast_injective (congrArg (fun z : (NV.fieldNodes s : Finset ℚ) => z.val) hab)
    · intro y
      obtain ⟨a,ha,hay⟩ := Finset.mem_image.mp y.property
      exact ⟨⟨a,ha⟩,Subtype.ext hay⟩)

@[simp] theorem castEquiv_val (s : Finset ℕ) (a : s) :
    (castEquiv s a : ℚ) = (a.val : ℚ) := rfl

noncomputable def rowField (G : Rect.Geometry) : Index G ≃ (NV.fieldNodes G.rows : Finset ℚ) :=
  (rowEquiv G).trans (castEquiv G.rows)
noncomputable def colField (G : Rect.Geometry) : Index G ≃ (NV.fieldNodes G.cols : Finset ℚ) :=
  (colEquiv G).trans (castEquiv G.cols)

@[simp] theorem rowField_inl (G : Rect.Geometry) (a : G.C) :
    (rowField G (.inl a) : ℚ) = (a.val : ℚ) := rfl
@[simp] theorem rowField_inr (G : Rect.Geometry) (i : Fin G.k) :
    (rowField G (.inr i) : ℚ) = (G.xs i : ℚ) := rfl
@[simp] theorem colField_inl (G : Rect.Geometry) (a : G.C) :
    (colField G (.inl a) : ℚ) = (a.val : ℚ) := rfl
@[simp] theorem colField_inr (G : Rect.Geometry) (i : Fin G.k) :
    (colField G (.inr i) : ℚ) = (G.ys i : ℚ) := rfl

theorem rows_inter_cols (G : Rect.Geometry) : G.rows ∩ G.cols = G.C := by
  ext a
  simp only [Rect.Geometry.rows, Rect.Geometry.cols, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hc | hx, hc' | hy⟩
    · exact hc
    · exact hc
    · exact hc'
    · exact (Finset.disjoint_left.mp G.disjXY hx hy).elim
  · intro hc
    exact ⟨Or.inl hc,Or.inl hc⟩

theorem field_inter (G : Rect.Geometry) :
    (NV.fieldNodes G.rows : Finset ℚ) ∩ NV.fieldNodes G.cols = NV.fieldNodes G.C := by
  rw [show (NV.fieldNodes G.rows : Finset ℚ) ∩ NV.fieldNodes G.cols =
      NV.fieldNodes (G.rows ∩ G.cols) from
    (Finset.image_inter G.rows G.cols (Nat.cast_injective (R := ℚ))).symm]
  rw [rows_inter_cols]

/-- The field-node model is constructed from the actual finite geometry.
Its square indexing is the same common/border ordering used by FullN. -/
noncomputable abbrev model (G : Rect.Geometry) : NV.NodeGeometry (K := ℚ) where
  rows := NV.fieldNodes G.rows
  cols := NV.fieldNodes G.cols
  equiv := (rowField G).symm.trans (colField G)
  align := by
    intro a
    have ha : a.val ∈ (NV.fieldNodes G.C : Finset ℚ) := by
      rw [← field_inter]
      exact a.property
    obtain ⟨j,hj,hja⟩ := Finset.mem_image.mp ha
    let jC : G.C := ⟨j,hj⟩
    have hrow : rowField G (.inl jC) =
        ⟨a.val,(Finset.mem_inter.mp a.property).1⟩ := by
      apply Subtype.ext
      exact hja
    change (colField G ((rowField G).symm ⟨a.val,_⟩) : ℚ) = a.val
    rw [← hrow, Equiv.symm_apply_apply]
    exact hja

@[simp] theorem model_equiv_rowField (G : Rect.Geometry) (i : Index G) :
    (model G).equiv (rowField G i) = colField G i := by
  change colField G ((rowField G).symm (rowField G i)) = colField G i
  rw [Equiv.symm_apply_apply]

noncomputable def commonField (G : Rect.Geometry) :
    G.C ≃ ((model G).rows ∩ (model G).cols : Finset ℚ) :=
  Equiv.ofBijective (fun a => ⟨(a.val : ℚ),by
    change (a.val : ℚ) ∈ (NV.fieldNodes G.rows : Finset ℚ) ∩ NV.fieldNodes G.cols
    rw [field_inter]
    exact Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩⟩) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact Nat.cast_injective (congrArg (fun z : ((model G).rows ∩ (model G).cols : Finset ℚ) => z.val) hab)
    · intro y
      have hy : y.val ∈ (NV.fieldNodes G.C : Finset ℚ) := by
        rw [← field_inter]
        exact y.property
      obtain ⟨a,ha,hay⟩ := Finset.mem_image.mp hy
      exact ⟨⟨a,ha⟩,Subtype.ext hay⟩)

@[simp] theorem commonField_val (G : Rect.Geometry) (a : G.C) :
    (commonField G a : ℚ) = (a.val : ℚ) := rfl

theorem common_compat (G : Rect.Geometry) (a : G.C) :
    (model G).common (commonField G a) = rowField G (.inl a) := by
  apply Subtype.ext
  rfl

theorem model_union (G : Rect.Geometry) :
    (model G).rows ∪ (model G).cols = NV.fieldNodes (G.C ∪ G.X' ∪ G.Y') := by
  change (NV.fieldNodes (G.C ∪ G.X') : Finset ℚ) ∪ NV.fieldNodes (G.C ∪ G.Y') = _
  unfold NV.fieldNodes
  rw [← Finset.image_union]
  congr 1
  ext a
  simp only [Finset.mem_union]
  tauto

theorem model_inter (G : Rect.Geometry) :
    (model G).rows ∩ (model G).cols = NV.fieldNodes G.C := field_inter G

theorem model_rows_card (G : Rect.Geometry) : (model G).rows.card = G.C.card + G.k := by
  rw [show (model G).rows = (NV.fieldNodes G.rows : Finset ℚ) from rfl,
    NV.card_fieldNodes]
  exact Finset.card_union_of_disjoint G.disjCX

theorem full_nodes_card (G : Rect.Geometry) : (G.C ∪ G.X' ∪ G.Y').card = G.C.card + 2 * G.k := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨G.disjCY,G.disjXY⟩),
    Finset.card_union_of_disjoint G.disjCX, ← G.card_eq]
  unfold Rect.Geometry.k
  omega

/-- Reindexing the concrete model gives its natural row/column kernel entries. -/
theorem matrix_reindex (G : Rect.Geometry) (f tau : ℚ → ℚ) :
    ((model G).matrix f tau).submatrix (rowField G) (rowField G) =
      Matrix.of (fun a b : Index G =>
        NV.loewnerEntry f tau (rowField G a).val (colField G b).val) := by
  ext a b
  change NV.loewnerEntry f tau (rowField G a).val ((model G).equiv (rowField G b)).val = _
  rw [model_equiv_rowField]
  rfl

end CatalanCore.Uniform.NVAdapter





