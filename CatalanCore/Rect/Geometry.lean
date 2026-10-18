module

public import CatalanCore.Rect.Full

@[expose] public section

/-!
# Geometries (WP-H1)

A `Geometry` is the triple of node sets `(C, X', Y')`.  `Geometry.Full` is `FullN` on the common
nodes `C` (as a subtype) and the order-preserving enumerations of `X'` and `Y'`.

* `after r m`    : `C = [0,r)`, `X' = {r+2i}`, `Y' = {r+2i+1}` (`i < m`): "member 1" of the
  hybrid, the geometry of `Frame.fullPoly`.  (The `x = 2+4n` of the plan is the same grid in
  physical coordinates; here nodes are the integers `a` with `Frame.Mn a b`.)
* `afterTop r m` : `after r m` plus one extra common node `b = r+2m` above the block
  (DO's "member 2", audit item 4); `r = r₁+1` with the same `X'`, `Y'`.
* `det_full_after` : `det Full(after r m) = Frame.fullPoly r m` (bridge to Spec).
-/

open Polynomial Finset Matrix

namespace CatalanCore.Rect

/-- Node sets of a rectangular Löwner frame. -/
structure Geometry where
  C : Finset ℕ
  X' : Finset ℕ
  Y' : Finset ℕ
  disjCX : Disjoint C X'
  disjCY : Disjoint C Y'
  disjXY : Disjoint X' Y'
  card_eq : X'.card = Y'.card

namespace Geometry

variable (G : Geometry)

/-- Row nodes `C ∪ X'` and column nodes `C ∪ Y'`. -/
def rows : Finset ℕ := G.C ∪ G.X'
def cols : Finset ℕ := G.C ∪ G.Y'

/-- `m = |X'| = |Y'|`. -/
def k : ℕ := G.X'.card

/-- Increasing enumeration of `X'`. -/
noncomputable def xs : Fin G.k → ℕ := fun i => G.X'.orderEmbOfFin rfl i
/-- Increasing enumeration of `Y'`. -/
noncomputable def ys : Fin G.k → ℕ := fun i => G.Y'.orderEmbOfFin G.card_eq.symm i

variable (Fr : Frame) {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `Full(x)` of a geometry: index `C ⊕ Fin m`, the `i`-th `X'` row paired with the `i`-th `Y'`
column. -/
noncomputable def Full (x : R) : Matrix (G.C ⊕ Fin G.k) (G.C ⊕ Fin G.k) R :=
  FullN Fr (fun a : G.C => (a : ℕ)) G.xs G.ys x

/-- `det Full(X)` as a polynomial over `ℚ`. -/
noncomputable def fullPolyG : ℚ[X] := (G.Full Fr (X : ℚ[X])).det

/-- The block `R_{X'Y'}`. -/
noncomputable def RXYG : Matrix (Fin G.k) (Fin G.k) ℚ := RXY Fr G.xs G.ys

/-- `P_r(X) = det (X I + M)`, `M` the Schur complement. -/
noncomputable def schurPG : ℚ[X] := schurP Fr (fun a : G.C => (a : ℕ)) G.xs G.ys

/-- **Schur step** `det Full(X) = det R_{X'Y'} · P_r(X)`. -/
theorem det_full_eq (hD : (G.RXYG Fr).det ≠ 0) :
    G.fullPolyG Fr = Polynomial.C (G.RXYG Fr).det * G.schurPG Fr :=
  det_fullN_eq Fr _ _ _ hD

theorem schurPG_monic : (G.schurPG Fr).Monic := schurP_monic Fr _ _ _

theorem schurPG_natDegree : (G.schurPG Fr).natDegree = G.C.card := by
  rw [schurPG, schurP_natDegree]; simp

/-- **Minor expansion** `det Full(x+t) = ∑_{S ⊆ C} t^{|C|-|S|} det Full_x[S ∪ X', S ∪ Y']`,
over any field `K` of characteristic `0`-algebra over `ℚ` (e.g. `ℝ`). -/
theorem det_full_expansion {K : Type*} [Field K] [Algebra ℚ K] (x t : K) :
    (G.Full Fr (x + t)).det
      = ∑ S ∈ (univ : Finset G.C).powerset, t ^ (G.C.card - S.card) *
          (FullN Fr (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys x).det := by
  have := det_fullN_expansion Fr (fun a : G.C => (a : ℕ)) G.xs G.ys x t
  unfold Geometry.Full
  simpa using this

end Geometry

/-! ### The hybrid geometries -/

/-- Member 1: `C = [0,r)`, `X' = {r+2i}`, `Y' = {r+2i+1}`, `i < m`. -/
def after (r m : ℕ) : Geometry where
  C := range r
  X' := (range m).image fun i => r + 2 * i
  Y' := (range m).image fun i => r + 2 * i + 1
  disjCX := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [mem_range, mem_image] at ha hb; omega
  disjCY := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [mem_range, mem_image] at ha hb; omega
  disjXY := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [mem_range, mem_image] at ha hb; omega
  card_eq := by
    rw [Finset.card_image_of_injective _ (by intro a b h; simp at h; omega),
      Finset.card_image_of_injective _ (by intro a b h; simp at h; omega)]

/-- Member 2: `after r m` with one extra common node `b = r + 2m` above `X' ∪ Y'`. -/
def afterTop (r m : ℕ) : Geometry where
  C := insert (r + 2 * m) (range r)
  X' := (after r m).X'
  Y' := (after r m).Y'
  disjCX := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [mem_insert, mem_range, after, mem_image] at ha hb; omega
  disjCY := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [mem_insert, mem_range, after, mem_image] at ha hb; omega
  disjXY := (after r m).disjXY
  card_eq := (after r m).card_eq

theorem after_k (r m : ℕ) : (after r m).k = m := by
  simp only [Geometry.k, after]
  rw [Finset.card_image_of_injective _ (by intro a b h; simp at h; omega)]; simp

theorem after_card_C (r m : ℕ) : (after r m).C.card = r := by simp [after]

theorem afterTop_card_C (r m : ℕ) : (afterTop r m).C.card = r + 1 := by
  simp only [afterTop]
  rw [Finset.card_insert_of_notMem (by simp)]; simp

theorem after_xs (r m : ℕ) (i : Fin (after r m).k) :
    (after r m).xs i = r + 2 * (i : ℕ) := by
  have hk : (after r m).k = m := after_k r m
  have := Finset.orderEmbOfFin_unique (s := (after r m).X') (k := (after r m).k) rfl
    (f := fun j : Fin (after r m).k => r + 2 * (j : ℕ))
    (fun j => by
      simp only [after, mem_image, mem_range]; exact ⟨j, by have := j.2; omega, rfl⟩)
    (fun a b h => by simp only; have : (a : ℕ) < b := h; omega)
  exact (congrFun this i).symm

theorem after_ys (r m : ℕ) (i : Fin (after r m).k) :
    (after r m).ys i = r + 2 * (i : ℕ) + 1 := by
  have hk : (after r m).k = m := after_k r m
  have := Finset.orderEmbOfFin_unique (s := (after r m).Y') (k := (after r m).k)
    (after r m).card_eq.symm
    (f := fun j : Fin (after r m).k => r + 2 * (j : ℕ) + 1)
    (fun j => by
      simp only [after, mem_image, mem_range]; exact ⟨j, by have := j.2; omega, rfl⟩)
    (fun a b h => by simp only; have : (a : ℕ) < b := h; omega)
  exact (congrFun this i).symm

theorem afterTop_xs (r m : ℕ) (i : Fin (afterTop r m).k) :
    (afterTop r m).xs i = r + 2 * (i : ℕ) := after_xs r m i
theorem afterTop_ys (r m : ℕ) (i : Fin (afterTop r m).k) :
    (afterTop r m).ys i = r + 2 * (i : ℕ) + 1 := after_ys r m i

/-- Reindexing invariance of `FullN`. -/
theorem det_fullN_reindex (Fr : Frame) {R : Type*} [CommRing R] [Algebra ℚ R]
    {ι κ ι' κ' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    (c : ι → ℕ) (xs ys : κ → ℕ) (c' : ι' → ℕ) (xs' ys' : κ' → ℕ)
    (eι : ι' ≃ ι) (eκ : κ' ≃ κ) (hc : ∀ a, c (eι a) = c' a) (hx : ∀ i, xs (eκ i) = xs' i)
    (hy : ∀ i, ys (eκ i) = ys' i) (x : R) :
    (FullN Fr c' xs' ys' x).det = (FullN Fr c xs ys x).det := by
  rw [← Matrix.det_submatrix_equiv_self (Equiv.sumCongr eι eκ) (FullN Fr c xs ys x)]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks, Matrix.one_apply, hc, hx, hy]

/-- Bridge to Spec: `det Full(after r m) = Frame.fullPoly r m`. -/
theorem det_full_after (Fr : Frame) (r m : ℕ) :
    (after r m).fullPolyG Fr = Fr.fullPoly r m := by
  have hk : (after r m).k = m := after_k r m
  have e1 : Fr.fullPoly r m = (FullN Fr (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
      (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
    unfold Frame.fullPoly
    congr 1
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks, Matrix.one_apply,
        Frame.hybRow, Frame.hybCol, Matrix.of_apply, add_comm]
  rw [e1]
  unfold Geometry.fullPolyG Geometry.Full
  let eι : Fin r ≃ (after r m).C :=
    { toFun := fun i => ⟨i, by simp [after]⟩
      invFun := fun a => ⟨a.1, by have := a.2; simpa [after] using this⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine (det_fullN_reindex Fr (fun a : (after r m).C => (a : ℕ)) (after r m).xs (after r m).ys
    (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) eι (finCongr hk).symm (fun _ => rfl)
    (fun i => by rw [after_xs]; simp) (fun i => by rw [after_ys]; simp) (X : ℚ[X])).symm

end CatalanCore.Rect
