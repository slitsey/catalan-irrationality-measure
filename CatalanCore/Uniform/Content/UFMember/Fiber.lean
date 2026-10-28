module

public import CatalanCore.Uniform.Content.UFMember.Expansion

@[expose] public section

/-!
# UF member package: first-order moments are FIBER-LOCAL

Modulo `p` the core block `Q` is block diagonal over residue classes (`SchurDiv`), and a border
row of `S'` only meets the core fiber of its own residue.  Hence (`bordered_local`)

  `det Q̄ - s̄ adj(Q̄) ū = det Q̄_{¬F} · (det Q̄_F - s̄_F adj(Q̄_F) ū_F)`

for `s` supported on the fiber `F`: the first-order moments `ᾱ_z`, `β̄¹_z` of a border node are
the product of the OTHER fibers' determinants and a bordered determinant of its OWN fiber
(`rowMomA_reduction`, `rowMomB1_reduction`).  So the first-order direction `(ᾱ_z : β̄¹_z)` of a
border node depends only on its own residue fiber (relative digits and pole data) — the
transport statement behind the joint types `J` — and the first-order wedges of the kills are
fiber-local.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMember

section Color

variable {K : Type*} [Field K] {n α : Type*} [Fintype n] [DecidableEq n] [DecidableEq α]

/-- Determinant split by one colour class. -/
theorem det_color_split (M : Matrix n n K) (col : n → α) (k : α)
    (hM : ∀ a b, col a ≠ col b → M a b = 0) :
    M.det = (M.toSquareBlockProp fun i => col i = k).det *
      (M.toSquareBlockProp fun i => ¬ col i = k).det :=
  Matrix.twoBlockTriangular_det' M (fun i => col i = k) fun i hi j hj =>
    hM i j (by rw [hi]; exact fun h => hj h.symm)

lemma tsb_apply (M : Matrix n n K) (P : n → Prop) (a b : {x // P x}) :
    (M.toSquareBlockProp P) a b = M a.1 b.1 := rfl

/-- Sum over a colour class: terms outside vanish. -/
lemma sum_color {β : Type*} [AddCommMonoid β] (col : n → α) (k : α) (f : n → β)
    (hf : ∀ x, col x ≠ k → f x = 0) :
    ∑ x, f x = ∑ x : {x // col x = k}, f x.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x => col x = k) f]
  have : ∑ i : {x // ¬ col x = k}, f i.1 = 0 :=
    Finset.sum_eq_zero fun i _ => hf i.1 i.2
  rw [this, add_zero]

/-- The inverse restricts to a colour class. -/
theorem inv_toSquareBlock_color (M : Matrix n n K) (col : n → α) (k : α)
    (hM : ∀ a b, col a ≠ col b → M a b = 0) (hdet : M.det ≠ 0) :
    (M.toSquareBlockProp fun i => col i = k)⁻¹ =
      M⁻¹.toSquareBlockProp fun i => col i = k := by
  apply Matrix.inv_eq_right_inv
  ext i j
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv M hu) i.1) j.1
  rw [Matrix.mul_apply, sum_color col k _ (fun x hx => by
    rw [hM i.1 x (by rw [i.2]; exact fun h => hx h.symm), zero_mul])] at h1
  rw [Matrix.mul_apply]
  simp only [tsb_apply]
  rw [h1, Matrix.one_apply, Matrix.one_apply]
  simp only [Subtype.ext_iff]

/-- **Bordered determinant of a block-diagonal matrix, local form.** -/
theorem bordered_local (M : Matrix n n K) (col : n → α) (k : α)
    (hM : ∀ a b, col a ≠ col b → M a b = 0) (hdet : M.det ≠ 0) (t : K) (s u : n → K)
    (hs : ∀ i, col i ≠ k → s i = 0) :
    M.det * t - ∑ i, s i * ∑ j, M.adjugate i j * u j =
      (M.toSquareBlockProp fun i => ¬ col i = k).det *
        ((M.toSquareBlockProp fun i => col i = k).det * t -
          ∑ i : {i // col i = k}, s i * ∑ j : {i // col i = k},
            (M.toSquareBlockProp fun i => col i = k).adjugate i j * u j) := by
  classical
  set MF := M.toSquareBlockProp fun i => col i = k
  set MN := M.toSquareBlockProp fun i => ¬ col i = k
  have hsplit := det_color_split M col k hM
  have hF : MF.det ≠ 0 := by
    intro h; apply hdet; rw [hsplit, h, zero_mul]
  have huM : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  have huF : IsUnit MF.det := isUnit_iff_ne_zero.2 hF
  have hadjM : M.adjugate = M.det • M⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ huM, one_smul]
  have hadjF : MF.adjugate = MF.det • MF⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ huF, one_smul]
  have hinv := inv_toSquareBlock_color M col k hM hdet
  have h0 := inv_eq_zero_of_color M col hM hdet
  have hsum : ∑ i, s i * ∑ j, M.adjugate i j * u j =
      M.det * ∑ i : {i // col i = k}, s i * ∑ j : {i // col i = k}, MF⁻¹ i j * u j := by
    rw [sum_color col k _ (fun x hx => by rw [hs x hx, zero_mul]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_color col k _ (fun x hx => by
      rw [hadjM, Matrix.smul_apply, h0 i.1 x (by rw [i.2]; exact fun h => hx h.symm),
        smul_zero, zero_mul])]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hinv, tsb_apply, hadjM, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hsum, hsplit, hadjF]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end Color

end CatalanCore.Uniform.Content.UFMember
