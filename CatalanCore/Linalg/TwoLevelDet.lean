module
public import CatalanCore.Linalg.RankDvd
public import Mathlib.Tactic
@[expose] public section
open Matrix Finset
namespace CatalanCore.Linalg

lemma rank_upper_block_le {K I J : Type*} [Field K]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (H : Matrix I I K) (B : Matrix I J K) (D : Matrix J J K) :
    (Matrix.fromBlocks H B 0 D).rank≤H.rank+Fintype.card J := by
  let M:=Matrix.fromBlocks H B 0 D
  let T : LinearMap.ker H.mulVecLin→ₗ[K]LinearMap.ker M.mulVecLin := {
    toFun:=fun x=>⟨Sum.elim x.val (fun _=>0),by
      rw [LinearMap.mem_ker,Matrix.mulVecLin_apply]
      have hx:=x.property
      rw [LinearMap.mem_ker,Matrix.mulVecLin_apply] at hx
      ext i
      rcases i with i|i
      · simpa [M,Matrix.mulVec,dotProduct,Fintype.sum_sum_type] using congrFun hx i
      · simp [M,Matrix.mulVec,dotProduct,Fintype.sum_sum_type]⟩
    map_add':=by intro x y;ext i;rcases i with i|i <;> simp
    map_smul':=by intro a x;ext i;rcases i with i|i <;> simp }
  have hi : Function.Injective T := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrFun (congrArg Subtype.val hxy) (Sum.inl i)
  have hk:=LinearMap.finrank_le_finrank_of_injective hi
  have h1:=LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  have h2:=LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_sum] at h1 h2
  change Module.finrank K (LinearMap.range M.mulVecLin)≤
    Module.finrank K (LinearMap.range H.mulVecLin)+Fintype.card J
  omega

/-- Two successive determinant levels. A low-rank divided intersection gives
an additional saving without requiring that the first-level corank be exact. -/
theorem two_level_dvd_det {R K I J : Type*} [CommRing R] [IsDomain R]
    [Field K] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (φ : R→+*K) {π : R} (hπ : Prime π) (hker : ∀x,φ x=0↔π∣x)
    (H : Matrix I I R) (B : Matrix I J R) (C : Matrix J I R)
    (D : Matrix J J R) (b : ℕ) (hrank : (H.map φ).rank≤b) :
    π^(Fintype.card I+(Fintype.card I-b))∣
      (Matrix.fromBlocks (π • H) (π • B) (π • C) D).det := by
  classical
  let N:=Matrix.fromBlocks H B (π • C) D
  have hπ0 : φ π=0 := (hker π).mpr (dvd_refl _)
  have hmap : N.map φ=Matrix.fromBlocks (H.map φ) (B.map φ) 0 (D.map φ) := by
    ext i j
    rcases i with i|i <;> rcases j with j|j <;> simp [N,Matrix.smul_apply,hπ0]
  have hn : (N.map φ).rank+(Fintype.card I-b)≤Fintype.card (I⊕J) := by
    have h:=rank_upper_block_le (H.map φ) (B.map φ) (D.map φ)
    have hwidth:=Matrix.rank_le_card_width (H.map φ)
    rw [hmap]
    simp only [Fintype.card_sum]
    omega
  let e : Fin (Fintype.card (I⊕J))≃(I⊕J):=(Fintype.equivFin (I⊕J)).symm
  have hd : π^(Fintype.card I-b)∣N.det := by
    have hmap' : (N.submatrix e e).map φ=(N.map φ).submatrix e e := rfl
    have h:=dvd_det_of_rank φ hπ hker _ (Fintype.card I-b) (N.submatrix e e)
      (by rw [hmap',Matrix.rank_submatrix];exact hn)
    simpa only [Matrix.det_submatrix_equiv_self] using h
  have heq : Matrix.fromBlocks (π • H) (π • B) (π • C) D=
      Matrix.diagonal (Sum.elim (fun _:I=>π) (fun _:J=>1))*N := by
    ext i j
    rcases i with i|i <;> rcases j with j|j <;>
      simp [Matrix.diagonal_mul,N,Matrix.smul_apply]
  rw [heq,Matrix.det_mul,Matrix.det_diagonal,Fintype.prod_sum_type]
  simpa [pow_add] using mul_dvd_mul_left (π^Fintype.card I) hd

/-- Primitive changes of basis may be cancelled after the two-level estimate.
They need not be invertible over the coefficient ring. -/
theorem two_level_dvd_det_of_primitive_changes {R K I J : Type*}
    [CommRing R] [IsDomain R] [Field K] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (φ : R→+*K) {π : R} (hπ : Prime π) (hker : ∀x,φ x=0↔π∣x)
    (M L P : Matrix (I⊕J) (I⊕J) R)
    (hL : φ L.det≠0) (hP : φ P.det≠0)
    (H : Matrix I I R) (B : Matrix I J R) (C : Matrix J I R)
    (D : Matrix J J R) (b : ℕ) (hrank : (H.map φ).rank≤b)
    (hform : L*M*P=Matrix.fromBlocks (π • H) (π • B) (π • C) D) :
    π^(Fintype.card I+(Fintype.card I-b))∣M.det := by
  let k:=Fintype.card I+(Fintype.card I-b)
  have hd:=two_level_dvd_det φ hπ hker H B C D b hrank
  rw [←hform,Matrix.det_mul,Matrix.det_mul] at hd
  have hndL : ¬π∣L.det:=fun h=>hL ((hker _).mpr h)
  have hndP : ¬π∣P.det:=fun h=>hP ((hker _).mpr h)
  have hd' : π^k∣P.det*(L.det*M.det) := by
    simpa only [k,mul_comm P.det] using hd
  exact hπ.pow_dvd_of_dvd_mul_left k hndL
    (hπ.pow_dvd_of_dvd_mul_left k hndP hd')
end CatalanCore.Linalg
