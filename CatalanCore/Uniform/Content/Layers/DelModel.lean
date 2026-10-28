module
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.PeriodicWeighted
@[expose] public section

/-!
# The periodic matrix model on an arbitrary core (M3D, part 1)

The model of `Arith/Hybrid/ChainModel`, `ChainAlgebra` for the core `Fin r` is re-indexed
by a finite type `ι` together with a map `e : ι → Fin r`; the core nodes are `(e i).val`.
For `ι = Fin r`, `e = id` this is the original model; for `ι` the subtype of `Fin r` avoiding a
deleted index set `I` it is the model of the deletion member `P_{r,I}`.
-/

open Matrix Polynomial CatalanCore
namespace CatalanCore.Uniform.Content.Layers.Del
open CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.LemmaE
  CatalanCore.Arith.Hybrid.ChainClasses
variable {p r : ℕ} [Fact p.Prime] {ι Z : Type} [Fintype ι] [DecidableEq ι] [Fintype Z] [DecidableEq Z]
  {Fr : Frame} {e : ι → Fin r} {xs ys : Z → ℕ}

noncomputable def full (Fr : Frame) (p : ℕ) (e : ι → Fin r) (xs ys : Z → ℕ) :
    Matrix (ι ⊕ Z) (ι ⊕ Z) ℚ[X] :=
  (Rect.FullN Fr (fun i : ι => (e i).val) xs ys (X : ℚ[X])).map (rescaleHom p 2)
noncomputable def Q (Fr : Frame) (p : ℕ) (e : ι → Fin r) (xs ys : Z → ℕ) :=
  Atil p (fun _ : ι => 1) (full Fr p e xs ys).toBlocks₁₁
noncomputable def Q0 (Fr : Frame) (p : ℕ) (e : ι → Fin r) (xs ys : Z → ℕ) :=
  blockProject (fun i : ι => (e i).val % p) (Q Fr p e xs ys)
noncomputable def h (Fr : Frame) (p : ℕ) (e : ι → Fin r) (xs ys : Z → ℕ) :=
  (Q0 Fr p e xs ys).det
noncomputable def B2 (Fr : Frame) (p : ℕ) (e : ι → Fin r) (xs ys : Z → ℕ) :=
  C ((p : ℚ)^2) • (full Fr p e xs ys).toBlocks₁₂
noncomputable def C2 (Fr : Frame) (p : ℕ) (e : ι → Fin r) (xs ys : Z → ℕ) :=
  C ((p : ℚ)^2) • (full Fr p e xs ys).toBlocks₂₁
noncomputable def Sr (Fr : Frame) (p : ℕ) (e : ι → Fin r) (xs ys : Z → ℕ) :=
  modelRow (fun i : ι => (e i).val % p) (fun z => xs z % p)
    (Q0 Fr p e xs ys) (C2 Fr p e xs ys)
noncomputable def Sc (Fr : Frame) (p : ℕ) (e : ι → Fin r) (xs ys : Z → ℕ) :=
  modelCol (fun i : ι => (e i).val % p) (fun z => ys z % p)
    (Q0 Fr p e xs ys) (B2 Fr p e xs ys)

lemma Q_eq_shift : Q Fr p e xs ys =
    ((p:ℚ)^2 • (Matrix.of (fun i j : ι => Fr.Mn (e i).val (e j).val))).map
      (C : ℚ →+* ℚ[X]) + (X : ℚ[X]) • 1 := by
  change Atil p (fun _ : ι => 1)
    (((Matrix.of (fun i j : ι => Fr.Mn (e i).val (e j).val)).map (C : ℚ →+* ℚ[X]) +
      (X : ℚ[X]) • 1).map (rescaleHom p 2)) = _
  simpa using Atil_rescale_shift (p:=p)
    (Matrix.of (fun i j : ι => Fr.Mn (e i).val (e j).val)) 1

lemma Q_apply (i j : ι) : Q Fr p e xs ys i j =
    C ((p:ℚ)^2 * Fr.Mn (e i).val (e j).val) + X*(if i=j then 1 else 0) := by
  rw [Q_eq_shift]
  simp [Matrix.smul_apply, Matrix.one_apply]

lemma Q0_apply_same (i j : ι) (hij : (e i).val%p=(e j).val%p) :
    Q0 Fr p e xs ys i j = Q Fr p e xs ys i j := by
  simp [Q0, blockProject, blockRect, hij]

lemma B2_apply (i : ι) (y : Z) :
    B2 Fr p e xs ys i y=C ((p:ℚ)^2 * Fr.Mn (e i).val (ys y)) := by
  change C ((p:ℚ)^2) * rescaleHom p 2 (C (Fr.Mn (e i).val (ys y))) = _
  simp [rescaleHom]

lemma C2_apply (z : Z) (i : ι) :
    C2 Fr p e xs ys z i=C ((p:ℚ)^2 * Fr.Mn (xs z) (e i).val) := by
  change C ((p:ℚ)^2) * rescaleHom p 2 (C (Fr.Mn (xs z) (e i).val)) = _
  simp [rescaleHom]

lemma Q0_support (i j : ι) (hij : (e i).val%p≠(e j).val%p) : Q0 Fr p e xs ys i j=0 :=
  by simp [Q0, blockProject, blockRect, hij]

lemma full_B_apply (i : ι) (y : Z) :
    (full Fr p e xs ys).toBlocks₁₂ i y=C (Fr.Mn (e i).val (ys y)) := by
  change rescaleHom p 2 (C (Fr.Mn (e i).val (ys y))) = _
  simp [rescaleHom]

lemma full_C_apply (z : Z) (i : ι) :
    (full Fr p e xs ys).toBlocks₂₁ z i=C (Fr.Mn (xs z) (e i).val) := by
  change rescaleHom p 2 (C (Fr.Mn (xs z) (e i).val)) = _
  simp [rescaleHom]

lemma full_A_apply_ne (i j : ι) (hij : i≠j) :
    (full Fr p e xs ys).toBlocks₁₁ i j=C (Fr.Mn (e i).val (e j).val) := by
  change rescaleHom p 2 (C (Fr.Mn (e i).val (e j).val)+X*(if i=j then 1 else 0)) = _
  simp [hij,rescaleHom]

lemma Q_eq_smul : Q Fr p e xs ys=C ((p:ℚ)^2) • (full Fr p e xs ys).toBlocks₁₁ := by
  ext i j
  simp only [Q, Atil_apply, pow_one, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm _ (C (p:ℚ)), ← mul_assoc, ← map_mul]
  simp [pow_two]

lemma Sr_solve : Sr Fr p e xs ys * blockProject (fun i:ι=>(e i).val%p)
      (full Fr p e xs ys).toBlocks₁₁ =
    h Fr p e xs ys • blockRect (fun z=>xs z%p) (fun i:ι=>(e i).val%p)
      (full Fr p e xs ys).toBlocks₂₁ := by
  have hp0 : C ((p:ℚ)^2)≠(0:ℚ[X]) := by simp [(Fact.out : p.Prime).ne_zero]
  simpa only [Sr, h, Q0, Q_eq_smul, C2] using projected_row_solve
    (fun i:ι=>(e i).val%p) (fun z=>xs z%p) (C ((p:ℚ)^2)) hp0
    (full Fr p e xs ys).toBlocks₁₁ (full Fr p e xs ys).toBlocks₂₁

lemma Sc_solve : blockProject (fun i:ι=>(e i).val%p) (full Fr p e xs ys).toBlocks₁₁ *
      Sc Fr p e xs ys =
    h Fr p e xs ys • blockRect (fun i:ι=>(e i).val%p) (fun z=>ys z%p)
      (full Fr p e xs ys).toBlocks₁₂ := by
  have hp0 : C ((p:ℚ)^2)≠(0:ℚ[X]) := by simp [(Fact.out : p.Prime).ne_zero]
  simpa only [Sc, h, Q0, Q_eq_smul, B2] using projected_col_solve
    (fun i:ι=>(e i).val%p) (fun z=>ys z%p) (C ((p:ℚ)^2)) hp0
    (full Fr p e xs ys).toBlocks₁₁ (full Fr p e xs ys).toBlocks₁₂

lemma full_D_apply (z y : Z) :
    (full Fr p e xs ys).toBlocks₂₂ z y=C (Fr.Mn (xs z) (ys y)) := by
  change rescaleHom p 2 (C (Fr.Mn (xs z) (ys y))) = _
  simp [rescaleHom]

noncomputable def delta (Fr : Frame) (p : ℕ) (e : ι → Fin r) (xs ys : Z → ℕ) :=
    h Fr p e xs ys ^ 2 • (full Fr p e xs ys).toBlocks₂₂-
    h Fr p e xs ys • (Sr Fr p e xs ys*(full Fr p e xs ys).toBlocks₁₂)-
    h Fr p e xs ys • ((full Fr p e xs ys).toBlocks₂₁*Sc Fr p e xs ys)+
    Sr Fr p e xs ys*(full Fr p e xs ys).toBlocks₁₁*Sc Fr p e xs ys

lemma Q0_swap : Q0 Fr p e ys xs=Q0 Fr p e xs ys := rfl

lemma h_swap : h Fr p e ys xs=h Fr p e xs ys := rfl

lemma Q0_transpose : (Q0 Fr p e xs ys).transpose=Q0 Fr p e ys xs := by
  apply Matrix.ext
  intro i j
  change Q0 Fr p e xs ys j i = Q0 Fr p e ys xs i j
  by_cases hij : (e i).val%p=(e j).val%p
  · rw [Q0_apply_same j i hij.symm,Q0_apply_same i j hij,Q_apply,Q_apply]
    simp only [Mn_symm (Fr:=Fr) (e j).val (e i).val,eq_comm (a:=i) (b:=j)]
  · simp [Q0,blockProject,blockRect,hij,Ne.symm hij]

lemma Sr_swap : Sr Fr p e ys xs=(Sc Fr p e xs ys).transpose := by
  unfold Sr Sc modelRow modelCol
  rw [Matrix.transpose_mul, Matrix.adjugate_transpose,Q0_transpose]
  congr 1
  apply Matrix.ext
  intro z i
  simp only [blockRect,Matrix.transpose_apply,B2_apply,C2_apply]
  simp only [Mn_symm (Fr:=Fr) (ys z) (e i).val,eq_comm (a:=ys z%p) (b:=(e i).val%p)]

lemma Sc_swap : Sc Fr p e ys xs=(Sr Fr p e xs ys).transpose := by
  rw [Sr_swap (xs:=ys) (ys:=xs),Matrix.transpose_transpose]

lemma full_A_swap : (full Fr p e ys xs).toBlocks₁₁=(full Fr p e xs ys).toBlocks₁₁.transpose := by
  apply Matrix.ext
  intro i j
  change rescaleHom p 2 (C (Fr.Mn (e i).val (e j).val)+X*(if i=j then 1 else 0)) =
    rescaleHom p 2 (C (Fr.Mn (e j).val (e i).val)+X*(if j=i then 1 else 0))
  simp only [Mn_symm (Fr:=Fr) (e i).val (e j).val,eq_comm (a:=i) (b:=j)]

lemma full_B_swap : (full Fr p e ys xs).toBlocks₁₂=(full Fr p e xs ys).toBlocks₂₁.transpose := by
  apply Matrix.ext
  intro i z
  simp only [Matrix.transpose_apply,full_B_apply,full_C_apply,Mn_symm (Fr:=Fr) (e i).val (xs z)]

lemma full_C_swap : (full Fr p e ys xs).toBlocks₂₁=(full Fr p e xs ys).toBlocks₁₂.transpose := by
  rw [full_B_swap (xs:=ys) (ys:=xs),Matrix.transpose_transpose]

lemma full_D_swap : (full Fr p e ys xs).toBlocks₂₂=(full Fr p e xs ys).toBlocks₂₂.transpose := by
  apply Matrix.ext
  intro z y
  simp only [Matrix.transpose_apply,full_D_apply,Mn_symm (Fr:=Fr) (ys z) (xs y)]

lemma delta_swap : delta Fr p e ys xs=(delta Fr p e xs ys).transpose := by
  unfold delta
  conv_lhs =>
    rw [h_swap (xs:=xs) (ys:=ys),Sr_swap (xs:=xs) (ys:=ys),
      Sc_swap (xs:=xs) (ys:=ys),full_A_swap (xs:=xs) (ys:=ys),
      full_B_swap (xs:=xs) (ys:=ys),full_C_swap (xs:=xs) (ys:=ys),
      full_D_swap (xs:=xs) (ys:=ys)]
  simp only [Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_smul,
    Matrix.transpose_mul,Matrix.mul_assoc]
  abel

end CatalanCore.Uniform.Content.Layers.Del
