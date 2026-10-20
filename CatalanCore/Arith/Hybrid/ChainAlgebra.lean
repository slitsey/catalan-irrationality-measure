module
public import CatalanCore.Arith.Hybrid.ChainModel
public import CatalanCore.Arith.Hybrid.ChainEntries
public import CatalanCore.Arith.Hybrid.LemmaE.ChainSolve
public import CatalanCore.Arith.Hybrid.LemmaE.ModelWeighted
public import CatalanCore.Arith.Hybrid.LemmaE.ProjectedBounds
public import CatalanCore.Arith.Hybrid.ClearedCancellation
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
lemma Q_eq_shift : Q Fr p r xs ys =
    ((p:ℚ)^2 • (Matrix.of (fun i j : Fin r=>Fr.Mn i.val j.val))).map (C : ℚ →+* ℚ[X])+(X : ℚ[X]) • 1 := by
  change Atil p (fun _ : Fin r=>1)
    (((Matrix.of (fun i j : Fin r=>Fr.Mn i.val j.val)).map (C : ℚ →+* ℚ[X])+(X : ℚ[X]) • 1).map (rescaleHom p 2)) = _
  simpa using Atil_rescale_shift (p:=p) (Matrix.of (fun i j : Fin r=>Fr.Mn i.val j.val)) 1

lemma Q_apply (i j : Fin r) : Q Fr p r xs ys i j =
    C ((p:ℚ)^2 * Fr.Mn i.val j.val)+X*(if i=j then 1 else 0) := by
  rw [Q_eq_shift]
  simp [Matrix.smul_apply, Matrix.one_apply]

lemma Q0_apply_same (i j : Fin r) (hij : i.val%p=j.val%p) :
    Q0 Fr p r xs ys i j = Q Fr p r xs ys i j := by
  simp [Q0, blockProject, blockRect, hij]

lemma B2_apply (i : Fin r) (y : Z) :
    B2 Fr p r xs ys i y=C ((p:ℚ)^2 * Fr.Mn i.val (ys y)) := by
  change C ((p:ℚ)^2) * rescaleHom p 2 (C (Fr.Mn i.val (ys y))) = _
  simp [rescaleHom]

lemma C2_apply (z : Z) (i : Fin r) :
    C2 Fr p r xs ys z i=C ((p:ℚ)^2 * Fr.Mn (xs z) i.val) := by
  change C ((p:ℚ)^2) * rescaleHom p 2 (C (Fr.Mn (xs z) i.val)) = _
  simp [rescaleHom]

lemma Q0_support (i j : Fin r) (hij : i.val%p≠j.val%p) : Q0 Fr p r xs ys i j=0 :=
  by simp [Q0, blockProject, blockRect, hij]

lemma full_B_apply (i : Fin r) (y : Z) :
    (full Fr p r xs ys).toBlocks₁₂ i y=C (Fr.Mn i.val (ys y)) := by
  change rescaleHom p 2 (C (Fr.Mn i.val (ys y))) = _
  simp [rescaleHom]

lemma full_C_apply (z : Z) (i : Fin r) :
    (full Fr p r xs ys).toBlocks₂₁ z i=C (Fr.Mn (xs z) i.val) := by
  change rescaleHom p 2 (C (Fr.Mn (xs z) i.val)) = _
  simp [rescaleHom]

lemma full_A_apply_ne (i j : Fin r) (hij : i≠j) :
    (full Fr p r xs ys).toBlocks₁₁ i j=C (Fr.Mn i.val j.val) := by
  change rescaleHom p 2 (C (Fr.Mn i.val j.val)+X*(if i=j then 1 else 0)) = _
  simp [hij,rescaleHom]

lemma Q_eq_smul : Q Fr p r xs ys=C ((p:ℚ)^2) • (full Fr p r xs ys).toBlocks₁₁ := by
  ext i j
  simp only [Q, Atil_apply, pow_one, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm _ (C (p:ℚ)), ← mul_assoc, ← map_mul]
  simp [pow_two]

lemma Sr_solve : Sr Fr p r xs ys * blockProject (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₁₁ =
    h Fr p r xs ys • blockRect (fun z=>xs z%p) (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₂₁ := by
  have hp0 : C ((p:ℚ)^2)≠(0:ℚ[X]) := by simp [(Fact.out : p.Prime).ne_zero]
  simpa only [Sr, h, Q0, Q_eq_smul, C2] using projected_row_solve
    (fun i:Fin r=>i.val%p) (fun z=>xs z%p) (C ((p:ℚ)^2)) hp0
    (full Fr p r xs ys).toBlocks₁₁ (full Fr p r xs ys).toBlocks₂₁

lemma Sc_solve : blockProject (fun i:Fin r=>i.val%p) (full Fr p r xs ys).toBlocks₁₁ * Sc Fr p r xs ys =
    h Fr p r xs ys • blockRect (fun i:Fin r=>i.val%p) (fun z=>ys z%p) (full Fr p r xs ys).toBlocks₁₂ := by
  have hp0 : C ((p:ℚ)^2)≠(0:ℚ[X]) := by simp [(Fact.out : p.Prime).ne_zero]
  simpa only [Sc, h, Q0, Q_eq_smul, B2] using projected_col_solve
    (fun i:Fin r=>i.val%p) (fun z=>ys z%p) (C ((p:ℚ)^2)) hp0
    (full Fr p r xs ys).toBlocks₁₁ (full Fr p r xs ys).toBlocks₁₂

lemma full_D_apply (z y : Z) :
    (full Fr p r xs ys).toBlocks₂₂ z y=C (Fr.Mn (xs z) (ys y)) := by
  change rescaleHom p 2 (C (Fr.Mn (xs z) (ys y))) = _
  simp [rescaleHom]

noncomputable def delta (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :=
    h Fr p r xs ys ^ 2 • (full Fr p r xs ys).toBlocks₂₂-
    h Fr p r xs ys • (Sr Fr p r xs ys*(full Fr p r xs ys).toBlocks₁₂)-
    h Fr p r xs ys • ((full Fr p r xs ys).toBlocks₂₁*Sc Fr p r xs ys)+
    Sr Fr p r xs ys*(full Fr p r xs ys).toBlocks₁₁*Sc Fr p r xs ys

lemma Q0_swap : Q0 Fr p r ys xs=Q0 Fr p r xs ys := rfl

lemma h_swap : h Fr p r ys xs=h Fr p r xs ys := rfl

lemma Q0_transpose : (Q0 Fr p r xs ys).transpose=Q0 Fr p r ys xs := by
  apply Matrix.ext
  intro i j
  change Q0 Fr p r xs ys j i = Q0 Fr p r ys xs i j
  by_cases hij : i.val%p=j.val%p
  · rw [Q0_apply_same j i hij.symm,Q0_apply_same i j hij,Q_apply,Q_apply]
    simp only [Mn_symm (Fr:=Fr) j.val i.val,eq_comm (a:=i) (b:=j)]
  · simp [Q0,blockProject,blockRect,hij,Ne.symm hij]

lemma Sr_swap : Sr Fr p r ys xs=(Sc Fr p r xs ys).transpose := by
  unfold Sr Sc modelRow modelCol
  rw [Matrix.transpose_mul, Matrix.adjugate_transpose,Q0_transpose]
  congr 1
  apply Matrix.ext
  intro z i
  simp only [blockRect,Matrix.transpose_apply,B2_apply,C2_apply]
  simp only [Mn_symm (Fr:=Fr) (ys z) i.val,eq_comm (a:=ys z%p) (b:=i.val%p)]

lemma Sc_swap : Sc Fr p r ys xs=(Sr Fr p r xs ys).transpose := by
  rw [Sr_swap (xs:=ys) (ys:=xs),Matrix.transpose_transpose]

lemma full_A_swap : (full Fr p r ys xs).toBlocks₁₁=(full Fr p r xs ys).toBlocks₁₁.transpose := by
  apply Matrix.ext
  intro i j
  change rescaleHom p 2 (C (Fr.Mn i.val j.val)+X*(if i=j then 1 else 0)) =
    rescaleHom p 2 (C (Fr.Mn j.val i.val)+X*(if j=i then 1 else 0))
  simp only [Mn_symm (Fr:=Fr) i.val j.val,eq_comm (a:=i) (b:=j)]

lemma full_B_swap : (full Fr p r ys xs).toBlocks₁₂=(full Fr p r xs ys).toBlocks₂₁.transpose := by
  apply Matrix.ext
  intro i z
  simp only [Matrix.transpose_apply,full_B_apply,full_C_apply,Mn_symm (Fr:=Fr) i.val (xs z)]

lemma full_C_swap : (full Fr p r ys xs).toBlocks₂₁=(full Fr p r xs ys).toBlocks₁₂.transpose := by
  rw [full_B_swap (xs:=ys) (ys:=xs),Matrix.transpose_transpose]

lemma full_D_swap : (full Fr p r ys xs).toBlocks₂₂=(full Fr p r xs ys).toBlocks₂₂.transpose := by
  apply Matrix.ext
  intro z y
  simp only [Matrix.transpose_apply,full_D_apply,Mn_symm (Fr:=Fr) (ys z) (xs y)]

lemma delta_swap : delta Fr p r ys xs=(delta Fr p r xs ys).transpose := by
  unfold delta
  conv_lhs =>
    rw [h_swap (xs:=xs) (ys:=ys),Sr_swap (xs:=xs) (ys:=ys),
      Sc_swap (xs:=xs) (ys:=ys),full_A_swap (xs:=xs) (ys:=ys),
      full_B_swap (xs:=xs) (ys:=ys),full_C_swap (xs:=xs) (ys:=ys),
      full_D_swap (xs:=xs) (ys:=ys)]
  simp only [Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_smul,
    Matrix.transpose_mul,Matrix.mul_assoc]
  abel
end CatalanCore.Arith.Hybrid.ChainModel
namespace CatalanCore.Arith.Hybrid.ChainClasses
open LemmaE
variable {p : ℕ} [Fact p.Prime]
lemma chainNode_mod {r z : ℕ} (i : ChainIndex p r z) :
    (chainNode i).val % p = z % p :=
  Nat.modEq_iff_dvd.mpr (chainNode_dvd i)

lemma chain_image_of_mod {r z : ℕ} (hz : r≤z) (a : Fin r)
    (ha : a.val%p=z%p) : a∈Set.range (@chainNode p r z) := by
  obtain ⟨i,hi⟩ := exists_chainNode (Fact.out : p.Prime).pos hz a (Nat.modEq_iff_dvd.mp ha)
  exact ⟨i,hi⟩

noncomputable def chainMatrix (Fr : Frame) (r z : ℕ) :
    Matrix (ChainIndex p r z) (ChainIndex p r z) ℚ[X] :=
  (Matrix.of (fun i j : ChainIndex p r z => (p:ℚ)^2*Fr.Mn (chainNode i).val (chainNode j).val)).map (C : ℚ →+* ℚ[X]) + (X : ℚ[X]) • 1

lemma Q0_chain {Fr : Frame} {r z : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (xs ys : Z→ℕ) :
    (ChainModel.Q0 Fr p r xs ys).submatrix (@chainNode p r z) chainNode =
      chainMatrix (p:=p) Fr r z := by
  ext i j
  rw [Matrix.submatrix_apply, ChainModel.Q0_apply_same _ _ (by rw [chainNode_mod,chainNode_mod]), ChainModel.Q_apply]
  simp only [chainMatrix, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  simp only [(chainNode_injective (Fact.out : p.Prime).pos).eq_iff]

noncomputable def residueLift (a : ZMod p) : ℚ := a.val

lemma good_residueLift (a : ZMod p) : Good p (residueLift a) a := by
  simpa only [residueLift, ZMod.natCast_zmod_val] using Good.natCast (ℓ:=p) a.val

lemma residueLift_int1 (a : ZMod p) : Int1 p (C (residueLift a)) := by
  rw [Int1,gn_C]
  exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp (good_residueLift a).mem

lemma chainNode_zmod {r z : ℕ} (i : ChainIndex p r z) :
    ((chainNode i).val : ZMod p) = z :=
  (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (chainNode_mod i)

lemma noCut_mod_ne_ordered {p r a b : ℕ} {sing : ℤ→Prop} (hp : 0<p) (hab : a<b)
    (hc : NoCut (Cut p r sing) a b) : a%p≠b%p := by
  intro he
  have hstep : a+p≤b := Nat.ModEq.add_le_of_lt he hab
  have hmod := Nat.mod_add_div a p
  have hlt := Nat.mod_lt a hp
  let t := p*(a/p+1)
  have hat : a<t := by dsimp [t]; nlinarith
  have htb : t≤b := by dsimp [t]; nlinarith [Nat.zero_le (a%p)]
  apply hc t (by exact_mod_cast hat) (by exact_mod_cast htb)
  exact Or.inr (Or.inl ⟨(a/p+1:ℕ),by dsimp [t]; push_cast; ring⟩)

lemma noCut_mod_ne {p r a b : ℕ} {sing : ℤ→Prop} (hp : 0<p) (hne : a≠b)
    (hc : NoCut (Cut p r sing) (min (a:ℤ) b) (max (a:ℤ) b)) : a%p≠b%p := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · apply noCut_mod_ne_ordered hp hab
    have hle : (a:ℤ)≤b := by exact_mod_cast hab.le
    simpa only [min_eq_left hle,max_eq_right hle] using hc
  · apply Ne.symm
    apply noCut_mod_ne_ordered hp hba
    have hle : (b:ℤ)≤a := by exact_mod_cast hba.le
    simpa only [min_eq_right hle,max_eq_left hle] using hc
end CatalanCore.Arith.Hybrid.ChainClasses
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p : ℕ} [Fact p.Prime]
lemma chainMatrix_symmetric (Fr : Frame) (r z : ℕ)
    (i j : ChainIndex p r z) :
    chainMatrix (p:=p) Fr r z i j = chainMatrix (p:=p) Fr r z j i := by
  simp only [chainMatrix, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  simp only [Mn_symm (Fr:=Fr) (chainNode i).val (chainNode j).val, eq_comm (a:=i) (b:=j)]
end CatalanCore.Arith.Hybrid.ChainModel
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]
lemma gle_of_scaled_int1 (b : ℕ) (f : ℚ[X]) (hf : Int1 p (C ((p:ℚ)^b)*f)) :
    GLE p b f := by
  intro i
  have hi : (C ((p:ℚ)^b)*f).coeff i ∈ Basic.LocRing p := by
    apply (mem_locRing_iff_padicNorm (p:=p)).mpr
    exact_mod_cast (padic_coeff_le_gn p _ i).trans hf
  simpa only [coeff_C_mul] using hi
end CatalanCore.Arith.Hybrid.LemmaE
