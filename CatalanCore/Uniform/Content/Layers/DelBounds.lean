module
public import CatalanCore.Uniform.Content.Layers.DelModel
@[expose] public section

/-!
# The weighted denominator bound on an arbitrary core (M3D, part 2)

Re-indexed version of `Arith/Hybrid/PeriodicModelBounds`, `PeriodicPartners`,
`PeriodicCancellation`, `PeriodicWeighted` for the model of `DelModel`.  The core is any finite
type `ι` with an *injective* map `e : ι → Fin r`.

The only new hypothesis is the covering condition `Covers e p s`: every node of `[0,r)`
congruent to `s` modulo `p` is a core node (`∈ range e`).  It is needed exactly at the zero
entries of the weight table: the zero-weight argument transports the residue chain of a border
node, and the chain must lie in the (reduced) core.  For `e = id` it is automatic.
-/

open Matrix Polynomial CatalanCore
namespace CatalanCore.Uniform.Content.Layers.Del
open CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.LemmaE
  CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Arith.Hybrid.Periodic
variable {p r N : ℕ} [Fact p.Prime] {Fr : Frame} {ι Z : Type} [Fintype ι] [DecidableEq ι]
  [Fintype Z] [DecidableEq Z] {e : ι → Fin r} {xs ys : Z → ℕ}

/-- Every core-range node of `[0,r)` in the residue class of `s` lies in the core. -/
def Covers (p : ℕ) (e : ι → Fin r) (s : ℕ) : Prop :=
  ∀ a : Fin r, a.val % p = s % p → a ∈ Set.range e

section Lift
variable {z : ℕ} (hcov : Covers p e z)
include hcov

noncomputable def lift (i : ChainIndex p r z) : ι :=
  Classical.choose (hcov (chainNode i) (chainNode_mod i))

lemma lift_spec (i : ChainIndex p r z) : e (lift hcov i) = chainNode i :=
  Classical.choose_spec (hcov (chainNode i) (chainNode_mod i))

lemma lift_val (i : ChainIndex p r z) : (e (lift hcov i)).val = (chainNode i).val := by
  rw [lift_spec hcov i]

lemma lift_mod (i : ChainIndex p r z) : (e (lift hcov i)).val % p = z % p := by
  rw [lift_val hcov i]; exact chainNode_mod i

lemma lift_zmod (i : ChainIndex p r z) : ((e (lift hcov i)).val : ZMod p) = z := by
  rw [lift_val hcov i]; exact chainNode_zmod i

lemma lift_injective : Function.Injective (lift hcov : ChainIndex p r z → ι) := by
  intro i j hij
  apply chainNode_injective (Fact.out : p.Prime).pos
  rw [← lift_spec hcov i, ← lift_spec hcov j, hij]
end Lift

lemma Q_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ i j,Int1 p (Q Fr p e xs ys i j) := by
  rw [Q_eq_shift]
  intro i j
  apply Int1.add
  · change Int1 p (C ((p:ℚ)^2 * Fr.Mn (e i).val (e j).val))
    rw [Int1, gn_C]
    exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp
      (D.square_mem hN ((e i).isLt.trans_le hr) ((e j).isLt.trans_le hr))
  · by_cases hi : i=j
    · subst j; simpa using (show Int1 p (X:ℚ[X]) from by
        unfold Int1; exact (gle_iff_gn p 0 X).mp GLE.X)
    · simp [Matrix.smul_apply, Matrix.one_apply, hi, Int1.zero]

lemma Q0_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ i j,Int1 p (Q0 Fr p e xs ys i j) :=
  blockRect_int1 _ _ _ (Q_int1 D hN hr)

lemma h_primitive (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    gn p (h Fr p e xs ys)=1 := by
  unfold h Q0
  rw [Q_eq_shift]
  apply prim_blockProject_shift
  intro i j
  exact D.square_mem hN ((e i).isLt.trans_le hr) ((e j).isLt.trans_le hr)

lemma B2_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,Int1 p (B2 Fr p e xs ys i y) := by
  intro i y
  rw [B2_apply, Int1, gn_C]
  exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp
    (D.square_mem hN ((e i).isLt.trans_le hr) (hy y))

lemma C2_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,Int1 p (C2 Fr p e xs ys z i) := by
  intro z i
  rw [C2_apply, Int1, gn_C]
  exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp
    (D.square_mem hN (hx z) ((e i).isLt.trans_le hr))

lemma Sr_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,Int1 p (Sr Fr p e xs ys z i) :=
  modelRow_int1 _ _ _ _ (Q0_int1 D hN hr) (C2_int1 D hN hr hx)

lemma Sc_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,Int1 p (Sc Fr p e xs ys i y) :=
  modelCol_int1 _ _ _ _ (Q0_int1 D hN hr) (B2_int1 D hN hr hy)

lemma Q0_det_ne (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    (Q0 Fr p e xs ys).det≠0 := by
  intro he
  have H:=h_primitive (e:=e) (xs:=xs) (ys:=ys) D hN hr
  unfold h at H
  rw [he, gn_zero] at H
  norm_num at H

lemma Sr_support (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ z i,xs z%p≠(e i).val%p→Sr Fr p e xs ys z i=0 :=
  modelRow_support _ _ _ _ (Q0_det_ne D hN hr) Q0_support

lemma Sc_support (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ i y,(e i).val%p≠ys y%p→Sc Fr p e xs ys i y=0 :=
  modelCol_support _ _ _ _ (Q0_det_ne D hN hr) Q0_support

lemma Q_primitive (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    gn p (Q Fr p e xs ys).det=1 := by
  rw [Q_eq_shift]
  apply prim_det_shift
  intro i j
  exact D.square_mem hN ((e i).isLt.trans_le hr) ((e j).isLt.trans_le hr)

lemma A_project_defect (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ i j,gn p ((blockProject (fun i:ι=>(e i).val%p) (full Fr p e xs ys).toBlocks₁₁-
      (full Fr p e xs ys).toBlocks₁₁) i j)≤p := by
  intro i j
  by_cases hij : (e i).val%p=(e j).val%p
  · simp [blockProject,blockRect,hij,Matrix.sub_apply,gn_zero]
  · have hne : i≠j := by intro he; subst j; exact hij rfl
    simpa [blockProject,blockRect,hij,Matrix.sub_apply,gn_neg,full_A_apply_ne i j hne] using
      (gle_iff_gn p 1 _).mp (Periodic.Model.Mn_cross_gle D ((e i).isLt.trans_le hr)
        ((e j).isLt.trans_le hr) hij)

lemma C_project_defect (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) (hx : ∀ z,xs z<N) :
    ∀ z i,gn p (((full Fr p e xs ys).toBlocks₂₁-
      blockRect (fun z=>xs z%p) (fun i:ι=>(e i).val%p)
        (full Fr p e xs ys).toBlocks₂₁) z i)≤p := by
  intro z i
  by_cases hi : xs z%p=(e i).val%p
  · simp [blockRect,hi,Matrix.sub_apply,gn_zero]
  · simpa [blockRect,hi,Matrix.sub_apply,full_C_apply] using
      (gle_iff_gn p 1 _).mp (Periodic.Model.Mn_cross_gle D (hx z)
        ((e i).isLt.trans_le hr) hi)

lemma B_project_defect (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) (hy : ∀ z,ys z<N) :
    ∀ i y,gn p (((full Fr p e xs ys).toBlocks₁₂-
      blockRect (fun i:ι=>(e i).val%p) (fun z=>ys z%p)
        (full Fr p e xs ys).toBlocks₁₂) i y)≤p := by
  intro i y
  by_cases hi : (e i).val%p=ys y%p
  · simp [blockRect,hi,Matrix.sub_apply,gn_zero]
  · simpa [blockRect,hi,Matrix.sub_apply,full_B_apply] using
      (gle_iff_gn p 1 _).mp (Periodic.Model.Mn_cross_gle D ((e i).isLt.trans_le hr)
        (hy y) hi)

lemma Sr_residual_bound (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) (hx : ∀ z,xs z<N) :
    ∀ z i,gn p ((h Fr p e xs ys • (full Fr p e xs ys).toBlocks₂₁-
      Sr Fr p e xs ys*(full Fr p e xs ys).toBlocks₁₁) z i)≤p :=
  row_residual_bound _ _ _ _ _ _ (le_of_eq (h_primitive D hN hr))
    (Sr_int1 D hN hr hx) Sr_solve p (by positivity)
    (A_project_defect D hN hr) (C_project_defect D hN hr hx)

lemma Sc_residual_bound (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) (hy : ∀ z,ys z<N) :
    ∀ i y,gn p ((h Fr p e xs ys • (full Fr p e xs ys).toBlocks₁₂-
      (full Fr p e xs ys).toBlocks₁₁*Sc Fr p e xs ys) i y)≤p :=
  col_residual_bound _ _ _ _ _ _ (le_of_eq (h_primitive D hN hr))
    (Sc_int1 D hN hr hy) Sc_solve p (by positivity)
    (A_project_defect D hN hr) (B_project_defect D hN hr hy)

lemma delta_gle_one_at (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) (z y : Z) (hxy : xs z%p≠ys y%p) :
    GLE p 1 (delta Fr p e xs ys z y) := by
  apply cleared_delta_gle_at _ _ _ _ _ _ _ (le_of_eq (h_primitive D hN hr))
    (Sr_int1 D hN hr hx) (Sc_int1 D hN hr hy) z y 1
  · rw [full_D_apply]
    exact Periodic.Model.Mn_cross_gle D (hx z) (hy y) (hxy)
  · intro i hsi
    have hi : xs z%p=(e i).val%p := by
      by_contra hn
      exact hsi (Sr_support D hN hr z i hn)
    rw [full_B_apply]
    exact Periodic.Model.Mn_cross_gle D ((e i).isLt.trans_le hr) (hy y)
      (by simpa [← hi] using hxy)
  · intro i hsi
    have hi : (e i).val%p=ys y%p := by
      by_contra hn
      exact hsi (Sc_support D hN hr i y hn)
    rw [full_C_apply]
    exact Periodic.Model.Mn_cross_gle D (hx z) ((e i).isLt.trans_le hr)
      (by simpa [hi] using hxy)
  · intro i j hsi hsj
    have hi : xs z%p=(e i).val%p := by
      by_contra hn
      exact hsi (Sr_support D hN hr z i hn)
    have hj : (e j).val%p=ys y%p := by
      by_contra hn
      exact hsj (Sc_support D hN hr j y hn)
    have hij : (e i).val%p≠(e j).val%p := by simpa [← hi,hj] using hxy
    rw [full_A_apply_ne i j (by intro he; subst j; exact hij rfl)]
    exact Periodic.Model.Mn_cross_gle D ((e i).isLt.trans_le hr) ((e j).isLt.trans_le hr) hij

lemma A_gle_two (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ i j,GLE p 2 ((full Fr p e xs ys).toBlocks₁₁ i j) := by
  intro i j
  apply gle_of_scaled_int1
  have H:=Q_int1 (e:=e) (xs:=xs) (ys:=ys) D hN hr i j
  rwa [Q_eq_smul,Matrix.smul_apply,smul_eq_mul] at H

lemma B_gle_two (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,GLE p 2 ((full Fr p e xs ys).toBlocks₁₂ i y) := by
  intro i y
  exact gle_of_scaled_int1 2 _ (B2_int1 D hN hr hy i y)

lemma C_gle_two (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,GLE p 2 ((full Fr p e xs ys).toBlocks₂₁ z i) := by
  intro z i
  exact gle_of_scaled_int1 2 _ (C2_int1 D hN hr hx z i)

lemma D_gle_two (D : PoleData Fr p N) (hN : N<p*p)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) : ∀ z y,GLE p 2 ((full Fr p e xs ys).toBlocks₂₂ z y) := by
  intro z y
  rw [full_D_apply]
  exact GLE.C_iff.mpr (D.square_mem hN (hx z) (hy y))

lemma delta_gle_two (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) (z y : Z) : GLE p 2 (delta Fr p e xs ys z y) :=
  cleared_delta_gle_at _ _ _ _ _ _ _ (le_of_eq (h_primitive D hN hr))
    (Sr_int1 D hN hr hx) (Sc_int1 D hN hr hy) z y 2
    (D_gle_two D hN hx hy z y)
    (fun i _=>B_gle_two D hN hr hy i y)
    (fun i _=>C_gle_two D hN hr hx z i)
    (fun i j _ _=>A_gle_two D hN hr i j)

/-! ### Chains inside the core -/

lemma Q0_chain {z : ℕ} (hcov : Covers p e z) :
    (Q0 Fr p e xs ys).submatrix (lift hcov) (lift hcov) = chainMatrix (p:=p) Fr r z := by
  ext i j
  rw [Matrix.submatrix_apply, Q0_apply_same _ _
    (by rw [lift_mod hcov, lift_mod hcov]), Q_apply]
  simp only [chainMatrix, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, lift_val hcov]
  simp only [(lift_injective hcov).eq_iff, (chainNode_injective (Fact.out : p.Prime).pos).eq_iff]

lemma Sr_chain_solve (he : Function.Injective e) (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (z : Z) (hz : r≤xs z) (hcov : Covers p e (xs z))
    (i : ChainIndex p r (xs z)) :
    ((fun j : ChainIndex p r (xs z) => Sr Fr p e xs ys z (lift hcov j)) ᵥ*
      chainMatrix (p:=p) Fr r (xs z)) i =
      h Fr p e xs ys * C2 Fr p e xs ys z (lift hcov i) := by
  have Hv := vecMul_restrict (Q0 Fr p e xs ys) (Sr Fr p e xs ys z)
    (lift hcov) (lift_injective hcov)
    (fun a ha => Sr_support D hN hr z a (by
      intro hne
      apply ha
      obtain ⟨j, hj⟩ := chain_image_of_mod hz (e a) hne.symm
      exact ⟨j, he (by rw [lift_spec hcov j]; exact hj)⟩)) i
  rw [Q0_chain hcov] at Hv
  refine (show _ = _ from Hv).trans ?_
  have H := congrArg (fun M => M z (lift hcov i))
    (modelRow_mul (fun a : ι => (e a).val%p) (fun z=>xs z%p)
      (Q0 Fr p e xs ys) (C2 Fr p e xs ys))
  simpa only [Sr, h, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.smul_apply, smul_eq_mul, blockRect, lift_mod hcov, ite_true] using H

lemma Sc_chain_solve (he : Function.Injective e) (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (y : Z) (hy : r≤ys y) (hcov : Covers p e (ys y))
    (i : ChainIndex p r (ys y)) :
    (chainMatrix (p:=p) Fr r (ys y) *ᵥ
      (fun j : ChainIndex p r (ys y) => Sc Fr p e xs ys (lift hcov j) y)) i =
      h Fr p e xs ys * B2 Fr p e xs ys (lift hcov i) y := by
  have Hv := mulVec_restrict (Q0 Fr p e xs ys) (fun a=>Sc Fr p e xs ys a y)
    (lift hcov) (lift_injective hcov)
    (fun a ha => Sc_support D hN hr a y (by
      intro hne
      apply ha
      obtain ⟨j, hj⟩ := chain_image_of_mod hy (e a) hne
      exact ⟨j, he (by rw [lift_spec hcov j]; exact hj)⟩)) i
  rw [Q0_chain hcov] at Hv
  refine (show _ = _ from Hv).trans ?_
  have H := congrArg (fun M => M (lift hcov i) y)
    (mul_modelCol (fun a : ι => (e a).val%p) (fun y=>ys y%p)
      (Q0 Fr p e xs ys) (B2 Fr p e xs ys))
  simpa only [Sc, h, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.smul_apply, smul_eq_mul, blockRect, lift_mod hcov, ite_true] using H

theorem partners_chain_cng (he : Function.Injective e) (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r D.singular) (xs z) (ys y))
    (hcz : Covers p e (xs z)) (hcy : Covers p e (ys y))
    (i : ChainIndex p r (xs z)) :
    Cng p (Sr Fr p e xs ys z (lift hcz i))
      (Sc Fr p e xs ys (lift hcy (chainTransport hzy hc i)) y) := by
  let tr := chainTransport hzy hc
  let M := chainMatrix (p:=p) Fr r (xs z)
  let M' := (chainMatrix (p:=p) Fr r (ys y)).submatrix tr tr
  let v := fun j : ChainIndex p r (xs z) => Sr Fr p e xs ys z (lift hcz j)
  let w := fun j : ChainIndex p r (xs z) => Sc Fr p e xs ys (lift hcy (tr j)) y
  apply row_partners_cng M M'
    (fun a b => by
      change Int1 p (chainMatrix (p:=p) Fr r (xs z) a b)
      rw [←Q0_chain (e:=e) (xs:=xs) (ys:=ys) hcz]
      exact Q0_int1 D hN hr _ _)
    (Periodic.Model.chainMatrix_primitive D hN hr) v w
    (fun j=>Sc_int1 D hN hr hyN _ _)
    (fun a b=>(Periodic.Model.chainMatrix_cng D hN hr hzy hc a b).symm)
  intro j
  have Hv := Sr_chain_solve (ys:=ys) he D hN hr z hz hcz j
  have Hw := Sc_chain_solve (xs:=xs) he D hN hr y hy hcy (tr j)
  have Hw' : (w ᵥ* M') j = h Fr p e xs ys * B2 Fr p e xs ys (lift hcy (tr j)) y := by
    change (∑a, Sc Fr p e xs ys (lift hcy (tr a)) y *
      chainMatrix (p:=p) Fr r (ys y) (tr a) (tr j)) = _
    have he' := tr.sum_comp (fun a => Sc Fr p e xs ys (lift hcy a) y *
      chainMatrix (p:=p) Fr r (ys y) a (tr j))
    rw [he']
    convert Hw using 1
    apply Finset.sum_congr rfl
    intro a _
    rw [ChainModel.chainMatrix_symmetric, mul_comm]
  change Cng p ((v ᵥ* M) j) ((w ᵥ* M') j)
  rw [show (v ᵥ* M) j = _ from Hv, Hw']
  apply Cng.mul_left_integral
  · exact det_int1 (Q0_int1 D hN hr)
  · rw [C2_apply, B2_apply]
    simp only [lift_val]
    rw [Mn_symm (Fr:=Fr) (xs z) (chainNode j).val]
    exact D.zone_chain_cng hN hr (hxN z) (hyN y) hzy hc j

theorem restricted_delta_int1 (he : Function.Injective e) (D : PoleData Fr p N)
    (hN : N<p*p) (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r D.singular) (xs z) (ys y))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0)
    (hcz : Covers p e (xs z)) (hcy : Covers p e (ys y)) :
    let tr := chainTransport hzy hc
    let sr := fun i : ChainIndex p r (xs z) => Sr Fr p e xs ys z (lift hcz i)
    let sc := fun i : ChainIndex p r (xs z) => Sc Fr p e xs ys (lift hcy (tr i)) y
    Int1 p ((h Fr p e xs ys)^2*C (Fr.Mn (xs z) (ys y))-
      h Fr p e xs ys*(∑i,sr i*C (Fr.Mn (chainNode i).val (ys y)))-
      h Fr p e xs ys*(∑i,C (Fr.Mn (xs z) (chainNode (tr i)).val)*sc i)+
      ∑i,∑j,sr i*C (Fr.Mn (chainNode i).val (chainNode (tr j)).val)*sc j) := by
  dsimp only
  let tr := chainTransport hzy hc
  let V := D.V
  let gamma := C (residueLift (((red p Fr.norm)*((ys y : ZMod p)-(xs z : ZMod p)))⁻¹))
  let l := C (residueLift (V (xs z)))
  let L := fun i : ChainIndex p r (xs z) => C (residueLift (V (chainNode i).val))
  have hzone : V (xs z)=V (ys y) := D.V_zone hzy (hyN y) hc
  have hchain (i : ChainIndex p r (xs z)) : V (chainNode i).val=V (chainNode (tr i)).val :=
    D.V_chain hr hzy hc i
  apply same_class_delta_int1 _ _ gamma l L
    (fun i=>Sr Fr p e xs ys z (lift hcz i))
    (fun i=>Sc Fr p e xs ys (lift hcy (tr i)) y)
  · exact det_int1 (Q0_int1 D hN hr)
  · exact residueLift_int1 _
  · exact residueLift_int1 _
  · intro i; exact residueLift_int1 _
  · exact fun i=>Sr_int1 D hN hr hxN _ _
  · exact fun i=>Sc_int1 D hN hr hyN _ _
  · exact fun i=>(partners_chain_cng he D hN hr hxN hyN z y hz hy hzy hc hcz hcy i).symm
  · have H := Periodic.Model.loewner_entry_cng D (hxN z) (hyN y) hd rfl rfl hzone.symm
    simpa only [V, ←C_mul, sub_self, mul_zero] using H
  · intro i
    have H := Periodic.Model.loewner_entry_cng D
      ((chainNode i).isLt.trans_le hr) (hyN y) hd
      (by rw [chainNode_zmod]) rfl hzone.symm
    simpa only [←C_mul] using H
  · intro i
    have H := Periodic.Model.loewner_entry_cng D
      (hxN z) ((chainNode (tr i)).isLt.trans_le hr) hd
      (by rw [chainNode_zmod]) rfl (hchain i).symm
    simpa only [←C_mul] using H
  · intro i j
    have H := Periodic.Model.loewner_entry_cng D
      ((chainNode i).isLt.trans_le hr) ((chainNode (tr j)).isLt.trans_le hr) hd
      (by rw [chainNode_zmod,chainNode_zmod]) rfl (hchain j).symm
    simpa only [←C_mul] using H

theorem delta_int1_ordered (he : Function.Injective e) (D : PoleData Fr p N)
    (hN : N<p*p) (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r D.singular) (xs z) (ys y))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0)
    (hcz : Covers p e (xs z)) (hcy : Covers p e (ys y)) :
    Int1 p (delta Fr p e xs ys z y) := by
  let tr:=chainTransport hzy hc
  let er : ChainIndex p r (xs z) → ι := lift hcz
  let ec : ChainIndex p r (xs z) → ι := fun i=>lift hcy (tr i)
  have her : Function.Injective er:=lift_injective hcz
  have hec : Function.Injective ec:=(lift_injective hcy).comp tr.injective
  have hr0 (a : ι) (ha : a∉Set.range er) : Sr Fr p e xs ys z a=0 := by
    apply Sr_support D hN hr
    intro H
    obtain ⟨j, hj⟩ := chain_image_of_mod hz (e a) H.symm
    exact ha ⟨j, he (by rw [lift_spec hcz j]; exact hj)⟩
  have hc0 (a : ι) (ha : a∉Set.range ec) : Sc Fr p e xs ys a y=0 := by
    apply Sc_support D hN hr
    intro H
    obtain ⟨j,hj⟩:=chain_image_of_mod hy (e a) H
    refine ha ⟨tr.symm j, ?_⟩
    apply he
    simp only [ec, Equiv.apply_symm_apply]
    rw [lift_spec hcy j]; exact hj
  have hrSum (f : ι→ℚ[X]) :
      (∑a,Sr Fr p e xs ys z a*f a)=∑i,Sr Fr p e xs ys z (er i)*f (er i) := by
    symm
    apply Fintype.sum_of_injective er her
    · intro a ha; rw [hr0 a ha,zero_mul]
    · intro i; rfl
  have hcSum (f : ι→ℚ[X]) :
      (∑a,f a*Sc Fr p e xs ys a y)=∑i,f (ec i)*Sc Fr p e xs ys (ec i) y := by
    symm
    apply Fintype.sum_of_injective ec hec
    · intro a ha; rw [hc0 a ha,mul_zero]
    · intro i; rfl
  have hneq (i j : ChainIndex p r (xs z)) : er i≠ec j := by
    intro H
    apply hd
    apply sub_eq_zero.mpr
    have H': ((e (er i)).val : ZMod p)=((e (ec j)).val : ZMod p):=
      congrArg (fun a:ι=>((e a).val:ZMod p)) H
    simpa only [er,ec,lift_zmod] using H'.symm
  have HB : ((Sr Fr p e xs ys)*(full Fr p e xs ys).toBlocks₁₂) z y =
      ∑i,Sr Fr p e xs ys z (er i)*C (Fr.Mn (chainNode i).val (ys y)) := by
    rw [Matrix.mul_apply,hrSum]
    simp only [full_B_apply, er, lift_val hcz]
  have HC : ((full Fr p e xs ys).toBlocks₂₁*Sc Fr p e xs ys) z y =
      ∑i,C (Fr.Mn (xs z) (chainNode (tr i)).val)*Sc Fr p e xs ys (ec i) y := by
    rw [Matrix.mul_apply,hcSum]
    simp only [full_C_apply, ec, lift_val hcy]
  have HA : (Sr Fr p e xs ys*(full Fr p e xs ys).toBlocks₁₁*Sc Fr p e xs ys) z y =
      ∑i,∑j,Sr Fr p e xs ys z (er i)*C (Fr.Mn (chainNode i).val (chainNode (tr j)).val)*
        Sc Fr p e xs ys (ec j) y := by
    rw [Matrix.mul_apply,hcSum]
    simp only [Matrix.mul_apply]
    simp_rw [hrSum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [full_A_apply_ne _ _ (hneq i j)]
    simp only [er, ec, lift_val hcz, lift_val hcy]
  have H:=restricted_delta_int1 he D hN hr hxN hyN z y hz hy hzy hc hd hcz hcy
  change Int1 p (_ - _ - _ + _) at H
  simpa only [delta,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    full_D_apply,HB,HC,HA,er,ec,tr] using H

theorem delta_int1_noCut (he : Function.Injective e) (D : PoleData Fr p N)
    (hN : N<p*p) (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y)
    (hc : NoCut (Cut p r D.singular)
      (min (xs z) (ys y)) (max (xs z) (ys y)))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0)
    (hcz : Covers p e (xs z)) (hcy : Covers p e (ys y)) :
    Int1 p (delta Fr p e xs ys z y) := by
  rcases le_total (xs z) (ys y) with hzy | hyz
  · have hzy' : (xs z:ℤ)≤ys y := by exact_mod_cast hzy
    exact delta_int1_ordered he D hN hr hxN hyN z y hz hy hzy
      (by simpa only [min_eq_left hzy',max_eq_right hzy'] using hc) hd hcz hcy
  · have hd' : (xs z : ZMod p)-(ys y : ZMod p)≠0 := by
      intro he'
      exact hd (sub_eq_zero.mpr (sub_eq_zero.mp he').symm)
    have hyz' : (ys y:ℤ)≤xs z := by exact_mod_cast hyz
    have H := delta_int1_ordered (xs:=ys) (ys:=xs) he D hN hr hyN hxN y z hy hz hyz
      (by simpa only [min_eq_right hyz',max_eq_left hyz'] using hc) hd' hcy hcz
    rw [delta_swap] at H
    exact H

theorem delta_int1_distinct (he : Function.Injective e) (D : PoleData Fr p N)
    (hN : N<p*p) (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y)
    (hc : NoCut (Cut p r D.singular) (min (xs z:ℤ) (ys y)) (max (xs z:ℤ) (ys y)))
    (hne : xs z≠ys y) (hcz : Covers p e (xs z)) (hcy : Covers p e (ys y)) :
    Int1 p (delta Fr p e xs ys z y) := by
  apply delta_int1_noCut he D hN hr hxN hyN z y hz hy hc _ hcz hcy
  intro he'
  have H := noCut_mod_ne (Fact.out : p.Prime).pos hne hc
  exact H ((ZMod.natCast_eq_natCast_iff' _ _ _).mp (sub_eq_zero.mp he').symm)

/-! ### The weighted bound -/

theorem delta_gle_weighted (he : Function.Injective e) (D : PoleData Fr p N)
    (hN : N<p*p) (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y)
    (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r D.singular) (min (xs z) (ys y)) (max (xs z) (ys y)) ∧
        Covers p e (xs z) ∧ Covers p e (ys y))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    ∀ z y,GLE p (W z y) (delta Fr p e xs ys z y) := by
  intro z y
  by_cases hw0 : W z y=0
  · rw [hw0,gle_iff_gn,pow_zero]
    obtain ⟨hc, hcz, hcy⟩ := hzero z y hw0
    exact delta_int1_distinct he D hN hr hx hy z y (hxlo z) (hylo y) hc (hne z y) hcz hcy
  by_cases hw1 : W z y=1
  · rw [hw1]
    exact delta_gle_one_at D hN hr hx hy z y (hone z y hw1)
  have hw2 : W z y=2 := by have:=hW z y; omega
  rw [hw2]
  exact delta_gle_two D hN hr hx hy z y

theorem T_entry_weighted (he : Function.Injective e) (D : PoleData Fr p N)
    (hN : N<p*p) (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y)
    (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r D.singular) (min (xs z) (ys y)) (max (xs z) (ys y)) ∧
        Covers p e (xs z) ∧ Covers p e (ys y))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    ∀ z y,GLE p (W z y) (Tscaled (Q Fr p e xs ys).det
      (full Fr p e xs ys).toBlocks₁₁ (full Fr p e xs ys).toBlocks₁₂
      (full Fr p e xs ys).toBlocks₂₁ (full Fr p e xs ys).toBlocks₂₂
      (Nmat p (fun _:ι=>1) (full Fr p e xs ys).toBlocks₁₁) z y) :=
  tcore_vec_T_cleared _ (Q_int1 D hN hr) (Q_primitive D hN hr) _
    (h_primitive D hN hr) (Sr Fr p e xs ys) (Sc Fr p e xs ys) W
    (Sr_residual_bound D hN hr hx) (Sc_residual_bound D hN hr hy)
    (delta_gle_weighted he D hN hr hx hy hxlo hylo hne W hW hzero hone)

theorem full_det_weighted (he : Function.Injective e) (D : PoleData Fr p N)
    (hN : N<p*p) (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y)
    (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r D.singular) (min (xs z) (ys y)) (max (xs z) (ys y)) ∧
        Covers p e (xs z) ∧ Covers p e (ys y))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    GLE p (tropVal W+2*Fintype.card ι) (full Fr p e xs ys).det := by
  simpa using tcore_scaled_weighted p (full Fr p e xs ys) (fun _:ι=>1)
    (Q_primitive D hN hr) W
    (T_entry_weighted he D hN hr hx hy hxlo hylo hne W hW hzero hone)

/-- **Weighted denominator bound for an arbitrary core.**  For a core `e : ι ↪ Fin r`, border
rows `xs` and columns `ys`, and a weight table `W` with entries at most `2`, zero only where no
cut separates the two border nodes and both residue classes lie in the core, and one only where
the residues differ, the `p`-adic denominator of `det Full(X)` is at most
`tropVal W + 2 |ι|`. -/
theorem member_det_weighted (he : Function.Injective e) (D : PoleData Fr p N)
    (hN : N<p*p) (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y)
    (W : Z→Z→ℕ) (hW : ∀z y,W z y≤2)
    (hzero : ∀z y,W z y=0 →
      NoCut (Cut p r D.singular) (min (xs z) (ys y)) (max (xs z) (ys y)) ∧
        Covers p e (xs z) ∧ Covers p e (ys y))
    (hone : ∀z y,W z y=1 → xs z%p≠ys y%p) :
    GLE p (tropVal W+2*Fintype.card ι)
      (Rect.FullN Fr (fun i:ι=>(e i).val) xs ys (X:ℚ[X])).det := by
  have H:=full_det_weighted he D hN hr hx hy hxlo hylo hne W hW hzero hone
  rw [full,det_rescale] at H
  exact GLE.of_rescale H

end CatalanCore.Uniform.Content.Layers.Del
