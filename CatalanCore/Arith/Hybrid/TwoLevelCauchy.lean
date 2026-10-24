module

public import CatalanCore.Arith.Hybrid.TwoLevelGLE
public import CatalanCore.Linalg.WeightedProjection
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

@[expose] public section

/-!
# G3 : the Cauchy projection into the two levels

A field-level, frame-free statement.  The zone is an abstract finite index `Z` with residue map
`resR resC : Z → ZMod p` (residues of the row and of the column node of an index).  The overfull cell supplies a row set `CR` and a column set `CC`.
Suppose, for the integral lift `Bl = p · T` of the scaled Schur complement:

* (lead) `Bl z y mod p = κ y · (resC y - resR z)⁻¹` for `z ∈ CR`, `y ∉ CC`, and symmetrically
  `Bl z y mod p = κ' z · (resC y - resR z)⁻¹` for `z ∉ CR`, `y ∈ CC`;
* (wt) for `z ∈ CR`, `y ∈ CC`, `Bl z y = p · T z y` with `T z y mod p = ∑_c F(z,c) w(c) G(c,y)`;
* (zero) the weight `w` vanishes at every residue outside `sb` that is not the residue of a node
  outside `CC` (rows) or outside `CR` (columns).

Then there is a two-level witness (`TwoLevelWit`) with `s` of size `σ = |CR| + |CC| - |Z|` and
corank bound `b = |sb|`.  No barycentric Cauchy basis is needed: the changes of basis are
*constant* matrices over `ZMod p` (lifted to `ℤ_(p)`), obtained by rank-nullity and basis
extension; the Cauchy structure enters only through the hypothesis (lead).
-/

open Polynomial CatalanCore.Basic CatalanCore.Linalg Matrix Module

namespace CatalanCore.Arith.Hybrid

section LinAlg

variable {F : Type*} [Field F] {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- Vectors supported on `R` whose image under `Cm` vanishes. -/
noncomputable def kerSub (R : Finset Z) {Y : Type*} [Fintype Y] (Cm : Matrix Z Y F) :
    Submodule F (Z → F) :=
  LinearMap.ker ((LinearMap.funLeft F F (Subtype.val : {z // z ∉ R} → Z)).prod
    (Matrix.vecMulLinear Cm))

lemma mem_kerSub {R : Finset Z} {Y : Type*} [Fintype Y] {Cm : Matrix Z Y F} {v : Z → F} :
    v ∈ kerSub R Cm ↔ (∀ z, z ∉ R → v z = 0) ∧ v ᵥ* Cm = 0 := by
  simp only [kerSub, LinearMap.mem_ker]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact ⟨fun z hz => congrFun h1 ⟨z, hz⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext (funext fun z => h1 z.1 z.2) h2

lemma card_le_finrank_kerSub (R : Finset Z) {Y : Type*} [Fintype Y] (Cm : Matrix Z Y F) :
    R.card ≤ finrank F (kerSub R Cm) + Fintype.card Y := by
  set Φ := (LinearMap.funLeft F F (Subtype.val : {z // z ∉ R} → Z)).prod (Matrix.vecMulLinear Cm)
  have h := LinearMap.finrank_range_add_finrank_ker Φ
  have hr : finrank F (LinearMap.range Φ) ≤
      finrank F (({z // z ∉ R} → F) × (Y → F)) := Submodule.finrank_le _
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype_compl, Fintype.card_coe] at hr
  rw [Module.finrank_fintype_fun_eq_card] at h
  have hR : R.card ≤ Fintype.card Z := Finset.card_le_univ R
  change R.card ≤ finrank F (LinearMap.ker Φ) + Fintype.card Y
  omega

/-- **Basis completion.** A subspace of dimension `≥ |s|` contributes the rows indexed by `s`
of an invertible matrix. -/
lemma exists_invertible_rows (W : Submodule F (Z → F)) (s : Finset Z)
    (hs : s.card ≤ finrank F W) :
    ∃ M : Matrix Z Z F, M.det ≠ 0 ∧ ∀ i ∈ s, M i ∈ W := by
  classical
  let b := Module.finBasis F W
  let f : s ≃ Fin s.card := s.equivFin
  let g : s → (Z → F) := fun i => (b (Fin.castLE hs (f i)) : Z → F)
  have hg : LinearIndependent F g := by
    have h1 : LinearIndependent F (fun i : s => b (Fin.castLE hs (f i))) :=
      b.linearIndependent.comp _ ((Fin.castLE_injective hs).comp f.injective)
    exact h1.map' W.subtype (Submodule.ker_subtype W)
  let bb := Basis.sumExtend hg
  haveI : Finite (↥s ⊕ Basis.sumExtendIndex hg) := Module.Finite.finite_basis bb
  haveI : Finite (Basis.sumExtendIndex hg) := Finite.of_injective (Sum.inr : Basis.sumExtendIndex hg → ↥s ⊕ Basis.sumExtendIndex hg)
    Sum.inr_injective
  letI : Fintype (Basis.sumExtendIndex hg) := Fintype.ofFinite _
  have hcard : Fintype.card s + Fintype.card (Basis.sumExtendIndex hg) = Fintype.card Z := by
    have := Module.finrank_eq_card_basis bb
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at this
    omega
  have hE : Fintype.card {z // z ∉ s} = Fintype.card (Basis.sumExtendIndex hg) := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    have : Fintype.card s = s.card := Fintype.card_coe s
    omega
  let e0 : Z ≃ s ⊕ Basis.sumExtendIndex hg :=
    (Equiv.sumCompl (· ∈ s)).symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivOfCardEq hE))
  refine ⟨Matrix.of fun i j => bb (e0 i) j, ?_, ?_⟩
  · have hli : LinearIndependent F (fun i => (Matrix.of fun i j => bb (e0 i) j) i) :=
      bb.linearIndependent.comp e0 e0.injective
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli)))
  · intro i hi
    have he : e0 i = Sum.inl ⟨i, hi⟩ := by
      simp [e0, Equiv.sumCompl_symm_apply_of_pos hi]
    have hb : bb (Sum.inl ⟨i, hi⟩) = g ⟨i, hi⟩ := by
      simp only [bb, Basis.sumExtend, Basis.reindex_apply, Equiv.symm_symm, Trans.trans,
        Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.ofInjective_apply,
        Equiv.Set.sumDiffSubset_apply_inl, Basis.extend_apply_self]
      erw [Equiv.symm_symm_apply, Equiv.trans_apply]
      erw [Equiv.sumCongr_apply, Sum.map_inl]
      erw [Equiv.Set.sumDiffSubset_apply_inl]
      rfl
    show (fun j => bb (e0 i) j) ∈ W
    rw [he]
    change bb (Sum.inl ⟨i, hi⟩) ∈ W
    rw [hb]
    exact (b _).2

end LinAlg


section Assemble

variable (p : ℕ) [Fact p.Prime]

/-- `a ∈ ZMod p` as a constant of `ℤ_(p)`. -/
noncomputable def liftZ (a : ZMod p) : LocRing p :=
  ⟨(a.val : ℚ), by exact_mod_cast int_mem_locRing (ℓ := p) (a.val : ℤ)⟩

lemma redQ_liftZ (a : ZMod p) : redQ p (liftZ p a) = a := by
  rw [redQ_apply]
  show (((a.val : ℕ) : ℚ) : ZMod p) = a
  rw [Rat.cast_natCast, ZMod.natCast_zmod_val]

lemma liftZ_zero : liftZ p (0 : ZMod p) = 0 := by
  apply Subtype.ext
  simp [liftZ]

/-- The constants of `𝔽_p` as a ring homomorphism into `𝔽_p(X)`. -/
noncomputable def rfCHom : ZMod p →+* RatFunc (ZMod p) :=
  (algebraMap (ZMod p)[X] (RatFunc (ZMod p))).comp Polynomial.C

lemma rfCHom_apply (a : ZMod p) : rfCHom p a = rfC p a := rfl

lemma phiP_liftZ (a : ZMod p) : phiP p (C (liftZ p a)) = rfCHom p a := by
  rw [phiP_C, redQ_liftZ]; rfl

/-- Entrywise lift of a constant matrix. -/
noncomputable def liftMat {Z : Type*} (M : Matrix Z Z (ZMod p)) : Matrix Z Z (LocRing p)[X] :=
  M.map fun a => C (liftZ p a)

lemma liftMat_map {Z : Type*} (M : Matrix Z Z (ZMod p)) :
    (liftMat p M).map (phiP p) = M.map (rfCHom p) := by
  ext i j
  simp [liftMat, phiP_liftZ]

lemma phiP_det_liftMat {Z : Type*} [Fintype Z] [DecidableEq Z] (M : Matrix Z Z (ZMod p))
    (hM : M.det ≠ 0) : phiP p (liftMat p M).det ≠ 0 := by
  rw [RingHom.map_det]
  have : (phiP p).mapMatrix (liftMat p M) = M.map (rfCHom p) := liftMat_map p M
  rw [this, ← (rfCHom p).mapMatrix_apply, ← RingHom.map_det]
  exact fun h => hM ((map_eq_zero_iff _ (rfCHom p).injective).1 h)

lemma phiP_eq_zero_of_dvd {x : (LocRing p)[X]} (h : C ((p : ℕ) : LocRing p) ∣ x) :
    phiP p x = 0 := (phiP_eq_zero_iff p x).2 h

lemma C_p_ne_zero : (C ((p : ℕ) : LocRing p) : (LocRing p)[X]) ≠ 0 := by
  rw [Ne, Polynomial.C_eq_zero]
  exact (prime_p p).ne_zero

/-- **G3 (Cauchy projection into the two levels).**  See the module docstring. -/
theorem exists_twoLevelWit_of_cauchy {Z : Type} [Fintype Z] [DecidableEq Z]
    (M : Matrix Z Z ℚ[X]) (Bl : Matrix Z Z (LocRing p)[X]) (u v : Z → ℕ)
    (hB : ∀ i j, toQ p (Bl i j) = C ((p : ℚ) ^ (u i + v j)) * M i j)
    (resR resC : Z → ZMod p) (CR CC : Finset Z)
    (hlead₁ : ∀ y, y ∉ CC → ∃ κ : RatFunc (ZMod p), ∀ z ∈ CR,
      phiP p (Bl z y) = κ * rfC p ((resC y - resR z)⁻¹))
    (hlead₂ : ∀ z, z ∉ CR → ∃ κ : RatFunc (ZMod p), ∀ y ∈ CC,
      phiP p (Bl z y) = κ * rfC p ((resC y - resR z)⁻¹))
    (w : ZMod p → RatFunc (ZMod p))
    (hwt : ∀ z ∈ CR, ∀ y ∈ CC, ∃ T : (LocRing p)[X],
      Bl z y = C ((p : ℕ) : LocRing p) * T ∧
      phiP p T = ∑ c : ZMod p, rfC p ((c - resR z)⁻¹) * w c * rfC p ((c - resC y)⁻¹))
    (sb : Finset (ZMod p))
    (hzero : ∀ c, c ∉ sb → w c = 0 ∨ (∃ y, y ∉ CC ∧ resC y = c) ∨ (∃ z, z ∉ CR ∧ resR z = c)) :
    ∃ W : TwoLevelWit p M sb.card, W.u = u ∧ W.v = v ∧
      W.s.card = CR.card + CC.card - Fintype.card Z ∧ W.cost = ∑ i, u i + ∑ j, v j -
        ((CR.card + CC.card - Fintype.card Z) +
          ((CR.card + CC.card - Fintype.card Z) - sb.card)) := by
  classical
  -- the two kernel spaces over `𝔽_p`
  let CL : Matrix Z {y // y ∉ CC} (ZMod p) := fun z y => (resC y.1 - resR z)⁻¹
  let CRm : Matrix Z {z // z ∉ CR} (ZMod p) := fun y z => (resR z.1 - resC y)⁻¹
  have h1 := card_le_finrank_kerSub CR CL
  have h2 := card_le_finrank_kerSub CC CRm
  have hcC : Fintype.card {y // y ∉ CC} = Fintype.card Z - CC.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have hcR : Fintype.card {z // z ∉ CR} = Fintype.card Z - CR.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have hCRle : CR.card ≤ Fintype.card Z := Finset.card_le_univ CR
  have hCCle : CC.card ≤ Fintype.card Z := Finset.card_le_univ CC
  set σ := CR.card + CC.card - Fintype.card Z with hσ
  obtain ⟨s, -, hs_card⟩ := Finset.exists_subset_card_eq
    (show σ ≤ (Finset.univ : Finset Z).card by rw [Finset.card_univ]; omega)
  obtain ⟨ML, hMLdet, hMLrows⟩ := exists_invertible_rows (kerSub CR CL) s (by omega)
  obtain ⟨MP, hMPdet, hMProws⟩ := exists_invertible_rows (kerSub CC CRm) s (by omega)
  -- the lifted changes of basis
  let L : Matrix Z Z (LocRing p)[X] := liftMat p ML
  let P : Matrix Z Z (LocRing p)[X] := (liftMat p MP).transpose
  have hLphi : ∀ i z, phiP p (L i z) = rfCHom p (ML i z) := fun i z => phiP_liftZ p _
  have hPphi : ∀ y j, phiP p (P y j) = rfCHom p (MP j y) := fun y j => phiP_liftZ p _
  -- support and kernel properties
  have hLsupp : ∀ i ∈ s, ∀ z, z ∉ CR → ML i z = 0 := fun i hi z hz =>
    ((mem_kerSub.1 (hMLrows i hi)).1 z hz)
  have hLker : ∀ i ∈ s, ∀ y, y ∉ CC → ∑ z, ML i z * (resC y - resR z)⁻¹ = 0 := by
    intro i hi y hy
    have := congrFun (mem_kerSub.1 (hMLrows i hi)).2 ⟨y, hy⟩
    simpa [Matrix.vecMul, dotProduct, CL] using this
  have hPsupp : ∀ j ∈ s, ∀ y, y ∉ CC → MP j y = 0 := fun j hj y hy =>
    ((mem_kerSub.1 (hMProws j hj)).1 y hy)
  have hPker : ∀ j ∈ s, ∀ z, z ∉ CR → ∑ y, MP j y * (resR z - resC y)⁻¹ = 0 := by
    intro j hj z hz
    have := congrFun (mem_kerSub.1 (hMProws j hj)).2 ⟨z, hz⟩
    simpa [Matrix.vecMul, dotProduct, CRm] using this
  have hLz : ∀ i ∈ s, ∀ z, z ∉ CR → L i z = 0 := fun i hi z hz => by
    simp [L, liftMat, hLsupp i hi z hz, liftZ_zero]
  have hPz : ∀ j ∈ s, ∀ y, y ∉ CC → P y j = 0 := fun j hj y hy => by
    simp [P, liftMat, Matrix.transpose_apply, hPsupp j hj y hy, liftZ_zero]
  have hcellzero : ∀ z ∈ CR, ∀ y ∈ CC, phiP p (Bl z y) = 0 := by
    intro z hz y hy
    obtain ⟨T, hT, -⟩ := hwt z hz y hy
    exact phiP_eq_zero_of_dvd p (hT ▸ dvd_mul_right _ _)
  -- row/column annihilation modulo `p`
  have hrowzero : ∀ i ∈ s, ∀ y, ∑ z, rfCHom p (ML i z) * phiP p (Bl z y) = 0 := by
    intro i hi y
    by_cases hy : y ∈ CC
    · apply Finset.sum_eq_zero
      intro z _
      by_cases hz : z ∈ CR
      · rw [hcellzero z hz y hy, mul_zero]
      · rw [hLsupp i hi z hz, map_zero, zero_mul]
    · obtain ⟨κ, hκ⟩ := hlead₁ y hy
      have : ∑ z, rfCHom p (ML i z) * phiP p (Bl z y) =
          κ * rfCHom p (∑ z, ML i z * (resC y - resR z)⁻¹) := by
        rw [map_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z ∈ CR
        · rw [hκ z hz]; simp only [← rfCHom_apply, map_mul]; ring
        · rw [hLsupp i hi z hz]; simp
      rw [this, hLker i hi y hy, map_zero, mul_zero]
  have hcolzero : ∀ j ∈ s, ∀ z, ∑ y, phiP p (Bl z y) * rfCHom p (MP j y) = 0 := by
    intro j hj z
    by_cases hz : z ∈ CR
    · apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y ∈ CC
      · rw [hcellzero z hz y hy, zero_mul]
      · rw [hPsupp j hj y hy, map_zero, mul_zero]
    · obtain ⟨κ, hκ⟩ := hlead₂ z hz
      have : ∑ y, phiP p (Bl z y) * rfCHom p (MP j y) =
          -(κ * rfCHom p (∑ y, MP j y * (resR z - resC y)⁻¹)) := by
        rw [map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ CC
        · have e : (resC y - resR z)⁻¹ = -(resR z - resC y)⁻¹ := by rw [← inv_neg, neg_sub]
          rw [hκ y hy, e]
          simp only [← rfCHom_apply, map_neg, map_mul]
          ring
        · rw [hPsupp j hj y hy]; simp
      rw [this, hPker j hj z hz, map_zero, mul_zero, neg_zero]
  -- the mod-`p` matrices
  have hphiMul : ∀ i j, phiP p ((L * Bl * P) i j) =
      ∑ y, (∑ z, rfCHom p (ML i z) * phiP p (Bl z y)) * rfCHom p (MP j y) := by
    intro i j
    simp only [Matrix.mul_apply, map_sum, map_mul, hLphi, hPphi]
  have hrow : ∀ i ∈ s, ∀ j, C ((p : ℕ) : LocRing p) ∣ (L * Bl * P) i j := by
    intro i hi j
    rw [← phiP_eq_zero_iff p, hphiMul]
    apply Finset.sum_eq_zero
    intro y _
    rw [hrowzero i hi y, zero_mul]
  have hcol : ∀ i, ∀ j ∈ s, C ((p : ℕ) : LocRing p) ∣ (L * Bl * P) i j := by
    intro i j hj
    rw [← phiP_eq_zero_iff p, hphiMul]
    have : ∑ y, (∑ z, rfCHom p (ML i z) * phiP p (Bl z y)) * rfCHom p (MP j y) =
        ∑ z, rfCHom p (ML i z) * ∑ y, phiP p (Bl z y) * rfCHom p (MP j y) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro y _; ring
    rw [this]
    apply Finset.sum_eq_zero; intro z _; rw [hcolzero j hj z, mul_zero]
  -- the divided block
  choose! Tm hTm1 hTm2 using hwt
  let Tm' : Z → Z → (LocRing p)[X] := fun z y => if z ∈ CR ∧ y ∈ CC then Tm z y else 0
  have hquot : ∀ i ∈ s, ∀ j ∈ s, (L * Bl * P) i j =
      C ((p : ℕ) : LocRing p) * ∑ z, ∑ y, L i z * Tm' z y * P y j := by
    intro i hi j hj
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro y _
    by_cases hz : z ∈ CR
    · by_cases hy : y ∈ CC
      · rw [hTm1 z hz y hy]; simp only [Tm', if_pos (And.intro hz hy)]; ring
      · rw [hPz j hj y hy]; simp
    · rw [hLz i hi z hz]; simp
  have hq : ∀ i ∈ s, ∀ j ∈ s, quotP p ((L * Bl * P) i j) =
      ∑ z, ∑ y, L i z * Tm' z y * P y j := by
    intro i hi j hj
    apply mul_left_cancel₀ (C_p_ne_zero p)
    rw [quotP_spec p (by rw [hquot i hi j hj]; exact dvd_mul_right _ _), hquot i hi j hj]
  let Lw : Matrix s Z (RatFunc (ZMod p)) := Matrix.of fun i z => rfCHom p (ML i z)
  let Fm : Matrix Z (ZMod p) (RatFunc (ZMod p)) := Matrix.of fun z c => rfC p ((c - resR z)⁻¹)
  let Gm : Matrix (ZMod p) Z (RatFunc (ZMod p)) := Matrix.of fun c y => rfC p ((c - resC y)⁻¹)
  let Rw : Matrix Z s (RatFunc (ZMod p)) := Matrix.of fun y j => rfCHom p (MP j y)
  have hpt : ∀ (i j : s) (z y : Z), phiP p (L i z * Tm' z y * P y j) =
      rfCHom p (ML i z) * (∑ c : ZMod p, rfC p ((c - resR z)⁻¹) * w c * rfC p ((c - resC y)⁻¹)) *
        rfCHom p (MP j y) := by
    intro i j z y
    rw [map_mul, map_mul, hLphi, hPphi]
    by_cases hz : z ∈ CR
    · by_cases hy : y ∈ CC
      · simp only [Tm', if_pos (And.intro hz hy), hTm2 z hz y hy]
      · rw [hPsupp j.1 j.2 y hy]; simp
    · rw [hLsupp i.1 i.2 z hz]; simp
  have hHeq : (Matrix.of fun i j : s => phiP p (quotP p ((L * Bl * P) i j))) =
      Lw * (Fm * Matrix.diagonal w * Gm) * Rw := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply]
    rw [hq i.1 i.2 j.1 j.2, map_sum]
    set G3 : Matrix Z Z (RatFunc (ZMod p)) := Fm * Matrix.diagonal w * Gm with hG3def
    have hG3 : ∀ z y, G3 z y =
        ∑ c : ZMod p, rfC p ((c - resR z)⁻¹) * w c * rfC p ((c - resC y)⁻¹) := by
      intro z y
      rw [hG3def, Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.of_apply, Fm, Gm]
    have hL1 : ∀ z, phiP p (∑ y, L i z * Tm' z y * P y j) =
        ∑ y, Lw i z * G3 z y * Rw y j := by
      intro z
      rw [map_sum]
      apply Finset.sum_congr rfl; intro y _
      rw [hpt i j z y, hG3]; rfl
    simp only [map_sum] at hL1 ⊢
    rw [Finset.sum_congr rfl (fun z _ => hL1 z)]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  refine ⟨{ Bl := Bl, u := u, v := v, hB := hB, s := s, L := L, P := P, hL := ?_, hP := ?_,
            hrow := hrow, hcol := hcol, hH := ?_ }, rfl, rfl, hs_card, ?_⟩
  · exact phiP_det_liftMat p ML hMLdet
  · change phiP p (liftMat p MP).transpose.det ≠ 0
    rw [Matrix.det_transpose]
    exact phiP_det_liftMat p MP hMPdet
  · rw [hHeq]
    refine weighted_projection_rank Fm Gm Lw Rw w sb ?_
    intro c hc
    rcases hzero c hc with h | ⟨y, hy, hyc⟩ | ⟨z, hz, hzc⟩
    · exact Or.inl h
    · right; left
      intro u'
      subst hyc
      have hk := hLker u'.1 u'.2 y hy
      have : (Lw * Fm) u' (resC y) = rfCHom p (∑ z, ML u'.1 z * (resC y - resR z)⁻¹) := by
        simp only [Matrix.mul_apply, map_sum, map_mul, Lw, Fm]; rfl
      rw [this, hk, map_zero]
    · right; right
      intro v'
      subst hzc
      have hk := hPker v'.1 v'.2 z hz
      have : (Gm * Rw) (resR z) v' = rfCHom p (∑ y, MP v'.1 y * (resR z - resC y)⁻¹) := by
        simp only [Matrix.mul_apply, map_sum, map_mul, Gm, Rw]
        apply Finset.sum_congr rfl; intro y _
        change _ = rfCHom p _ * rfCHom p _
        rw [mul_comm]; rfl
      rw [this, hk, map_zero]
  · simp only [TwoLevelWit.cost, hs_card, hσ]

/-- **G3, determinant form.**  Same hypotheses as `exists_twoLevelWit_of_cauchy`; the conclusion is
the `GLE` bound with the two-level saving `σ + (σ - b)`, `σ = |CR| + |CC| - |Z|`, `b = |sb|`. -/
theorem gle_det_of_cauchy {Z : Type} [Fintype Z] [DecidableEq Z]
    (M : Matrix Z Z ℚ[X]) (Bl : Matrix Z Z (LocRing p)[X]) (u v : Z → ℕ)
    (hB : ∀ i j, toQ p (Bl i j) = C ((p : ℚ) ^ (u i + v j)) * M i j)
    (resR resC : Z → ZMod p) (CR CC : Finset Z)
    (hlead₁ : ∀ y, y ∉ CC → ∃ κ : RatFunc (ZMod p), ∀ z ∈ CR,
      phiP p (Bl z y) = κ * rfC p ((resC y - resR z)⁻¹))
    (hlead₂ : ∀ z, z ∉ CR → ∃ κ : RatFunc (ZMod p), ∀ y ∈ CC,
      phiP p (Bl z y) = κ * rfC p ((resC y - resR z)⁻¹))
    (w : ZMod p → RatFunc (ZMod p))
    (hwt : ∀ z ∈ CR, ∀ y ∈ CC, ∃ T : (LocRing p)[X],
      Bl z y = C ((p : ℕ) : LocRing p) * T ∧
      phiP p T = ∑ c : ZMod p, rfC p ((c - resR z)⁻¹) * w c * rfC p ((c - resC y)⁻¹))
    (sb : Finset (ZMod p))
    (hzero : ∀ c, c ∉ sb → w c = 0 ∨ (∃ y, y ∉ CC ∧ resC y = c) ∨ (∃ z, z ∉ CR ∧ resR z = c)) :
    GLE p (∑ i, u i + ∑ j, v j -
        ((CR.card + CC.card - Fintype.card Z) +
          ((CR.card + CC.card - Fintype.card Z) - sb.card))) M.det := by
  obtain ⟨W, -, -, -, hW⟩ :=
    exists_twoLevelWit_of_cauchy p M Bl u v hB resR resC CR CC hlead₁ hlead₂ w hwt sb hzero
  rw [← hW]
  exact W.gle

end Assemble

end CatalanCore.Arith.Hybrid

#print axioms CatalanCore.Arith.Hybrid.exists_twoLevelWit_of_cauchy
#print axioms CatalanCore.Arith.Hybrid.gle_det_of_cauchy
