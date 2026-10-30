module
public import CatalanCore.Arith.Hybrid.ShiftMoments
public import CatalanCore.Arith.Hybrid.ResponseLongChain
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # Reduction of the first-order partners to the reduced chain model

For a zone node `x ≥ r`, the row partner `Sr_x` is supported on the chain of `x`; modulo `p` it is
`h · Q̄⁻¹ b̄`, where `Q̄ = poleRed` of the chain and `b̄` the reduced pole row of `x`. -/

open ChainClasses

section SumChain
variable {p r : ℕ} [Fact p.Prime]

/-- A function on the core supported on the residue class of `x ≥ r` sums over the chain. -/
theorem sum_chain {M : Type*} [AddCommMonoid M] {x : ℕ} (hx : r ≤ x) (f : Fin r → M)
    (hf : ∀ m : Fin r, m.val % p ≠ x % p → f m = 0) :
    ∑ m, f m = ∑ j : ChainIndex p r x, f (chainNode j) := by
  classical
  have hinj := chainNode_injective (p := p) (r := r) (z := x) (Fact.out : p.Prime).pos
  rw [← Finset.sum_image (f := f) (g := chainNode) (fun a _ b _ h => hinj h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro m _ hm
  apply hf
  intro hmod
  obtain ⟨j, hj⟩ := chain_image_of_mod (p := p) hx m hmod
  exact hm (Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩)

end SumChain

section Entries
variable {p o N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- The `p²`-scaled entry and the pole entry have the same reduction (same residue). -/
theorem red_pse_eq (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) {a b : ℕ}
    (ha : a<N) (hb : b<N) (hc : a%p=b%p) :
    red p (poleScaledEntry Fr p o a b) = red p ((p:ℚ)^2 * Fr.Mn a b) := by
  have H := square_entry_pole_cng hL hp hN ha hb hc
  have hm1 : (p:ℚ)^2 * Fr.Mn a b ∈ LocRing p := Mn_square_mem hL hp hN ha hb
  have hm2 : poleScaledEntry Fr p o a b ∈ LocRing p := poleScaledEntry_mem hL hp hN ha hb hc
  have := (LemmaE.cng_C_iff hm1 hm2).1 H
  exact this.symm

end Entries


section Chain
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

/-- The reduction of the actual chain matrix is the reduced pole model of its nodes. -/
theorem redI_chainMatrix (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) {x : ℕ}
    (j i : ChainIndex p r x) :
    redI p (chainMatrix (p:=p) Fr r x j i) =
      poleRed Fr p o (fun j : ChainIndex p r x => (chainNode j).val) j i := by
  have H := chainMatrix_cng_pole hL hp hN hr j i
  have hmod : (chainNode j).val % p = (chainNode i).val % p := by
    rw [chainNode_mod, chainNode_mod]
  have hj : (chainNode j).val < N := lt_of_lt_of_le (chainNode j).isLt hr
  have hi : (chainNode i).val < N := lt_of_lt_of_le (chainNode i).isLt hr
  have hmem : poleScaledEntry Fr p o (chainNode j).val (chainNode i).val ∈ LocRing p :=
    poleScaledEntry_mem hL hp hN hj hi hmod
  have hG : GLE p 0 (C (poleScaledEntry Fr p o (chainNode j).val (chainNode i).val) +
      X * (if j = i then (1:ℚ[X]) else 0)) := by
    refine GLE.add (GLE.C_iff.2 (by simpa using hmem)) ?_
    by_cases hji : j = i
    · simpa [hji] using (gle0_mul GLE.X GLE.one)
    · simpa [hji] using GLE.zero 0
  have hG' : GLE p 0 (chainMatrix (p:=p) Fr r x j i) :=
    gle0_of_int1 (LemmaE.Cng.int1_of_right H (int1_of_gle0 hG))
  rw [redI_cng hG' hG H]
  rw [redI_add (GLE.C_iff.2 (by simpa using hmem))
    (by by_cases hji : j = i
        · simpa [hji] using (gle0_mul GLE.X GLE.one)
        · simpa [hji] using GLE.zero 0), redI_C hmem]
  by_cases hji : j = i
  · subst hji
    simp [poleRed, redI_mul GLE.X GLE.one, redI_X, redI_one]
  · simp [poleRed, hji, redI_zero]


/-- The `p²`-scaled zone-to-core entry reduces to the pole entry. -/
theorem redI_C2 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z, xs z<N) (z : Z) (i : Fin r) (hmod : xs z % p = i.val % p) :
    redI p (ChainModel.C2 Fr p r xs ys z i) =
      rfC p (red p (poleScaledEntry Fr p o (xs z) i.val)) := by
  have hi : i.val < N := lt_of_lt_of_le i.isLt hr
  have hmem : (p:ℚ)^2 * Fr.Mn (xs z) i.val ∈ LocRing p := Mn_square_mem hL hp hN (hx z) hi
  rw [ChainModel.C2_apply, redI_C hmem, red_pse_eq hL hp hN (hx z) hi hmod]

/-- **Row solve on the chain, polynomial level.** -/
theorem Sr_chain_eq (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) (z : Z)
    (hxz : r ≤ xs z) (i : ChainIndex p r (xs z)) :
    ∑ j : ChainIndex p r (xs z), ChainModel.Sr Fr p r xs ys z (chainNode j) *
        chainMatrix (p:=p) Fr r (xs z) j i =
      ChainModel.h Fr p r xs ys * ChainModel.C2 Fr p r xs ys z (chainNode i) := by
  have hS : ChainModel.Sr Fr p r xs ys * ChainModel.Q0 Fr p r xs ys =
      ChainModel.h Fr p r xs ys •
        LemmaE.blockRect (fun z => xs z % p) (fun i : Fin r => i.val % p)
          (ChainModel.C2 Fr p r xs ys) :=
    LemmaE.modelRow_mul _ _ _ _
  have H := congrFun (congrFun hS z) (chainNode i)
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at H
  have hb : LemmaE.blockRect (fun z => xs z % p) (fun i : Fin r => i.val % p)
      (ChainModel.C2 Fr p r xs ys) z (chainNode i) = ChainModel.C2 Fr p r xs ys z (chainNode i) := by
    simp [LemmaE.blockRect, (chainNode_mod i).symm]
  rw [hb] at H
  rw [← H]
  rw [sum_chain (p := p) hxz (fun m => ChainModel.Sr Fr p r xs ys z m *
      ChainModel.Q0 Fr p r xs ys m (chainNode i))]
  · apply Finset.sum_congr rfl; intro j _
    congr 1
    have := congrFun (congrFun (Q0_chain (Fr := Fr) (r := r) (z := xs z) (p := p) xs ys) j) i
    simpa using this.symm
  · intro m hm
    have : ChainModel.Sr Fr p r xs ys z m = 0 :=
      ChainModel.Sr_support hL hp hN hr z m (fun h => hm h.symm)
    rw [this, zero_mul]

end Chain



section Red2
variable {p o N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- `p ·` the full cumulative and `p ·` the pole cumulative have the same reduction. -/
theorem red_pPf_eq_poleL (hL : LamData Fr o) (hN : 4*N<p*p) {a : ℕ} (ha : a<N) :
    red p ((p:ℚ) * fullPrefix Fr a) = red p ((p:ℚ) * polePrefix Fr p o a) := by
  have hreg : ∀ k, Good p ((p:ℚ) * regularDelta p (o:ℤ) (k:ℤ)) 0 := fun k => by
    have := (Good.natCast (ℓ := p) p).mul (good_regularDelta (p := p) (o:ℤ) (k:ℤ))
    simpa using this
  have hsum : Good p ((p:ℚ) * ∑ k ∈ Icc 1 a, regularDelta p (o:ℤ) (k:ℤ)) 0 := by
    rw [Finset.mul_sum]
    have := Good.sum (ℓ := p) (Icc 1 a) (fun k => (p:ℚ) * regularDelta p (o:ℤ) (k:ℤ))
      (fun _ => (0 : ZMod p)) (fun k _ => hreg k)
    simpa using this
  have hpole := good_red (p_polePrefix_mem hL hN ha)
  have hE : (p:ℚ) * fullPrefix Fr a =
      (p:ℚ) * polePrefix Fr p o a + (p:ℚ) * ∑ k ∈ Icc 1 a, regularDelta p (o:ℤ) (k:ℤ) := by
    unfold fullPrefix polePrefix poleDelta
    simp only [Finset.sum_sub_distrib]
    ring
  have := (hpole.add hsum).eq
  rw [← hE] at this
  simpa using this

theorem redI_pPf (hL : LamData Fr o) (hN : 4*N<p*p) {a : ℕ} (ha : a<N) :
    redI p (C ((p:ℚ) * fullPrefix Fr a)) = poleL Fr p o a := by
  have hmem : (p:ℚ) * fullPrefix Fr a ∈ LocRing p := by
    have hG := good_interval_delta (p := p) (Fr := Fr) (o := o) (A := 0) hL hN ha
    have he : Ioc 0 a = Icc 1 a := by ext t; simp only [mem_Ioc, mem_Icc]; omega
    rw [he] at hG
    exact hG.mem
  rw [redI_C hmem, red_pPf_eq_poleL hL hN ha]
  rfl

/-- Symmetric solve: `s M = c b` gives `s = c M⁻¹ b`. -/
theorem solve_symm {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hM : M.transpose = M) (hu : IsUnit M.det) (s b : ι → K) (c : K)
    (h : ∀ i, ∑ j, s j * M j i = c * b i) (j : ι) : s j = c * (M⁻¹ *ᵥ b) j := by
  have h1 : s ᵥ* M = c • b := funext fun i => by simpa [Matrix.vecMul, dotProduct] using h i
  have h2 : s = (c • b) ᵥ* M⁻¹ := by
    rw [← h1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
  have h3 : (c • b) ᵥ* M⁻¹ = c • (M⁻¹ *ᵥ b) := by
    have hT : (M⁻¹).transpose = M⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hM]
    rw [Matrix.smul_vecMul, ← Matrix.mulVec_transpose, hT]
  have := congrFun (h2.trans h3) j
  simpa using this

end Red2


section Moments2
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

theorem gle0_chainMatrix (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) {x : ℕ}
    (j i : ChainIndex p r x) : GLE p 0 (chainMatrix (p:=p) Fr r x j i) := by
  have H := chainMatrix_cng_pole hL hp hN hr j i
  have hmod : (chainNode j).val % p = (chainNode i).val % p := by
    rw [chainNode_mod, chainNode_mod]
  have hj : (chainNode j).val < N := lt_of_lt_of_le (chainNode j).isLt hr
  have hi : (chainNode i).val < N := lt_of_lt_of_le (chainNode i).isLt hr
  have hmem : poleScaledEntry Fr p o (chainNode j).val (chainNode i).val ∈ LocRing p :=
    poleScaledEntry_mem hL hp hN hj hi hmod
  have hG : GLE p 0 (C (poleScaledEntry Fr p o (chainNode j).val (chainNode i).val) +
      X * (if j = i then (1:ℚ[X]) else 0)) := by
    refine GLE.add (GLE.C_iff.2 (by simpa using hmem)) ?_
    by_cases hji : j = i
    · simpa [hji] using (gle0_mul GLE.X GLE.one)
    · simpa [hji] using GLE.zero 0
  exact gle0_of_int1 (LemmaE.Cng.int1_of_right H (int1_of_gle0 hG))

theorem gle0_h (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    GLE p 0 (ChainModel.h Fr p r xs ys) :=
  gle0_of_int1 (by
    have := ChainModel.h_primitive (xs := xs) (ys := ys) hL hp hN hr
    unfold LemmaE.Int1; exact this.le)

/-- **The first-order row partner reduces to the source solve of its chain.** -/
theorem redI_Sr_chain (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z, xs z<N) (z : Z) (hxz : r ≤ xs z) (j : ChainIndex p r (xs z)) :
    redI p (ChainModel.Sr Fr p r xs ys z (chainNode j)) =
      redI p (ChainModel.h Fr p r xs ys) *
        ((poleRed Fr p o (fun j : ChainIndex p r (xs z) => (chainNode j).val))⁻¹ *ᵥ
          (fun i => rfC p (red p (poleScaledEntry Fr p o (chainNode i).val (xs z))))) j := by
  set a : ChainIndex p r (xs z) → ℕ := fun j => (chainNode j).val with ha
  have hM : (poleRed Fr p o a).transpose = poleRed Fr p o a := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [poleRed]
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [poleRed, hij, hji, poleScaledEntry_symm (Fr := Fr) (p := p) (o := o) (a i) (a j)]
  refine solve_symm (poleRed Fr p o a) hM (isUnit_det_poleRed a)
    (fun j => redI p (ChainModel.Sr Fr p r xs ys z (chainNode j)))
    (fun i => rfC p (red p (poleScaledEntry Fr p o (chainNode i).val (xs z))))
    (redI p (ChainModel.h Fr p r xs ys)) ?_ j
  intro i
  have H := congrArg (redI p) (Sr_chain_eq (ys := ys) hL hp hN hr z hxz i)
  have hSr : ∀ m, GLE p 0 (ChainModel.Sr Fr p r xs ys z m) := fun m =>
    gle0_of_int1 (ChainModel.Sr_int1 hL hp hN hr hx z m)
  rw [redI_sum _ _ (fun j _ => gle0_mul (hSr _) (gle0_chainMatrix hL hp hN hr j i))] at H
  simp only [redI_mul (hSr _) (gle0_chainMatrix hL hp hN hr _ i),
    redI_chainMatrix hL hp hN hr] at H
  rw [redI_mul (gle0_h hL hp hN hr) (gle0_of_int1 (ChainModel.C2_int1 hL hp hN hr hx z _))] at H
  rw [redI_C2 hL hp hN hr hx z (chainNode i) (chainNode_mod i).symm] at H
  rw [H, poleScaledEntry_symm (Fr := Fr) (p := p) (o := o)]

end Moments2

section Moments3
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

theorem redI_h_ne_zero (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    redI p (ChainModel.h Fr p r xs ys) ≠ 0 :=
  redI_ne_zero_of_gn_eq_one (gle0_h hL hp hN hr) (ChainModel.h_primitive hL hp hN hr)

/-- Sum of the reduced partner row over the core equals the sum over the chain. -/
theorem sum_redI_Sr_chain (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z, xs z<N) (z : Z) (hxz : r ≤ xs z) (w : Fin r → RatFunc (ZMod p)) :
    ∑ m, redI p (ChainModel.Sr Fr p r xs ys z m) * w m =
      redI p (ChainModel.h Fr p r xs ys) *
        ∑ j : ChainIndex p r (xs z),
          ((poleRed Fr p o (fun j : ChainIndex p r (xs z) => (chainNode j).val))⁻¹ *ᵥ
            (fun i => rfC p (red p (poleScaledEntry Fr p o (chainNode i).val (xs z))))) j *
              w (chainNode j) := by
  rw [sum_chain (p := p) hxz (fun m => redI p (ChainModel.Sr Fr p r xs ys z m) * w m)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [redI_Sr_chain hL hp hN hr hx z hxz j]; ring
  · intro m hm
    have : ChainModel.Sr Fr p r xs ys z m = 0 :=
      ChainModel.Sr_support hL hp hN hr z m (fun h => hm h.symm)
    rw [this, redI_zero, zero_mul]

end Moments3


section Moments4
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N) (hy : ∀ y, ys y<N)
include hL hp hN hr hk hx hy

/-- **Leading moment `α_z` is the source moment `B` of its chain** (up to the unit `det Q`). -/
theorem redI_aR (z : Z) (hxz : r ≤ xs z) :
    redI p (ChainModel.aR Fr p r xs ys z) = redI p (ChainModel.Q Fr p r xs ys).det *
      sourceB Fr p o (fun j : ChainIndex p r (xs z) => (chainNode j).val) (xs z) := by
  have hcng := ChainModel.aR_lead (xs := xs) (ys := ys) hL hp hN hr hk hx z
  have hSr : ∀ m, GLE p 0 (ChainModel.Sr Fr p r xs ys z m) := fun m =>
    gle0_of_int1 (ChainModel.Sr_int1 hL hp hN hr hx z m)
  have hh := gle0_h (xs := xs) (ys := ys) hL hp hN hr
  have g1 : GLE p 0 (ChainModel.h Fr p r xs ys * ChainModel.aR Fr p r xs ys z) :=
    gle0_mul hh (gle0_of_int1 (ChainModel.int1_aR hL hp hN hr hx hy z))
  have hsum : GLE p 0 (∑ m, ChainModel.Sr Fr p r xs ys z m) := GLE.sum fun m _ => hSr m
  have g2 : GLE p 0 ((ChainModel.Q Fr p r xs ys).det *
      (ChainModel.h Fr p r xs ys - ∑ m, ChainModel.Sr Fr p r xs ys z m)) :=
    gle0_mul (ChainModel.gle0_det hL hp hN hr) (gle0_of_int1
      ((int1_of_gle0 hh).sub (int1_of_gle0 hsum)))
  have e := redI_cng g1 g2 hcng
  rw [redI_mul hh (gle0_of_int1 (ChainModel.int1_aR hL hp hN hr hx hy z)),
    redI_mul (ChainModel.gle0_det hL hp hN hr) (gle0_of_int1
      ((int1_of_gle0 hh).sub (int1_of_gle0 hsum))),
    redI_sub hh hsum, redI_sum _ _ (fun m _ => hSr m)] at e
  have hs := sum_redI_Sr_chain (ys := ys) hL hp hN hr hx z hxz (fun _ => 1)
  simp only [mul_one] at hs
  rw [hs] at e
  unfold sourceB
  apply mul_left_cancel₀ (redI_h_ne_zero (xs := xs) (ys := ys) hL hp hN hr)
  linear_combination e

/-- **Leading moment `p β_z` is the source moment `A` of its chain** (up to the unit `det Q`). -/
theorem redI_bR (z : Z) (hxz : r ≤ xs z) :
    redI p (ChainModel.bR Fr p r xs ys z) = redI p (ChainModel.Q Fr p r xs ys).det *
      sourceA Fr p o (fun j : ChainIndex p r (xs z) => (chainNode j).val) (xs z) := by
  have hcng := ChainModel.bR_lead (xs := xs) (ys := ys) hL hp hN hr hk hx z
  have hSr : ∀ m, GLE p 0 (ChainModel.Sr Fr p r xs ys z m) := fun m =>
    gle0_of_int1 (ChainModel.Sr_int1 hL hp hN hr hx z m)
  have hh := gle0_h (xs := xs) (ys := ys) hL hp hN hr
  have hP : ∀ m : Fin r, GLE p 0 (C ((p:ℚ) * fullPrefix Fr m.val)) := fun m =>
    ChainModel.gle0_pPf hL hp hN hr (lt_of_lt_of_le m.isLt hr)
  have hPz : GLE p 0 (C ((p:ℚ) * fullPrefix Fr (xs z))) := ChainModel.gle0_pPf hL hp hN hr (hx z)
  have hbR := gle0_of_int1 (ChainModel.int1_bR hL hp hN hr hx hy z)
  have g1 : GLE p 0 (ChainModel.h Fr p r xs ys * ChainModel.bR Fr p r xs ys z) :=
    gle0_mul hh hbR
  have hsum : GLE p 0 (∑ m, ChainModel.Sr Fr p r xs ys z m * C ((p:ℚ) * fullPrefix Fr m.val)) :=
    GLE.sum fun m _ => gle0_mul (hSr m) (hP m)
  have hin : GLE p 0 (ChainModel.h Fr p r xs ys * C ((p:ℚ) * fullPrefix Fr (xs z)) -
      ∑ m, ChainModel.Sr Fr p r xs ys z m * C ((p:ℚ) * fullPrefix Fr m.val)) :=
    gle0_of_int1 ((int1_of_gle0 (gle0_mul hh hPz)).sub (int1_of_gle0 hsum))
  have g2 : GLE p 0 ((ChainModel.Q Fr p r xs ys).det *
      (ChainModel.h Fr p r xs ys * C ((p:ℚ) * fullPrefix Fr (xs z)) -
        ∑ m, ChainModel.Sr Fr p r xs ys z m * C ((p:ℚ) * fullPrefix Fr m.val))) :=
    gle0_mul (ChainModel.gle0_det hL hp hN hr) hin
  have e := redI_cng g1 g2 hcng
  rw [redI_mul hh hbR, redI_mul (ChainModel.gle0_det hL hp hN hr) hin,
    redI_sub (gle0_mul hh hPz) hsum, redI_mul hh hPz,
    redI_sum _ _ (fun m _ => gle0_mul (hSr m) (hP m))] at e
  have hpl : ∀ m : Fin r, redI p (C ((p:ℚ) * fullPrefix Fr m.val)) = poleL Fr p o m.val :=
    fun m => redI_pPf hL hN (lt_of_lt_of_le m.isLt hr)
  simp only [redI_mul (hSr _) (hP _), hpl, redI_pPf hL hN (hx z)] at e
  have hs := sum_redI_Sr_chain (ys := ys) hL hp hN hr hx z hxz (fun m => poleL Fr p o m.val)
  rw [hs] at e
  unfold sourceA
  apply mul_left_cancel₀ (redI_h_ne_zero (xs := xs) (ys := ys) hL hp hN hr)
  linear_combination e

end Moments4

#print axioms redI_aR
#print axioms redI_bR
end CatalanCore.Arith.Hybrid
