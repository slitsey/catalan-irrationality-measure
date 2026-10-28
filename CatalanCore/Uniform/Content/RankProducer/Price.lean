module

public import CatalanCore.Uniform.Content.RankProducer.Loads2
public import CatalanCore.Uniform.Content.RankProducer.Cost

@[expose] public section

/-!
# Fibre-additive rank-layer price of a certificate assignment (lane H15)

`rank_price_certs`: for a Loewner matrix whose residue fibres carry certificates, any constant
subspace `V` of `𝔽_p(X)²` and per-fibre lower bounds `mc x ≤ dim (V ∩ U^col_x)`,
`mr x ≤ dim (V ∩ U^row_x)` (`U^col_x` the span of the killed column loads of the certificate,
`U^row_x` the annihilator of its killed row loads):

  `GLE p (2h - |s| - (F + Σ_{col fibres} mc - Σ_{row fibres} (dim V - mr)))  det`.
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.RankProducer

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-- Span of the killed column loads of a certificate. -/
noncomputable def Ucol (p : ℕ) [Fact p.Prime] (c : FibreCert) :
    Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)) :=
  Submodule.span _ ((fun e => castV p (c.cload e)) '' (c.kc : Set ℕ))

/-- Annihilator of the killed row loads of a certificate. -/
noncomputable def Urow (p : ℕ) [Fact p.Prime] (c : FibreCert) :
    Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)) :=
  ⨅ d ∈ c.kr, LinearMap.ker (omegaL (castV p (c.rload d)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ} {f e : ℕ → ℚ}
variable (PS : PoleSplit p B f e) (a b : ι → ℕ) (hd : DigitHyp p B a b)
  (ha : Function.Injective a) (hb : Function.Injective b)
  (cert : ZMod p → FibreCert) (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
  (hReal : ∀ x, Realizes PS a b x (cert x))
  (hcard : (killRows (p := p) a cert).card = (killCols (p := p) b cert).card)

/-- The block kernel of the assignment. -/
noncomputable abbrev BKc : BlockKernel p (erOf a p) (erOf b p) (PS.K a b) :=
  blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard

/-- Residues of the matched killed columns. -/
noncomputable def colFib : Finset (ZMod p) :=
  (Finset.univ : Finset {i // i ∈ (BKc PS a b hd ha hb cert hOk hInt hReal hcard).s}).image
    (fun j => (erOf b p ((BKc PS a b hd ha hb cert hOk hInt hReal hcard).perm j.1)).1)

/-- Residues of the killed rows. -/
noncomputable def rowFib : Finset (ZMod p) :=
  (Finset.univ : Finset {i // i ∈ (BKc PS a b hd ha hb cert hOk hInt hReal hcard).s}).image
    (fun i => (erOf a p i.1).1)


include hd ha hb hOk hInt hReal in
/-- The certificate column loads lie in the column spans of the global kernel. -/
theorem ucol_le_colSpan (x : ZMod p) :
    Ucol p (cert x) ≤ colSpan
      (fun j : (BKc PS a b hd ha hb cert hOk hInt hReal hcard).s =>
        rfH p ((erOf b p ((BKc PS a b hd ha hb cert hOk hInt hReal hcard).perm j)).1))
      (fun j => mapPair (rfH p) (load (fun l => PS.lf (b l)) (fun l => redQ p
        ((BKc PS a b hd ha hb cert hOk hInt hReal hcard).P l j)))) (rfH p x) := by
  unfold Ucol
  rw [Submodule.span_le]
  rintro _ ⟨e, he, rfl⟩
  have hex := (hReal x).c_cov e ((hOk x).kc_sub he)
  obtain ⟨l0, hl0, hl0d⟩ := hex
  have hsc : l0 ∈ (BKc PS a b hd ha hb cert hOk hInt hReal hcard).sc := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show b l0 / p ∈ (cert (b l0 : ZMod p)).kc
    rw [hl0, hl0d]; exact he
  set BK := BKc PS a b hd ha hb cert hOk hInt hReal hcard with hBK
  set j := BK.perm.symm l0 with hj
  have hjs : j ∈ BK.s := (BK.perm_mem j).1 (by rw [hj, Equiv.apply_symm_apply]; exact hsc)
  have hpj : BK.perm j = l0 := by rw [hj, Equiv.apply_symm_apply]
  refine Submodule.subset_span ⟨⟨j, hjs⟩, ?_⟩
  have hβ : rfH p ((erOf b p (BK.perm j)).1) = rfH p x := by
    rw [hpj]; show rfH p (b l0 : ZMod p) = _; rw [hl0]
  have hy : mapPair (rfH p) (load (fun l => PS.lf (b l)) (fun l => redQ p (BK.P l j))) =
      castV p ((cert x).cload e) := by
    have := colLoad_block PS a b hd ha hb cert hOk hInt hReal hcard (BK.perm j)
    rw [hpj, hl0, hl0d] at this
    have e : ∀ l, BK.P l j = blockMat (erOf b p) (erOf b p) BK.Px l l0 := fun l => by
      simp only [BlockKernel.P, Matrix.submatrix_apply, id_eq, hpj]
    simp only [e]
    exact this
  simp only [colVec, hβ, ite_true]
  exact hy

include hd ha hb hOk hInt hReal in
theorem urow_le_rowAnn (x : ZMod p) :
    Urow p (cert x) ≤ rowAnn
      (fun i : (BKc PS a b hd ha hb cert hOk hInt hReal hcard).s => rfH p ((erOf a p i).1))
      (fun i => mapPair (rfH p) (load (fun k => PS.lf (a k)) (fun k => redQ p
        ((BKc PS a b hd ha hb cert hOk hInt hReal hcard).L i k)))) (rfH p x) := by
  intro w hw
  unfold Urow at hw
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hw
  unfold rowAnn
  rw [LinearMap.mem_ker]
  funext r
  simp only [LinearMap.pi_apply, Pi.zero_apply]
  split_ifs with h
  · have hr : (erOf a p r.1).1 = x := rfH_injective h
    have hrs := r.2
    have hdig : a r.1 / p ∈ (cert (a r.1 : ZMod p)).kr :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 hrs).2).2
    have hx : (a r.1 : ZMod p) = x := hr
    have hl := rowLoad_eq PS a b hd ha hb cert hOk hInt hReal hcard r.1
    rw [hl]
    rw [hx] at hdig
    have := hw (a r.1 / p) hdig
    rw [hx]; exact this
  · rfl


include hd ha hb hOk hInt hReal in
/-- **Fibre-additive rank-layer price.** -/
theorem rank_price_certs
    (Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)))
    (mc mr : ZMod p → ℕ)
    (hmc : ∀ x ∈ colFib PS a b hd ha hb cert hOk hInt hReal hcard,
      mc x ≤ finrank (RatFunc (ZMod p)) ↥(Vs ⊓ Ucol p (cert x)))
    (hmr : ∀ x ∈ rowFib PS a b hd ha hb cert hOk hInt hReal hcard,
      mr x ≤ finrank (RatFunc (ZMod p)) ↥(Vs ⊓ Urow p (cert x)))
    (hmc2 : ∀ x, mc x ≤ finrank (RatFunc (ZMod p)) Vs)
    (hmr2 : ∀ x, mr x ≤ finrank (RatFunc (ZMod p)) Vs) :
    GLE p (Fintype.card ι + (Fintype.card ι - (BKc PS a b hd ha hb cert hOk hInt hReal hcard).s.card) -
      (Fintype.card {j : (BKc PS a b hd ha hb cert hOk hInt hReal hcard).s //
          load (fun l => PS.lf (b l)) (fun l => redQ p
            ((BKc PS a b hd ha hb cert hOk hInt hReal hcard).P l j)) = 0} +
        (∑ x ∈ colFib PS a b hd ha hb cert hOk hInt hReal hcard, mc x -
          ∑ x ∈ rowFib PS a b hd ha hb cert hOk hInt hReal hcard,
            (finrank (RatFunc (ZMod p)) Vs - mr x))))
      (loewner a b f e).det := by
  set BK := BKc PS a b hd ha hb cert hOk hInt hReal hcard with hBK
  set dV := finrank (RatFunc (ZMod p)) Vs with hdV
  let σ : BK.s → ZMod p := fun j => (erOf b p (BK.perm j.1)).1
  let ρ : BK.s → ZMod p := fun i => (erOf a p i.1).1
  let inv : RatFunc (ZMod p) → ZMod p := Function.invFun (rfH p)
  have hinv : ∀ x, inv (rfH p x) = x := fun x => Function.leftInverse_invFun rfH_injective x
  let cost : Cond (fun i : BK.s => rfH p (ρ i)) (fun j : BK.s => rfH p (σ j)) → ℕ :=
    fun c => Sum.elim (fun b => dV - mc (inv b.1)) (fun a => dV - mr (inv a.1)) c
  have hcost : ∀ c, finrank (RatFunc (ZMod p)) (LinearMap.range (condMap
        (fun i : BK.s => rfH p (ρ i))
        (fun i => mapPair (rfH p) (load (fun k => PS.lf (a k)) (fun k => redQ p (BK.L i k))))
        (fun j : BK.s => rfH p (σ j))
        (fun j => mapPair (rfH p) (load (fun l => PS.lf (b l)) (fun l => redQ p (BK.P l j))))
        Vs c)) ≤ cost c := by
    intro c
    rcases c with ⟨_, hbb⟩ | ⟨_, haa⟩
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hbb
      subst hj
      have hx : σ j ∈ colFib PS a b hd ha hb cert hOk hInt hReal hcard :=
        Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
      have hU := ucol_le_colSpan PS a b hd ha hb cert hOk hInt hReal hcard (σ j)
      have hm : mc (σ j) ≤ finrank (RatFunc (ZMod p)) ↥(Vs ⊓ condSpace
          (fun i : BK.s => rfH p (ρ i))
          (fun i => mapPair (rfH p) (load (fun k => PS.lf (a k)) (fun k => redQ p (BK.L i k))))
          (fun j : BK.s => rfH p (σ j))
          (fun j => mapPair (rfH p) (load (fun l => PS.lf (b l)) (fun l => redQ p (BK.P l j))))
          (Sum.inl ⟨_, hbb⟩)) := by
        refine (hmc _ hx).trans (Submodule.finrank_mono (inf_le_inf_left Vs ?_))
        show _ ≤ colSpan _ _ _
        exact hU
      have := finrank_range_condMap_le_of_lb _ _ _ _ Vs (Sum.inl ⟨_, hbb⟩) hm
      simp only [cost, Sum.elim_inl]
      rw [hinv]
      exact this
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 haa
      subst hi
      have hx : ρ i ∈ rowFib PS a b hd ha hb cert hOk hInt hReal hcard :=
        Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
      have hU := urow_le_rowAnn PS a b hd ha hb cert hOk hInt hReal hcard (ρ i)
      have hm : mr (ρ i) ≤ finrank (RatFunc (ZMod p)) ↥(Vs ⊓ condSpace
          (fun i : BK.s => rfH p (ρ i))
          (fun i => mapPair (rfH p) (load (fun k => PS.lf (a k)) (fun k => redQ p (BK.L i k))))
          (fun j : BK.s => rfH p (σ j))
          (fun j => mapPair (rfH p) (load (fun l => PS.lf (b l)) (fun l => redQ p (BK.P l j))))
          (Sum.inr ⟨_, haa⟩)) := by
        refine (hmr _ hx).trans (Submodule.finrank_mono (inf_le_inf_left Vs ?_))
        show _ ≤ rowAnn _ _ _
        exact hU
      have := finrank_range_condMap_le_of_lb _ _ _ _ Vs (Sum.inr ⟨_, haa⟩) hm
      simp only [cost, Sum.elim_inr]
      rw [hinv]
      exact this
  have hR : (Fintype.card ι - BK.s.card) + BK.s.card = Fintype.card ι :=
    Nat.sub_add_cancel (by simpa using Finset.card_le_univ BK.s)
  have hmain := BlockKernel.gle_det_frame PS hd BK id (fun i => rfl) (fun j => rfl)
    (Fintype.card ι - BK.s.card) hR Vs cost hcost
  simp only [id_eq] at hmain
  refine hmain.mono ?_
  -- arithmetic
  have hcolRes : colRes (fun j : BK.s => rfH p (σ j)) =
      (colFib PS a b hd ha hb cert hOk hInt hReal hcard).image (rfH p) := by
    unfold colRes colFib
    rw [Finset.image_image]; rfl
  have hrowRes : rowRes (fun i : BK.s => rfH p (ρ i)) =
      (rowFib PS a b hd ha hb cert hOk hInt hReal hcard).image (rfH p) := by
    unfold rowRes rowFib
    rw [Finset.image_image]; rfl
  have hcard1 : (colRes (fun j : BK.s => rfH p (σ j))).card =
      (colFib PS a b hd ha hb cert hOk hInt hReal hcard).card := by
    rw [hcolRes, Finset.card_image_of_injective _ rfH_injective]
  have hsum : ∑ c, cost c =
      ∑ x ∈ colFib PS a b hd ha hb cert hOk hInt hReal hcard, (dV - mc x) +
      ∑ x ∈ rowFib PS a b hd ha hb cert hOk hInt hReal hcard, (dV - mr x) := by
    simp only [cost, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · rw [Finset.sum_coe_sort (colRes (fun j : BK.s => rfH p (σ j))) (fun b => dV - mc (inv b)),
        hcolRes, Finset.sum_image (fun x _ y _ h => rfH_injective h)]
      exact Finset.sum_congr rfl fun x _ => by rw [hinv]
    · rw [Finset.sum_coe_sort (rowRes (fun i : BK.s => rfH p (ρ i))) (fun b => dV - mr (inv b)),
        hrowRes, Finset.sum_image (fun x _ y _ h => rfH_injective h)]
      exact Finset.sum_congr rfl fun x _ => by rw [hinv]
  have hsplit : ∑ x ∈ colFib PS a b hd ha hb cert hOk hInt hReal hcard, (dV - mc x) +
      ∑ x ∈ colFib PS a b hd ha hb cert hOk hInt hReal hcard, mc x =
      (colFib PS a b hd ha hb cert hOk hInt hReal hcard).card * dV := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (hmc2 x))]
    simp
  rw [hcard1, hsum]
  have key : ∑ x ∈ colFib PS a b hd ha hb cert hOk hInt hReal hcard, mc x -
      ∑ x ∈ rowFib PS a b hd ha hb cert hOk hInt hReal hcard, (dV - mr x) ≤
      (colFib PS a b hd ha hb cert hOk hInt hReal hcard).card * dV -
        (∑ x ∈ colFib PS a b hd ha hb cert hOk hInt hReal hcard, (dV - mc x) +
          ∑ x ∈ rowFib PS a b hd ha hb cert hOk hInt hReal hcard, (dV - mr x)) := by
    omega
  exact Nat.sub_le_sub_left (Nat.add_le_add_left key _) _

end CatalanCore.Uniform.Content.RankProducer
