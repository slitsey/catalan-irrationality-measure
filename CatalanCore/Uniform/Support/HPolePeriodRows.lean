module

public import CatalanCore.Uniform.Support.Producer
public import CatalanCore.Uniform.Content.Sweep.HPoleK0
public import CatalanCore.Uniform.Content.Sweep.RowNodes

@[expose] public section

/-!
# Full-period refined first row for arbitrary integer-pole pencils

Q18: the generic k0 covariance row, including arbitrary common deletions.
The determinant algebra, node suppliers and descent are accepted generic engines;
only the class-free k0 weight, its dual potentials and their counts are new.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Content.Sweep CatalanCore.Uniform.Content.Sweep.Gen

namespace CatalanCore.Uniform.Support.HPolePeriodRows

private theorem minor_k0
    {p : ℕ} [hp : Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (LocRing p) R]
    (h : ℕ) (d : ℕ → ℚ) {N κ π : ℕ} (ξ : R)
    (hh : 3 ≤ h) (hd : ∀ j ∈ Icc 1 (h-1), d j ∈ LocRing p)
    (hp5 : 5 ≤ p) (hπ : π ≤ 1) (hN : 2*N < p*p) (hH : κ*p ≤ N)
    (hU : IsUnit (HPole.Qp (p := p) h d κ 0 π ξ).det)
    (Y : ℕ → ℕ → ℕ → R)
    (hclass : ∀ b o, o ≤ 1 → ∀ l ∈ Cper κ 0 (1-o),
      ∑ j ∈ Cper κ 0 o, HPole.Bm (p := p) h d ξ l j * Y b o j = HPole.GamR (p := p) h d b l)
    (hYind : ∀ b o o' j, Y b o j = Y b o' j)
    {L : Type} [Fintype L] [DecidableEq L] (rn cl : L → ℕ)
    (hrinj : Function.Injective rn) (hcinj : Function.Injective cl)
    (hrc : ∀ a, (rn a / p + 1)*p ≤ N) (hcc : ∀ a, (cl a / p + 1)*p ≤ N)
    (φR φC : ℕ → ℕ)
    (hW : ∀ (n m : ℕ) (kR kC : Bool), RowLab rn cl p κ 0 π kR n → ColLab rn cl p κ 0 π kC m →
      HPole.k0Weight h p kR kC n m ≤ φR n + φC m)
    (E : ℕ)
    (hcond : h * Fintype.card L +
      (∑ a ∈ Finset.univ.filter (fun a : L => ¬ ∃ x : PivIdx p κ 0, rowNode p κ 0 π x = rn a), φR (rn a) +
       ∑ y ∈ Finset.univ.filter (fun y : PivIdx p κ 0 => ∀ b, colNode p κ 0 π y ≠ cl b),
          φR (colNode p κ 0 π y) +
       ∑ b ∈ Finset.univ.filter (fun b : L => ¬ ∃ y : PivIdx p κ 0, colNode p κ 0 π y = cl b), φC (cl b) +
       ∑ x ∈ Finset.univ.filter (fun x : PivIdx p κ 0 => ∀ a, rowNode p κ 0 π x ≠ rn a),
          φC (rowNode p κ 0 π x)) ≤
      E + h * ((Finset.univ.filter (fun a : L => ¬ ∃ x : PivIdx p κ 0, rowNode p κ 0 π x = rn a)).card +
        (Finset.univ.filter (fun y : PivIdx p κ 0 => ∀ b, colNode p κ 0 π y ≠ cl b)).card)) :
    (p : R) ^ (h * Fintype.card L - E) ∣
      (Matrix.of fun a b => HPole.Qh (p := p) h d ξ (rn a) (cl b)).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  set DelR : Finset (PivIdx p κ 0) := Finset.univ.filter (fun x => ∀ a, rowNode p κ 0 π x ≠ rn a) with hDelR
  set DelC : Finset (PivIdx p κ 0) := Finset.univ.filter (fun y => ∀ b, colNode p κ 0 π y ≠ cl b) with hDelC
  set RowOut : Finset L := Finset.univ.filter (fun a : L => ¬ ∃ x : PivIdx p κ 0, rowNode p κ 0 π x = rn a)
    with hRowOut
  set ColOut : Finset L := Finset.univ.filter (fun b : L => ¬ ∃ y : PivIdx p κ 0, colNode p κ 0 π y = cl b)
    with hColOut
  obtain ⟨eR, heR⟩ := exists_equiv_side (rowNode p κ 0 π) (rowNode_injective hp0) rn hrinj
  obtain ⟨eC, heC⟩ := exists_equiv_side (colNode p κ 0 π) (colNode_injective hp0) cl hcinj
  let Lo := {a : L // ¬ ∃ x : PivIdx p κ 0, rowNode p κ 0 π x = rn a}
  let Lc := {b : L // ¬ ∃ y : PivIdx p κ 0, colNode p κ 0 π y = cl b}
  let zn : Lo → ℕ := fun o => rn o.1
  let yn : Lc → ℕ := fun o => cl o.1
  have hcL1 : Fintype.card L = (Fintype.card (PivIdx p κ 0) - DelR.card) + Fintype.card Lo := by
    rw [Fintype.card_congr eR, Fintype.card_sum, Fintype.card_subtype_compl (fun x => x ∈ DelR),
      Fintype.card_coe]
  have hcL2 : Fintype.card L = (Fintype.card (PivIdx p κ 0) - DelC.card) + Fintype.card Lc := by
    rw [Fintype.card_congr eC, Fintype.card_sum, Fintype.card_subtype_compl (fun x => x ∈ DelC),
      Fintype.card_coe]
  have hcLo : Fintype.card Lo = RowOut.card := Fintype.card_subtype _
  have hcLc : Fintype.card Lc = ColOut.card := Fintype.card_subtype _
  have hle1 : DelR.card ≤ Fintype.card (PivIdx p κ 0) := Finset.card_le_univ _
  have hle2 : DelC.card ≤ Fintype.card (PivIdx p κ 0) := Finset.card_le_univ _
  let eC' : (Lo ⊕ ↥DelC) ≃ (Lc ⊕ ↥DelR) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_coe]; omega)
  have hZ1 : Schur.Qm (HPole.Hq (p := p) h d κ 0 π ξ zn yn) * HPole.Zp (p := p) h d κ 0 π ξ = 1 := by
    rw [HPole.Qm_Hq]; exact HPole.Qp_mul_Zp h d κ 0 π ξ hU
  have hZ2 : HPole.Zp (p := p) h d κ 0 π ξ * Schur.Qm (HPole.Hq (p := p) h d κ 0 π ξ zn yn) = 1 := by
    rw [HPole.Qm_Hq]; exact HPole.Zp_mul_Qp h d κ 0 π ξ hU
  have hJ := Schur.jacobi_L (HPole.Hq (p := p) h d κ 0 π ξ zn yn) DelR DelC
    (HPole.Zp (p := p) h d κ 0 π ξ) hZ1 hZ2
    (fun a => Sum.map Subtype.val id (eR a)) (fun a => Sum.map Subtype.val id (eC a))
    (fun l : Lo ⊕ ↥DelC => Sum.map id Subtype.val (Equiv.refl _ l))
    (fun l => Sum.map id Subtype.val (eC' l)) eR eC (Equiv.refl _) eC'
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  -- the minor is the Q-minor
  have hM1 : (Matrix.of fun a b => HPole.Hq (p := p) h d κ 0 π ξ zn yn (Sum.map Subtype.val id (eR a))
      (Sum.map Subtype.val id (eC b))) = Matrix.of fun a b => HPole.Qh (p := p) h d ξ (rn a) (cl b) := by
    ext a b
    simp only [HPole.Hq, Matrix.of_apply]
    have h1 := heR a
    have h2 := heC b
    have e1 : Sum.elim (rowNode p κ 0 π) zn (Sum.map Subtype.val id (eR a)) = rn a := by
      rcases h : eR a with x | o <;> rw [h] at h1 <;> simpa [zn] using h1
    have e2 : Sum.elim (colNode p κ 0 π) yn (Sum.map Subtype.val id (eC b)) = cl b := by
      rcases h : eC b with x | o <;> rw [h] at h2 <;> simpa [yn] using h2
    rw [e1, e2]
  rw [hM1] at hJ
  simp only [Equiv.refl_apply] at hJ
  by_cases hE : E ≤ h * Fintype.card L
  swap
  · have : h * Fintype.card L - E = 0 := by omega
    rw [this, pow_zero]; exact one_dvd _
  have hzc : ∀ o : Lo, (zn o / p + 1) * p ≤ N := fun o => hrc o.1
  have hyc : ∀ o : Lc, (yn o / p + 1) * p ≤ N := fun o => hcc o.1
  have hcardLab : Fintype.card (Lo ⊕ ↥DelC) = RowOut.card + DelC.card := by
    rw [Fintype.card_sum, hcLo, Fintype.card_coe]
  have rowLab_of : ∀ a : Lo ⊕ ↥DelC, RowLab rn cl p κ 0 π (Sum.map id Subtype.val a).isLeft
      (nR (p := p) (κ := κ) (k' := 0) (π := π) zn (Sum.map id Subtype.val a)) := by
    rintro (o | ⟨y, hy⟩)
    · exact Or.inl ⟨rfl, o.1, rfl, o.2⟩
    · refine Or.inr ⟨rfl, y, rfl, fun b => ?_⟩
      simp only [hDelC, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact (hy b).symm
  have colLab_of : ∀ b : Lc ⊕ ↥DelR, ColLab rn cl p κ 0 π (Sum.map id Subtype.val b).isLeft
      (nC (p := p) (κ := κ) (k' := 0) (π := π) yn (Sum.map id Subtype.val b)) := by
    rintro (o | ⟨x, hx⟩)
    · exact Or.inl ⟨rfl, o.1, rfl, o.2⟩
    · refine Or.inr ⟨rfl, x, rfl, fun a => ?_⟩
      simp only [hDelR, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact (hx a).symm
  let ρ' : (Lo ⊕ ↥DelC) → (Lo ⊕ PivIdx p κ 0) := fun l => Sum.map id Subtype.val l
  let κ'' : (Lo ⊕ ↥DelC) → (Lc ⊕ PivIdx p κ 0) := fun l => Sum.map id Subtype.val (eC' l)
  let ur : (Lo ⊕ ↥DelC) → ℕ := fun l => φR (nR (p := p) (κ := κ) (k' := 0) (π := π) zn (ρ' l))
  let uc : (Lo ⊕ ↥DelC) → ℕ := fun l => φC (nC (p := p) (κ := κ) (k' := 0) (π := π) yn (κ'' l))
  have hsumR : ∑ a, ur a = ∑ a ∈ RowOut, φR (rn a) + ∑ y ∈ DelC, φR (colNode p κ 0 π y) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · exact (Finset.sum_subtype RowOut (fun a => by simp [hRowOut]) (fun a => φR (rn a))).symm
    · exact Finset.sum_coe_sort DelC (fun y => φR (colNode p κ 0 π y))
  have hsumC : ∑ b, uc b = ∑ b ∈ ColOut, φC (cl b) + ∑ x ∈ DelR, φC (rowNode p κ 0 π x) := by
    have h1 : ∑ b, uc b = ∑ l : Lc ⊕ ↥DelR, φC (nC (p := p) (κ := κ) (k' := 0) (π := π) yn
        (Sum.map id Subtype.val l)) :=
      Equiv.sum_comp eC' (fun l => φC (nC (p := p) (κ := κ) (k' := 0) (π := π) yn
        (Sum.map id Subtype.val l)))
    rw [h1, Fintype.sum_sum_type]
    congr 1
    · exact (Finset.sum_subtype ColOut (fun a => by simp [hColOut]) (fun a => φC (cl a))).symm
    · exact Finset.sum_coe_sort DelR (fun x => φC (rowNode p κ 0 π x))
  have hdetSw : (p : R) ^ (h * Fintype.card L - E) ∣
      (Matrix.of fun a b => (Schur.Sw (HPole.Hq (p := p) h d κ 0 π ξ zn yn)
        (HPole.Zp (p := p) h d κ 0 π ξ)) (ρ' a) (κ'' b)).det := by
    refine det_dvd_of_potentials_h h (p : R) _
      (fun a b => h - HPole.k0Weight h p (ρ' a).isLeft (κ'' b).isLeft
        (nR (p := p) (κ := κ) (k' := 0) (π := π) zn (ρ' a))
        (nC (p := p) (κ := κ) (k' := 0) (π := π) yn (κ'' b))) ur uc ?_ ?_ _ ?_
    · intro a b
      exact HPole.sw_dvd_k0 h d ξ zn yn hh hd hp5 hπ hN hH hU Y hclass hYind hzc hyc (ρ' a) (κ'' b)
    · intro a b
      have hw := hW _ _ _ _ (rowLab_of a) (colLab_of (eC' b))
      have hwle : HPole.k0Weight h p (ρ' a).isLeft (κ'' b).isLeft
          (nR (p := p) (κ := κ) (k' := 0) (π := π) zn (ρ' a))
          (nC (p := p) (κ := κ) (k' := 0) (π := π) yn (κ'' b)) ≤ h := by
        unfold HPole.k0Weight; split_ifs <;> omega
      change h ≤ h - _ + _ + _
      dsimp only [ur, uc, ρ', κ''] at hw hwle ⊢
      omega
    · rw [hsumR, hsumC, hcardLab]
      omega
  exact hdetSw.trans hJ.symm.dvd


private theorem member_k0
    {p : ℕ} [hp : Fact p.Prime] (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h-1), d j ∈ LocRing p)
    {N κ π : ℕ} (hp5 : 5 ≤ p) (hπ : π ≤ 1)
    (hN : 2*N < p*p) (hH : κ*p ≤ N)
    {ι κw : Type} [Fintype ι] [DecidableEq ι] [Fintype κw] [DecidableEq κw]
    (c : ι → ℕ) (xs ys : κw → ℕ)
    (hcinj : Function.Injective c) (hxinj : Function.Injective xs) (hyinj : Function.Injective ys)
    (h1 : ∀ i j, c i ≠ ys j) (h2 : ∀ i j, xs i ≠ c j) (h3 : ∀ i j, xs i ≠ ys j)
    (hrc : ∀ a, (memRow c xs a / p + 1) * p ≤ N) (hcc : ∀ b, (memCol c ys b / p + 1) * p ≤ N)
    (φR φC : ℕ → ℕ)
    (hW : ∀ (n m : ℕ) (kR kC : Bool), RowLab (memRow c xs) (memCol c ys) p κ 0 π kR n →
      ColLab (memRow c xs) (memCol c ys) p κ 0 π kC m →
      HPole.k0Weight h p kR kC n m ≤ φR n + φC m)
    (E : ℕ)
    (hcond : by classical exact h * Fintype.card (ι ⊕ κw) +
      (∑ a ∈ Finset.univ.filter (fun a : ι ⊕ κw => ¬ ∃ x : PivIdx p κ 0, rowNode p κ 0 π x = memRow c xs a),
          φR (memRow c xs a) +
       ∑ y ∈ Finset.univ.filter (fun y : PivIdx p κ 0 => ∀ b, colNode p κ 0 π y ≠ memCol c ys b),
          φR (colNode p κ 0 π y) +
       ∑ b ∈ Finset.univ.filter (fun b : ι ⊕ κw => ¬ ∃ y : PivIdx p κ 0, colNode p κ 0 π y = memCol c ys b),
          φC (memCol c ys b) +
       ∑ x ∈ Finset.univ.filter (fun x : PivIdx p κ 0 => ∀ a, rowNode p κ 0 π x ≠ memRow c xs a),
          φC (rowNode p κ 0 π x)) ≤
      E + h * ((Finset.univ.filter (fun a : ι ⊕ κw => ¬ ∃ x : PivIdx p κ 0, rowNode p κ 0 π x = memRow c xs a)).card +
        (Finset.univ.filter (fun y : PivIdx p κ 0 => ∀ b, colNode p κ 0 π y ≠ memCol c ys b)).card)) :
    GLE p E (seqFullN (hpoleF h d) (hpoleE h d) c xs ys (X : ℚ[X])).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hr : ∀ a, memRow c xs a < p*p := fun a => by
    have := lt_of_complete hp0 (hrc a); omega
  have hc : ∀ b, memCol c ys b < p*p := fun b => by
    have := lt_of_complete hp0 (hcc b); omega
  obtain ⟨hU, Y, hclass, hYind⟩ := HPole.k0_source_rp h hh d hd hp5 hπ hN hH
  have hv := minor_k0 h d (xiP p) hh hd hp5 hπ hN hH hU Y hclass hYind
    (memRow c xs) (memCol c ys)
    (memRow_injective c xs hcinj hxinj h2) (memCol_injective c ys hcinj hyinj h1)
    hrc hcc φR φC hW E hcond
  let B : Matrix (ι ⊕ κw) (ι ⊕ κw) (LocRing p)[X] :=
    fun a b => HPole.Qpoly (p := p) h d (memRow c xs a) (memCol c ys b)
  have hB : ∀ a b, toQ p (B a b) = C ((p : ℚ)^h) *
      seqFullN (hpoleF h d) (hpoleE h d) c xs ys (C (((p : ℚ)^h)⁻¹)*X) a b := by
    intro a b
    rw [show B a b = HPole.Qpoly (p := p) h d (memRow c xs a) (memCol c ys b) from rfl,
      HPole.toQ_Qpoly h hh d hd (hr a) (hc b),
      seqFullN_entry c xs ys _ _ _ hcinj h1 h2 h3]
    have hpc : (p : ℚ)^h ≠ 0 := pow_ne_zero h (by exact_mod_cast hp.out.ne_zero)
    split_ifs <;> simp only [Polynomial.algebraMap_eq, mul_add, mul_zero, zero_add]
    · rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hpc, C_1, one_mul, ← C_mul]
    · rw [← C_mul]
  have hmap : algebraMap ((LocRing p)[X]) (RP p) B.det =
      (Matrix.of fun a b => HPole.Qh (p := p) h d (xiP p) (memRow c xs a) (memCol c ys b)).det := by
    have hm := RingHom.map_det (S := RP p)
      (algebraMap ((LocRing p)[X]) (RP p)) B
    rw [hm]
    congr 1
    ext a b
    change algebraMap ((LocRing p)[X]) (RP p) (B a b) = _
    rw [← aeval_xiP p (B a b)]
    exact HPole.aeval_Qpoly h hh d hd (xiP p) (hr a) (hc b)
  have hdvd : (p : RP p)^(h*Fintype.card (ι ⊕ κw)-E) ∣
      algebraMap ((LocRing p)[X]) (RP p) B.det := by rw [hmap]; exact hv
  have hg := gle_member_h h (hpoleF h d) (hpoleE h d) c xs ys B hB hdvd
  refine hg.mono ?_
  rw [Fintype.card_sum] at *
  omega


private theorem window_k0
    {p : ℕ} [hp : Fact p.Prime] (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h-1), d j ∈ LocRing p)
    {N' : ℕ} (hodd : p%2=1) (hp5 : 5 ≤ p) (hN : 2*N' < p*p)
    {r m κ : ℕ} (hκr : r < κ * p) (hH : (κ + 2 * 0) * p ≤ N')
    (hcompl : ∀ n, n < r + 2 * m → (n / p + 1) * p ≤ N')
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (hcinj : Function.Injective c)
    (hcr : ∀ i, c i < r) (φR φC : ℕ → ℕ) (hφ : ∀ t, t < r → φR t = h ∧ φC t = h)
    (hpp : ∀ n ∈ TRs p κ 0 r m, ∀ n' ∈ TCs p κ 0 r m,
      HPole.k0Weight h p false false n n' ≤ φR n + φC n')
    (hpo : ∀ n ∈ TRs p κ 0 r m, ∀ n' ∈ OCs p κ 0 r m,
      HPole.k0Weight h p false true n n' ≤ φR n + φC n')
    (hop : ∀ n ∈ ORs p κ 0 r m, ∀ n' ∈ TCs p κ 0 r m,
      HPole.k0Weight h p true false n n' ≤ φR n + φC n')
    (hoo : ∀ n ∈ ORs p κ 0 r m, ∀ n' ∈ OCs p κ 0 r m,
      HPole.k0Weight h p true true n n' ≤ φR n + φC n')
    (E : ℕ)
    (hsum : h * r + h * m + (∑ t ∈ TRs p κ 0 r m, φR t + ∑ t ∈ ORs p κ 0 r m, φR t +
        ∑ t ∈ TCs p κ 0 r m, φC t + ∑ t ∈ OCs p κ 0 r m, φC t) ≤
      E + h * ((TRs p κ 0 r m).card + (ORs p κ 0 r m).card)) :
    GLE p E (seqFullN (hpoleF h d) (hpoleE h d) c
      (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hπ : (r + 1) % 2 ≤ 1 := by omega
  have hκH : κ * p ≤ (κ + 2 * 0) * p := Nat.mul_le_mul_right p (by omega)
  have hxinj : Function.Injective (fun i : Fin m => r + 2 * (i : ℕ)) := by
    intro i j h; apply Fin.ext; simp only at h; omega
  have hyinj : Function.Injective (fun i : Fin m => r + 2 * (i : ℕ) + 1) := by
    intro i j h; apply Fin.ext; simp only at h; omega
  have h1 : ∀ (i : ι) (j : Fin m), c i ≠ r + 2 * (j : ℕ) + 1 := by
    intro i j; have := hcr i; omega
  have h2 : ∀ (i : Fin m) (j : ι), r + 2 * (i : ℕ) ≠ c j := by
    intro i j; have := hcr j; omega
  have h3 : ∀ (i j : Fin m), r + 2 * (i : ℕ) ≠ r + 2 * (j : ℕ) + 1 := by
    intro i j; omega
  have hrow : ∀ a, memRow c (fun i : Fin m => r + 2 * (i : ℕ)) a < r + 2 * m := by
    rintro (i | i)
    · have := hcr i; simp only [memRow, Sum.elim_inl]; omega
    · have := i.2; simp only [memRow, Sum.elim_inr]; omega
  have hcol : ∀ a, memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) a < r + 2 * m := by
    rintro (i | i)
    · have := hcr i; simp only [memCol, Sum.elim_inl]; omega
    · have := i.2; simp only [memCol, Sum.elim_inr]; omega
  have hcardι : Fintype.card ι ≤ r := by
    have := Fintype.card_le_of_injective (fun i => (⟨c i, hcr i⟩ : Fin r)) (by
      intro i j h; apply hcinj; simpa using congrArg Fin.val h)
    simpa using this
  have hfree := card_free c hcinj r hcr
  refine member_k0 (p := p) (π := (r+1)%2) (κ := κ) h hh d hd hp5 hπ hN hH c
    (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) hcinj hxinj
    hyinj h1 h2 h3 (fun a => hcompl _ (hrow a)) (fun a => hcompl _ (hcol a)) φR φC ?_ E ?_
  · -- the weights
    intro n n' kR kC hR hC
    have hRc : (kR = true ∧ n ∈ ORs p κ 0 r m) ∨ (kR = false ∧ (n < r ∨ n ∈ TRs p κ 0 r m)) := by
      rcases hR with ⟨hk, a, hna, hnp⟩ | ⟨hk, y, hyn, hb⟩
      · left
        refine ⟨hk, ?_⟩
        rcases a with i | j
        · exfalso
          apply hnp
          simp only [memRow, Sum.elim_inl] at hna
          rw [← hna, exists_rowNode_iff hodd hπ]
          exact ⟨by have := hcr i; nlinarith, Or.inl (by have := hcr i; nlinarith)⟩
        · simp only [memRow, Sum.elim_inr] at hna
          rw [exists_rowNode_iff hodd hπ] at hnp
          have hj := j.2
          unfold ORs
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
          by_contra hlt
          apply hnp
          exact ⟨by omega, Or.inr (by omega)⟩
      · right
        refine ⟨hk, ?_⟩
        obtain ⟨hyn1, hyn2⟩ := (exists_colNode_iff hodd hπ n).1 ⟨y, hyn⟩
        by_cases hr : n < r
        · exact Or.inl hr
        · right
          unfold TRs Tdel
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, hyn1⟩, ?_⟩
          by_cases hpar : (n - r) % 2 = 1
          · left
            refine ⟨hpar, ?_⟩
            by_contra hlt
            have hlt : n < r + 2 * m := by omega
            exact hb (Sum.inr ⟨(n - r - 1) / 2, by omega⟩) (by simp only [memCol, Sum.elim_inr]; omega)
          · right
            exact ⟨by omega, by omega⟩
    have hCc : (kC = true ∧ n' ∈ OCs p κ 0 r m) ∨ (kC = false ∧ (n' < r ∨ n' ∈ TCs p κ 0 r m)) := by
      rcases hC with ⟨hk, a, hna, hnp⟩ | ⟨hk, x, hxn, hb⟩
      · left
        refine ⟨hk, ?_⟩
        rcases a with i | j
        · exfalso
          apply hnp
          simp only [memCol, Sum.elim_inl] at hna
          rw [← hna, exists_colNode_iff hodd hπ]
          exact ⟨by have := hcr i; nlinarith, Or.inl (by have := hcr i; nlinarith)⟩
        · simp only [memCol, Sum.elim_inr] at hna
          rw [exists_colNode_iff hodd hπ] at hnp
          have hj := j.2
          unfold OCs
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
          by_contra hlt
          apply hnp
          exact ⟨by omega, Or.inr (by omega)⟩
      · right
        refine ⟨hk, ?_⟩
        obtain ⟨hxn1, hxn2⟩ := (exists_rowNode_iff hodd hπ n').1 ⟨x, hxn⟩
        by_cases hr : n' < r
        · exact Or.inl hr
        · right
          unfold TCs Tdel
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, hxn1⟩, ?_⟩
          by_cases hpar : (n' - r) % 2 = 0
          · left
            refine ⟨hpar, ?_⟩
            by_contra hlt
            have hlt : n' < r + 2 * m := by omega
            exact hb (Sum.inr ⟨(n' - r) / 2, by omega⟩) (by simp only [memRow, Sum.elim_inr]; omega)
          · right
            exact ⟨by omega, by omega⟩
    have hle : HPole.k0Weight h p kR kC n n' ≤ h := by
      unfold HPole.k0Weight; split_ifs <;> omega
    rcases hRc with ⟨rfl, hn⟩ | ⟨rfl, hn | hn⟩
    · rcases hCc with ⟨rfl, hn'⟩ | ⟨rfl, hn' | hn'⟩
      · exact hoo n hn n' hn'
      · have := (hφ n' hn').2; omega
      · exact hop n hn n' hn'
    · have := (hφ n hn).1; omega
    · rcases hCc with ⟨rfl, hn'⟩ | ⟨rfl, hn' | hn'⟩
      · exact hpo n hn n' hn'
      · have := (hφ n' hn').2; omega
      · exact hpp n hn n' hn'
  · -- the sum condition
    have eR := sum_RowOut (p := p) (κ := κ) (k' := 0) (m := m) c hodd hκr hκH hcr φR
    have eR1 := sum_RowOut (p := p) (κ := κ) (k' := 0) (m := m) c hodd hκr hκH hcr (fun _ => 1)
    have eC := sum_ColOut (p := p) (κ := κ) (k' := 0) (m := m) c hodd hκr hκH hcr φC
    have dC := sum_DelC (p := p) (κ := κ) (k' := 0) (m := m) c hodd hκr hκH hcr φR
    have dC1 := sum_DelC (p := p) (κ := κ) (k' := 0) (m := m) c hodd hκr hκH hcr (fun _ => 1)
    have dR := sum_DelR (p := p) (κ := κ) (k' := 0) (m := m) c hodd hκr hκH hcr φC
    have hFh : ∑ t ∈ (Finset.range r).filter (fun t => ∀ i, t ≠ c i), φR t =
        h * ((Finset.range r).filter (fun t => ∀ i, t ≠ c i)).card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have := (hφ t (Finset.mem_range.1 (Finset.mem_filter.1 ht).1)).1
      omega
    have hFh' : ∑ t ∈ (Finset.range r).filter (fun t => ∀ i, t ≠ c i), φC t =
        h * ((Finset.range r).filter (fun t => ∀ i, t ≠ c i)).card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have := (hφ t (Finset.mem_range.1 (Finset.mem_filter.1 ht).1)).2
      omega
    simp only [Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_eq_sum_ones] at eR1 dC1
    rw [Fintype.card_sum, Fintype.card_fin]
    rw [hFh] at dC
    rw [hFh'] at dR
    have hfreeh := congrArg (fun k => h*k) hfree
    have hcardιh := Nat.mul_le_mul_left h hcardι
    have hfree_cancel : h*(r-Fintype.card ι)+h*Fintype.card ι=h*r := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hcardι]
    nlinarith



/-- Number of border nodes before the next full-period boundary. -/
def borderBefore (p r m : ℕ) : ℕ := min (2*m) ((r/p+1)*p-r)

/-- The first k0 price, including the smaller side of a crossed boundary. -/
def refinedFirst (h p r m : ℕ) : ℕ :=
  h*(r+m)-3*m+2*min (borderBefore p r m) (2*m-borderBefore p r m)

private def band (A r m off : ℕ) (kind : Bool) (n : ℕ) : Prop :=
  r ≤ n ∧ if kind then A ≤ n ∧ n < r+2*m ∧ (n-r)%2=off
    else n < A ∧ (r+2*m ≤ n ∨ (n-r)%2=off)

private def chosen (A r m n : ℕ) : Prop :=
  if A-r ≤ r+2*m-A then n < A else A ≤ n

private noncomputable def phiR (h A r m n : ℕ) : ℕ := by
  classical
  exact if n < r then h else h-3 +
    if A < r+2*m ∧ chosen A r m n then 2 else 0

private noncomputable def phiC (h A r m n : ℕ) : ℕ := by
  classical
  exact if n < r then h else
    if r+2*m ≤ A then (if r+2*m ≤ n then 3 else 0)
    else if chosen A r m n then 2 else 0

private theorem band_TR {p κ r m n : ℕ} :
    n ∈ TRs p κ 0 r m ↔ band (κ*p) r m 0 false n := by
  simp only [TRs, Tdel, band, Bool.false_eq_true, if_false, Nat.mul_zero,
    Nat.add_zero, Finset.mem_filter, Finset.mem_Ico]
  omega

private theorem band_TC {p κ r m n : ℕ} :
    n ∈ TCs p κ 0 r m ↔ band (κ*p) r m 1 false n := by
  simp only [TCs, Tdel, band, Bool.false_eq_true, if_false, Nat.mul_zero,
    Nat.add_zero, Finset.mem_filter, Finset.mem_Ico]
  omega

private theorem band_OR {p κ r m n : ℕ} :
    n ∈ ORs p κ 0 r m ↔ band (κ*p) r m 0 true n := by
  simp only [ORs, band, eq_self_iff_true, if_true, Nat.mul_zero,
    Nat.add_zero, Finset.mem_filter, Finset.mem_Ico]
  omega

private theorem band_OC {p κ r m n : ℕ} :
    n ∈ OCs p κ 0 r m ↔ band (κ*p) r m 1 true n := by
  simp only [OCs, band, eq_self_iff_true, if_true, Nat.mul_zero,
    Nat.add_zero, Finset.mem_filter, Finset.mem_Ico]
  omega

private theorem mod_injective_short {p r l n t : ℕ} (hp : 0 < p)
    (hl : l < p) (hn : r ≤ n ∧ n < r+l) (ht : r ≤ t ∧ t < r+l)
    (hm : n%p=t%p) : n=t := by
  by_contra hne
  by_cases hnt : n<t
  · have hz : (t-n)%p=0 := Nat.sub_mod_eq_zero_of_mod_eq hm.symm
    have hlt : t-n < p := by omega
    rw [Nat.mod_eq_of_lt hlt] at hz
    omega
  · have hz : (n-t)%p=0 := Nat.sub_mod_eq_zero_of_mod_eq hm
    have hlt : n-t < p := by omega
    rw [Nat.mod_eq_of_lt hlt] at hz
    omega

private theorem period_before {p r n : ℕ} (hp : 0 < p)
    (hn : r ≤ n) (hu : n < (r/p+1)*p) : n/p=r/p := by
  have h1 : r/p ≤ n/p := Nat.div_le_div_right hn
  have h2 := (Nat.div_lt_iff_lt_mul hp).2 hu
  omega

private theorem period_after {p r m n : ℕ} (hp : 0 < p)
    (hs : 2*m<p) (hn : (r/p+1)*p ≤ n) (hu : n<r+2*m) : n/p=r/p+1 := by
  apply (Nat.div_eq_iff hp).2
  have hr : r < (r/p+1)*p := by
    have := Nat.mod_lt r hp
    have := Nat.div_add_mod r p
    nlinarith
  constructor
  · exact hn
  · omega

private theorem potentials_cover {h p r m : ℕ} (hh : 3≤h) (hp : 0<p) (hs : 2*m<p)
    (n t : ℕ) (kR kC : Bool)
    (hn : band ((r/p+1)*p) r m 0 kR n)
    (ht : band ((r/p+1)*p) r m 1 kC t) :
    HPole.k0Weight h p kR kC n t ≤
      phiR h ((r/p+1)*p) r m n + phiC h ((r/p+1)*p) r m t := by
  have hr : r < (r/p+1)*p := by
    have := Nat.mod_lt r hp
    have := Nat.div_add_mod r p
    nlinarith
  have hnr : r ≤ n := hn.1
  have htr : r ≤ t := ht.1
  by_cases hc : (r/p+1)*p < r+2*m
  · have hnn : n<r+2*m := by cases kR <;> simp only [band, Bool.false_eq_true,
      eq_self_iff_true, if_false, if_true] at hn <;> omega
    have htt : t<r+2*m := by cases kC <;> simp only [band, Bool.false_eq_true,
      eq_self_iff_true, if_false, if_true] at ht <;> omega
    have hnp : (n-r)%2=0 := by cases kR <;> simp only [band, Bool.false_eq_true,
      eq_self_iff_true, if_false, if_true] at hn <;> omega
    have htp : (t-r)%2=1 := by cases kC <;> simp only [band, Bool.false_eq_true,
      eq_self_iff_true, if_false, if_true] at ht <;> omega
    have hmod : n%p ≠ t%p := by
      intro hm
      have := mod_injective_short hp hs ⟨hnr, hnn⟩ ⟨htr, htt⟩ hm
      omega
    simp only [HPole.k0Weight, hmod, if_false, phiR, phiC,
      show ¬n<r by omega, show ¬t<r by omega, if_false,
      show ¬r+2*m≤(r/p+1)*p by omega]
    cases kR <;> cases kC
    · have hnb : n<(r/p+1)*p := by simpa [band] using hn.2.1
      have htb : t<(r/p+1)*p := by simpa [band] using ht.2.1
      have he : n/p=t/p := (period_before hp hnr hnb).trans (period_before hp htr htb).symm
      simp only [Bool.false_eq_true, eq_self_iff_true, he, and_self, if_true]
      split_ifs <;> omega
    · simp only [Bool.false_eq_true, false_and, if_false]
      simp only [band, Bool.false_eq_true, if_false] at hn
      simp only [band, eq_self_iff_true, if_true] at ht
      unfold chosen
      split_ifs <;> omega
    · simp only [Bool.true_eq_false, false_and, if_false]
      simp only [band, eq_self_iff_true, if_true] at hn
      simp only [band, Bool.false_eq_true, if_false] at ht
      unfold chosen
      split_ifs <;> omega
    · have hnb : (r/p+1)*p≤n := by simpa [band] using hn.2.1
      have htb : (r/p+1)*p≤t := by simpa [band] using ht.2.1
      have he : n/p=t/p := (period_after hp hs hnb hnn).trans (period_after hp hs htb htt).symm
      simp only [he, and_self, if_true]
      split_ifs <;> omega
  · have hn0 : kR=false := by
      cases kR <;> simp_all only [band, Bool.false_eq_true, eq_self_iff_true, if_false, if_true]
      omega
    have ht0 : kC=false := by
      cases kC <;> simp_all only [band, Bool.false_eq_true, eq_self_iff_true, if_false, if_true]
      omega
    subst kR; subst kC
    simp only [band, Bool.false_eq_true, if_false] at hn ht
    have he : n/p=t/p := (period_before hp hnr hn.2.1).trans (period_before hp htr ht.2.1).symm
    have hm : n%p=t%p → n=t := by
      intro hx
      have hnid := Nat.div_add_mod n p
      have htid := Nat.div_add_mod t p
      rw [he, hx] at hnid
      omega
    unfold HPole.k0Weight phiR phiC
    simp only [show ¬n<r by omega, show ¬t<r by omega, if_false,
      show ¬((r/p+1)*p<r+2*m) by omega, false_and,
      show r+2*m≤(r/p+1)*p by omega, if_true, he, and_self]
    split_ifs with hmod htN
    · have := hm hmod; omega
    · have := hm hmod; omega
    · omega
    · omega



private theorem sum_pair_k0 (p κ r m : ℕ) (φ : ℕ → ℕ) :
    (∑ t ∈ TRs p κ 0 r m, φ t) +
      (∑ t ∈ ORs p κ 0 r m, φ t) =
    (∑ i : Fin m, φ (r + 2 * (i : ℕ))) +
      ∑ t ∈ Ico (r + 2*m) (κ*p), φ t := by
  classical
  let U := (Ico r (r+2*m)).filter (fun t => (t-r)%2=0)
  let V := Ico (r+2*m) (κ*p)
  have hleft : Disjoint (TRs p κ 0 r m) (ORs p κ 0 r m) := by
    apply Finset.disjoint_left.mpr
    intro t ht ho
    simp only [TRs, Tdel, ORs, Nat.mul_zero, Nat.add_zero,
      Finset.mem_filter, Finset.mem_Ico] at ht ho
    omega
  have hright : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro t ht hv
    simp only [U, V, Finset.mem_filter, Finset.mem_Ico] at ht hv
    omega
  have hu : TRs p κ 0 r m ∪ ORs p κ 0 r m = U ∪ V := by
    ext t
    have htmod : (t-r)%2 < 2 := Nat.mod_lt _ (by decide)
    simp only [TRs, Tdel, ORs, U, V, Nat.mul_zero, Nat.add_zero,
      Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    omega
  have hw := sum_stride r m 0 (by omega) (fun _ => True) φ
  simp only [if_true, and_true, Nat.add_zero] at hw
  calc
    _ = ∑ t ∈ TRs p κ 0 r m ∪ ORs p κ 0 r m, φ t :=
      (Finset.sum_union hleft).symm
    _ = (∑ t ∈ U, φ t) + ∑ t ∈ V, φ t := by
      rw [hu, Finset.sum_union hright]
    _ = (∑ i ∈ range m, φ (r+2*i)) + ∑ t ∈ V, φ t := by
      rw [show (∑ t ∈ U, φ t) = ∑ i ∈ range m, φ (r+2*i) from hw.symm]
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun i => φ (r+2*i)) m]

private theorem sum_pairC_k0 (p κ r m : ℕ) (φ : ℕ → ℕ) :
    (∑ t ∈ TCs p κ 0 r m, φ t) +
      (∑ t ∈ OCs p κ 0 r m, φ t) =
    (∑ i : Fin m, φ (r + 2 * (i : ℕ) + 1)) +
      ∑ t ∈ Ico (r + 2*m) (κ*p), φ t := by
  classical
  let U := (Ico r (r+2*m)).filter (fun t => (t-r)%2=1)
  let V := Ico (r+2*m) (κ*p)
  have hleft : Disjoint (TCs p κ 0 r m) (OCs p κ 0 r m) := by
    apply Finset.disjoint_left.mpr
    intro t ht ho
    simp only [TCs, Tdel, OCs, Nat.mul_zero, Nat.add_zero,
      Finset.mem_filter, Finset.mem_Ico] at ht ho
    omega
  have hright : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro t ht hv
    simp only [U, V, Finset.mem_filter, Finset.mem_Ico] at ht hv
    omega
  have hu : TCs p κ 0 r m ∪ OCs p κ 0 r m = U ∪ V := by
    ext t
    have htmod : (t-r)%2 < 2 := Nat.mod_lt _ (by decide)
    simp only [TCs, Tdel, OCs, U, V, Nat.mul_zero, Nat.add_zero,
      Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    omega
  have hw := sum_stride r m 1 (by omega) (fun _ => True) φ
  simp only [if_true, and_true] at hw
  calc
    _ = ∑ t ∈ TCs p κ 0 r m ∪ OCs p κ 0 r m, φ t :=
      (Finset.sum_union hleft).symm
    _ = (∑ t ∈ U, φ t) + ∑ t ∈ V, φ t := by
      rw [hu, Finset.sum_union hright]
    _ = (∑ i ∈ range m, φ (r+2*i+1)) + ∑ t ∈ V, φ t := by
      rw [show (∑ t ∈ U, φ t) = ∑ i ∈ range m, φ (r+2*i+1) from hw.symm]
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun i => φ (r+2*i+1)) m]

private theorem label_card_k0 (p κ r m : ℕ) :
    (TRs p κ 0 r m).card + (ORs p κ 0 r m).card =
      m + (κ*p - (r+2*m)) := by
  have he := sum_pair_k0 p κ r m (fun _ => 1)
  simpa only [← Finset.card_eq_sum_ones, Finset.card_univ,
    Fintype.card_fin, Nat.card_Ico] using he

open Classical in
private theorem chosen_sum (A r m : ℕ) (hr : r < A) :
    (∑ t ∈ Ico r (r+2*m), if chosen A r m t then 1 else 0) =
      min (min (2*m) (A-r)) (2*m-min (2*m) (A-r)) := by
  classical
  by_cases hcross : A < r+2*m
  · have hmin : min (2*m) (A-r) = A-r := Nat.min_eq_right (by omega)
    rw [hmin]
    by_cases hsmall : A-r ≤ r+2*m-A
    · simp only [chosen, hsmall, if_true]
      rw [Finset.sum_boole, Finset.Ico_filter_lt_of_le_right hcross.le,
        Nat.card_Ico]
      simp only [Nat.cast_id]
      omega
    · simp only [chosen, hsmall, if_false]
      rw [Finset.sum_boole, Finset.Ico_filter_le_of_left_le hr.le,
        Nat.card_Ico]
      simp only [Nat.cast_id]
      omega
  · have hmin : min (2*m) (A-r) = 2*m := Nat.min_eq_left (by omega)
    rw [hmin, Nat.sub_self, Nat.min_zero]
    apply Finset.sum_eq_zero
    intro t ht
    have hti := Finset.mem_Ico.mp ht
    have hnot : ¬ chosen A r m t := by
      unfold chosen
      split_ifs <;> omega
    exact if_neg hnot


private theorem potentials_sum (h p κ r m : ℕ) (hh : 3≤h) (hr : r<κ*p) :
    (∑ t ∈ TRs p κ 0 r m, phiR h (κ*p) r m t) +
    (∑ t ∈ ORs p κ 0 r m, phiR h (κ*p) r m t) +
    (∑ t ∈ TCs p κ 0 r m, phiC h (κ*p) r m t) +
    (∑ t ∈ OCs p κ 0 r m, phiC h (κ*p) r m t) =
      (h-3)*m + h*(κ*p-(r+2*m)) +
      2*min (min (2*m) (κ*p-r)) (2*m-min (2*m) (κ*p-r)) := by
  classical
  have hpairR := sum_pair_k0 p κ r m (phiR h (κ*p) r m)
  have hpairC := sum_pairC_k0 p κ r m (phiC h (κ*p) r m)
  by_cases hcross : κ*p<r+2*m
  · have hpad : Ico (r+2*m) (κ*p)=∅ := Finset.Ico_eq_empty_of_le hcross.le
    simp only [hpad, Finset.sum_empty, Nat.add_zero] at hpairR hpairC
    have hzero : κ*p-(r+2*m)=0 := by omega
    rw [hzero, Nat.mul_zero, Nat.add_zero]
    let χ : ℕ→ℕ := fun t => if chosen (κ*p) r m t then 1 else 0
    have hR : (∑ i : Fin m, phiR h (κ*p) r m (r+2*(i:ℕ))) =
        m*(h-3)+2*∑ i : Fin m, χ (r+2*(i:ℕ)) := by
      have he : ∀ i : Fin m, phiR h (κ*p) r m (r+2*(i:ℕ)) =
          h-3+2*χ (r+2*(i:ℕ)) := by
        intro i
        simp only [phiR, show ¬r+2*(i:ℕ)<r by omega, if_false,
          hcross, true_and, χ]
        split_ifs <;> simp
      simp_rw [he]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [mul_comm]
    have hC : (∑ i : Fin m, phiC h (κ*p) r m (r+2*(i:ℕ)+1)) =
        2*∑ i : Fin m, χ (r+2*(i:ℕ)+1) := by
      have he : ∀ i : Fin m, phiC h (κ*p) r m (r+2*(i:ℕ)+1) =
          2*χ (r+2*(i:ℕ)+1) := by
        intro i
        simp only [phiC, show ¬r+2*(i:ℕ)+1<r by omega, if_false,
          show ¬r+2*m≤κ*p by omega, χ]
        split_ifs <;> simp
      simp_rw [he]
      exact (Finset.mul_sum _ _ _).symm
    have hχ := win_sum χ r m
    have hchosen := chosen_sum (κ*p) r m hr
    have hIco : (∑ t∈Ico r (r+2*m), χ t)=∑ t∈range (2*m), χ (r+t) := by
      rw [Finset.sum_Ico_eq_sum_range, show r+2*m-r=2*m by omega]
    change (∑ t∈Ico r (r+2*m), χ t)=_ at hchosen
    rw [hIco] at hchosen
    nlinarith only [hpairR,hpairC,hR,hC,hχ,hchosen]
  · have hN : r+2*m≤κ*p := by omega
    have hmin : min (2*m) (κ*p-r)=2*m := min_eq_left (by omega)
    rw [hmin, Nat.sub_self, Nat.min_zero, Nat.mul_zero, Nat.add_zero]
    have hR : (∑ i : Fin m, phiR h (κ*p) r m (r+2*(i:ℕ))) = m*(h-3) := by
      have he : ∀ i : Fin m, phiR h (κ*p) r m (r+2*(i:ℕ))=h-3 := by
        intro i
        simp [phiR, show ¬r+2*(i:ℕ)<r by omega, hcross]
      simp_rw [he]
      simp
    have hC : (∑ i : Fin m, phiC h (κ*p) r m (r+2*(i:ℕ)+1))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi := i.2
      simp [phiC, show ¬r+2*(i:ℕ)+1<r by omega, hN,
        show ¬r+2*m≤r+2*(i:ℕ)+1 by omega]
    have hPadR : (∑ t∈Ico (r+2*m) (κ*p), phiR h (κ*p) r m t)=
        (κ*p-(r+2*m))*(h-3) := by
      have he : ∀ t∈Ico (r+2*m) (κ*p), phiR h (κ*p) r m t=h-3 := by
        intro t ht
        have := (Finset.mem_Ico.mp ht).1
        simp [phiR, show ¬t<r by omega, hcross]
      rw [Finset.sum_congr rfl he]
      simp [Nat.card_Ico]
    have hPadC : (∑ t∈Ico (r+2*m) (κ*p), phiC h (κ*p) r m t)=
        (κ*p-(r+2*m))*3 := by
      have he : ∀ t∈Ico (r+2*m) (κ*p), phiC h (κ*p) r m t=3 := by
        intro t ht
        have hnt := (Finset.mem_Ico.mp ht).1
        simp [phiC, show ¬t<r by omega, hN, hnt]
      rw [Finset.sum_congr rfl he]
      simp [Nat.card_Ico]
    have hcancel : h-3+3=h := by omega
    have hmul := congrArg (fun x : ℕ => x*(κ*p-(r+2*m))) hcancel
    nlinarith only [hpairR,hpairC,hR,hC,hPadR,hPadC,hmul]

/-- The full-period refined first row for every retained common set. -/
theorem row_refined_first
    {p : ℕ} [hp : Fact p.Prime]
    (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ k ∈ Finset.Icc 1 (h-1), d k ∈ LocRing p)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (cn : ι → ℕ) (hinj : Function.Injective cn)
    {r m : ℕ} (hcr : ∀ a, cn a < r)
    (hp5 : 5 ≤ p) (hshort : 2*m < p)
    (hsq : 2*(r+2*m+p) < p*p) :
    GLE p (refinedFirst h p r m)
      (IntegerPoleRows.rowDet h d cn r m) := by
  classical
  have hp0 : 0<p := hp.out.pos
  have hodd : p%2=1 := by
    rcases hp.out.eq_two_or_odd with he | he
    · omega
    · exact he
  have hrA : r<(r/p+1)*p := by
    have := Nat.mod_lt r hp0
    have := Nat.div_add_mod r p
    nlinarith
  have hH : ((r/p+1)+2*0)*p ≤ r+2*m+p := by
    have := Nat.div_mul_le_self r p
    nlinarith
  have hcompl : ∀ n, n<r+2*m → (n/p+1)*p≤r+2*m+p := by
    intro n hn
    have := Nat.div_mul_le_self n p
    nlinarith
  apply window_k0 h hh d hd hodd hp5 hsq hrA hH hcompl cn hinj hcr
    (phiR h ((r/p+1)*p) r m) (phiC h ((r/p+1)*p) r m)
  · intro t ht
    simp [phiR,phiC,ht]
  · intro n hn t ht
    exact potentials_cover hh hp0 hshort n t false false (band_TR.mp hn) (band_TC.mp ht)
  · intro n hn t ht
    exact potentials_cover hh hp0 hshort n t false true (band_TR.mp hn) (band_OC.mp ht)
  · intro n hn t ht
    exact potentials_cover hh hp0 hshort n t true false (band_OR.mp hn) (band_TC.mp ht)
  · intro n hn t ht
    exact potentials_cover hh hp0 hshort n t true true (band_OR.mp hn) (band_OC.mp ht)
  · have hs := potentials_sum h p (r/p+1) r m hh hrA
    have hc := label_card_k0 p (r/p+1) r m
    rw [hs, hc]
    unfold refinedFirst borderBefore
    have hh3 := Nat.sub_add_cancel hh
    have hmul := congrArg (fun t : ℕ => t*m) hh3
    have hsub : 3*m≤h*(r+m) := by
      nlinarith [Nat.mul_le_mul_right m hh, Nat.zero_le (h*r)]
    have hex := Nat.sub_add_cancel hsub
    nlinarith


private theorem refined_nonwrap {h p r m : ℕ} (hh : 3≤h)
    (hN : r+2*m ≤ (r/p+1)*p) :
    refinedFirst h p r m = h*r+(h-3)*m := by
  have ha : 2*m ≤ (r/p+1)*p-r := by omega
  simp only [refinedFirst, borderBefore, min_eq_left ha, Nat.sub_self,
    Nat.min_zero, mul_zero, Nat.add_zero]
  have hm : 3*m ≤ h*(r+m) := by
    nlinarith [Nat.mul_le_mul_right m hh, Nat.zero_le (h*r)]
  have he := Nat.sub_add_cancel hm
  have hh3 := Nat.sub_add_cancel hh
  have hh3m := congrArg (fun k : ℕ => k*m) hh3
  nlinarith

private theorem refined_cross {h p r m : ℕ} (hh : 3≤h)
    (hr : r ≤ (r/p+1)*p) (hN : (r/p+1)*p ≤ r+2*m) :
    refinedFirst h p r m = h*r+(h-3)*m+
      2*min ((r/p+1)*p-r) (r+2*m-(r/p+1)*p) := by
  have ha : (r/p+1)*p-r ≤ 2*m := by omega
  have hb : 2*m-((r/p+1)*p-r)=r+2*m-(r/p+1)*p := by omega
  simp only [refinedFirst, borderBefore, min_eq_right ha, hb]
  have hm : 3*m ≤ h*(r+m) := by
    nlinarith [Nat.mul_le_mul_right m hh, Nat.zero_le (h*r)]
  have he := Nat.sub_add_cancel hm
  have hh3 := Nat.sub_add_cancel hh
  have hh3m := congrArg (fun k : ℕ => k*m) hh3
  nlinarith

/-- Closed integer chamber guards suffice for the completion square bound. -/
theorem completion_guard_of_chamber
    {p r m j : ℕ} (hshort : 2*m < p)
    (hhi : r ≤ j*p) (hpj : 2*(j+2) ≤ p) :
    2*(r+2*m+p) < p*p := by
  have hmul := Nat.mul_le_mul_right p hpj
  nlinarith

private theorem chamber_div {p r j : ℕ} (hp : 0<p) (hj : 1≤j)
    (hlo : (j-1)*p≤r) (hhi : r<j*p) : r/p+1=j := by
  have hj0 : j-1+1=j := by omega
  have hjp : (j-1)*p+p=j*p := by
    have hm := congrArg (fun k : ℕ => k*p) hj0
    nlinarith
  have hd : r/p=j-1 := (Nat.div_eq_iff hp).2 ⟨hlo, by omega⟩
  omega

theorem row_refined_first_nonwrap
    {p : ℕ} [Fact p.Prime]
    (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ k ∈ Finset.Icc 1 (h-1), d k ∈ LocRing p)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (cn : ι → ℕ) (hinj : Function.Injective cn)
    {r m j : ℕ} (hcr : ∀ a, cn a < r)
    (hp5 : 5 ≤ p) (hshort : 2*m < p)
    (hj1 : 1 ≤ j) (hlo : (j-1)*p ≤ r) (hhi : r ≤ j*p)
    (hpj : 2*(j+2) ≤ p) (hN : r+2*m ≤ j*p) :
    GLE p (h*r+(h-3)*m)
      (IntegerPoleRows.rowDet h d cn r m) := by
  have hb := row_refined_first h hh d hd cn hinj hcr hp5 hshort
    (completion_guard_of_chamber hshort hhi hpj)
  refine hb.mono ?_
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  have hhr := Nat.mul_le_mul_right r hh
  have hhm := Nat.mul_le_mul_right m hh
  by_cases hre : r=j*p
  · have hdiv : r/p=j := by rw [hre]; exact Nat.mul_div_cancel j hp0
    have hnr : r+2*m≤(r/p+1)*p := by rw [hdiv, hre]; nlinarith
    rw [refined_nonwrap hh hnr]
  · have hlt : r<j*p := by omega
    have hdiv := chamber_div hp0 hj1 hlo hlt
    have hnr : r+2*m≤(r/p+1)*p := by rw [hdiv]; exact hN
    rw [refined_nonwrap hh hnr]

theorem row_refined_first_cross_left
    {p : ℕ} [Fact p.Prime]
    (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ k ∈ Finset.Icc 1 (h-1), d k ∈ LocRing p)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (cn : ι → ℕ) (hinj : Function.Injective cn)
    {r m j : ℕ} (hcr : ∀ a, cn a < r)
    (hp5 : 5 ≤ p) (hshort : 2*m < p)
    (hj1 : 1 ≤ j) (hlo : (j-1)*p ≤ r) (hhi : r ≤ j*p)
    (hpj : 2*(j+2) ≤ p)
    (hmid : j*p ≤ r+m) (hN : j*p ≤ r+2*m) :
    GLE p ((h-2)*r+(h-3)*m+2*j*p)
      (IntegerPoleRows.rowDet h d cn r m) := by
  have hb := row_refined_first h hh d hd cn hinj hcr hp5 hshort
    (completion_guard_of_chamber hshort hhi hpj)
  refine hb.mono ?_
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  have hhr := Nat.mul_le_mul_right r hh
  have hhm := Nat.mul_le_mul_right m hh
  by_cases hre : r=j*p
  · have hdiv : r/p=j := by rw [hre]; exact Nat.mul_div_cancel j hp0
    have hnr : r+2*m≤(r/p+1)*p := by rw [hdiv, hre]; nlinarith
    rw [refined_nonwrap hh hnr]
    have hh2 := Nat.sub_add_cancel (show 2≤h by omega)
    have hh2r := congrArg (fun k : ℕ => k*(j*p)) hh2
    rw [hre]
    nlinarith
  · have hlt : r<j*p := by omega
    have hdiv := chamber_div hp0 hj1 hlo hlt
    have hcross : (r/p+1)*p ≤ r+2*m := by rw [hdiv]; exact hN
    have hrA : r≤(r/p+1)*p := by rw [hdiv]; exact hhi
    rw [refined_cross hh hrA hcross, hdiv]
    have hab : j*p-r≤r+2*m-j*p := by omega
    rw [min_eq_left hab]
    have hh2 := Nat.sub_add_cancel (show 2≤h by omega)
    have hh2r := congrArg (fun k : ℕ => k*r) hh2
    have hr := Nat.sub_add_cancel hhi
    nlinarith

theorem row_refined_first_cross_right
    {p : ℕ} [Fact p.Prime]
    (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ k ∈ Finset.Icc 1 (h-1), d k ∈ LocRing p)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (cn : ι → ℕ) (hinj : Function.Injective cn)
    {r m j : ℕ} (hcr : ∀ a, cn a < r)
    (hp5 : 5 ≤ p) (hshort : 2*m < p)
    (hj1 : 1 ≤ j) (hlo : (j-1)*p ≤ r) (hhi : r ≤ j*p)
    (hpj : 2*(j+2) ≤ p)
    (hmid : r+m ≤ j*p) (hN : j*p ≤ r+2*m) :
    GLE p ((h+2)*r+(h+1)*m-2*j*p)
      (IntegerPoleRows.rowDet h d cn r m) := by
  have hb := row_refined_first h hh d hd cn hinj hcr hp5 hshort
    (completion_guard_of_chamber hshort hhi hpj)
  refine hb.mono ?_
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  have hhr := Nat.mul_le_mul_right r hh
  have hhm := Nat.mul_le_mul_right m hh
  by_cases hre : r=j*p
  · have hdiv : r/p=j := by rw [hre]; exact Nat.mul_div_cancel j hp0
    have hnr : r+2*m≤(r/p+1)*p := by rw [hdiv, hre]; nlinarith
    rw [refined_nonwrap hh hnr]
    have hm : m=0 := by omega
    rw [hm, hre]
    simp only [Nat.mul_zero, Nat.add_zero]
    have hle : 2*j*p ≤ (h+2)*(j*p) := by nlinarith
    have he := Nat.sub_add_cancel hle
    nlinarith
  · have hlt : r<j*p := by omega
    have hdiv := chamber_div hp0 hj1 hlo hlt
    have hcross : (r/p+1)*p ≤ r+2*m := by rw [hdiv]; exact hN
    have hrA : r≤(r/p+1)*p := by rw [hdiv]; exact hhi
    rw [refined_cross hh hrA hcross, hdiv]
    have hba : r+2*m-j*p≤j*p-r := by omega
    rw [min_eq_right hba]
    have hrem := Nat.sub_add_cancel hN
    have hh3m := congrArg (fun k : ℕ => k*m) (Nat.sub_add_cancel hh)
    have hsub : 2*j*p ≤ (h+2)*r+(h+1)*m := by nlinarith
    have he := Nat.sub_add_cancel hsub
    nlinarith


section Family
open CatalanCore.Uniform.Content.Wire
variable {p : ℕ} [Fact p.Prime] (h : ℕ) (hh : 3≤h) (d : ℕ→ℚ)
  (hd : ∀ k∈Finset.Icc 1 (h-1), d k∈LocRing p)
  {G : BlockGeom} {r : ℕ} (hs : HybShape G r) (S : Finset (G.geometry r).C)
  (hp5 : 5≤p) (hshort : 2*(G.geometry r).k<p)

include hh hd hs hp5 hshort

theorem family_refined_first (hsq : 2*(r+2*(G.geometry r).k+p)<p*p) :
    GLE p (refinedFirst h p r (G.geometry r).k)
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r,S⟩) := by
  apply IntegerPoleRows.family_of_window h d hs S
  intro ι _ _ cn hinj hcr
  exact row_refined_first h hh d hd cn hinj hcr hp5 hshort hsq

theorem family_refined_first_nonwrap {j : ℕ} (hj : 1≤j)
    (hlo : (j-1)*p≤r) (hhi : r≤j*p) (hpj : 2*(j+2)≤p)
    (hN : r+2*(G.geometry r).k≤j*p) :
    GLE p (h*r+(h-3)*(G.geometry r).k)
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r,S⟩) := by
  apply IntegerPoleRows.family_of_window h d hs S
  intro ι _ _ cn hinj hcr
  exact row_refined_first_nonwrap h hh d hd cn hinj hcr hp5 hshort hj hlo hhi hpj hN

theorem family_refined_first_cross_left {j : ℕ} (hj : 1≤j)
    (hlo : (j-1)*p≤r) (hhi : r≤j*p) (hpj : 2*(j+2)≤p)
    (hmid : j*p≤r+(G.geometry r).k) (hN : j*p≤r+2*(G.geometry r).k) :
    GLE p ((h-2)*r+(h-3)*(G.geometry r).k+2*j*p)
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r,S⟩) := by
  apply IntegerPoleRows.family_of_window h d hs S
  intro ι _ _ cn hinj hcr
  exact row_refined_first_cross_left h hh d hd cn hinj hcr hp5 hshort hj hlo hhi hpj hmid hN

theorem family_refined_first_cross_right {j : ℕ} (hj : 1≤j)
    (hlo : (j-1)*p≤r) (hhi : r≤j*p) (hpj : 2*(j+2)≤p)
    (hmid : r+(G.geometry r).k≤j*p) (hN : j*p≤r+2*(G.geometry r).k) :
    GLE p ((h+2)*r+(h+1)*(G.geometry r).k-2*j*p)
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r,S⟩) := by
  apply IntegerPoleRows.family_of_window h d hs S
  intro ι _ _ cn hinj hcr
  exact row_refined_first_cross_right h hh d hd cn hinj hcr hp5 hshort hj hlo hhi hpj hmid hN
end Family

end CatalanCore.Uniform.Support.HPolePeriodRows

#print axioms CatalanCore.Uniform.Support.HPolePeriodRows.row_refined_first
#print axioms CatalanCore.Uniform.Support.HPolePeriodRows.row_refined_first_cross_left
#print axioms CatalanCore.Uniform.Support.HPolePeriodRows.family_refined_first_cross_right

