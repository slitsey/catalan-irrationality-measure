module

public import CatalanCore.Uniform.Content.Sweep.RInst

@[expose] public section

/-!
# Theorem G for the plane 2 family (lane H, wave H2b; ledger P204, P213)

`PLANE2-P1-ROW` §4, Theorem G, for an arbitrary square minor of the Löwner matrix and an arbitrary pivot
system `(κ, k', π)`.

* `det_dvd_of_potentials`: Leibniz bound, `q^(e a b) ∣ M a b` and `3 ≤ e a b + ur a + uc b` give
  `q^K ∣ det M` for `K + ∑ ur + ∑ uc ≤ 3 |n|`.
* `exists_equiv_side`: the rows of a minor split as kept pivot rows and outside rows.
* `minor_dvd`: with `Schur.jacobi_L` (bordering, one Schur complement; the pairing of row-type and
  column-type labels is arbitrary) and `sw_dvd` (Proposition W): `p^(3 |L| − E)` divides the `Q`-minor
  as soon as `3 |L| + ∑ φ ≤ E + 3 #labels`, where the row-type labels are the outside rows and the deleted
  pivot columns, the column-type labels the outside columns and the deleted pivot rows (`RowLab`,
  `ColLab`), and the potentials `φR`, `φC` (functions of the node) cover `Wlab` on every pair.
* `member_gle`: the same for a member of the family (retained common nodes `c`, window `xs`, `ys`) over
  `R = ℤ_(p)[X]_(p)`, concluding `GLE p E` of the determinant.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep.Gen

namespace CatalanCore.Uniform.Content.Sweep

section Leibniz

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Leibniz bound**: if every entry `M a b` is divisible by `q^(e a b)` and `3 ≤ e a b + ur a + uc b`, then
`q^K ∣ det M` for `K + ∑ ur + ∑ uc ≤ 3 |n|`. -/
theorem det_dvd_of_potentials (q : R) (M : Matrix n n R) (e : n → n → ℕ) (ur uc : n → ℕ)
    (hM : ∀ a b, q ^ e a b ∣ M a b) (he : ∀ a b, 3 ≤ e a b + ur a + uc b) (K : ℕ)
    (hK : K + ∑ a, ur a + ∑ b, uc b ≤ 3 * Fintype.card n) : q ^ K ∣ M.det := by
  rw [Matrix.det_apply]
  refine Finset.dvd_sum fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine Dvd.dvd.mul_left ?_ _
  have h1 : ∏ i, q ^ e (σ i) i ∣ ∏ i, M (σ i) i :=
    Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hM (σ i) i
  rw [Finset.prod_pow_eq_pow_sum] at h1
  refine (pow_dvd_pow q ?_).trans h1
  have h2 : ∑ i, (3 : ℕ) ≤ ∑ i, (e (σ i) i + ur (σ i) + uc i) :=
    Finset.sum_le_sum fun i _ => he (σ i) i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Equiv.sum_comp σ ur] at h2
  simp only [smul_eq_mul] at h2
  omega


end Leibniz

section Side

/-- The rows of a minor split into pivot nodes (kept pivots) and outside nodes. -/
theorem exists_equiv_side {Ω L : Type} [Fintype Ω] [DecidableEq Ω] [Fintype L] [DecidableEq L]
    (nodeF : Ω → ℕ) (hinj : Function.Injective nodeF) (rn : L → ℕ) (hrn : Function.Injective rn) :
    ∃ e : L ≃ ({x : Ω // x ∉ (Finset.univ.filter fun x => ∀ a, nodeF x ≠ rn a)} ⊕
        {a : L // ¬ ∃ x, nodeF x = rn a}),
      ∀ a, Sum.elim (fun x => nodeF x.1) (fun o => rn o.1) (e a) = rn a := by
  classical
  have key : ∀ a (h : ∃ x, nodeF x = rn a),
      h.choose ∉ (Finset.univ.filter fun x => ∀ a, nodeF x ≠ rn a) := by
    intro a h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not]
    exact ⟨a, h.choose_spec⟩
  let f : L → ({x : Ω // x ∉ (Finset.univ.filter fun x => ∀ a, nodeF x ≠ rn a)} ⊕
        {a : L // ¬ ∃ x, nodeF x = rn a}) :=
    fun a => if h : ∃ x, nodeF x = rn a then Sum.inl ⟨h.choose, key a h⟩ else Sum.inr ⟨a, h⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      by_cases h : ∃ x, nodeF x = rn a <;> by_cases h' : ∃ x, nodeF x = rn a'
      · simp only [f, dif_pos h, dif_pos h', Sum.inl.injEq, Subtype.mk.injEq] at haa
        apply hrn
        rw [← h.choose_spec, ← h'.choose_spec, haa]
      · simp [f, dif_pos h, dif_neg h'] at haa
      · simp [f, dif_neg h, dif_pos h'] at haa
      · simp only [f, dif_neg h, dif_neg h', Sum.inr.injEq, Subtype.mk.injEq] at haa
        exact haa
    · rintro (⟨x, hx⟩ | ⟨a, ha⟩)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hx
        obtain ⟨a, ha⟩ := hx
        have h : ∃ y, nodeF y = rn a := ⟨x, ha⟩
        refine ⟨a, ?_⟩
        simp only [f, dif_pos h]
        congr 2
        exact hinj (h.choose_spec.trans ha.symm)
      · refine ⟨a, ?_⟩
        simp only [f, dif_neg ha]
  refine ⟨Equiv.ofBijective f hf, fun a => ?_⟩
  by_cases h : ∃ x, nodeF x = rn a
  · simp only [Equiv.ofBijective_apply, f, dif_pos h, Sum.elim_inl]
    exact h.choose_spec
  · simp [Equiv.ofBijective_apply, f, dif_neg h]

end Side

section Minor

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] {κ k' π : ℕ} {ξ : R}
  {L : Type} [Fintype L] [DecidableEq L] (rn cl : L → ℕ)

/-- Nodes of the row-type labels: outside rows (`kR = true`) and deleted pivot columns (`kR = false`). -/
def RowLab (p κ k' π : ℕ) (kR : Bool) (n : ℕ) : Prop :=
  (kR = true ∧ ∃ a, rn a = n ∧ ¬ ∃ x : PivIdx p κ k', rowNode p κ k' π x = n) ∨
  (kR = false ∧ ∃ y : PivIdx p κ k', colNode p κ k' π y = n ∧ ∀ b, cl b ≠ n)

/-- Nodes of the column-type labels: outside columns and deleted pivot rows. -/
def ColLab (p κ k' π : ℕ) (kC : Bool) (m : ℕ) : Prop :=
  (kC = true ∧ ∃ b, cl b = m ∧ ¬ ∃ y : PivIdx p κ k', colNode p κ k' π y = m) ∨
  (kC = false ∧ ∃ x : PivIdx p κ k', rowNode p κ k' π x = m ∧ ∀ a, rn a ≠ m)

open Classical in
/-- **Theorem G (general minor)**.  Let `rn`, `cl` be the row and column nodes of a square minor of the
Löwner matrix (injective, complete periods).  Row-type labels are the outside rows `RowOut` and the deleted
pivot columns `DelC`; column-type labels the outside columns `ColOut` and the deleted pivot rows `DelR`.
If potentials `φR`, `φC` (functions of the node) cover the weights of all pairs of labels, then
`p^(3 |L| − E) ∣ det` as soon as `3 |L| + ∑ potentials ≤ E + 3 #(row-type labels)`. -/
theorem minor_dvd (hU : UnitDet p v u κ k' ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (hπ : π ≤ 1)
    (hrinj : Function.Injective rn) (hcinj : Function.Injective cl)
    (hrc : ∀ a, (rn a / p + 1) * p ≤ N) (hcc : ∀ b, (cl b / p + 1) * p ≤ N)
    (φR φC : ℕ → ℕ)
    (hW : ∀ (n m : ℕ) (kR kC : Bool), RowLab rn cl p κ k' π kR n → ColLab rn cl p κ k' π kC m →
      Wlab u p kR kC (oc p κ π (n % p)) (oc p κ (1 - π) (m % p)) n m ≤ φR n + φC m)
    (E : ℕ)
    (hcond : 3 * Fintype.card L +
      (∑ a ∈ Finset.univ.filter (fun a : L => ¬ ∃ x : PivIdx p κ k', rowNode p κ k' π x = rn a), φR (rn a) +
       ∑ y ∈ Finset.univ.filter (fun y : PivIdx p κ k' => ∀ b, colNode p κ k' π y ≠ cl b),
          φR (colNode p κ k' π y) +
       ∑ b ∈ Finset.univ.filter (fun b : L => ¬ ∃ y : PivIdx p κ k', colNode p κ k' π y = cl b), φC (cl b) +
       ∑ x ∈ Finset.univ.filter (fun x : PivIdx p κ k' => ∀ a, rowNode p κ k' π x ≠ rn a),
          φC (rowNode p κ k' π x)) ≤
      E + 3 * ((Finset.univ.filter (fun a : L => ¬ ∃ x : PivIdx p κ k', rowNode p κ k' π x = rn a)).card +
        (Finset.univ.filter (fun y : PivIdx p κ k' => ∀ b, colNode p κ k' π y ≠ cl b)).card)) :
    (p : R) ^ (3 * Fintype.card L - E) ∣
      (Matrix.of fun a b => Qent (p := p) v u ξ (rn a) (cl b)).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  set DelR : Finset (PivIdx p κ k') := Finset.univ.filter (fun x => ∀ a, rowNode p κ k' π x ≠ rn a) with hDelR
  set DelC : Finset (PivIdx p κ k') := Finset.univ.filter (fun y => ∀ b, colNode p κ k' π y ≠ cl b) with hDelC
  set RowOut : Finset L := Finset.univ.filter (fun a : L => ¬ ∃ x : PivIdx p κ k', rowNode p κ k' π x = rn a)
    with hRowOut
  set ColOut : Finset L := Finset.univ.filter (fun b : L => ¬ ∃ y : PivIdx p κ k', colNode p κ k' π y = cl b)
    with hColOut
  obtain ⟨eR, heR⟩ := exists_equiv_side (rowNode p κ k' π) (rowNode_injective hp0) rn hrinj
  obtain ⟨eC, heC⟩ := exists_equiv_side (colNode p κ k' π) (colNode_injective hp0) cl hcinj
  let Lo := {a : L // ¬ ∃ x : PivIdx p κ k', rowNode p κ k' π x = rn a}
  let Lc := {b : L // ¬ ∃ y : PivIdx p κ k', colNode p κ k' π y = cl b}
  let zn : Lo → ℕ := fun o => rn o.1
  let yn : Lc → ℕ := fun o => cl o.1
  have hcL1 : Fintype.card L = (Fintype.card (PivIdx p κ k') - DelR.card) + Fintype.card Lo := by
    rw [Fintype.card_congr eR, Fintype.card_sum, Fintype.card_subtype_compl (fun x => x ∈ DelR),
      Fintype.card_coe]
  have hcL2 : Fintype.card L = (Fintype.card (PivIdx p κ k') - DelC.card) + Fintype.card Lc := by
    rw [Fintype.card_congr eC, Fintype.card_sum, Fintype.card_subtype_compl (fun x => x ∈ DelC),
      Fintype.card_coe]
  have hcLo : Fintype.card Lo = RowOut.card := Fintype.card_subtype _
  have hcLc : Fintype.card Lc = ColOut.card := Fintype.card_subtype _
  have hle1 : DelR.card ≤ Fintype.card (PivIdx p κ k') := Finset.card_le_univ _
  have hle2 : DelC.card ≤ Fintype.card (PivIdx p κ k') := Finset.card_le_univ _
  let eC' : (Lo ⊕ ↥DelC) ≃ (Lc ⊕ ↥DelR) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_coe]; omega)
  have hZ1 : Schur.Qm (Hq (p := p) v u κ k' π ξ zn yn) * Zp (p := p) v u κ k' π ξ = 1 := by
    rw [Qm_Hq]; exact Qp_mul_Zp v u hU hpv hodd hp5 hN hH hRad
  have hZ2 : Zp (p := p) v u κ k' π ξ * Schur.Qm (Hq (p := p) v u κ k' π ξ zn yn) = 1 := by
    rw [Qm_Hq]; exact Zp_mul_Qp v u hU hpv hodd hp5 hN hH hRad
  have hJ := Schur.jacobi_L (Hq (p := p) v u κ k' π ξ zn yn) DelR DelC
    (Zp (p := p) v u κ k' π ξ) hZ1 hZ2
    (fun a => Sum.map Subtype.val id (eR a)) (fun a => Sum.map Subtype.val id (eC a))
    (fun l : Lo ⊕ ↥DelC => Sum.map id Subtype.val (Equiv.refl _ l))
    (fun l => Sum.map id Subtype.val (eC' l)) eR eC (Equiv.refl _) eC'
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  -- the minor is the Q-minor
  have hM1 : (Matrix.of fun a b => Hq (p := p) v u κ k' π ξ zn yn (Sum.map Subtype.val id (eR a))
      (Sum.map Subtype.val id (eC b))) = Matrix.of fun a b => Qent (p := p) v u ξ (rn a) (cl b) := by
    ext a b
    simp only [Hq, Matrix.of_apply]
    have h1 := heR a
    have h2 := heC b
    have e1 : Sum.elim (rowNode p κ k' π) zn (Sum.map Subtype.val id (eR a)) = rn a := by
      rcases h : eR a with x | o <;> rw [h] at h1 <;> simpa [zn] using h1
    have e2 : Sum.elim (colNode p κ k' π) yn (Sum.map Subtype.val id (eC b)) = cl b := by
      rcases h : eC b with x | o <;> rw [h] at h2 <;> simpa [yn] using h2
    rw [e1, e2]
  rw [hM1] at hJ
  simp only [Equiv.refl_apply] at hJ
  by_cases hE : E ≤ 3 * Fintype.card L
  swap
  · have : 3 * Fintype.card L - E = 0 := by omega
    rw [this, pow_zero]; exact one_dvd _
  have hzc : ∀ o : Lo, (zn o / p + 1) * p ≤ N := fun o => hrc o.1
  have hyc : ∀ o : Lc, (yn o / p + 1) * p ≤ N := fun o => hcc o.1
  have hcardLab : Fintype.card (Lo ⊕ ↥DelC) = RowOut.card + DelC.card := by
    rw [Fintype.card_sum, hcLo, Fintype.card_coe]
  have rowLab_of : ∀ a : Lo ⊕ ↥DelC, RowLab rn cl p κ k' π (Sum.map id Subtype.val a).isLeft
      (nR (p := p) (κ := κ) (k' := k') (π := π) zn (Sum.map id Subtype.val a)) := by
    rintro (o | ⟨y, hy⟩)
    · exact Or.inl ⟨rfl, o.1, rfl, o.2⟩
    · refine Or.inr ⟨rfl, y, rfl, fun b => ?_⟩
      simp only [hDelC, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact (hy b).symm
  have colLab_of : ∀ b : Lc ⊕ ↥DelR, ColLab rn cl p κ k' π (Sum.map id Subtype.val b).isLeft
      (nC (p := p) (κ := κ) (k' := k') (π := π) yn (Sum.map id Subtype.val b)) := by
    rintro (o | ⟨x, hx⟩)
    · exact Or.inl ⟨rfl, o.1, rfl, o.2⟩
    · refine Or.inr ⟨rfl, x, rfl, fun a => ?_⟩
      simp only [hDelR, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact (hx a).symm
  let ρ' : (Lo ⊕ ↥DelC) → (Lo ⊕ PivIdx p κ k') := fun l => Sum.map id Subtype.val l
  let κ'' : (Lo ⊕ ↥DelC) → (Lc ⊕ PivIdx p κ k') := fun l => Sum.map id Subtype.val (eC' l)
  let ur : (Lo ⊕ ↥DelC) → ℕ := fun l => φR (nR (p := p) (κ := κ) (k' := k') (π := π) zn (ρ' l))
  let uc : (Lo ⊕ ↥DelC) → ℕ := fun l => φC (nC (p := p) (κ := κ) (k' := k') (π := π) yn (κ'' l))
  have hsumR : ∑ a, ur a = ∑ a ∈ RowOut, φR (rn a) + ∑ y ∈ DelC, φR (colNode p κ k' π y) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · exact (Finset.sum_subtype RowOut (fun a => by simp [hRowOut]) (fun a => φR (rn a))).symm
    · exact Finset.sum_coe_sort DelC (fun y => φR (colNode p κ k' π y))
  have hsumC : ∑ b, uc b = ∑ b ∈ ColOut, φC (cl b) + ∑ x ∈ DelR, φC (rowNode p κ k' π x) := by
    have h1 : ∑ b, uc b = ∑ l : Lc ⊕ ↥DelR, φC (nC (p := p) (κ := κ) (k' := k') (π := π) yn
        (Sum.map id Subtype.val l)) :=
      Equiv.sum_comp eC' (fun l => φC (nC (p := p) (κ := κ) (k' := k') (π := π) yn
        (Sum.map id Subtype.val l)))
    rw [h1, Fintype.sum_sum_type]
    congr 1
    · exact (Finset.sum_subtype ColOut (fun a => by simp [hColOut]) (fun a => φC (cl a))).symm
    · exact Finset.sum_coe_sort DelR (fun x => φC (rowNode p κ k' π x))
  have hdetSw : (p : R) ^ (3 * Fintype.card L - E) ∣
      (Matrix.of fun a b => (Schur.Sw (Hq (p := p) v u κ k' π ξ zn yn)
        (Zp (p := p) v u κ k' π ξ)) (ρ' a) (κ'' b)).det := by
    refine det_dvd_of_potentials (p : R) _ (fun a b => 3 - wR u (p := p) (κ := κ) (k' := k') (π := π) zn yn (ρ' a) (κ'' b))
      ur uc ?_ ?_ _ ?_
    · intro a b
      exact sw_dvd v u zn yn hU hpv hodd hp5 hN hH hRad hπ hzc hyc (ρ' a) (κ'' b)
    · intro a b
      have h3 : wR u (p := p) (κ := κ) (k' := k') (π := π) zn yn (ρ' a) (κ'' b) ≤
          φR (nR (p := p) (κ := κ) (k' := k') (π := π) zn (ρ' a)) +
            φC (nC (p := p) (κ := κ) (k' := k') (π := π) yn (κ'' b)) :=
        hW _ _ _ _ (rowLab_of a) (colLab_of (eC' b))
      have h4 : wR u (p := p) (κ := κ) (k' := k') (π := π) zn yn (ρ' a) (κ'' b) ≤ 3 := Wlab_le _ _ _ _ _ _ _ _
      show 3 ≤ (3 - wR u (p := p) (κ := κ) (k' := k') (π := π) zn yn (ρ' a) (κ'' b)) +
        φR (nR (p := p) (κ := κ) (k' := k') (π := π) zn (ρ' a)) +
          φC (nC (p := p) (κ := κ) (k' := k') (π := π) yn (κ'' b))
      omega
    · rw [hsumR, hsumC, hcardLab]
      omega
  exact hdetSw.trans hJ.symm.dvd

end Minor


section MemberG

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {κ k' π : ℕ} {ι κw : Type} [Fintype ι] [DecidableEq ι] [Fintype κw] [DecidableEq κw]
  (c : ι → ℕ) (xs ys : κw → ℕ)

theorem memRow_injective (hc : Function.Injective c) (hx : Function.Injective xs)
    (h2 : ∀ i j, xs i ≠ c j) : Function.Injective (memRow c xs) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (hc h)
  · exact absurd h.symm (h2 b a)
  · exact absurd h (h2 a b)
  · exact congrArg Sum.inr (hx h)

theorem memCol_injective (hc : Function.Injective c) (hy : Function.Injective ys)
    (h1 : ∀ i j, c i ≠ ys j) : Function.Injective (memCol c ys) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (hc h)
  · exact absurd h (h1 a b)
  · exact absurd h.symm (h1 b a)
  · exact congrArg Sum.inr (hy h)

/-- **Theorem G for a member of the plane 2 family.**  Retained common nodes `c`, window rows `xs` and
columns `ys` (all complete periods below `N`, `p² > 2N`), pivot system `(κ, k', π)` with `(κ + 2k') p ≤ N`:
if potentials `φR`, `φC` cover the weights of all labels, every coefficient of the determinant has
`p`-adic denominator at most `E`, whenever `3 (|ι| + |κ|) + ∑ potentials ≤ E + 3 #(row-type labels)`. -/
theorem member_gle (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p)
    (hH : (κ + 2 * k') * p ≤ N) (hπ : π ≤ 1)
    (hcinj : Function.Injective c) (hxinj : Function.Injective xs) (hyinj : Function.Injective ys)
    (h1 : ∀ i j, c i ≠ ys j) (h2 : ∀ i j, xs i ≠ c j) (h3 : ∀ i j, xs i ≠ ys j)
    (hrc : ∀ a, (memRow c xs a / p + 1) * p ≤ N) (hcc : ∀ b, (memCol c ys b / p + 1) * p ≤ N)
    (φR φC : ℕ → ℕ)
    (hW : ∀ (n m : ℕ) (kR kC : Bool), RowLab (memRow c xs) (memCol c ys) p κ k' π kR n →
      ColLab (memRow c xs) (memCol c ys) p κ k' π kC m →
      Wlab u p kR kC (oc p κ π (n % p)) (oc p κ (1 - π) (m % p)) n m ≤ φR n + φC m)
    (E : ℕ)
    (hcond : by classical exact 3 * Fintype.card (ι ⊕ κw) +
      (∑ a ∈ Finset.univ.filter (fun a : ι ⊕ κw => ¬ ∃ x : PivIdx p κ k', rowNode p κ k' π x = memRow c xs a),
          φR (memRow c xs a) +
       ∑ y ∈ Finset.univ.filter (fun y : PivIdx p κ k' => ∀ b, colNode p κ k' π y ≠ memCol c ys b),
          φR (colNode p κ k' π y) +
       ∑ b ∈ Finset.univ.filter (fun b : ι ⊕ κw => ¬ ∃ y : PivIdx p κ k', colNode p κ k' π y = memCol c ys b),
          φC (memCol c ys b) +
       ∑ x ∈ Finset.univ.filter (fun x : PivIdx p κ k' => ∀ a, rowNode p κ k' π x ≠ memRow c xs a),
          φC (rowNode p κ k' π x)) ≤
      E + 3 * ((Finset.univ.filter (fun a : ι ⊕ κw => ¬ ∃ x : PivIdx p κ k', rowNode p κ k' π x = memRow c xs a)).card +
        (Finset.univ.filter (fun y : PivIdx p κ k' => ∀ b, colNode p κ k' π y ≠ memCol c ys b)).card)) :
    GLE p E (seqFullN (fS v u) (eS v u) c xs ys (X : ℚ[X])).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hr : ∀ a, memRow c xs a < N := fun a => lt_of_complete hp0 (hrc a)
  have hcl : ∀ b, memCol c ys b < N := fun b => lt_of_complete hp0 (hcc b)
  have hd := minor_dvd (p := p) (R := RP p) (ξ := xiP p) (π := π) (κ := κ) (k' := k') v u
    (memRow c xs) (memCol c ys) (unitDet_of_unitProp v u κ k' (xiP_unitProp p) hodd hN hH hpv) hpv hodd hp5 hN hH (pRad_RP p) hπ
    (memRow_injective c xs hcinj hxinj h2) (memCol_injective c ys hcinj hyinj h1) hrc hcc φR φC hW E hcond
  have hg := gle_member (p := p) v u c xs ys hN hr hcl hcinj h1 h2 h3 hd
  refine GLE.mono ?_ hg
  rw [Fintype.card_sum] at *
  omega

end MemberG

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.member_gle
