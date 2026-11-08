module

public import CatalanCore.Uniform.Content.Sweep.CellAction
public import CatalanCore.Uniform.Content.Sweep.Rows

@[expose] public section

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support
/-!
# Cells and the tropical rows of the one-term datum, zeta(3) (lane H, wave H2b; ledger N2, Z04 table)

The datum with a double pole at `1` only (`u = 0`, `b = u/v = 0`): `f_t = ∑_{κ ≤ t} (-v/κ²)`,
`e_t = ∑_{κ ≤ t} (-2v/κ³)` (`fB`, `eB`).  `Datum.plane2` needs `u ≠ 0`, so `Sweep.Cells` does not apply; its
polar/regular splitting lemmas are generic in `(v, u)` and are reused with `u = 0`.  Cells are periods
(`T2 = U2 = 0`): the weight table `WtB` is `3` for distinct congruent nodes, `0` in one period, `2`
across periods; the diagonal is `3` in periods `≥ 1` and `0` in period `0` (`weight_tableB`).

Rows (ZETA3-ONE-TERM): `row_B1` (`3(r+m) - ‖m‖_p`, the class potentials of `Sweep.Rows`), `row_B2`
(`p ≤ r`: `6(r+m-p)`), `row_B4` (`p ≥ r`: `3(r+2m-p)₊`).  Statements as `GLE` bounds on the member
determinant of the window geometry, exactly as in `Sweep.Rows`.
-/

namespace CatalanCore.Uniform.Content.Sweep

/-! ### The one-term (zeta(3)) sequences -/

section Seq

variable (v : ℤ)

/-- `f_t = ∑_{κ ≤ t} (-v/κ²)` of the datum with a double pole at `1` only (`u = 0`). -/
noncomputable def fB (t : ℕ) : ℚ := ∑ k ∈ range t, (T1 v 0 (k + 1) + T2 0 (k + 1))
/-- `e_t = ∑_{κ ≤ t} (-2v/κ³)`. -/
noncomputable def eB (t : ℕ) : ℚ := ∑ k ∈ range t, (U1 v 0 (k + 1) + U2 0 (k + 1))

variable {p : ℕ} [hp : Fact p.Prime]

theorem fB_eq (t : ℕ) : fB v t = PF v 0 p t + RF v 0 p t := by
  unfold fB PF RF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [polF_add_regF]

theorem eB_eq (t : ℕ) : eB v t = PE v 0 p t + RE v 0 p t := by
  unfold eB PE RE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [polE_add_regE]

theorem polF_zero_of_not_dvd {κ : ℕ} (h : ¬ p ∣ κ) : polF v 0 p κ = 0 := by
  have h2 : T2 0 κ = 0 := by simp [T2]
  unfold polF; rw [if_neg h]; simp [h2]

theorem polE_zero_of_not_dvd {κ : ℕ} (h : ¬ p ∣ κ) : polE v 0 p κ = 0 := by
  have h2 : U2 0 κ = 0 := by simp [U2]
  unfold polE; rw [if_neg h]; simp [h2]

theorem PF_same_period {s t : ℕ} (hst : s ≤ t) (hper : s / p = t / p) :
    PF v 0 p t = PF v 0 p s :=
  eq_telescope _ s t hst fun i hsi hi => by
    have h := PF_step v 0 (p := p) i
    have := polF_zero_of_not_dvd (p := p) v (no_mult_same_period (s := s) (κ := i + 1) (t := t) (by omega) (by omega) hper)
    linarith

theorem PE_same_period {s t : ℕ} (hst : s ≤ t) (hper : s / p = t / p) :
    PE v 0 p t = PE v 0 p s :=
  eq_telescope _ s t hst fun i hsi hi => by
    have h := PE_step v 0 (p := p) i
    have := polE_zero_of_not_dvd (p := p) v (no_mult_same_period (s := s) (κ := i + 1) (t := t) (by omega) (by omega) hper)
    linarith

end Seq

/-! ### The period weights -/

variable (p : ℕ)

/-- Diagonal weight: `3` in periods `≥ 1`, `0` in period `0`. -/
def WdB (t : ℕ) : ℕ := if 1 ≤ t / p then 3 else 0
/-- `0` in one period, `2` across periods. -/
def w3B (s t : ℕ) : ℕ := if s / p = t / p then 0 else 2
/-- The joint weight of the one-term table. -/
def WtB (s t : ℕ) : ℕ := if s = t then WdB p s else if s % p = t % p then 3 else w3B p s t

theorem WtB_le_three (a b : ℕ) : WtB p a b ≤ 3 := by
  unfold WtB WdB w3B; split_ifs <;> omega

/-! ### The generic chain at `u = 0` is this table

`Sweep.Cells` carries the half map `half p u`, which is `0` for `u = 0`: cells are periods.  So at `u = 0`
the generic weights `Wd`, `Wt`, `w3` are exactly `WdB`, `WtB`, `w3B`, and `fS v 0`, `eS v 0` are `fB`, `eB`. -/

theorem fB_eq_fS (v : ℤ) : fB v = fS v 0 := rfl
theorem eB_eq_eS (v : ℤ) : eB v = eS v 0 := rfl

theorem half_zero (t : ℕ) : half p 0 t = 0 := by simp [half]

theorem cell_zero (t : ℕ) : cell p 0 t = (t / p, 0) := by simp [cell, half]

theorem w3_zero (s t : ℕ) : w3 (cell p 0 s) (cell p 0 t) = w3B p s t := by
  unfold w3 w3B
  simp only [cell_zero, Prod.mk.injEq, and_true]
  split_ifs <;> simp_all

theorem Wd_zero (t : ℕ) : Wd p 0 t = WdB p t := by
  unfold Wd WdB
  simp [half_zero]

theorem Wt_zero (s t : ℕ) : Wt p 0 s t = WtB p s t := by
  unfold Wt WtB
  rw [Wd_zero, w3_zero]


section TableB

variable {p : ℕ} [hp : Fact p.Prime] (v : ℤ) {N : ℕ}

theorem lwB_offdiag {s t : ℕ} (hst : s < t) :
    lw (fB v) (eB v) s t = (fB v t - fB v s) / (((t - s : ℕ) : ℚ)) := by
  unfold lw
  rw [if_neg (Nat.ne_of_lt hst), Nat.cast_sub hst.le]

/-- **The weight table of the one-term datum.** -/
theorem weight_tableB (hp5 : 5 ≤ p) (hN : 2 * N < p * p) (s t : ℕ) (hs : s < N) (ht : t < N) :
    Vp p (WtB p s t) (lw (fB v) (eB v) s t) := by
  have lt_case : ∀ s t : ℕ, s < t → t < N → Vp p (WtB p s t) (lw (fB v) (eB v) s t) := by
    intro s t hst ht
    rw [lwB_offdiag v hst]
    have hdec : fB v t - fB v s = (PF v 0 p t - PF v 0 p s) + (RF v 0 p t - RF v 0 p s) := by
      rw [fB_eq (p := p), fB_eq (p := p)]; ring
    have hR : Vp p 0 (RF v 0 p t - RF v 0 p s) :=
      Vp.zero_iff.2 ((LocRing p).sub_mem (RF_mem v 0 t) (RF_mem v 0 s))
    have hne : s ≠ t := Nat.ne_of_lt hst
    by_cases hper : s / p = t / p
    · have h0 : PF v 0 p t - PF v 0 p s = 0 := by rw [PF_same_period v hst.le hper]; ring
      have hnc : ¬ s % p = t % p := by
        intro hm
        apply hne
        have h1 := Nat.div_add_mod s p
        have h2 := Nat.div_add_mod t p
        rw [hper, hm] at h1
        omega
      have hw : WtB p s t = 0 := by unfold WtB w3B; rw [if_neg hne, if_neg hnc, if_pos hper]
      rw [hw]
      have := RF_div_mem v 0 hp5 hN (a := s) (b := t) (by omega) ht hne
      rw [hdec, h0, zero_add, Nat.cast_sub hst.le]
      unfold Vp; simpa using this
    · have h1 := PF_diff_period v 0 hN hst.le ht
      have hf : Vp p 2 (fB v t - fB v s) := by
        rw [hdec]; exact Vp.add h1 (hR.mono (by omega))
      by_cases hcong : s % p = t % p
      · have hdvd : p ∣ t - s := (Nat.modEq_iff_dvd' hst.le).1 hcong
        obtain ⟨l, hl⟩ := hdvd
        have hl0 : 0 < l := by
          rcases Nat.eq_zero_or_pos l with h0 | h0
          · simp [h0] at hl; omega
          · exact h0
        have hlp : l < p := by
          by_contra hge
          have := Nat.mul_le_mul_left p (not_lt.1 hge)
          omega
        have hw : WtB p s t = 3 := by unfold WtB; rw [if_neg hne, if_pos hcong]
        rw [hw]
        rw [hl]
        exact Vp.div_p_mul hf hl0 hlp
      · have hnd : ¬ p ∣ t - s := fun h => hcong ((Nat.modEq_iff_dvd' hst.le).2 h)
        have hw : WtB p s t = 2 := by unfold WtB w3B; rw [if_neg hne, if_neg hcong, if_neg hper]
        rw [hw]
        exact Vp.div_unit hf hnd
  by_cases hst : s = t
  · subst hst
    unfold lw; rw [if_pos rfl]
    unfold WtB; rw [if_pos rfl]
    rw [eB_eq (p := p) v]
    have hRE : RE v 0 p s ∈ LocRing p := RE_mem v 0 s
    have hPE0 : PE v 0 p 0 = 0 := by simp [PE]
    unfold WdB
    by_cases h1 : 1 ≤ s / p
    · rw [if_pos h1]
      have := PE_diff_period v 0 hN (Nat.zero_le s) hs
      rw [hPE0, sub_zero] at this
      exact (Vp.add this (Vp.of_mem hRE)).neg
    · rw [if_neg h1]
      have hs0 : s / p = 0 := Nat.lt_one_iff.mp (not_le.mp h1)
      have := PE_same_period v (Nat.zero_le s) (p := p) (by rw [hs0]; simp)
      rw [hPE0] at this
      rw [this, zero_add]
      exact (Vp.of_mem hRE).neg
  · rcases Nat.lt_or_gt_of_ne hst with hlt | hgt
    · exact lt_case s t hlt ht
    · have h := lt_case t s hgt hs
      have hsym : lw (fB v) (eB v) s t = lw (fB v) (eB v) t s := by
        unfold lw
        rw [if_neg hst, if_neg (Ne.symm hst)]
        have h1 : (s : ℚ) - t ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hst)
        have h2 : (t : ℚ) - s ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Ne.symm hst))
        field_simp
        ring
      have hsy : WtB p s t = WtB p t s := by
        unfold WtB w3B
        by_cases h : s = t
        · exact absurd h hst
        · rw [if_neg h, if_neg (Ne.symm h)]
          by_cases hm : s % p = t % p
          · rw [if_pos hm, if_pos hm.symm]
          · rw [if_neg hm, if_neg (Ne.symm hm)]
            by_cases hq : s / p = t / p
            · rw [if_pos hq, if_pos hq.symm]
            · rw [if_neg hq, if_neg (Ne.symm hq)]
      rw [hsym, hsy]
      exact h

end TableB


section AssignmentB

variable {p : ℕ} [hp : Fact p.Prime] (v : ℤ) {N : ℕ}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem entry_gleB (hp5 : 5 ≤ p) (hN : 2 * N < p * p) (cn : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, cn a < N) (hx : ∀ i, xs i < N) (hy : ∀ i, ys i < N) (a b : ι ⊕ κ) :
    GLE p (WtB p (Sum.elim cn xs a) (Sum.elim cn ys b))
      (seqFullN (fB v) (eB v) cn xs ys (X : ℚ[X]) a b) := by
  have bnd : ∀ a, Sum.elim cn xs a < N := fun a => by
    rcases a with a | i
    · exact hc a
    · exact hx i
  have bnd' : ∀ b, Sum.elim cn ys b < N := fun b => by
    rcases b with b | j
    · exact hc b
    · exact hy j
  have key := fun a b => GLE.C_iff.2 (weight_tableB v hp5 hN _ _ (bnd a) (bnd' b))
  rcases a with a | i <;> rcases b with b | j
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, smul_eq_mul, Polynomial.algebraMap_eq]
    by_cases h : a = b
    · simp only [h, if_true, mul_one]
      exact (key (Sum.inl b) (Sum.inl b)).add (GLE.X.mono (Nat.zero_le _))
    · simp only [h, if_false, mul_zero, add_zero]
      exact key (Sum.inl a) (Sum.inl b)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact key (Sum.inl a) (Sum.inr j)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact key (Sum.inr i) (Sum.inl b)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact key (Sum.inr i) (Sum.inr j)

theorem det_gle_of_dualB (hp5 : 5 ≤ p) (hN : 2 * N < p * p) (cn : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, cn a < N) (hx : ∀ i, xs i < N) (hy : ∀ i, ys i < N) (uR uC : ι ⊕ κ → ℕ)
    (hW : ∀ a b, WtB p (Sum.elim cn xs a) (Sum.elim cn ys b) ≤ uR a + uC b) :
    GLE p (∑ a, uR a + ∑ b, uC b)
      (seqFullN (fB v) (eB v) cn xs ys (X : ℚ[X])).det := by
  have h := det_gle (p := p) (seqFullN (fB v) (eB v) cn xs ys (X : ℚ[X]))
    (fun a b => WtB p (Sum.elim cn xs a) (Sum.elim cn ys b))
    (entry_gleB v hp5 hN cn xs ys hc hx hy)
  refine h.mono ?_
  refine tropVal_le_of_dual (fun a b => WtB p (Sum.elim cn xs a) (Sum.elim cn ys b))
    (fun a => (uR a : ℚ)) (fun b => (uC b : ℚ)) ?_ ?_
  · intro a b; exact_mod_cast hW a b
  · push_cast; exact le_rfl

end AssignmentB


/-! ### The rows B1, B2, B4 -/

section RowsB

variable {p : ℕ} [hp : Fact p.Prime] (v : ℤ) {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The member determinant of the one-term datum on the window geometry. -/
noncomputable abbrev rowDetB (cn : ι → ℕ) (r m : ℕ) : ℚ[X] :=
  (seqFullN (fB v) (eB v) cn (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det

theorem win_sum (g : ℕ → ℕ) (r m : ℕ) :
    ∑ i : Fin m, g (r + 2 * (i : ℕ)) + ∑ i : Fin m, g (r + 2 * (i : ℕ) + 1) =
      ∑ t ∈ range (2 * m), g (r + t) := by
  have step : ∀ k : ℕ, ∑ i ∈ range k, g (r + 2 * i) + ∑ i ∈ range k, g (r + 2 * i + 1) =
      ∑ t ∈ range (2 * k), g (r + t) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
      have := ih
      simp only [Nat.add_assoc] at this ⊢
      omega
  rw [Fin.sum_univ_eq_sum_range (fun i => g (r + 2 * i)), Fin.sum_univ_eq_sum_range
    (fun i => g (r + 2 * i + 1)), step]

theorem Wt_le_uB (p N : ℕ) {a b : ℕ} (ha : a < N) (hb : b < N) :
    WtB p a b ≤ uRow p N a + uCol p N b := by
  by_cases hab : a = b
  · subst hab
    have := uRow_add_uCol p N a
    have : WdB p a ≤ 3 := by unfold WdB; split_ifs <;> omega
    unfold WtB; rw [if_pos rfl]; omega
  by_cases hm : a % p = b % p
  · have := uRow_cong ha hb hm
    have := uRow_add_uCol p N b
    unfold WtB; rw [if_neg hab, if_pos hm]; omega
  · have h1 : 1 ≤ uRow p N a := by unfold uRow; split_ifs <;> omega
    have h2 : 1 ≤ uCol p N b := by unfold uCol; split_ifs <;> omega
    have : w3B p a b ≤ 2 := by unfold w3B; split_ifs <;> omega
    unfold WtB; rw [if_neg hab, if_neg hm]; omega

/-- **Row B1**: `v_p(den) ≤ 3 (r + m) - ‖m‖_p`. -/
theorem row_B1 (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ} (hcr : ∀ a, cn a < r)
    (hN : 2 * (r + 2 * m) < p * p) (hp5 : 5 ≤ p) :
    GLE p (3 * (r + m) - min (m % p) (p - m % p)) (rowDetB v cn r m) := by
  have hodd := odd_of_five (p := p) hp5
  have hc : ∀ a, cn a < r + 2 * m := fun a => by have := hcr a; omega
  have hx : ∀ i : Fin m, r + 2 * (i : ℕ) < r + 2 * m := fun i => by have := i.2; omega
  have hy : ∀ i : Fin m, r + 2 * (i : ℕ) + 1 < r + 2 * m := fun i => by have := i.2; omega
  have h := det_gle_of_dualB v hp5 hN cn (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) hc hx hy
    (fun a => uRow p (r + 2 * m) (Sum.elim cn (fun i : Fin m => r + 2 * (i : ℕ)) a))
    (fun b => uCol p (r + 2 * m) (Sum.elim cn (fun i : Fin m => r + 2 * (i : ℕ) + 1) b))
    (fun a b => Wt_le_uB p _ (by rcases a with a | i; exacts [hc a, hx i])
      (by rcases b with b | i; exacts [hc b, hy i]))
  refine h.mono ?_
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hcard : Fintype.card ι ≤ r := by
    have := Fintype.card_le_of_injective (fun a : ι => (⟨cn a, hcr a⟩ : Fin r))
      (fun a b hab => hinj (by simpa using hab))
    simpa using this
  have hcom : ∑ a : ι, uRow p (r + 2 * m) (cn a) + ∑ a : ι, uCol p (r + 2 * m) (cn a) = 3 * Fintype.card ι := by
    rw [← Finset.sum_add_distrib]
    simp [uRow_add_uCol, mul_comm]
  have hwin : ∑ i : Fin m, uRow p (r + 2 * m) (r + 2 * (i : ℕ)) +
      ∑ i : Fin m, uCol p (r + 2 * m) (r + 2 * (i : ℕ) + 1) = 2 * m + Aphi p (2 * m) := by
    rw [← Finset.sum_add_distrib]
    have : ∀ i : Fin m, uRow p (r + 2 * m) (r + 2 * (i : ℕ)) + uCol p (r + 2 * m) (r + 2 * (i : ℕ) + 1) =
        ((1 + ((2 * (m - 1 - (i : ℕ)) + 1) / p) % 2) + (1 + ((2 * (m - 1 - (i : ℕ))) / p) % 2)) := by
      intro i
      rw [uRow_window p _ r m i hodd rfl i.2, uCol_window p _ r m i hodd rfl i.2]
    rw [Finset.sum_congr rfl (fun i _ => this i),
      Fin.sum_univ_eq_sum_range (fun i => ((1 + ((2 * (m - 1 - i) + 1) / p) % 2) +
        (1 + ((2 * (m - 1 - i)) / p) % 2))) m,
      Finset.sum_range_reflect (fun k => ((1 + ((2 * k + 1) / p) % 2) + (1 + ((2 * k) / p) % 2))) m,
      window_sum]
  have hmin := Aphi_min p m hodd
  omega

/-- The potential `3·1[t ≥ p]`. -/
def phiB (p t : ℕ) : ℕ := if 1 ≤ t / p then 3 else 0

theorem WtB_le_phiB (hp0 : 0 < p) (a b : ℕ) : WtB p a b ≤ phiB p a + phiB p b := by
  by_cases h1 : 1 ≤ a / p
  · have := WtB_le_three p a b; unfold phiB; rw [if_pos h1]; omega
  by_cases h2 : 1 ≤ b / p
  · have := WtB_le_three p a b; unfold phiB; rw [if_pos h2]; omega
  have ha : a / p = 0 := Nat.lt_one_iff.mp (not_le.mp h1)
  have hb : b / p = 0 := Nat.lt_one_iff.mp (not_le.mp h2)
  have ha' : a < p := (Nat.div_eq_zero_iff.1 ha).resolve_left hp0.ne'
  have hb' : b < p := (Nat.div_eq_zero_iff.1 hb).resolve_left hp0.ne'
  have hma : a % p = a := Nat.mod_eq_of_lt ha'
  have hmb : b % p = b := Nat.mod_eq_of_lt hb'
  unfold WtB WdB w3B
  by_cases hab : a = b
  · subst hab; simp [ha]
  · simp [hab, hma, hmb, ha, hb]




theorem TB_eq (hp0 : 0 < p) : ∀ n : ℕ, ∑ t ∈ range n, phiB p t = 3 * (n - p) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold phiB
    by_cases h : p ≤ n
    · rw [if_pos ((Nat.one_le_div_iff hp0).2 h)]; omega
    · rw [if_neg (fun h' => h ((Nat.one_le_div_iff hp0).1 h'))]; omega

theorem det_gle_phiB (hp5 : 5 ≤ p) (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ}
    (hcr : ∀ a, cn a < r) (hN : 2 * (r + 2 * m) < p * p) :
    GLE p (3 * (r - p) + 3 * (r + 2 * m - p)) (rowDetB v cn r m) := by
  have hp0 : 0 < p := hp.out.pos
  have hc : ∀ a, cn a < r + 2 * m := fun a => by have := hcr a; omega
  have hx : ∀ i : Fin m, r + 2 * (i : ℕ) < r + 2 * m := fun i => by have := i.2; omega
  have hy : ∀ i : Fin m, r + 2 * (i : ℕ) + 1 < r + 2 * m := fun i => by have := i.2; omega
  have h := det_gle_of_dualB v hp5 hN cn (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) hc hx hy
    (fun a => phiB p (Sum.elim cn (fun i : Fin m => r + 2 * (i : ℕ)) a))
    (fun b => phiB p (Sum.elim cn (fun i : Fin m => r + 2 * (i : ℕ) + 1) b))
    (fun a b => WtB_le_phiB hp0 _ _)
  refine h.mono ?_
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hcom : ∑ a : ι, phiB p (cn a) ≤ 3 * (r - p) := by
    rw [← Finset.sum_image (f := fun t => phiB p t) (g := cn) (s := Finset.univ) (fun a _ b _ h => hinj h),
      ← TB_eq hp0 r]
    apply Finset.sum_le_sum_of_subset
    intro t ht
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 ht
    exact Finset.mem_range.2 (hcr a)
  have hwin := win_sum (phiB p) r m
  have e : ∑ t ∈ range (2 * m), phiB p (r + t) = 3 * (r + 2 * m - p) - 3 * (r - p) := by
    have := Finset.sum_range_add (phiB p) r (2 * m)
    rw [TB_eq hp0, TB_eq hp0] at this
    omega
  omega

theorem row_B2 (hp5 : 5 ≤ p) (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ}
    (hcr : ∀ a, cn a < r) (hN : 2 * (r + 2 * m) < p * p) (hpr : p ≤ r) :
    GLE p (6 * (r + m - p)) (rowDetB v cn r m) :=
  (det_gle_phiB v hp5 cn hinj hcr hN).mono (by omega)

theorem row_B4 (hp5 : 5 ≤ p) (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ}
    (hcr : ∀ a, cn a < r) (hN : 2 * (r + 2 * m) < p * p) (hpr : r ≤ p) :
    GLE p (3 * (r + 2 * m - p)) (rowDetB v cn r m) :=
  (det_gle_phiB v hp5 cn hinj hcr hN).mono (by omega)

end RowsB

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.weight_tableB
#print axioms CatalanCore.Uniform.Content.Sweep.row_B1
#print axioms CatalanCore.Uniform.Content.Sweep.row_B2
#print axioms CatalanCore.Uniform.Content.Sweep.row_B4
