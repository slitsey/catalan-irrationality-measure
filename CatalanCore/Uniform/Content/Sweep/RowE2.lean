module

public import CatalanCore.Uniform.Content.Sweep.RowE1

@[expose] public section

/-!
# Row `E₂` (lane H, wave H2b; ledger P207)

`PLANE2-SIMPLIFICATION` Theorem 7: for `p ≤ r` and `N = r + 2 m ≤ 2 p` (`κ = 2`, `k' = 0`, `ξ = p X`) and
potentials `uX`, `uY` on the window rows `r + 2 i` and columns `r + 2 j + 1` with `W₃ ≤ uX i + uY j`, every
coefficient of the determinant of every member (any retained set `c` of common nodes below `r`) has `p`-adic
denominator at most `4 r − 2 p + 2 m + ∑ uX + ∑ uY`.

At `ξ = p X` the hypothesis `UnitProp p ξ` of the built sweep chain fails (`p X` is not a unit), and only its
consequence is used there: the determinants of the class matrices are units (`UnitDet`).  The chain
`Yr_class … colLab` is stated under `UnitDet` (`Sweep.Classes`), which `UnitProp` implies; `sw_dvdE` is Proposition W for `k' = 0` with (i) the class-free weight (for `k' = 0` the
class solutions do not depend on the class) and (ii) the diagonal weight `2` of the pivot labels in the
period `1` (`B̄⁻¹[1,1] = 0`, since `M⁰[0,0] = 0`: there is no pole at `k = 0`).
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep.Gen
open CatalanCore CatalanCore.Rect

namespace CatalanCore.Uniform.Content.Sweep

namespace E2

section K0

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {R : Type*} [CommRing R] [Algebra (LocRing p) R]

theorem rowPer_k0 (κ o o' : ℕ) : rowPer κ 0 o = rowPer κ 0 o' := by
  funext a
  rcases a with a | i
  · simp [rowPer]
  · exact i.elim0

theorem colPer_k0 (κ o o' : ℕ) : colPer κ 0 o = colPer κ 0 o' := by
  funext a
  rcases a with a | i
  · simp [colPer]
  · exact i.elim0

theorem rowPer_eq_colPer_k0 (κ o : ℕ) : rowPer κ 0 o = colPer κ 0 o := by
  funext a
  rcases a with a | i
  · simp [rowPer, colPer]
  · exact i.elim0

theorem Cper_k0 (κ o o' : ℕ) : Cper κ 0 o = Cper κ 0 o' := by
  ext j
  rw [mem_Cper, mem_Cper]
  omega

theorem rowNode_eq_colNode_k0 (κ π : ℕ) (x : PivIdx p κ 0) : rowNode p κ 0 π x = colNode p κ 0 π x := by
  unfold rowNode colNode
  rw [rowPer_eq_colPer_k0 κ (oc p κ π x.1)]

theorem BclR_k0 (κ : ℕ) (ξ : R) (h o o' : ℕ) :
    BclR (p := p) v u κ 0 ξ h o = BclR (p := p) v u κ 0 ξ h o' := by
  unfold BclR
  rw [rowPer_k0 κ o o', colPer_k0 κ o o']

theorem Yr_k0 (κ : ℕ) (ξ : R) (b h o o' j : ℕ) :
    Yr (p := p) v u κ 0 ξ b h o j = Yr (p := p) v u κ 0 ξ b h o' j := by
  unfold Yr Wvec
  rw [BclR_k0 v u κ ξ h o o', rowPer_k0 κ o o', colPer_k0 κ o o']

/-- For `k' = 0` the pattern of a label does not depend on the class. -/
theorem patF_o_indep (κ : ℕ) (ξ : R) (isOut : Bool) (b h o o' l : ℕ) :
    patF (p := p) v u κ 0 ξ isOut b h o l = patF (p := p) v u κ 0 ξ isOut b h o' l := by
  unfold patF
  cases isOut
  · simp only [Bool.false_eq_true, if_false, YrF]
    exact Yr_k0 v u κ ξ b h o o' l
  · simp only [if_true, Gout]
    rw [Cper_k0 κ o o']
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold YrF
    rw [Yr_k0 v u κ ξ b h o o' j]

end K0

section WlabESec

/-- The weight of a pair of labels for `k' = 0`: `3` for congruent nodes, except `2` for the diagonal pair of
two pivot labels in the period `1`; otherwise `0` in one cell and `1` in one period (other half) when the
kinds agree, else `2`.  (No class condition: for `k' = 0` the class solutions do not depend on the class.) -/
def WlabE (p : ℕ) (u : ℤ) (kR kC : Bool) (n m : ℕ) : ℕ :=
  if n % p = m % p then (if n = m ∧ kR = false ∧ kC = false ∧ n / p = 1 then 2 else 3)
  else if kR = kC ∧ n / p = m / p then (if half p u n = half p u m then 0 else 1) else 2

theorem WlabE_le (p : ℕ) (u : ℤ) (kR kC : Bool) (n m : ℕ) : WlabE p u kR kC n m ≤ 3 := by
  unfold WlabE; split_ifs <;> omega

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [Algebra (LocRing p) R] {κ k' π : ℕ} (u : ℤ)
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The weight of the pair of labels `(r, c)`. -/
noncomputable def wRE (zn : I → ℕ) (yn : J → ℕ) (r : I ⊕ PivIdx p κ k') (c : J ⊕ PivIdx p κ k') : ℕ :=
  WlabE p u r.isLeft c.isLeft (nR (p := p) (κ := κ) (k' := k') (π := π) zn r)
    (nC (p := p) (κ := κ) (k' := k') (π := π) yn c)

end WlabESec

section SwE

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] {κ k' π : ℕ} {ξ : R}
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (zn : I → ℕ) (yn : J → ℕ)

/-- **Proposition W for `k' = 0`** (class-free weight, diagonal weight `2` of the pivot labels in the period
`1` under `hdiag`). -/
theorem sw_dvdE (hU : UnitDet p v u κ k' ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (hπ : π ≤ 1) (hk0 : k' = 0)
    (hdiag : ∀ y : PivIdx p κ k', colNode p κ k' π y / p = 1 →
      (p : R) ∣ Zp (p := p) v u κ k' π ξ y y)
    (hzc : ∀ z, (zn z / p + 1) * p ≤ N) (hyc : ∀ w, (yn w / p + 1) * p ≤ N)
    (r : I ⊕ PivIdx p κ k') (c : J ⊕ PivIdx p κ k') :
    (p : R) ^ (3 - wRE u (p := p) (κ := κ) (k' := k') (π := π) zn yn r c) ∣
      Schur.Sw (Hq (p := p) v u κ k' π ξ zn yn) (Zp (p := p) v u κ k' π ξ) r c := by
  have hp0 : 0 < p := hp.out.pos
  have hzn : ∀ z, zn z < N := fun z => lt_of_complete hp0 (hzc z)
  have hyn : ∀ w, yn w < N := fun w => lt_of_complete hp0 (hyc w)
  subst hk0
  unfold wRE
  by_cases hcg : nR (p := p) (κ := κ) (k' := 0) (π := π) zn r % p =
      nC (p := p) (κ := κ) (k' := 0) (π := π) yn c % p
  · by_cases hdg : nR (p := p) (κ := κ) (k' := 0) (π := π) zn r = nC (p := p) (κ := κ) (k' := 0) (π := π) yn c ∧
        r.isLeft = false ∧ c.isLeft = false ∧ nR (p := p) (κ := κ) (k' := 0) (π := π) zn r / p = 1
    · have hW : WlabE p u r.isLeft c.isLeft (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r)
          (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c) = 2 := by
        unfold WlabE; rw [if_pos hcg, if_pos hdg]
      rw [hW]
      obtain ⟨hnn, hrl, hcl, hper⟩ := hdg
      rcases r with z | y
      · simp at hrl
      rcases c with w | x
      · simp at hcl
      have e1 : nR (p := p) (κ := κ) (k' := 0) (π := π) zn (Sum.inr y) = colNode p κ 0 π y := rfl
      have e2 : nC (p := p) (κ := κ) (k' := 0) (π := π) yn (Sum.inr x) = rowNode p κ 0 π x := rfl
      rw [e1, e2] at hnn
      rw [e1] at hper
      have hxy : y = x := by
        apply colNode_injective hp0 (π := π)
        rw [hnn, rowNode_eq_colNode_k0]
      subst hxy
      have hd := hdiag y hper
      have e3 : Schur.Sw (Hq (p := p) v u κ 0 π ξ zn yn) (Zp (p := p) v u κ 0 π ξ)
          (Sum.inr y) (Sum.inr y) = -(Zp (p := p) v u κ 0 π ξ y y) := by
        simp [Schur.Sw, Matrix.fromBlocks_apply₂₂]
      rw [e3]
      have e4 : (p : R) ^ (3 - 2) = (p : R) := by norm_num
      rw [e4]
      exact (dvd_neg).2 hd
    · have hW : WlabE p u r.isLeft c.isLeft (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r)
          (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c) = 3 := by
        unfold WlabE; rw [if_pos hcg, if_neg hdg]
      rw [hW, Nat.sub_self, pow_zero]; exact one_dvd _
  · obtain ⟨U, hUU⟩ := isUnit_natDiff (R := R) hcg
    have hmul := sw_mul v u zn yn hU hpv hodd hp5 hN hH hRad hπ hzn hyn r c
    rw [← hUU] at hmul
    have hSw : Schur.Sw (Hq (p := p) v u κ 0 π ξ zn yn) (Zp (p := p) v u κ 0 π ξ) r c =
        ((U⁻¹ : Rˣ) : R) * ((p : R) * (labR (p := p) v u κ 0 π ξ zn 1 r *
          labC (p := p) v u κ 0 π ξ yn 0 c - labR (p := p) v u κ 0 π ξ zn 0 r *
          labC (p := p) v u κ 0 π ξ yn 1 c)) := by
      rw [← hmul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hSw]
    refine Dvd.dvd.mul_left ?_ _
    by_cases hpat : r.isLeft = c.isLeft ∧
        nR (p := p) (κ := κ) (k' := 0) (π := π) zn r / p = nC (p := p) (κ := κ) (k' := 0) (π := π) yn c / p
    · obtain ⟨hk, hl⟩ := hpat
      obtain ⟨e, he⟩ := rowLab (π := π) v u zn hU hpv hodd hp5 hN hH hRad hzn r
      obtain ⟨e', he'⟩ := colLab (π := π) v u yn hU hpv hodd hp5 hN hH hRad hπ hyn c
      by_cases hh : half p u (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r) =
          half p u (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c)
      · have hW : WlabE p u r.isLeft c.isLeft (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r)
            (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c) = 0 := by
          unfold WlabE; rw [if_neg hcg, if_pos ⟨hk, hl⟩, if_pos hh]
        rw [hW]
        have hP : ∀ b, patR (p := p) v u κ 0 π ξ zn r b = patC (p := p) v u κ 0 π ξ yn c b := by
          intro b; unfold patR patC; rw [hk, ← hl, hh]
          exact patF_o_indep v u κ ξ c.isLeft b _ _ _ _
        have := omega_sq (p := p) (labR (p := p) v u κ 0 π ξ zn 0 r)
          (labR (p := p) v u κ 0 π ξ zn 1 r) (labC (p := p) v u κ 0 π ξ yn 0 c)
          (labC (p := p) v u κ 0 π ξ yn 1 c) e e' (patR (p := p) v u κ 0 π ξ zn r 0)
          (patR (p := p) v u κ 0 π ξ zn r 1) (he 0 (by norm_num)) (he 1 (by norm_num))
          (by rw [hP 0]; exact he' 0 (by norm_num)) (by rw [hP 1]; exact he' 1 (by norm_num))
        have e3 : (p : R) ^ (3 - 0) = (p : R) * (p : R) ^ 2 := by norm_num; ring
        rw [e3]; exact mul_dvd_mul_left _ this
      · have hW : WlabE p u r.isLeft c.isLeft (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r)
            (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c) = 1 := by
          unfold WlabE; rw [if_neg hcg, if_pos ⟨hk, hl⟩, if_neg hh]
        rw [hW]
        have hcompl := nR_compl (p := p) (κ := κ) (k' := 0) (π := π) (N := N) zn hzc hH r
        have hlc : r.isLeft = false → nR (p := p) (κ := κ) (k' := 0) (π := π) zn r / p ∈
            Cper κ 0 (oc p κ π (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r % p)) := by
          intro hl'
          rcases r with z | y
          · simp at hl'
          · exact pivR_mem y
        have hQ : ∀ b, b ≤ 1 → (p : R) ∣ patR (p := p) v u κ 0 π ξ zn r b -
            patC (p := p) v u κ 0 π ξ yn c b := by
          intro b _
          have hf := patF_halves v u hodd hN hU hpv hH r.isLeft
            (o := oc p κ π (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r % p))
            (l := nR (p := p) (κ := κ) (k' := 0) (π := π) zn r / p) b hcompl hlc (oc_le _)
          unfold patR patC
          rw [← hk, ← hl, patF_o_indep v u κ ξ r.isLeft b _
            (oc p κ (1 - π) (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c % p))
            (oc p κ π (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r % p))]
          rcases half_eq (p := p) (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r) with h0 | h1
          · rw [h0] at hh
            have h1' : half p u (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c) = 1 := by
              rcases half_eq (p := p) (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c) with h | h
              · exact absurd h.symm hh
              · exact h
            rw [h0, h1']
            have := dvd_neg.2 hf
            simpa using this
          · rw [h1]
            have h0' : half p u (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c) = 0 := by
              rcases half_eq (p := p) (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c) with h | h
              · exact h
              · exact absurd (by rw [h1, h]) hh
            rw [h0']
            exact hf
        have := omega_one (p := p) (labR (p := p) v u κ 0 π ξ zn 0 r)
          (labR (p := p) v u κ 0 π ξ zn 1 r) (labC (p := p) v u κ 0 π ξ yn 0 c)
          (labC (p := p) v u κ 0 π ξ yn 1 c) e e' (patR (p := p) v u κ 0 π ξ zn r 0)
          (patR (p := p) v u κ 0 π ξ zn r 1) (patC (p := p) v u κ 0 π ξ yn c 0)
          (patC (p := p) v u κ 0 π ξ yn c 1) (he 0 (by norm_num)) (he 1 (by norm_num))
          (he' 0 (by norm_num)) (he' 1 (by norm_num)) (hQ 0 (by norm_num)) (hQ 1 (by norm_num))
        have e3 : (p : R) ^ (3 - 1) = (p : R) * (p : R) := by norm_num [pow_two]
        rw [e3]; exact mul_dvd_mul_left _ this
    · have hW : WlabE p u r.isLeft c.isLeft (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r)
          (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c) = 2 := by
        unfold WlabE; rw [if_neg hcg, if_neg hpat]
      rw [hW]
      simp

end SwE

section DiagE

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R]

theorem toR_intCast (z : ℤ) : toR p ((z : ℤ) : ℚ) = (z : R) := by
  have hm : ((z : ℤ) : ℚ) ∈ LocRing p := int_mem_locRing (ℓ := p) z
  rw [toR_of_mem hm]
  have : (⟨((z : ℤ) : ℚ), hm⟩ : LocRing p) = (z : LocRing p) := by apply Subtype.ext; simp
  rw [this, map_intCast]

theorem isUnit_intR (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : IsUnit (z : R) := by
  have hz0 : (z : ℚ) ≠ 0 := by
    intro h0
    apply hz
    have : z = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  have h1 : (z : LocRing p) * invZ p z = 1 := by
    apply Subtype.ext
    simp only [Subring.coe_mul, coe_invZ, if_neg hz]
    push_cast
    field_simp
  have hu : IsUnit (z : LocRing p) := IsUnit.of_mul_eq_one _ h1
  have := hu.map (algebraMap (LocRing p) R)
  simpa using this

theorem isUnit_add_p {a : R} (ha : IsUnit a) (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (x : R) :
    IsUnit (a + (p : R) * x) := by
  obtain ⟨w, hw⟩ := ha
  have e : a + (p : R) * x = a * (1 + (p : R) * (((w⁻¹ : Rˣ) : R) * x)) := by
    have h1 : a * ((w⁻¹ : Rˣ) : R) = 1 := by rw [← hw]; exact w.mul_inv
    linear_combination (-(p : R) * x) * h1
  rw [e]
  exact (hw ▸ w.isUnit).mul (hRad _)

/-- No pole at `k = 0`: `p³ G(0, h)` is divisible by `p`. -/
theorem ggR_zero_dvd (hodd : p % 2 = 1) (hN : 2 * N < p * p) (hNp : p < N) {h : ℕ} (hh : h ≤ 1) :
    (p : R) ∣ ggR (p := p) v u (0, h) := by
  have hp0 : 0 < p := hp.out.pos
  have hp2 := hp.out.two_le
  have ht : cstart p (0, h) < p := by
    unfold cstart
    interval_cases h <;> simp <;> omega
  have hV := PE_diff_same_period v u hN (Nat.zero_le (cstart p (0, h))) (by omega)
    (show 0 / p = cstart p (0, h) / p by rw [Nat.div_eq_of_lt ht]; simp)
  have h0 : PE v u p 0 = 0 := by simp [PE]
  rw [h0, sub_zero] at hV
  have hV' : Vp p 2 (Gcell v u p (0, h)) := by unfold Gcell; exact Vp.neg hV
  have h4 : Dv p 1 ((p : ℚ) ^ 3 * Gcell v u p (0, h)) := by
    have := Dv.of_Vp (k := 1) hV'
    simpa using this
  unfold ggR
  have := toR_dvd (R := R) h4
  simpa using this

theorem Bm_one_zero (hodd : p % 2 = 1) (hN : 2 * N < p * p) (hNp : 2 * p ≤ N) {h : ℕ} (hh : h ≤ 1) (ξ : R) :
    ∃ y : R, Bm (p := p) v u ξ h 1 0 = -(v : R) + (p : R) * y ∧
      Bm (p := p) v u ξ h 0 1 = -(v : R) + (p : R) * y := by
  have hp2 := hp.out.two_le
  have hA := sig_mem_cell v u hodd hN (j := 1) hh (by omega)
  have hB := sig_mem_cell v u hodd hN (j := 0) hh (by omega)
  obtain ⟨T, hT⟩ : ∃ T : ℚ, T = (p : ℚ) ^ 2 * Scell v u p (1, h) - (p : ℚ) ^ 2 * Scell v u p (0, h) := ⟨_, rfl⟩
  have hTm : T ∈ LocRing p := by rw [hT]; exact (LocRing p).sub_mem hA hB
  have hvm : (v : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) v
  have hd := sig_step v u hodd hN (j := 0) hh (by omega) (by omega)
  have e : (p : ℚ) ^ 2 * (Scell v u p (0 + 1, h) - Scell v u p (0, h)) + (v : ℚ) / (((0 : ℕ) : ℚ) + 1) ^ 2 =
      T + (v : ℚ) := by
    rw [hT]; simp only [Nat.cast_zero, zero_add]; ring
  rw [e] at hd
  have hdv := toR_dvd (R := R) hd
  rw [toR_add hTm hvm, toR_intCast, pow_one] at hdv
  obtain ⟨y, hy⟩ := hdv
  have hTy : toR p T = -(v : R) + (p : R) * y := by linear_combination hy
  refine ⟨y, ?_, ?_⟩
  · unfold Bm
    rw [if_neg (by norm_num)]
    have e1 : (p : ℚ) ^ 2 * (Scell v u p (1, h) - Scell v u p (0, h)) / (((1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ)) = T := by
      rw [hT]; simp only [Nat.cast_one, Nat.cast_zero]; ring
    rw [e1, hTy]
  · unfold Bm
    rw [if_neg (by norm_num)]
    have e1 : (p : ℚ) ^ 2 * (Scell v u p (0, h) - Scell v u p (1, h)) / (((0 : ℕ) : ℚ) - ((1 : ℕ) : ℚ)) = T := by
      rw [hT]; simp only [Nat.cast_one, Nat.cast_zero]; ring
    rw [e1, hTy]

theorem Binv11_dvd (hRad : ∀ x : R, IsUnit (1 + (p : R) * x))
    {B : Matrix (Fin 2 ⊕ Fin 0) (Fin 2 ⊕ Fin 0) R}
    (hdet : IsUnit B.det) (h00 : (p : R) ∣ B (Sum.inl 0) (Sum.inl 0)) :
    (p : R) ∣ B⁻¹ (Sum.inl 1) (Sum.inl 1) := by
  have hCB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have e1 := congrFun (congrFun hCB (Sum.inl 0)) (Sum.inl 0)
  have e2 := congrFun (congrFun hCB (Sum.inl 1)) (Sum.inl 0)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, Matrix.one_apply] at e1 e2
  obtain ⟨b0, hb0⟩ := h00
  rw [hb0] at e1 e2
  simp only [Sum.inl.injEq, if_true, Fin.zero_eta, Fin.isValue, one_ne_zero, if_false] at e1 e2
  have hu1 : IsUnit (B⁻¹ (Sum.inl 0) (Sum.inl 1) * B (Sum.inl 1) (Sum.inl 0)) := by
    have : B⁻¹ (Sum.inl 0) (Sum.inl 1) * B (Sum.inl 1) (Sum.inl 0) =
        1 + (p : R) * (-(B⁻¹ (Sum.inl 0) (Sum.inl 0) * b0)) := by linear_combination e1
    rw [this]; exact hRad _
  have hB10 : IsUnit (B (Sum.inl 1) (Sum.inl 0)) := isUnit_of_mul_isUnit_right hu1
  obtain ⟨w, hw⟩ := hB10
  have h1 : B (Sum.inl 1) (Sum.inl 0) * ((w⁻¹ : Rˣ) : R) = 1 := by rw [← hw]; exact w.mul_inv
  refine ⟨-(B⁻¹ (Sum.inl 1) (Sum.inl 0) * b0 * ((w⁻¹ : Rˣ) : R)), ?_⟩
  linear_combination ((w⁻¹ : Rˣ) : R) * e2 - B⁻¹ (Sum.inl 1) (Sum.inl 1) * h1

end DiagE

section DiagE2

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] {κ k' π : ℕ} {ξ : R}

theorem Wp_sub_Zp_dvd (hU : UnitDet p v u κ k' ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (x z : PivIdx p κ k') :
    (p : R) ∣ Wp (p := p) v u κ k' π ξ x z - Zp (p := p) v u κ k' π ξ x z := by
  have hZQ := Zp_mul_Qp (π := π) v u hU hpv hodd hp5 hN hH hRad
  have e : Wp (p := p) v u κ k' π ξ - Zp (p := p) v u κ k' π ξ =
      Zp (p := p) v u κ k' π ξ *
        (Qp (p := p) v u κ k' π ξ * Wp (p := p) v u κ k' π ξ - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hZQ, Matrix.one_mul]
  have e2 : Wp (p := p) v u κ k' π ξ x z - Zp (p := p) v u κ k' π ξ x z =
      (Zp (p := p) v u κ k' π ξ *
        (Qp (p := p) v u κ k' π ξ * Wp (p := p) v u κ k' π ξ - 1)) x z := by
    rw [← e, Matrix.sub_apply]
  rw [e2, Matrix.mul_apply]
  refine Finset.dvd_sum fun y _ => ?_
  refine Dvd.dvd.mul_left ?_ _
  have := Qp_mul_Wp (π := π) v u hU hpv hodd hp5 hN hH y z
  simpa [Matrix.sub_apply] using this

theorem unitDet_two (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hN : 2 * N < p * p) (hNp : 2 * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (hξ : (p : R) ∣ ξ) : UnitDet p v u 2 0 ξ := by
  intro h o hh ho
  obtain ⟨y, hy10, hy01⟩ := Bm_one_zero v u hodd hN hNp hh ξ
  have hdet : (BclR (p := p) v u 2 0 ξ h o).det =
      BclR (p := p) v u 2 0 ξ h o (Sum.inl 0) (Sum.inl 0) * BclR (p := p) v u 2 0 ξ h o (Sum.inl 1) (Sum.inl 1) -
        BclR (p := p) v u 2 0 ξ h o (Sum.inl 0) (Sum.inl 1) * BclR (p := p) v u 2 0 ξ h o (Sum.inl 1) (Sum.inl 0) := by
    have := Matrix.det_submatrix_equiv_self (Equiv.sumEmpty (Fin 2) (Fin 0)).symm (BclR (p := p) v u 2 0 ξ h o)
    rw [← this, Matrix.det_fin_two]
    simp [Equiv.sumEmpty]
  have e00 : BclR (p := p) v u 2 0 ξ h o (Sum.inl 0) (Sum.inl 0) = ξ + ggR (p := p) v u (0, h) := by
    simp [BclR, rowPer, colPer, Bm]
  have e01 : BclR (p := p) v u 2 0 ξ h o (Sum.inl 0) (Sum.inl 1) = Bm (p := p) v u ξ h 0 1 := by
    simp [BclR, rowPer, colPer]
  have e10 : BclR (p := p) v u 2 0 ξ h o (Sum.inl 1) (Sum.inl 0) = Bm (p := p) v u ξ h 1 0 := by
    simp [BclR, rowPer, colPer]
  obtain ⟨c0, hc0⟩ := dvd_add hξ (ggR_zero_dvd (R := R) v u hodd hN (by omega) hh)
  have hbu : IsUnit (-(v : R) + (p : R) * y) := isUnit_add_p (isUnit_intR v hpv).neg hRad y
  rw [hdet, e00, e01, e10, hy10, hy01, hc0]
  have e : (p : R) * c0 * BclR (p := p) v u 2 0 ξ h o (Sum.inl 1) (Sum.inl 1) -
      (-(v : R) + (p : R) * y) * (-(v : R) + (p : R) * y) =
      -((-(v : R) + (p : R) * y) * (-(v : R) + (p : R) * y)) +
        (p : R) * (c0 * BclR (p := p) v u 2 0 ξ h o (Sum.inl 1) (Sum.inl 1)) := by ring
  rw [e]
  exact isUnit_add_p (hbu.mul hbu).neg hRad _

/-- `Zp(y,y) ∈ p R` for the pivot labels of the period `1` (`κ = 2`, `k' = 0`, `ξ ∈ p R`). -/
theorem hdiag_two (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p)
    (hNp : 2 * p ≤ N) (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (hξ : (p : R) ∣ ξ) :
    ∀ y : PivIdx p 2 0, colNode p 2 0 π y / p = 1 →
      (p : R) ∣ Zp (p := p) v u 2 0 π ξ y y := by
  intro y hy
  have hp0 := hp.out.pos
  have hU := unitDet_two (ξ := ξ) v u hpv hodd hN hNp hRad hξ
  obtain ⟨ω, a⟩ := y
  rcases a with a | i
  swap
  · exact i.elim0
  have ha : a = 1 := by
    rw [colNode_div hp0] at hy
    simp only [colPer, Sum.elim_inl] at hy
    exact Fin.ext hy
  subst ha
  have hd1 := Wp_sub_Zp_dvd (π := π) v u hU hpv hodd hp5 hN (by omega) hRad (ω, Sum.inl 1) (ω, Sum.inl 1)
  have hW : Wp (p := p) v u 2 0 π ξ (ω, Sum.inl 1) (ω, Sum.inl 1) =
      (BclR (p := p) v u 2 0 ξ (half p u ω) (oc p 2 π ω))⁻¹ (Sum.inl 1) (Sum.inl 1) := by
    simp [Wp]
  rw [hW] at hd1
  have h00 : (p : R) ∣ BclR (p := p) v u 2 0 ξ (half p u ω) (oc p 2 π ω) (Sum.inl 0) (Sum.inl 0) := by
    have e00 : BclR (p := p) v u 2 0 ξ (half p u ω) (oc p 2 π ω) (Sum.inl 0) (Sum.inl 0) =
        ξ + ggR (p := p) v u (0, half p u ω) := by
      simp [BclR, rowPer, colPer, Bm]
    rw [e00]
    exact dvd_add hξ (ggR_zero_dvd (R := R) v u hodd hN (by omega) (half_le_one' _))
  have hB := Binv11_dvd hRad (hU _ _ (half_le_one' _) (oc_le _)) h00
  have e : Zp (p := p) v u 2 0 π ξ (ω, Sum.inl 1) (ω, Sum.inl 1) =
      (BclR (p := p) v u 2 0 ξ (half p u ω) (oc p 2 π ω))⁻¹ (Sum.inl 1) (Sum.inl 1) -
        ((BclR (p := p) v u 2 0 ξ (half p u ω) (oc p 2 π ω))⁻¹ (Sum.inl 1) (Sum.inl 1) -
          Zp (p := p) v u 2 0 π ξ (ω, Sum.inl 1) (ω, Sum.inl 1)) := by ring
  rw [e]
  exact dvd_sub hB hd1

end DiagE2

section Scale2

variable (p : ℕ) [hp : Fact p.Prime]

/-- The variable `ξ = p X` of `ℤ_(p)[X]_(p)` (scale `p⁻²`). -/
noncomputable def xiP2 : RP p := algebraMap ((LocRing p)[X]) (RP p) (C ((p : ℕ) : LocRing p) * X)

theorem xiP2_dvd : ((p : ℕ) : RP p) ∣ xiP2 p := by
  refine ⟨xiP p, ?_⟩
  unfold xiP2 xiP
  rw [map_mul, ← natCast_RP]

end Scale2

section Member2

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {ι κw : Type} [Fintype ι] [DecidableEq ι] [Fintype κw] [DecidableEq κw]
  (c : ι → ℕ) (xs ys : κw → ℕ)

/-- The `p³`-scaled member matrix over `ℤ_(p)` for `x = X / p²`: diagonal `p X` on the common block. -/
noncomputable def BlM2 : Matrix (ι ⊕ κw) (ι ⊕ κw) (LocRing p)[X] :=
  Matrix.of fun a b => (if memRow c xs a = memCol c ys b then (C ((p : ℕ) : LocRing p) * X : (LocRing p)[X]) else 0) +
    C (toL p ((p : ℚ) ^ 3 * Lm v u (memRow c xs a) (memCol c ys b)))

theorem map_BlM2 {R : Type*} [CommRing R] [Algebra (LocRing p) R] (ξ : R)
    (f : (LocRing p)[X] →+* R) (hX : f (C ((p : ℕ) : LocRing p) * X) = ξ)
    (hC : ∀ x : LocRing p, f (C x) = algebraMap (LocRing p) R x)
    (hN : 2 * N < p * p) (hr : ∀ a, memRow c xs a < N) (hc : ∀ b, memCol c ys b < N) :
    f.mapMatrix (BlM2 (p := p) v u c xs ys) = QminR (p := p) v u c xs ys ξ := by
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, BlM2, QminR, Matrix.of_apply, Qent, map_add]
  congr 1
  · split_ifs
    · exact hX
    · simp
  · rw [hC, toR_eq_algebraMap_toL]

/-- **Descent of the Schur bound to a member, scale `p⁻²`.**  As `gle_member`, with the diagonal `ξ = p X`:
if the `Q`-minor of `p³ M + p X` on the nodes of a member is divisible by `p^K` in `ℤ_(p)[X]_(p)`, then every
coefficient of the determinant of the member has `p`-adic denominator at most `3 (|ι| + |κ|) − K`. -/
theorem gle_member2 (hN : 2 * N < p * p) (hr : ∀ a, memRow c xs a < N) (hcl : ∀ b, memCol c ys b < N)
    (hcinj : Function.Injective c) (h1 : ∀ i j, c i ≠ ys j) (h2 : ∀ i j, xs i ≠ c j)
    (h3 : ∀ i j, xs i ≠ ys j) {K : ℕ}
    (hdvd : ((p : ℕ) : RP p) ^ K ∣ (QminR (p := p) v u c xs ys (xiP2 p)).det) :
    GLE p (3 * (Fintype.card ι + Fintype.card κw) - K)
      (seqFullN (fS v u) (eS v u) c xs ys (X : ℚ[X])).det := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hmap := map_BlM2 (p := p) v u c xs ys (xiP2 p) (algebraMap ((LocRing p)[X]) (RP p)) rfl
    (fun x => by
      rw [IsScalarTower.algebraMap_apply (LocRing p) ((LocRing p)[X]) (RP p) x, Polynomial.algebraMap_eq])
    hN hr hcl
  have hd1 : ((p : ℕ) : RP p) ^ K ∣ algebraMap ((LocRing p)[X]) (RP p) (BlM2 (p := p) v u c xs ys).det := by
    have hm := RingHom.map_det (S := RP p) (algebraMap ((LocRing p)[X]) (RP p)) (BlM2 (p := p) v u c xs ys)
    rw [hm, hmap]; exact hdvd
  have hd2 := descent p hd1
  set Mt : Matrix (ι ⊕ κw) (ι ⊕ κw) ℚ[X] :=
    seqFullN (fS v u) (eS v u) c xs ys (C (((p : ℚ) ^ 2)⁻¹) * X) with hMt
  have hB : ∀ a b : ι ⊕ κw, toQ p (BlM2 (p := p) v u c xs ys a b) =
      C ((p : ℚ) ^ ((fun _ : ι ⊕ κw => 3) a + (fun _ : ι ⊕ κw => 0) b)) * Mt a b := by
    intro a b
    have hq := q_mem v u hN (hr a) (hcl b)
    rw [hMt, seqFullN_entry c xs ys _ _ _ hcinj h1 h2 h3]
    simp only [BlM2, Matrix.of_apply, map_add, toQ]
    rw [Polynomial.coe_mapRingHom]
    simp only [Polynomial.map_C, Subring.subtype_apply]
    rw [toL_val hq]
    have hc3 : (p : ℚ) ^ (3 + 0) * ((p : ℚ) ^ 2)⁻¹ = (p : ℚ) := by field_simp
    have hcp : ((((p : ℕ) : LocRing p) : ℚ)) = (p : ℚ) := by simp
    split_ifs
    · simp only [Polynomial.map_C, Polynomial.map_X, Polynomial.map_mul, Subring.subtype_apply]
      rw [hcp, mul_add, ← mul_assoc, ← C_mul, hc3, Polynomial.algebraMap_eq, ← C_mul]
    · rw [Polynomial.map_zero, zero_add, zero_add, Polynomial.algebraMap_eq, ← C_mul]
  have hG := gle_det_of_scaled_dvd p Mt (BlM2 (p := p) v u c xs ys) (fun _ => 3) (fun _ => 0) hB K hd2
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_zero, add_zero, Fintype.card_sum] at hG
  set MX : Matrix (ι ⊕ κw) (ι ⊕ κw) ℚ[X] :=
    seqFullN (fS v u) (eS v u) c xs ys (X : ℚ[X]) with hMX
  have hcomp : Mt = (Polynomial.compRingHom (C (((p : ℚ) ^ 2)⁻¹) * X : ℚ[X])).mapMatrix MX := by
    ext a b
    rw [hMt, hMX, seqFullN_entry c xs ys _ _ _ hcinj h1 h2 h3, RingHom.mapMatrix_apply, Matrix.map_apply,
      seqFullN_entry c xs ys _ _ _ hcinj h1 h2 h3]
    split_ifs <;> simp
  have hdet : Mt.det = MX.det.comp (C (((p : ℚ) ^ 2)⁻¹) * X) := by
    rw [hcomp, ← RingHom.map_det]; rfl
  intro i
  have hi := hG i
  rw [hdet, Polynomial.comp_C_mul_X_coeff] at hi
  have hpi : ((p : ℚ) ^ (2 * i)) ∈ LocRing p := by
    exact_mod_cast int_mem_locRing (ℓ := p) ((p : ℤ) ^ (2 * i))
  have := (LocRing p).mul_mem hi hpi
  convert this using 1
  have hp3 : ((p : ℚ) ^ 2) ^ i ≠ 0 := pow_ne_zero _ (pow_ne_zero 2 hp0)
  rw [inv_pow, pow_mul]
  field_simp
  rw [Nat.mul_comm (Fintype.card ι + Fintype.card κw) 3]
  ring

end Member2
section MinorE

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] {κ k' π : ℕ} {ξ : R}
  {L : Type} [Fintype L] [DecidableEq L] (rn cl : L → ℕ)

open Classical in
/-- **Theorem G (general minor)**.  Let `rn`, `cl` be the row and column nodes of a square minor of the
Löwner matrix (injective, complete periods).  Row-type labels are the outside rows `RowOut` and the deleted
pivot columns `DelC`; column-type labels the outside columns `ColOut` and the deleted pivot rows `DelR`.
If potentials `φR`, `φC` (functions of the node) cover the weights of all pairs of labels, then
`p^(3 |L| − E) ∣ det` as soon as `3 |L| + ∑ potentials ≤ E + 3 #(row-type labels)`. -/
theorem minor_dvdE (hU : UnitDet p v u κ k' ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (hπ : π ≤ 1) (hk0 : k' = 0)
    (hdiag : ∀ y : PivIdx p κ k', colNode p κ k' π y / p = 1 →
      (p : R) ∣ Zp (p := p) v u κ k' π ξ y y)
    (hrinj : Function.Injective rn) (hcinj : Function.Injective cl)
    (hrc : ∀ a, (rn a / p + 1) * p ≤ N) (hcc : ∀ b, (cl b / p + 1) * p ≤ N)
    (φR φC : ℕ → ℕ)
    (hW : ∀ (n m : ℕ) (kR kC : Bool), RowLab rn cl p κ k' π kR n → ColLab rn cl p κ k' π kC m →
      WlabE p u kR kC n m ≤ φR n + φC m)
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
    refine det_dvd_of_potentials (p : R) _ (fun a b => 3 - wRE u (p := p) (κ := κ) (k' := k') (π := π) zn yn (ρ' a) (κ'' b))
      ur uc ?_ ?_ _ ?_
    · intro a b
      exact sw_dvdE v u zn yn hU hpv hodd hp5 hN hH hRad hπ hk0 hdiag hzc hyc (ρ' a) (κ'' b)
    · intro a b
      have h3 : wRE u (p := p) (κ := κ) (k' := k') (π := π) zn yn (ρ' a) (κ'' b) ≤
          φR (nR (p := p) (κ := κ) (k' := k') (π := π) zn (ρ' a)) +
            φC (nC (p := p) (κ := κ) (k' := k') (π := π) yn (κ'' b)) :=
        hW _ _ _ _ (rowLab_of a) (colLab_of (eC' b))
      have h4 : wRE u (p := p) (κ := κ) (k' := k') (π := π) zn yn (ρ' a) (κ'' b) ≤ 3 := WlabE_le _ _ _ _ _ _
      show 3 ≤ (3 - wRE u (p := p) (κ := κ) (k' := k') (π := π) zn yn (ρ' a) (κ'' b)) +
        φR (nR (p := p) (κ := κ) (k' := k') (π := π) zn (ρ' a)) +
          φC (nC (p := p) (κ := κ) (k' := k') (π := π) yn (κ'' b))
      omega
    · rw [hsumR, hsumC, hcardLab]
      omega
  exact hdetSw.trans hJ.symm.dvd

end MinorE
section MemberGE

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {κ k' π : ℕ} {ι κw : Type} [Fintype ι] [DecidableEq ι] [Fintype κw] [DecidableEq κw]
  (c : ι → ℕ) (xs ys : κw → ℕ)

/-- **Theorem G for a member of the plane 2 family.**  Retained common nodes `c`, window rows `xs` and
columns `ys` (all complete periods below `N`, `p² > 2N`), pivot system `(κ, k', π)` with `(κ + 2k') p ≤ N`:
if potentials `φR`, `φC` cover the weights of all labels, every coefficient of the determinant has
`p`-adic denominator at most `E`, whenever `3 (|ι| + |κ|) + ∑ potentials ≤ E + 3 #(row-type labels)`. -/
theorem member_gleE (hU : UnitDet p v u κ k' (xiP2 p)) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p)
    (hH : (κ + 2 * k') * p ≤ N) (hπ : π ≤ 1) (hk0 : k' = 0)
    (hdiag : ∀ y : PivIdx p κ k', colNode p κ k' π y / p = 1 →
      ((p : ℕ) : RP p) ∣ Zp (p := p) (R := RP p) v u κ k' π (xiP2 p) y y)
    (hcinj : Function.Injective c) (hxinj : Function.Injective xs) (hyinj : Function.Injective ys)
    (h1 : ∀ i j, c i ≠ ys j) (h2 : ∀ i j, xs i ≠ c j) (h3 : ∀ i j, xs i ≠ ys j)
    (hrc : ∀ a, (memRow c xs a / p + 1) * p ≤ N) (hcc : ∀ b, (memCol c ys b / p + 1) * p ≤ N)
    (φR φC : ℕ → ℕ)
    (hW : ∀ (n m : ℕ) (kR kC : Bool), RowLab (memRow c xs) (memCol c ys) p κ k' π kR n →
      ColLab (memRow c xs) (memCol c ys) p κ k' π kC m →
      WlabE p u kR kC n m ≤ φR n + φC m)
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
  have hd := minor_dvdE (p := p) (R := RP p) (ξ := xiP2 p) (π := π) (κ := κ) (k' := k') v u
    (memRow c xs) (memCol c ys) hU hpv hodd hp5 hN hH (pRad_RP p) hπ hk0 hdiag
    (memRow_injective c xs hcinj hxinj h2) (memCol_injective c ys hcinj hyinj h1) hrc hcc φR φC hW E hcond
  have hg := gle_member2 (p := p) v u c xs ys hN hr hcl hcinj h1 h2 h3 hd
  refine GLE.mono ?_ hg
  rw [Fintype.card_sum] at *
  omega

end MemberGE
section MemberPE

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N' : ℕ}

/-- **Theorem G for the window family, in explicit node form.**  Window rows `r + 2 i`, columns
`r + 2 i + 1` (`i < m`), retained common nodes `c` below `r`, pivot system `(κ, k')` with
`(κ − 1) p ≤ r < κ p` and parity `π = (r + 1) % 2`.  The label nodes are the outside rows `ORs`, the
outside columns `OCs`, the deleted pivot columns `TRs` and the deleted pivot rows `TCs` at or above `r`
(the deleted common nodes below `r` carry the potential `3`).  If the potentials cover `Wlab` on the four
families of pairs and `hsum` holds, every coefficient of the determinant has denominator at most `E`. -/
theorem member_gle_PE (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N' < p * p)
    {r m κ k' : ℕ} (hU : UnitDet p v u κ k' (xiP2 p)) (hk0 : k' = 0)
    (hdiag : ∀ y : PivIdx p κ k', colNode p κ k' ((r + 1) % 2) y / p = 1 →
      ((p : ℕ) : RP p) ∣ Zp (p := p) (R := RP p) v u κ k' ((r + 1) % 2) (xiP2 p) y y)
    (hκr : r < κ * p) (hH : (κ + 2 * k') * p ≤ N')
    (hcompl : ∀ n, n < r + 2 * m → (n / p + 1) * p ≤ N')
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (hcinj : Function.Injective c)
    (hcr : ∀ i, c i < r) (φR φC : ℕ → ℕ) (hφ : ∀ t, t < r → φR t = 3 ∧ φC t = 3)
    (hpp : ∀ n ∈ TRs p κ k' r m, ∀ n' ∈ TCs p κ k' r m,
      WlabE p u false false n n' ≤ φR n + φC n')
    (hpo : ∀ n ∈ TRs p κ k' r m, ∀ n' ∈ OCs p κ k' r m,
      WlabE p u false true n n' ≤ φR n + φC n')
    (hop : ∀ n ∈ ORs p κ k' r m, ∀ n' ∈ TCs p κ k' r m,
      WlabE p u true false n n' ≤ φR n + φC n')
    (hoo : ∀ n ∈ ORs p κ k' r m, ∀ n' ∈ OCs p κ k' r m,
      WlabE p u true true n n' ≤ φR n + φC n')
    (E : ℕ)
    (hsum : 3 * r + 3 * m + (∑ t ∈ TRs p κ k' r m, φR t + ∑ t ∈ ORs p κ k' r m, φR t +
        ∑ t ∈ TCs p κ k' r m, φC t + ∑ t ∈ OCs p κ k' r m, φC t) ≤
      E + 3 * ((TRs p κ k' r m).card + (ORs p κ k' r m).card)) :
    GLE p E (seqFullN (fS v u) (eS v u) c
      (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hπ : (r + 1) % 2 ≤ 1 := by omega
  have hκH : κ * p ≤ (κ + 2 * k') * p := Nat.mul_le_mul_right p (by omega)
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
  refine member_gleE (p := p) (π := (r + 1) % 2) (κ := κ) (k' := k') v u c
    (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) hU hpv hodd hp5 hN hH hπ hk0 hdiag hcinj hxinj
    hyinj h1 h2 h3 (fun a => hcompl _ (hrow a)) (fun a => hcompl _ (hcol a)) φR φC ?_ E ?_
  · -- the weights
    intro n n' kR kC hR hC
    have hRc : (kR = true ∧ n ∈ ORs p κ k' r m) ∨ (kR = false ∧ (n < r ∨ n ∈ TRs p κ k' r m)) := by
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
    have hCc : (kC = true ∧ n' ∈ OCs p κ k' r m) ∨ (kC = false ∧ (n' < r ∨ n' ∈ TCs p κ k' r m)) := by
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
    have hle := WlabE_le p u kR kC n n'
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
    have eR := sum_RowOut (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr φR
    have eR1 := sum_RowOut (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr (fun _ => 1)
    have eC := sum_ColOut (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr φC
    have dC := sum_DelC (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr φR
    have dC1 := sum_DelC (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr (fun _ => 1)
    have dR := sum_DelR (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr φC
    have hF3 : ∑ t ∈ (Finset.range r).filter (fun t => ∀ i, t ≠ c i), φR t =
        3 * ((Finset.range r).filter (fun t => ∀ i, t ≠ c i)).card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have := (hφ t (Finset.mem_range.1 (Finset.mem_filter.1 ht).1)).1
      omega
    have hF3' : ∑ t ∈ (Finset.range r).filter (fun t => ∀ i, t ≠ c i), φC t =
        3 * ((Finset.range r).filter (fun t => ∀ i, t ≠ c i)).card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have := (hφ t (Finset.mem_range.1 (Finset.mem_filter.1 ht).1)).2
      omega
    simp only [Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_eq_sum_ones] at eR1 dC1
    rw [Fintype.card_sum, Fintype.card_fin]
    rw [hF3] at dC
    rw [hF3'] at dR
    omega

end MemberPE

section E2Pot

variable {p : ℕ} [hp : Fact p.Prime] {u : ℤ}

/-- Potentials: `3` below `r`, the window potential on its parity, and `1` on the virtual nodes (both types). -/
def phiR2 (r m : ℕ) (uX : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t < r then 3 else if t < r + 2 * m then (if (t - r) % 2 = 0 then uX ((t - r) / 2) else 0) else 1

def phiC2 (r m : ℕ) (uY : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t < r then 3 else if t < r + 2 * m then (if (t - r) % 2 = 1 then uY ((t - r) / 2) else 0) else 1

/-- Every pair of labels of the window is covered. -/
theorem e2_pair {r m : ℕ} (hpr : p ≤ r) (hN2 : r + 2 * m ≤ 2 * p) (uX uY : ℕ → ℕ)
    (hdual : ∀ i j, i < m → j < m → w3 (cell p u (r + 2 * i)) (cell p u (r + 2 * j + 1)) ≤ uX i + uY j)
    (n n' : ℕ) (hn1 : r ≤ n) (hn2 : n < 2 * p) (hn3 : (n - r) % 2 = 0 ∨ r + 2 * m ≤ n)
    (hm1 : r ≤ n') (hm2 : n' < 2 * p) (hm3 : (n' - r) % 2 = 1 ∨ r + 2 * m ≤ n') :
    WlabE p u false false n n' ≤ phiR2 r m uX n + phiC2 r m uY n' := by
  have hp0 : 0 < p := hp.out.pos
  have hper : ∀ x, p ≤ x → x < 2 * p → x / p = 1 := by
    intro x h1 h2
    apply le_antisymm
    · have : x / p < 2 := (Nat.div_lt_iff_lt_mul hp0).2 (by omega)
      omega
    · rw [Nat.le_div_iff_mul_le hp0]; omega
  have hdn : n / p = 1 := hper n (by omega) hn2
  have hdn' : n' / p = 1 := hper n' (by omega) hm2
  by_cases hnn : n = n'
  · subst hnn
    have hv : r + 2 * m ≤ n := by omega
    have e1 : phiR2 r m uX n = 1 := by unfold phiR2; rw [if_neg (by omega), if_neg (by omega)]
    have e2 : phiC2 r m uY n = 1 := by unfold phiC2; rw [if_neg (by omega), if_neg (by omega)]
    have hW : WlabE p u false false n n = 2 := by
      unfold WlabE; rw [if_pos rfl, if_pos ⟨rfl, rfl, rfl, hdn⟩]
    omega
  · have hne : n % p ≠ n' % p := fun h => hnn (cong_eq (by omega) (by omega) h)
    have hsame : n / p = n' / p := by rw [hdn, hdn']
    have hW1 : WlabE p u false false n n' ≤ 1 := by
      unfold WlabE; rw [if_neg hne, if_pos ⟨rfl, hsame⟩]; split_ifs <;> omega
    by_cases hv1 : r + 2 * m ≤ n
    · have e1 : phiR2 r m uX n = 1 := by unfold phiR2; rw [if_neg (by omega), if_neg (by omega)]
      omega
    by_cases hv2 : r + 2 * m ≤ n'
    · have e2 : phiC2 r m uY n' = 1 := by unfold phiC2; rw [if_neg (by omega), if_neg (by omega)]
      omega
    have h0 : (n - r) % 2 = 0 := by omega
    have h1 : (n' - r) % 2 = 1 := by omega
    have e1 : phiR2 r m uX n = uX ((n - r) / 2) := by
      unfold phiR2; rw [if_neg (by omega), if_pos (by omega), if_pos h0]
    have e2 : phiC2 r m uY n' = uY ((n' - r) / 2) := by
      unfold phiC2; rw [if_neg (by omega), if_pos (by omega), if_pos h1]
    rw [e1, e2]
    have hd := hdual ((n - r) / 2) ((n' - r) / 2) (by omega) (by omega)
    have f1 : r + 2 * ((n - r) / 2) = n := by omega
    have f2 : r + 2 * ((n' - r) / 2) + 1 = n' := by omega
    rw [f1, f2] at hd
    refine le_trans ?_ hd
    unfold WlabE w3 cell
    rw [if_neg hne, if_pos ⟨rfl, hsame⟩, hdn, hdn']
    by_cases hh : half p u n = half p u n'
    · simp [hh]
    · simp [hh]

theorem e2_point (p r m : ℕ) (uX uY : ℕ → ℕ) (hN2 : r + 2 * m ≤ 2 * p) (t : ℕ) :
    ((if t ∈ TRs p 2 0 r m then phiR2 r m uX t else 0) + (if t ∈ ORs p 2 0 r m then phiR2 r m uX t else 0) +
      (if t ∈ TCs p 2 0 r m then phiC2 r m uY t else 0) + (if t ∈ OCs p 2 0 r m then phiC2 r m uY t else 0) +
      3 * (if t ∈ FXs r m then 1 else 0) + (if t ∈ Finset.Ico (r + 2 * m) (2 * p) then 1 else 0)) ≤
    ((if t ∈ FXs r m then phiR2 r m uX t else 0) +
      (if t ∈ FYs r m then phiC2 r m uY t else 0) +
      3 * ((if t ∈ TRs p 2 0 r m then 1 else 0) + (if t ∈ ORs p 2 0 r m then 1 else 0))) := by
  unfold TRs TCs ORs OCs Tdel FXs FYs phiR2 phiC2
  simp only [Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero]
  split_ifs <;> omega

end E2Pot

section E2Main

variable {p : ℕ} [hp : Fact p.Prime]

theorem e2_sum (r m : ℕ) (hpr : p ≤ r) (hN2 : r + 2 * m ≤ 2 * p) (uX uY : ℕ → ℕ) :
    3 * r + 3 * m + (∑ t ∈ TRs p 2 0 r m, phiR2 r m uX t + ∑ t ∈ ORs p 2 0 r m, phiR2 r m uX t +
        ∑ t ∈ TCs p 2 0 r m, phiC2 r m uY t + ∑ t ∈ OCs p 2 0 r m, phiC2 r m uY t) ≤
      (4 * r - 2 * p + 2 * m + ∑ i ∈ Finset.range m, uX i + ∑ j ∈ Finset.range m, uY j) +
        3 * ((TRs p 2 0 r m).card + (ORs p 2 0 r m).card) := by
  have hX : ∑ i ∈ Finset.range m, uX i = ∑ t ∈ FXs r m, phiR2 r m uX t := by
    have h := sum_stride r m 0 (by norm_num) (fun t => r ≤ t) (phiR2 r m uX)
    rw [FXs, ← h]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [if_pos (by omega)]
    unfold phiR2
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    congr 1; omega
  have hY : ∑ i ∈ Finset.range m, uY i = ∑ t ∈ FYs r m, phiC2 r m uY t := by
    have h := sum_stride r m 1 (by norm_num) (fun t => r ≤ t) (phiC2 r m uY)
    rw [FYs, ← h]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [if_pos (by omega)]
    unfold phiC2
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    congr 1; omega
  have hcX : (FXs r m).card = m := by
    have h := sum_stride r m 0 (by norm_num) (fun t => r ≤ t) (fun _ => 1)
    rw [FXs, Finset.card_eq_sum_ones, ← h]
    simp
  set B := 2 * p with hB
  have hsTR : TRs p 2 0 r m ⊆ Finset.range B := by
    intro t ht
    simp only [TRs, Tdel, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at ht
    rw [Finset.mem_range]; omega
  have hsOR : ORs p 2 0 r m ⊆ Finset.range B := by
    intro t ht
    simp only [ORs, Finset.mem_filter, Finset.mem_Ico] at ht
    rw [Finset.mem_range]; omega
  have hsTC : TCs p 2 0 r m ⊆ Finset.range B := by
    intro t ht
    simp only [TCs, Tdel, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at ht
    rw [Finset.mem_range]; omega
  have hsOC : OCs p 2 0 r m ⊆ Finset.range B := by
    intro t ht
    simp only [OCs, Finset.mem_filter, Finset.mem_Ico] at ht
    rw [Finset.mem_range]; omega
  have hsFX : FXs r m ⊆ Finset.range B := by
    intro t ht
    simp only [FXs, Finset.mem_filter, Finset.mem_Ico] at ht
    rw [Finset.mem_range]; omega
  have hsFY : FYs r m ⊆ Finset.range B := by
    intro t ht
    simp only [FYs, Finset.mem_filter, Finset.mem_Ico] at ht
    rw [Finset.mem_range]; omega
  have hsFE : Finset.Ico (r + 2 * m) (2 * p) ⊆ Finset.range B := by
    intro t ht
    simp only [Finset.mem_Ico] at ht
    rw [Finset.mem_range]; omega
  have hle := Finset.sum_le_sum (s := Finset.range B) (fun t _ => e2_point p r m uX uY hN2 t)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
  rw [sum_ite_range B _ hsTR (phiR2 r m uX), sum_ite_range B _ hsOR (phiR2 r m uX),
    sum_ite_range B _ hsTC (phiC2 r m uY), sum_ite_range B _ hsOC (phiC2 r m uY),
    sum_ite_range B _ hsFX (fun _ => 1), sum_ite_range B _ hsFX (phiR2 r m uX),
    sum_ite_range B _ hsFY (phiC2 r m uY), sum_ite_range B _ hsTR (fun _ => 1),
    sum_ite_range B _ hsOR (fun _ => 1), sum_ite_range B _ hsFE (fun _ => 1)] at hle
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico] at hle
  rw [hcX] at hle
  omega

end E2Main

end E2

section E2Thm

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Row `E₂`** (`PLANE2-SIMPLIFICATION` Theorem 7): for `p ≤ r` and `N = r + 2 m ≤ 2 p`, every retained set
`c` of common nodes below `r` and potentials `uX`, `uY` on the window rows `r + 2 i` and columns `r + 2 j + 1`
with `W₃ ≤ uX i + uY j`, every coefficient of the determinant of the member has `p`-adic denominator at most
`4 r − 2 p + 2 m + ∑ uX + ∑ uY`.  The prime `p ≥ 5` satisfies `p² > 2 N + 2 p` and `p ∤ v`; nothing else
(no table, no `(ND)`). -/
theorem row_E2 (v u : ℤ) (hpv : ¬ (p : ℤ) ∣ v) (hp5 : 5 ≤ p)
    {r m : ℕ} (hpr : p ≤ r) (hN2 : r + 2 * m ≤ 2 * p) (hN : 2 * (r + 2 * m) + 2 * p < p * p)
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (hcinj : Function.Injective c)
    (hcr : ∀ i, c i < r) (uX uY : ℕ → ℕ)
    (hdual : ∀ i j, i < m → j < m → w3 (cell p u (r + 2 * i)) (cell p u (r + 2 * j + 1)) ≤ uX i + uY j) :
    GLE p (4 * r - 2 * p + 2 * m + ∑ i ∈ Finset.range m, uX i + ∑ j ∈ Finset.range m, uY j)
      (seqFullN (fS v u) (eS v u) c
        (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hodd : p % 2 = 1 := by
    by_contra h
    have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
    rcases hp.out.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega
  rcases Nat.lt_or_ge r (2 * p) with hr2 | hr2
  · -- `p ≤ r < 2 p`: `κ = 2`, `k' = 0`, `ξ = p X`
    have hN' : 2 * (2 * p) < p * p := by nlinarith
    have hNp : 2 * p ≤ 2 * p := le_refl _
    have hU := E2.unitDet_two (R := RP p) (ξ := E2.xiP2 p) v u hpv hodd hN' hNp (pRad_RP p)
      (E2.xiP2_dvd p)
    have hdiag := E2.hdiag_two (R := RP p) (ξ := E2.xiP2 p) (π := (r + 1) % 2) v u hpv hodd hp5 hN' hNp
      (pRad_RP p) (E2.xiP2_dvd p)
    have hcompl : ∀ n, n < r + 2 * m → (n / p + 1) * p ≤ 2 * p := by
      intro n hn
      have : n / p < 2 := (Nat.div_lt_iff_lt_mul hp0).2 (by omega)
      nlinarith
    refine E2.member_gle_PE (p := p) (κ := 2) (k' := 0) v u hpv hodd hp5 hN' hU rfl hdiag hr2
      (by omega) hcompl c hcinj hcr (E2.phiR2 r m uX) (E2.phiC2 r m uY) ?_ ?_ ?_ ?_ ?_
      (4 * r - 2 * p + 2 * m + ∑ i ∈ Finset.range m, uX i + ∑ j ∈ Finset.range m, uY j) ?_
    · intro t ht
      constructor <;> simp [E2.phiR2, E2.phiC2, ht]
    · intro n hn n' hn'
      simp only [TRs, TCs, Tdel, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at hn hn'
      exact E2.e2_pair hpr hN2 uX uY hdual n n' (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
    · intro n hn n' hn'
      exfalso
      simp only [OCs, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at hn'
      omega
    · intro n hn n' hn'
      exfalso
      simp only [ORs, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at hn
      omega
    · intro n hn n' hn'
      exfalso
      simp only [ORs, Finset.mem_filter, Finset.mem_Ico, mul_zero, add_zero] at hn
      omega
    · exact E2.e2_sum r m hpr hN2 uX uY
  · -- `r = 2 p`, `m = 0`: the crude bound `3 |ι| ≤ 6 p`
    have hm0 : m = 0 := by omega
    subst hm0
    have hN3 : 2 * r < p * p := by omega
    have hcardι : Fintype.card ι ≤ r := by
      have := Fintype.card_le_of_injective (fun i => (⟨c i, hcr i⟩ : Fin r)) (by
        intro i j h; apply hcinj; simpa using congrArg Fin.val h)
      simpa using this
    have hg := gle_member (p := p) v u c (fun i : Fin 0 => r + 2 * (i : ℕ))
      (fun i : Fin 0 => r + 2 * (i : ℕ) + 1) (N := r) hN3
      (by rintro (i | i)
          · exact hcr i
          · exact i.elim0)
      (by rintro (i | i)
          · exact hcr i
          · exact i.elim0)
      hcinj (fun i j => j.elim0) (fun i j => i.elim0) (fun i j => i.elim0) (K := 0)
      (by rw [pow_zero]; exact one_dvd _)
    refine GLE.mono ?_ hg
    simp only [Fintype.card_fin, Finset.range_zero, Finset.sum_empty]
    omega

end E2Thm

end CatalanCore.Uniform.Content.Sweep
#print axioms CatalanCore.Uniform.Content.Sweep.row_E2
#print axioms CatalanCore.Uniform.Content.Sweep.E2.sw_dvdE
#print axioms CatalanCore.Uniform.Content.Sweep.E2.hdiag_two
#print axioms CatalanCore.Uniform.Content.Sweep.E2.unitDet_two
#print axioms CatalanCore.Uniform.Content.Sweep.E2.member_gle_PE
#print axioms CatalanCore.Uniform.Content.Sweep.E2.gle_member2
