module

public import CatalanCore.Uniform.Content.Sweep.RInst

@[expose] public section

/-!
# Full-period integer-pole sources and class-free Schur weights

Canonical Q18 component. The full pivot and period class matrices are spectral
matrices with identical row and column nodes. Their monic determinants give
units in the Gauss ring. A common class solution removes orientation from the
three-level Schur weight. No nondegeneracy table is used.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep.Gen

namespace CatalanCore.Uniform.Content.Sweep.HPole

variable {p : ℕ} [hp : Fact p.Prime]
  {R : Type*} [CommRing R] [Algebra (LocRing p) R]

noncomputable def Qpoly (h : ℕ) (d : ℕ → ℚ) (n t : ℕ) : (LocRing p)[X] :=
  (if n = t then X else 0) +
    C (toL p ((p : ℚ)^h * lw (hpoleF h d) (hpoleE h d) n t))

theorem toQ_Qpoly (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    {n t : ℕ} (hn : n < p*p) (ht : t < p*p) :
    toQ p (Qpoly (p := p) h d n t) =
      (if n = t then (X : ℚ[X]) else 0) +
        C ((p : ℚ)^h * lw (hpoleF h d) (hpoleE h d) n t) := by
  classical
  have hq := q_mem h hh d hd hn ht
  simp only [Qpoly, map_add, toQ, Polynomial.coe_mapRingHom]
  split_ifs <;> simp [toL_val hq]

theorem aeval_Qpoly (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p) (ξ : R)
    {n t : ℕ} (hn : n < p*p) (ht : t < p*p) :
    Polynomial.aeval ξ (Qpoly (p := p) h d n t) =
      Qh (p := p) h d ξ n t := by
  classical
  simp only [Qpoly, Qh, map_add, toR_eq_algebraMap_toL]
  split_ifs <;> simp

/-- At zero stagger every orientation consists of the same full periods. -/
theorem Cper_zero (κ o : ℕ) : Cper κ 0 o = range κ := by
  ext j
  rw [Gen.mem_Cper, mem_range]
  omega

private theorem node_zero (κ π : ℕ) (x : PivIdx p κ 0) :
    rowNode p κ 0 π x = colNode p κ 0 π x := by
  rcases x with ⟨ω, a | i⟩
  · simp [rowNode, colNode, rowPer, colPer]
  · exact i.elim0

/-- A spectral matrix with coefficients in the local coefficient ring has unit
 determinant at the Gauss variable. This is the monic, full-square argument. -/
private theorem spectral_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ξ : R) (hξ : UnitProp p ξ) (M : Matrix ι ι (LocRing p)) :
    IsUnit ((Matrix.scalar ι ξ) + M.map (algebraMap (LocRing p) R)).det := by
  classical
  have hn : phiP p (-M).charpoly ≠ 0 := by
    unfold phiP
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom]
    rw [← Matrix.charpoly_map]
    intro hz
    exact (Matrix.charpoly_monic ((-M).map (redQ p))).ne_zero
      ((map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))).1 hz)
  have hu := hξ (-M).charpoly hn
  have he : Polynomial.aeval ξ (-M).charpoly =
      ((Matrix.scalar ι ξ) + M.map (algebraMap (LocRing p) R)).det := by
    rw [← Polynomial.eval_map_algebraMap]
    rw [← Matrix.charpoly_map (-M) (algebraMap (LocRing p) R),
      Matrix.eval_charpoly]
    congr 1
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]
  rw [he] at hu
  exact hu

private noncomputable def Bconstant (h : ℕ) (d : ℕ → ℚ) (l j : ℕ) : LocRing p :=
  if l = j then -toL p (hpoleTau p h d l)
  else toL p ((hpoleSigma p h d j - hpoleSigma p h d l) / ((j : ℚ) - l))

private theorem Bm_constant (h : ℕ) (d : ℕ → ℚ) (ξ : R) (l j : ℕ) :
    Bm (p := p) h d ξ l j = (if l = j then ξ else 0) +
      algebraMap (LocRing p) R (Bconstant (p := p) h d l j) := by
  classical
  by_cases hlj : l = j <;>
    simp [Bm, Bconstant, hlj, tauR, toR_eq_algebraMap_toL, sub_eq_add_neg]

theorem k0_source_rp (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (hp5 : 5 ≤ p) {κ π N : ℕ} (hπ : π ≤ 1)
    (hN : 2*N < p*p) (hH : κ*p ≤ N) :
    IsUnit (Qp (p := p) h d κ 0 π (xiP p)).det ∧
      ∃ Y : ℕ → ℕ → ℕ → RP p,
        (∀ b o, o ≤ 1 → ∀ l ∈ Cper κ 0 (1-o),
          ∑ j ∈ Cper κ 0 o,
            Bm (p := p) h d (xiP p) l j * Y b o j =
              GamR (p := p) h d b l) ∧
        (∀ b o o' j, Y b o j = Y b o' j) := by
  classical
  constructor
  · let M : Matrix (PivIdx p κ 0) (PivIdx p κ 0) (LocRing p) := fun x y =>
      toL p ((p : ℚ)^h * lw (hpoleF h d) (hpoleE h d)
        (rowNode p κ 0 π x) (colNode p κ 0 π y))
    convert spectral_unit (xiP p) (xiP_unitProp p) M using 1
    congr 1
    ext x y
    change Qh (p := p) h d (xiP p) (rowNode p κ 0 π x) (colNode p κ 0 π y) =
      (if x = y then xiP p else 0) + algebraMap (LocRing p) (RP p) (M x y)
    have he : rowNode p κ 0 π x = colNode p κ 0 π y ↔ x = y := by
      rw [node_zero]
      exact (colNode_injective hp.out.pos).eq_iff
    simp only [Qp, Matrix.of_apply, Qh, toR_eq_algebraMap_toL]
    simp only [he]
    rfl
  · let B : Matrix (Fin κ) (Fin κ) (RP p) := fun l j =>
      Bm (p := p) h d (xiP p) l j
    have hB : IsUnit B.det := by
      convert spectral_unit (xiP p) (xiP_unitProp p)
        (fun l j : Fin κ => Bconstant (p := p) h d l j) using 1
      congr 1
      ext l j
      change B l j = (if l = j then xiP p else 0) +
        algebraMap (LocRing p) (RP p) (Bconstant (p := p) h d l j)
      dsimp only [B]
      rw [Bm_constant]
      simp only [Fin.ext_iff]
    let V : ℕ → Fin κ → RP p := fun b =>
      B⁻¹ *ᵥ (fun l => GamR (p := p) h d b l)
    let Y : ℕ → ℕ → ℕ → RP p := fun b _ j => if hj : j < κ then V b ⟨j, hj⟩ else 0
    refine ⟨Y, ?_, fun _ _ _ _ => rfl⟩
    intro b o ho l hl
    rw [Cper_zero] at hl ⊢
    have hlk : l < κ := mem_range.mp hl
    have hv : B *ᵥ V b = (fun l : Fin κ => GamR (p := p) h d b l) := by
      dsimp [V]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hB, Matrix.one_mulVec]
    have hv' := congrFun hv ⟨l, hlk⟩
    have hv'' : (∑ j : Fin κ, Bm (p := p) h d (xiP p) l j * Y b o j) =
        GamR (p := p) h d b l := by
      simpa [Matrix.mulVec, dotProduct, B, Y] using hv'
    rw [Fin.sum_univ_eq_sum_range (fun j => Bm (p := p) h d (xiP p) l j * Y b o j)] at hv''
    exact hv''

private theorem pattern_zero (h : ℕ) (d : ℕ → ℚ) (κ : ℕ) (ξ : R)
    (Y : ℕ → ℕ → ℕ → R) (hY : ∀ b o o' j, Y b o j = Y b o' j)
    (isOut : Bool) (b o o' l : ℕ) :
    patF (p := p) h d κ 0 ξ Y isOut b o l =
      patF (p := p) h d κ 0 ξ Y isOut b o' l := by
  cases isOut
  · simp only [patF, Bool.false_eq_true, if_false]
    exact hY b o o' l
  · simp only [patF, if_true, Gout]
    rw [Cper_zero, Cper_zero]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [hY b o o' j])

def k0Weight (h p : ℕ) (kindR kindC : Bool) (n t : ℕ) : ℕ :=
  if n % p = t % p then h
  else if kindR = kindC ∧ n / p = t / p then h-3 else h-1

theorem sw_dvd_k0
    (h : ℕ) (d : ℕ → ℚ) {N κ π : ℕ} (ξ : R)
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (zn : I → ℕ) (yn : J → ℕ)
    (hh : 3 ≤ h)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (hp5 : 5 ≤ p) (hπ : π ≤ 1)
    (hN : 2*N < p*p) (hH : κ*p ≤ N)
    (hU : IsUnit (Qp (p := p) h d κ 0 π ξ).det)
    (Y : ℕ → ℕ → ℕ → R)
    (hclass : ∀ b o, o ≤ 1 → ∀ l ∈ Cper κ 0 (1-o),
      ∑ j ∈ Cper κ 0 o, Bm (p := p) h d ξ l j * Y b o j =
        GamR (p := p) h d b l)
    (hYind : ∀ b o o' j, Y b o j = Y b o' j)
    (hzc : ∀ z, (zn z / p + 1)*p ≤ N)
    (hyc : ∀ w, (yn w / p + 1)*p ≤ N)
    (r : I ⊕ PivIdx p κ 0) (c : J ⊕ PivIdx p κ 0) :
    (p : R) ^ (h - k0Weight h p r.isLeft c.isLeft
      (nR (p := p) (κ := κ) (k' := 0) (π := π) zn r)
      (nC (p := p) (κ := κ) (k' := 0) (π := π) yn c)) ∣
      Schur.Sw (Hq (p := p) h d κ 0 π ξ zn yn)
        (Zp (p := p) h d κ 0 π ξ) r c := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hzn : ∀ z, zn z < N := fun z => lt_of_complete hp0 (hzc z)
  have hyn : ∀ w, yn w < N := fun w => lt_of_complete hp0 (hyc w)
  have hH' : (κ + 2 * 0) * p ≤ N := by simpa using hH
  by_cases hcg : nR (p := p) (κ := κ) (k' := 0) (π := π) zn r % p =
      nC (p := p) (κ := κ) (k' := 0) (π := π) yn c % p
  · simp only [k0Weight, hcg, if_true, Nat.sub_self, pow_zero]
    exact one_dvd _
  · obtain ⟨U, hUU⟩ := isUnit_natDiff (R := R) hcg
    have hmul := sw_mul h d zn yn hh hd hN hH' hU hπ hzn hyn r c
    rw [← hUU] at hmul
    have hSw : Schur.Sw (Hq (p := p) h d κ 0 π ξ zn yn) (Zp (p := p) h d κ 0 π ξ) r c =
        ((U⁻¹ : Rˣ) : R) * ((p : R) * (labR (p := p) h d κ 0 π ξ zn 1 r *
          labC (p := p) h d κ 0 π ξ yn 0 c - labR (p := p) h d κ 0 π ξ zn 0 r *
          labC (p := p) h d κ 0 π ξ yn 1 c)) := by
      rw [← hmul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hSw]
    refine Dvd.dvd.mul_left ?_ _
    by_cases hpat : r.isLeft = c.isLeft ∧
        nR (p := p) (κ := κ) (k' := 0) (π := π) zn r / p =
          nC (p := p) (κ := κ) (k' := 0) (π := π) yn c / p
    · simp only [k0Weight, hcg, if_false, hpat, if_true, and_self]
      rw [show h - (h - 3) = 3 by omega]
      obtain ⟨hk, hl⟩ := hpat
      obtain ⟨e, he⟩ := rowLab h d zn hh hd hp5 hN hH' Y hclass hU hzn r
      obtain ⟨e', he'⟩ := colLab h d yn hh hd hp5 hN hH' Y hclass hU hπ hyn c
      have hP : ∀ b, patR (p := p) h d κ 0 π ξ zn Y r b =
          patC (p := p) h d κ 0 π ξ yn Y c b := by
        intro b
        unfold patR patC
        rw [hk, hl]
        exact pattern_zero h d κ ξ Y hYind _ _ _ _ _
      have hw := omega_sq (p := p) (labR (p := p) h d κ 0 π ξ zn 0 r)
        (labR (p := p) h d κ 0 π ξ zn 1 r) (labC (p := p) h d κ 0 π ξ yn 0 c)
        (labC (p := p) h d κ 0 π ξ yn 1 c) e e' (patR (p := p) h d κ 0 π ξ zn Y r 0)
        (patR (p := p) h d κ 0 π ξ zn Y r 1) (he 0 (by norm_num)) (he 1 (by norm_num))
        (by rw [hP 0]; exact he' 0 (by norm_num)) (by rw [hP 1]; exact he' 1 (by norm_num))
      have hpow : (p : R) ^ 3 = (p : R) * (p : R) ^ 2 := by ring
      rw [hpow]
      exact mul_dvd_mul_left _ hw
    · simp only [k0Weight, hcg, if_false, hpat]
      rw [show h - (h - 1) = 1 by omega, pow_one]
      exact dvd_mul_right _ _

end CatalanCore.Uniform.Content.Sweep.HPole

#print axioms CatalanCore.Uniform.Content.Sweep.HPole.toQ_Qpoly
#print axioms CatalanCore.Uniform.Content.Sweep.HPole.aeval_Qpoly
#print axioms CatalanCore.Uniform.Content.Sweep.HPole.k0_source_rp
#print axioms CatalanCore.Uniform.Content.Sweep.HPole.sw_dvd_k0


