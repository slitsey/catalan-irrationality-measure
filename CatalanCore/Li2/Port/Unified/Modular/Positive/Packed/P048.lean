/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Positive/Packed/P048.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P047
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P041
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P042
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P036
public import CatalanCore.Li2.Port.Unified.Modular.Base.PrimeTwoThreeSum
public import CatalanCore.Li2.Port.Unified.Modular.Base.IntegralPolynomials
public import Mathlib.Algebra.Polynomial.CoeffMem

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial CatalanCore.Li2.Port.Li2
open scoped BigOperators

namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section

lemma parameterInvPow_VG_two (lam : ℚ) (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1) (m : ℕ) :
    CatalanCore.Li2.Port.Li2.VG 2 (lam⁻¹^m) (m:ℚ) := by
  simpa using! hmu.pow m

lemma parameterCst_VG_two (lam : ℚ) (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1)
    {K N : ℕ} (hKN : K ≤ N) :
    CatalanCore.Li2.Port.Li2.VG 2 (parameterCst lam K) (-2 * (Nat.log 2 N : ℚ)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold parameterCst
  apply CatalanCore.Li2.Port.Li2.VG.sum
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have h1 : CatalanCore.Li2.Port.Li2.VG 2 (lam⁻¹^a) 0 :=
    (parameterInvPow_VG_two lam hmu a).mono (by exact_mod_cast Nat.zero_le a)
  have h2 := CatalanCore.Li2.Port.Li2.VG.inv_nat (p := 2) (j := a) (n := N) ha1 (ha2.trans hKN)
  have h3 : CatalanCore.Li2.Port.Li2.VG 2 (((a:ℚ)^2)⁻¹) (2 * -(Nat.log 2 N : ℚ)) := by
    rw [← inv_pow]
    exact_mod_cast h2.pow 2
  rw [div_eq_mul_inv]
  refine (h1.mul h3).mono ?_
  linarith

lemma parameterPoleNode_VG_two (lam : ℚ) (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1)
    {j m N : ℕ} (hjm : j ≠ m) (hN : j - m ≤ N ∧ m - j ≤ N) :
    CatalanCore.Li2.Port.Li2.VG 2 (parameterPoleNode lam j m)
      ((m:ℚ) - 2 * (Nat.log 2 N : ℚ)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold parameterPoleNode
  have hd : ((j:ℚ) - m)^2 =
      ((((j - m : ℕ) + (m - j : ℕ) : ℕ) : ℚ))^2 := by
    rcases le_total j m with h | h
    · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]
      ring
    · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h]
  set t := (j - m : ℕ) + (m - j : ℕ) with ht
  have ht1 : 1 ≤ t := by omega
  have htN : t ≤ N := by omega
  rw [hd, div_eq_mul_inv]
  have h2 := CatalanCore.Li2.Port.Li2.VG.inv_nat (p := 2) (j := t) (n := N) ht1 htN
  have h3 : CatalanCore.Li2.Port.Li2.VG 2 (((t:ℚ)^2)⁻¹) (2 * -(Nat.log 2 N : ℚ)) := by
    rw [← inv_pow]
    exact_mod_cast h2.pow 2
  have hpow := parameterInvPow_VG_two lam hmu m
  refine (((CatalanCore.Li2.Port.Li2.VG.natCast (p := 2) j).mul hpow).mul h3).mono ?_
  linarith

lemma parameterTailC_VG_two (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG 2 (lam/(1-lam)) 0)
    (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1) {n : ℕ} (hn : 1 ≤ n)
    (a b : ℕ) (ha : a < 2*n) (hb : b < 2*n) :
    CatalanCore.Li2.Port.Li2.VG 2 (parameterTailC lam (4*n) (CatalanCore.Li2.Port.Li2.gramNum n a b))
      ((4*n+1 : ℕ) - 2 * (Nat.log 2 (7*n-2) : ℚ)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : ℚ := Nat.log 2 (7*n-2)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  unfold parameterTailC
  apply CatalanCore.Li2.Port.Li2.VG.sub
  · set G := CatalanCore.Li2.Port.Li2.gpart (4*n) (CatalanCore.Li2.Port.Li2.gramNum n a b)
    have hGv : ∀ x : ℤ, CatalanCore.Li2.Port.Li2.VG 2 (G.eval (x:ℚ)) (-2 * L) := by
      intro x
      rw [CatalanCore.Li2.Port.Li2.gpart_eval]
      have hq := CatalanCore.Li2.Port.Li2.gramQuot_eval_VG 2 n a b x
      have hq' := CatalanCore.Li2.Port.Li2.derivative_eval_VG 2 (CatalanCore.Li2.Port.Li2.gramQuot_natDegree_le n a b)
        _ (CatalanCore.Li2.Port.Li2.gramQuot_eval_VG 2 n a b) x
      have l1 : (Nat.log 2 (3*n+a+b) : ℚ) ≤ L := by
        dsimp [L]
        exact_mod_cast Nat.log_mono_right (by omega : 3*n+a+b ≤ 7*n-2)
      have l2 : (Nat.log 2 (3*n+a+b-4*n) : ℚ) ≤ L := by
        dsimp [L]
        exact_mod_cast Nat.log_mono_right (by omega : 3*n+a+b-4*n ≤ 7*n-2)
      refine (hq.mono (by linarith)).add
        (((CatalanCore.Li2.Port.Li2.VG.intCast (p := 2) x).mul hq').mono ?_)
      linarith
    have hR := parameterG_VG_of_integral_ratio 2 lam h1 hratio
      (le_refl ((G.comp (X - C ((4*n+1 : ℕ):ℚ))).natDegree))
      (-2 * L) (fun i _ => by
        have := hGv ((i:ℤ) - ((4*n+1 : ℕ) : ℤ))
        simp only [eval_comp, eval_sub, eval_X, eval_C]
        push_cast at this ⊢
        exact this)
    refine ((parameterInvPow_VG_two lam hmu (4*n+1)).mul hR).mono ?_
    push_cast
    linarith
  · apply CatalanCore.Li2.Port.Li2.VG.sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hres : CatalanCore.Li2.Port.Li2.VG 2 (CatalanCore.Li2.Port.Li2.dres (4*n) (CatalanCore.Li2.Port.Li2.gramNum n a b) j) 0 :=
      CatalanCore.Li2.Port.Li2.gramRes_VG 2 n a b hj1 hj2
    have hin : CatalanCore.Li2.Port.Li2.VG 2
        (∑ m ∈ Finset.Ico (4*n+1) (j+4*n+1), parameterPoleNode lam j m)
        (((4*n+1 : ℕ) : ℚ) - 2 * L) := by
      apply CatalanCore.Li2.Port.Li2.VG.sum
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
      have hv := parameterPoleNode_VG_two lam hmu (j := j) (m := m)
        (N := 7*n-2) (by omega) ⟨by omega, by omega⟩
      refine hv.mono ?_
      have : ((4*n+1 : ℕ) : ℚ) ≤ m := by exact_mod_cast hm1
      push_cast at this ⊢
      linarith
    simpa only [zero_add] using! hres.mul hin

section LocalBounds
variable {n : ℕ} (hn : 1 ≤ n)
include hn
local notation "L" => ((Nat.log 2 (7*n-2) : ℕ) : ℚ)

lemma parameterBhat_GV_two (lam : ℚ) (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (4*n)) {t : ℕ} (ht : t ≤ 2) :
    CatalanCore.Li2.Port.Li2.GV 2 (parameterBhat lam (4*n) m t) (-(2 - (t:ℚ)) * L) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL := CatalanCore.Li2.Port.Li2.L_nonneg hn
  have e1 : CatalanCore.Li2.Port.Li2.VG 2 (CatalanCore.Li2.Port.Li2.eps (4*n) m 1) (-(1:ℚ) * L) := by
    simpa using! CatalanCore.Li2.Port.Li2.eps_VG 2 (N := 7*n-2) hm (by omega) (k := 1) (by norm_num)
  have e2 : CatalanCore.Li2.Port.Li2.VG 2 (CatalanCore.Li2.Port.Li2.eps (4*n) m 2) (-(2:ℚ) * L) := by
    simpa using! CatalanCore.Li2.Port.Li2.eps_VG 2 (N := 7*n-2) hm (by omega) (k := 2) le_rfl
  have hC : CatalanCore.Li2.Port.Li2.VG 2 (parameterCst lam (4*n)) (-2 * L) :=
    parameterCst_VG_two lam hmu (by omega)
  have hm' := CatalanCore.Li2.Port.Li2.VG.natCast (p := 2) m
  have t1 : CatalanCore.Li2.Port.Li2.VG 2 (CatalanCore.Li2.Port.Li2.eps (4*n) m 1) (-2 * L) := e1.mono (by linarith)
  have t2 : CatalanCore.Li2.Port.Li2.VG 2 (CatalanCore.Li2.Port.Li2.eps (4*n) m 1 ^ 2) (-2 * L) := by
    have h := e1.pow 2
    refine h.mono (le_of_eq ?_)
    push_cast
    ring
  have t3 : CatalanCore.Li2.Port.Li2.VG 2 ((m:ℚ) * (CatalanCore.Li2.Port.Li2.eps (4*n) m 1 ^ 2 - CatalanCore.Li2.Port.Li2.eps (4*n) m 2))
      (-2 * L) := by
    have h := hm'.mul (t2.sub e2)
    simpa using! h
  have t4 : CatalanCore.Li2.Port.Li2.VG 2 ((m:ℚ) * parameterCst lam (4*n)) (-2 * L) := by
    have h := hm'.mul hC
    simpa using! h
  have tX : CatalanCore.Li2.Port.Li2.GV 2 (C (m:ℚ) * X) (-2 * L) :=
    (CatalanCore.Li2.Port.Li2.GV.mul (CatalanCore.Li2.Port.Li2.GV.C hm') CatalanCore.Li2.Port.Li2.GV.X).mono (by linarith)
  interval_cases t
  · have g : CatalanCore.Li2.Port.Li2.GV 2 (parameterBhat lam (4*n) m 0) (-2 * L) := by
      simp only [parameterBhat]
      exact CatalanCore.Li2.Port.Li2.GV.add (CatalanCore.Li2.Port.Li2.GV.C ((t1.add t3).add t4)) tX
    convert g using 2
    push_cast
    ring
  · have g : CatalanCore.Li2.Port.Li2.GV 2 (parameterBhat lam (4*n) m 1) (-1 * L) := by
      simp only [parameterBhat]
      exact CatalanCore.Li2.Port.Li2.GV.C (((CatalanCore.Li2.Port.Li2.VG.one (p := 2)).neg.mono (by linarith)).sub
        (by simpa using! hm'.mul e1))
    convert g using 2
    push_cast
    ring
  · have g : CatalanCore.Li2.Port.Li2.GV 2 (parameterBhat lam (4*n) m 2) 0 := by
      simp only [parameterBhat]
      exact CatalanCore.Li2.Port.Li2.GV.C hm'
    convert g using 2
    push_cast
    ring

lemma parameterKap_GV_two (lam : ℚ) (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (4*n)) (s s' : ℕ) :
    CatalanCore.Li2.Port.Li2.GV 2 (parameterKap lam n m s s') (((s:ℚ) + s' - 2) * L) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  have hL := CatalanCore.Li2.Port.Li2.L_nonneg hn
  have hsig : CatalanCore.Li2.Port.Li2.JGV 2 ((CatalanCore.Li2.Port.Li2.shiftBinom n ^ 3).comp (X - C (m:ℚ))) L := by
    rw [pow_comp]
    exact (CatalanCore.Li2.Port.Li2.shiftBinom_JGV 2 n m (CatalanCore.Li2.Port.Li2.log_le_L hn (by omega))).pow 3
  unfold parameterKap
  apply CatalanCore.Li2.Port.Li2.GV.sum
  intro i hi
  have hi2 : i ≤ 2 := by simp at hi; omega
  split_ifs with hle
  · have hscale := CatalanCore.Li2.Port.Li2.residueScale_VG 2 (K := 4*n) h1 h2
    have hc := CatalanCore.Li2.Port.Li2.GV.C (hscale.mul (hsig i hi2))
    refine (hc.mul (parameterBhat_GV_two hn lam hmu hm hle)).mono ?_
    push_cast
    nlinarith
  · exact CatalanCore.Li2.Port.Li2.GV.zero _

end LocalBounds

section MatrixBounds
variable {n : ℕ} (hn : 1 ≤ n)
include hn
local notation "L" => ((Nat.log 2 (7*n-2) : ℕ) : ℚ)

lemma parameterWm_GV_two (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG 2 (lam/(1-lam)) 0)
    (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1) (a : Fin (2*n)) (i : CatalanCore.Li2.Port.Li2.Slot n) :
    CatalanCore.Li2.Port.Li2.GV 2 (parameterWm lam n a i) (CatalanCore.Li2.Port.Li2.ωw n i) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases i with _ | ⟨μ, s⟩ | b'
  · apply CatalanCore.Li2.Port.Li2.GV.C
    have h1' := CatalanCore.Li2.Port.Li2.shiftBinom_eval_int 2 n 0
    have h2 := CatalanCore.Li2.Port.Li2.binomPoly_eval_int_VG 2 a 0
    simp only [Int.cast_zero] at h1' h2
    simpa [CatalanCore.Li2.Port.Li2.ωw, parameterWm] using! (h1'.pow 3).mul h2
  · apply CatalanCore.Li2.Port.Li2.GV.C
    have hj := CatalanCore.Li2.Port.Li2.binom_JGV 2 a (CatalanCore.Li2.Port.Li2.nodeOf n μ)
      (CatalanCore.Li2.Port.Li2.log_le_L hn (d := a) (by have := a.isLt; omega))
    simpa [CatalanCore.Li2.Port.Li2.ωw, parameterWm] using! hj s.val (by omega)
  · simpa [CatalanCore.Li2.Port.Li2.ωw, parameterWm] using!
      CatalanCore.Li2.Port.Li2.GV.C (parameterTailC_VG_two lam h1 hratio hmu hn a b' a.isLt b'.isLt)

lemma parameterCmat_GV_two (lam : ℚ) (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1)
    (i : CatalanCore.Li2.Port.Li2.Slot n) (b : Fin (2*n)) :
    CatalanCore.Li2.Port.Li2.GV 2 (parameterCmat lam n i b) (CatalanCore.Li2.Port.Li2.κw n i) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL := CatalanCore.Li2.Port.Li2.L_nonneg hn
  rcases i with _ | ⟨μ, s⟩ | b'
  · apply CatalanCore.Li2.Port.Li2.GV.C
    have h2 := CatalanCore.Li2.Port.Li2.binomPoly_eval_int_VG 2 b 0
    simp only [Int.cast_zero] at h2
    simpa [CatalanCore.Li2.Port.Li2.κw, parameterCmat] using! h2.neg
  · have hm : CatalanCore.Li2.Port.Li2.nodeOf n μ ∈ Finset.Icc 1 (4*n) := by
      simp only [CatalanCore.Li2.Port.Li2.nodeOf, Finset.mem_Icc]
      have := μ.isLt
      omega
    have hsum : CatalanCore.Li2.Port.Li2.GV 2
        (∑ s' ∈ Finset.range 3,
          parameterKap lam n (CatalanCore.Li2.Port.Li2.nodeOf n μ) s.val s' *
            C (CatalanCore.Li2.Port.Li2.djet (CatalanCore.Li2.Port.Li2.binomPoly b) (CatalanCore.Li2.Port.Li2.nodeOf n μ) s'))
        (((s.val:ℚ) - 2) * L) := by
      apply CatalanCore.Li2.Port.Li2.GV.sum
      intro s' hs'
      have hs'2 : s' ≤ 2 := by simp at hs'; omega
      have hj := CatalanCore.Li2.Port.Li2.binom_JGV 2 b (CatalanCore.Li2.Port.Li2.nodeOf n μ)
        (CatalanCore.Li2.Port.Li2.log_le_L hn (d := b) (by have := b.isLt; omega))
      refine ((parameterKap_GV_two hn lam hmu hm s.val s').mul
        (CatalanCore.Li2.Port.Li2.GV.C (hj s' hs'2))).mono (le_of_eq ?_)
      ring
    exact (CatalanCore.Li2.Port.Li2.GV.mul (CatalanCore.Li2.Port.Li2.GV.C
      (parameterInvPow_VG_two lam hmu (CatalanCore.Li2.Port.Li2.nodeOf n μ))) hsum).mono
        (le_of_eq (by simp [CatalanCore.Li2.Port.Li2.κw]))
  · simp only [parameterCmat, CatalanCore.Li2.Port.Li2.κw]
    split_ifs
    · exact CatalanCore.Li2.Port.Li2.GV.C CatalanCore.Li2.Port.Li2.VG.one
    · exact CatalanCore.Li2.Port.Li2.GV.zero _

/-- The literal parameter-family determinant has the old ranked-slot 2-adic weight. -/
theorem parameterQtilde_GV_two_slots (lam : ℚ) (h0 : lam ≠ 0) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG 2 (lam/(1-lam)) 0)
    (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1) :
    CatalanCore.Li2.Port.Li2.GV 2 (ParameterFamily.Qtilde lam n)
      (∑ i ∈ Finset.range (2*n), CatalanCore.Li2.Port.Li2.θw n i) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ParameterFamily.Qtilde_eq_binomGram_det,
    parameterBinomGram_eq_mul lam h0 h1]
  apply CatalanCore.Li2.Port.Li2.det_mul_GV 2 (parameterWm lam n) (parameterCmat lam n)
    (CatalanCore.Li2.Port.Li2.ωw n) (CatalanCore.Li2.Port.Li2.κw n)
    (parameterWm_GV_two hn lam h1 hratio hmu)
    (parameterCmat_GV_two hn lam hmu)
  intro f hf
  calc
    ∑ i ∈ Finset.range (2*n), CatalanCore.Li2.Port.Li2.θw n i
        ≤ ∑ b, CatalanCore.Li2.Port.Li2.θw n (CatalanCore.Li2.Port.Li2.slotRank n (f b)) :=
      CatalanCore.Li2.Port.Li2.sum_range_le_of_injective (CatalanCore.Li2.Port.Li2.θw n) (CatalanCore.Li2.Port.Li2.θw_mono n)
        (fun b => CatalanCore.Li2.Port.Li2.slotRank n (f b)) ((CatalanCore.Li2.Port.Li2.slotRank_injective n).comp hf)
    _ ≤ ∑ b, (CatalanCore.Li2.Port.Li2.ωw n (f b) + CatalanCore.Li2.Port.Li2.κw n (f b)) :=
      Finset.sum_le_sum fun b _ => CatalanCore.Li2.Port.Li2.θw_le hn (f b)

theorem parameterQtilde_GV_two (lam : ℚ) (h0 : lam ≠ 0) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG 2 (lam/(1-lam)) 0)
    (hmu : CatalanCore.Li2.Port.Li2.VG 2 lam⁻¹ 1) :
    CatalanCore.Li2.Port.Li2.GV 2 (ParameterFamily.Qtilde lam n)
      ((CatalanCore.Li2.Port.Li2.A2 n : ℚ) - 4 * (n:ℚ) * (Nat.log 2 (7*n-2) : ℚ)) := by
  rw [← CatalanCore.Li2.Port.Li2.θw_sum hn]
  exact parameterQtilde_GV_two_slots hn lam h0 h1 hratio hmu

end MatrixBounds

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameterCst_VG_two
#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameterPoleNode_VG_two
#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameterTailC_VG_two
#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameterKap_GV_two
#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameterQtilde_GV_two

end

section
open Polynomial Filter Topology

namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open CatalanCore.Li2.Port.Unified.ParameterFamily CatalanCore.Li2.Port.Unified.Instances.PosHalf

theorem posHalf_Qtilde_GV_two (n : ℕ) (hn : 1 ≤ n) :
    CatalanCore.Li2.Port.Li2.GV 2 (Instances.PosHalf.Qtilde n)
      ((CatalanCore.Li2.Port.Li2.A2 n : ℚ) - 4 * (n:ℚ) * (Nat.log 2 (7*n-2) : ℚ)) := by
  have hmu : CatalanCore.Li2.Port.Li2.VG 2 lambda⁻¹ 1 := by
    have he : lambda⁻¹ = (2:ℚ) := by norm_num [lambda]
    rw [he]
    right
    have hv : padicValRat 2 (2:ℚ) = 1 := by
      simpa using! (padicValRat.self (p := 2) (by decide))
    rw [hv]
    norm_num
  have hratio : CatalanCore.Li2.Port.Li2.VG 2 (lambda/(1-lambda)) 0 := by
    convert CatalanCore.Li2.Port.Li2.VG.one (p := 2) using 1
    norm_num [lambda]
  simpa only [Instances.PosHalf.Qtilde] using!
    parameterQtilde_GV_two hn lambda lambda_nonzero lambda_ne_one hratio hmu

/-- The primitive scale pays at least the 2-adic ranked-slot valuation. -/
theorem posHalf_dtilde_two_lower (n : ℕ) (hn : 1 ≤ n)
    (hne : Instances.PosHalf.Qtilde n ≠ 0) :
    CatalanCore.Li2.Port.Li2.PrimeSums.twoAdicLowerBound n ≤
      (-padicValRat 2 (dtilde lambda n) : ℚ) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk0, hkval, _⟩ :=
    Qtilde_coeff_valuation_minimum lambda 2 (by simpa only [Instances.PosHalf.Qtilde] using! hne)
  have hcoeff := (posHalf_Qtilde_GV_two n hn) k
  change CatalanCore.Li2.Port.Li2.VG 2 ((ParameterFamily.Qtilde lambda n).coeff k) _ at hcoeff
  rcases hcoeff with hzero | hbound
  · exact (hk0 hzero).elim
  · rw [hkval] at hbound
    simpa only [CatalanCore.Li2.Port.Li2.PrimeSums.twoAdicLowerBound] using! hbound

/-- The exact positive-half 2-adic content estimate, before the Stage0 wrapper. -/
theorem posHalf_two_adic_content_raw :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Instances.PosHalf.Qtilde n ≠ 0 →
        ((8/3:ℝ)*Real.log 2-ε)*(n:ℝ)^2 ≤
          ((-padicValRat 2 (dtilde lambda n) : ℤ) : ℝ) * Real.log 2 := by
  intro ε hε
  have hlim : Tendsto
      (fun n : ℕ => ((CatalanCore.Li2.Port.Li2.PrimeSums.twoAdicLowerBound n : ℝ) * Real.log 2) /
        (n:ℝ)^2) atTop (𝓝 ((8/3:ℝ)*Real.log 2)) := by
    simpa only [div_mul_eq_mul_div] using!
      (CatalanCore.Li2.Port.Li2.PrimeSums.twoAdicLowerBound_tendsto.mul_const (Real.log 2))
  have hlt : ((8/3:ℝ)*Real.log 2-ε) < ((8/3:ℝ)*Real.log 2) :=
    sub_lt_self _ hε
  have he : ∀ᶠ n : ℕ in atTop,
      (8/3:ℝ)*Real.log 2-ε <
        ((CatalanCore.Li2.Port.Li2.PrimeSums.twoAdicLowerBound n : ℝ) * Real.log 2) / (n:ℝ)^2 :=
    hlim.eventually (isOpen_Ioi.mem_nhds hlt)
  filter_upwards [he, eventually_ge_atTop (1:ℕ)] with n hnear hn
  intro hne
  have hv := posHalf_dtilde_two_lower n hn hne
  have hvR : (CatalanCore.Li2.Port.Li2.PrimeSums.twoAdicLowerBound n : ℝ) ≤
      ((-padicValRat 2 (dtilde lambda n) : ℤ) : ℝ) := by
    exact_mod_cast hv
  have hsq : 0 < (n:ℝ)^2 := by
    have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hlog : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  calc
    ((8/3:ℝ)*Real.log 2-ε)*(n:ℝ)^2 ≤
        (((CatalanCore.Li2.Port.Li2.PrimeSums.twoAdicLowerBound n : ℝ) * Real.log 2) /
          (n:ℝ)^2) * (n:ℝ)^2 :=
      mul_le_mul_of_nonneg_right (le_of_lt hnear) (le_of_lt hsq)
    _ = (CatalanCore.Li2.Port.Li2.PrimeSums.twoAdicLowerBound n : ℝ) * Real.log 2 := by
      field_simp [ne_of_gt hsq]
    _ ≤ ((-padicValRat 2 (dtilde lambda n) : ℤ) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hvR hlog

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.posHalf_dtilde_two_lower
#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.posHalf_two_adic_content_raw

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open Polynomial
open scoped BigOperators

/-- A factorial below p is a p-adic unit. -/
lemma parameter_factorial_val_zero (p m : ℕ) [Fact p.Prime] (hm : m < p) :
    padicValRat p ((m.factorial : ℚ)) = 0 := by
  rw [padicValRat.of_nat]
  have h := padicValNat_factorial_mul_add (p := p) (m := 0) hm
  simpa using! h

lemma parameter_factorial_inv_VG (p m : ℕ) [Fact p.Prime] (hm : m < p) :
    CatalanCore.Li2.Port.Li2.VG p ((m.factorial : ℚ)⁻¹) 0 := by
  have hfac : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  simpa using! (CatalanCore.Li2.Port.Li2.VG.inv (p := p) (r := 0) hfac
    (by simp [parameter_factorial_val_zero p m hm]))

lemma parameter_descPochhammer_GV (p m : ℕ) [Fact p.Prime] :
    CatalanCore.Li2.Port.Li2.GV p (descPochhammer ℚ m) 0 := by
  induction m with
  | zero => simpa using! CatalanCore.Li2.Port.Li2.GV.C (p := p) CatalanCore.Li2.Port.Li2.VG.one
  | succ m ih =>
      rw [descPochhammer_succ_right]
      have hlinear : CatalanCore.Li2.Port.Li2.GV p (X - C (m:ℚ)) 0 :=
        CatalanCore.Li2.Port.Li2.GV.X.sub (CatalanCore.Li2.Port.Li2.GV.C (CatalanCore.Li2.Port.Li2.VG.natCast m))
      simpa using! ih.mul hlinear

lemma parameter_binomPoly_GV (p m : ℕ) [Fact p.Prime] (hm : m < p) :
    CatalanCore.Li2.Port.Li2.GV p (CatalanCore.Li2.Port.Li2.binomPoly m) 0 := by
  rw [CatalanCore.Li2.Port.Li2.binomPoly]
  simpa using! (CatalanCore.Li2.Port.Li2.GV.C_mul (parameter_factorial_inv_VG p m hm)
    (parameter_descPochhammer_GV p m))

lemma parameter_D_GV (p m : ℕ) [Fact p.Prime] :
    CatalanCore.Li2.Port.Li2.GV p (CatalanCore.Li2.Port.Li2.D m) 0 := by
  rw [CatalanCore.Li2.Port.Li2.D]
  have h := CatalanCore.Li2.Port.Li2.GV.prod (s := Finset.Icc 1 m)
    (r := fun _ : ℕ => (0:ℚ)) (fun j _ =>
      (CatalanCore.Li2.Port.Li2.GV.X.add (CatalanCore.Li2.Port.Li2.GV.C (CatalanCore.Li2.Port.Li2.VG.natCast j)) :
        CatalanCore.Li2.Port.Li2.GV p (X + C (j:ℚ)) 0))
  simpa using! h

lemma parameter_Sn_GV_large (p n : ℕ) [Fact p.Prime] (hpn : 4*n < p) :
    CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.Sn n) 0 := by
  have hn : n < p := by omega
  rw [CatalanCore.Li2.Port.Li2.Sn, div_eq_mul_inv, ← inv_pow]
  have hnum : CatalanCore.Li2.Port.Li2.VG p (((4*n).factorial : ℚ)) 0 := CatalanCore.Li2.Port.Li2.VG.natCast _
  have hden := (parameter_factorial_inv_VG p n hn).pow 3
  simpa using! hnum.mul hden

/-- Every coefficient of the actual binomial Gram numerator is p-integral
when p exceeds all poles. -/
theorem parameter_gramNum_GV_large (p n a b : ℕ) [Fact p.Prime]
    (hpn : 4*n < p) (ha : a < 2*n) (hb : b < 2*n) :
    CatalanCore.Li2.Port.Li2.GV p (CatalanCore.Li2.Port.Li2.gramNum n a b) 0 := by
  have hap : a < p := by omega
  have hbp : b < p := by omega
  rw [CatalanCore.Li2.Port.Li2.gramNum]
  have h := (((CatalanCore.Li2.Port.Li2.GV.C (parameter_Sn_GV_large p n hpn)).mul
    ((parameter_D_GV p n).pow 3)).mul
      (parameter_binomPoly_GV p a hap)).mul
      (parameter_binomPoly_GV p b hbp)
  simpa using! h

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameter_gramNum_GV_large

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open Polynomial

private def pIntegralSubmodule (p : ℕ) [Fact p.Prime] : Submodule ℤ ℚ where
  carrier := {q | CatalanCore.Li2.Port.Li2.VG p q 0}
  zero_mem' := CatalanCore.Li2.Port.Li2.VG.zero 0
  add_mem' := by
    intro a b ha hb
    exact CatalanCore.Li2.Port.Li2.VG.add ha hb
  smul_mem' := by
    intro c q hq
    change CatalanCore.Li2.Port.Li2.VG p ((c:ℚ)*q) 0
    simpa using! (CatalanCore.Li2.Port.Li2.VG.intCast (p := p) c).mul hq

/-- Polynomial long division by a monic polynomial preserves p-integral
coefficients. This is the coefficient-level algebra, independent of the CatalanCore.Li2.Port.Li2
numerator. -/
theorem parameter_GV_divByMonic (p : ℕ) [Fact p.Prime]
    {F G : ℚ[X]} (hF : CatalanCore.Li2.Port.Li2.GV p F 0) (hG : CatalanCore.Li2.Port.Li2.GV p G 0) :
    CatalanCore.Li2.Port.Li2.GV p (F /ₘ G) 0 := by
  let M := pIntegralSubmodule p
  have hOne : (1:ℚ) ∈ M := by
    change CatalanCore.Li2.Port.Li2.VG p 1 0
    exact CatalanCore.Li2.Port.Li2.VG.one
  have hMmul : M * M ≤ M := by
    apply Submodule.mul_le.mpr
    intro a ha b hb
    dsimp [M, pIntegralSubmodule] at ha hb ⊢
    simpa using! (ha.mul hb)
  have hMpow (k : ℕ) : M^k ≤ M := by
    induction k with
    | zero => simpa using! (Submodule.one_le.mpr hOne)
    | succ k ih =>
        rw [pow_succ]
        exact le_trans (mul_le_mul' ih le_rfl) hMmul
  have hMpowMul : M^F.natDegree * M ≤ M :=
    le_trans (mul_le_mul' (hMpow F.natDegree) le_rfl) hMmul
  intro k
  exact hMpowMul (Polynomial.coeff_divByMonic_mem_pow_natDegree_mul
    F G M hF hOne M hG hOne k)

theorem parameter_gramQuot_GV_large (p n a b : ℕ) [Fact p.Prime]
    (hpn : 4*n < p) (ha : a < 2*n) (hb : b < 2*n) :
    CatalanCore.Li2.Port.Li2.GV p (CatalanCore.Li2.Port.Li2.gramNum n a b /ₘ CatalanCore.Li2.Port.Li2.D (4*n)) 0 := by
  exact parameter_GV_divByMonic p
    (parameter_gramNum_GV_large p n a b hpn ha hb)
    (parameter_D_GV p (4*n))

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameter_GV_divByMonic
#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameter_gramQuot_GV_large

end


end
