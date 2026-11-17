/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Positive/Packed/P005.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P004
public import CatalanCore.Li2.Port.Unified.Modular.Base.PrimeOriginalBasis

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial CatalanCore.Li2.Port.Li2
open scoped BigOperators
namespace CatalanCore.Li2.Port.Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalJetSize_add_delta (n : ℕ) (hpn : p ≤ n) :
    generalJetSize n p +
      CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.delta n p = 2 * n := by
  simpa [generalJetSize] using
    (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.exact_counts n p
      (Fact.out : p.Prime) hpn).2

theorem general_delta_le_one (n : ℕ) (hpn : p ≤ n) :
    CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.delta n p ≤ 1 :=
  (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.exact_counts n p
    (Fact.out : p.Prime) hpn).1

def generalAppendedBasis (n : ℕ) : Fin (generalJetSize n p + 1) → ℤ[X] :=
  Fin.cases
    (CatalanCore.Li2.Port.Li2.fullClassProduct (CatalanCore.Li2.Port.Li2.primeCenter p)
      (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.multiplicity n p))
    (generalIndexedJetPoly n p)

theorem generalAppendedBasis_independent (n : ℕ)
    (v : Fin (generalJetSize n p + 1) → ZMod p)
    (hv : (∑ i, C (v i) *
      (generalAppendedBasis n i).map (Int.castRingHom (ZMod p))) = 0) :
    v = 0 := by
  refine CatalanCore.Li2.Port.Li2.polynomial_family_independent_append
    (fun i => (generalIndexedJetPoly n p i).map (Int.castRingHom (ZMod p)))
    (fun i => natDegree_map_le.trans_lt (generalIndexedJetPoly_natDegree_lt n p i))
    (generalIndexedJetPoly_independent n p)
    ((CatalanCore.Li2.Port.Li2.fullClassProduct (CatalanCore.Li2.Port.Li2.primeCenter p)
      (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.multiplicity n p)).map
        (Int.castRingHom (ZMod p)))
    ((CatalanCore.Li2.Port.Li2.fullClassProduct_monic (CatalanCore.Li2.Port.Li2.primeCenter p)
      (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.multiplicity n p)).map _)
    ?_ v ?_
  · rw [(CatalanCore.Li2.Port.Li2.fullClassProduct_monic (CatalanCore.Li2.Port.Li2.primeCenter p)
      (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.multiplicity n p)).natDegree_map,
      CatalanCore.Li2.Port.Li2.fullClassProduct_natDegree]
    rfl
  · convert hv using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; rfl

noncomputable def generalOriginalBasis (n : ℕ) (hpn : p ≤ n) :
    Fin (2 * n) → ℤ[X] := by
  by_cases hd : CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.delta n p = 0
  · exact fun i => generalIndexedJetPoly n p
      (Fin.cast (by have := generalJetSize_add_delta n hpn; omega) i)
  · have hd1 : CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.delta n p = 1 := by
      have := general_delta_le_one n hpn
      omega
    exact fun i => generalAppendedBasis (p := p) n
      (Fin.cast (by have := generalJetSize_add_delta n hpn; omega) i)

theorem generalOriginalBasis_natDegree_lt (n : ℕ) (hpn : p ≤ n)
    (i : Fin (2 * n)) :
    (generalOriginalBasis n hpn i).natDegree < 2 * n := by
  unfold generalOriginalBasis
  split
  · rename_i hd
    dsimp only
    have hdeg := generalIndexedJetPoly_natDegree_lt n p
      (Fin.cast (by have := generalJetSize_add_delta n hpn; omega) i)
    have hsize := generalJetSize_add_delta n hpn
    omega
  · rename_i hd
    have hd1 : CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.delta n p = 1 := by
      have := general_delta_le_one n hpn
      omega
    have hsize : generalJetSize n p + 1 = 2 * n := by
      have := generalJetSize_add_delta n hpn
      omega
    dsimp only
    let j : Fin (generalJetSize n p + 1) := Fin.cast hsize.symm i
    change ((Fin.cases
      (CatalanCore.Li2.Port.Li2.fullClassProduct (CatalanCore.Li2.Port.Li2.primeCenter p)
        (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.multiplicity n p))
      (generalIndexedJetPoly n p) :
        Fin (generalJetSize n p + 1) → ℤ[X]) j).natDegree < 2 * n
    rw [← hsize]
    refine Fin.cases ?_ ?_ j
    · simpa only [Function.comp_apply, Fin.cases_zero,
        CatalanCore.Li2.Port.Li2.fullClassProduct_natDegree] using!
        (Nat.lt_succ_self (generalJetSize n p))
    · intro k
      simpa only [Function.comp_apply, Fin.cases_succ] using
        (generalIndexedJetPoly_natDegree_lt n p k).trans (Nat.lt_succ_self _)

theorem generalOriginalBasis_independent (n : ℕ) (hpn : p ≤ n)
    (v : Fin (2 * n) → ZMod p)
    (hv : (∑ i, C (v i) *
      (generalOriginalBasis n hpn i).map (Int.castRingHom (ZMod p))) = 0) :
    v = 0 := by
  by_cases hd : CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.delta n p = 0
  · have hsize : 2 * n = generalJetSize n p := by
      have := generalJetSize_add_delta n hpn
      omega
    refine CatalanCore.Li2.Port.Li2.polynomial_family_independent_reindex
      (finCongr hsize)
      (fun i => (generalIndexedJetPoly n p i).map (Int.castRingHom (ZMod p)))
      (generalIndexedJetPoly_independent n p) v ?_
    simpa only [generalOriginalBasis, dif_pos hd] using! hv
  · have hd1 : CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.delta n p = 1 := by
      have := general_delta_le_one n hpn
      omega
    have hsize : 2 * n = generalJetSize n p + 1 := by
      have := generalJetSize_add_delta n hpn
      omega
    refine CatalanCore.Li2.Port.Li2.polynomial_family_independent_reindex
      (finCongr hsize)
      (fun i => (generalAppendedBasis (p := p) n i).map (Int.castRingHom (ZMod p)))
      (generalAppendedBasis_independent n) v ?_
    simpa only [generalOriginalBasis, dif_neg hd] using! hv

theorem generalOriginalBasis_det_unit (n : ℕ) (hpn : p ≤ n) :
    (CatalanCore.Li2.Port.Li2.coeffMat fun i =>
      (generalOriginalBasis n hpn i).map (Int.castRingHom ℚ)).det ≠ 0 ∧
    padicValRat p (CatalanCore.Li2.Port.Li2.coeffMat fun i =>
      (generalOriginalBasis n hpn i).map (Int.castRingHom ℚ)).det = 0 :=
  CatalanCore.Li2.Port.Li2.coeffMat_det_unit_of_independent _
    (generalOriginalBasis_natDegree_lt n hpn)
    (generalOriginalBasis_independent n hpn)

#print axioms generalJetSize_add_delta
#print axioms generalOriginalBasis_natDegree_lt
#print axioms generalOriginalBasis_independent
#print axioms generalOriginalBasis_det_unit

end
end CatalanCore.Li2.Port.Unified.Proofs.Hermite

end


end
