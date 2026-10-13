module
public import CatalanMeasure.Parametric.SparseCoreCombinations
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem sparse_combination_raw_relation {P : Parameters} {N p j : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hN : 0<N) (hlarge : 1000000 ≤ p) (hHsq : P.H N<p^2)
    (hcut : 3*p+P.g N ≤ P.C N) (hhi : P.H N ≤ 4*p) (hH : 4<P.H N)
    (hjb : P.b N ≤ j) (hjL : j<P.L N)
    (c : Fin (P.g N) → ZMod p) (hc : sparseBadCoefficientMap P N p c=0)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    (∑ d,c d*sparseRawResidueDelta P p N 2 (d.val+1) j z)=
      (292/59:ZMod p)*(∑ d,c d*sparseRawResidueDelta P p N 1 (d.val+1) j z)-
      (3281/177:ZMod p)*(∑ d,c d*sparseRawResidueDelta P p N 0 (d.val+1) j z) :=by
  have hp2 : p≠2 :=by omega
  let Q :=polynomialCombination (sparseCoreFamily P N p) c
  let Qlo :=polynomialCombination (sparseLowCoreFamily P N p) c
  let F :=fun k =>polynomialCombination (sparsePFamily P N p k) c
  let G :=fun k =>polynomialCombination (sparseDFamily P N p k) c
  have hid :=sparseCombination_identities hp2 hcut c
  have hsupp :=sparseCombination_support hcut hhi c hc
  have hpos : Q.coeff (2*p+j%p)≠0 → j/p=1 ∨ j/p=2 :=by
    intro hq
    have hh :=hsupp.2 (2*p+j%p) hq
    have hdiv :=Nat.mod_add_div j p
    have hC : P.C N=P.L N+P.g N :=rfl
    have hpL : p ≤ P.L N :=by omega
    have hsub :=Nat.sub_add_cancel hpL
    by_cases hz : j/p=0
    · rw [hz,mul_zero,add_zero] at hdiv
      omega
    · have hqsmall : j/p<3 :=by
        by_contra h
        have hm :=Nat.mul_le_mul_left p (show 3 ≤ j/p by omega)
        omega
      have hqpos : 0<j/p :=Nat.pos_of_ne_zero hz
      omega
  have hpair :=supportedDigitPair_relation hlarge (F 0) (G 0) (F 1) (G 1) (F 2) (G 2) Q Qlo
    hid.2.1 hid.2.2.1 hid.2.2.2.1 hid.2.2.2.2.1 hid.2.2.2.2.2.1 hid.2.2.2.2.2.2
    hid.1 hsupp.1 hH hpos
  have hjH : j<P.H N :=by unfold Parameters.H Parameters.C; omega
  have hactual (k : ℕ) : primeDigitPair (P.H N) p j (F k) (G k)=
      ∑ d,c d*sparseRawResidueDelta P p N k (d.val+1) j z :=by
    dsimp only [F,G]
    rw [primeDigitPair_combination]
    apply Finset.sum_congr rfl
    intro d hd
    exact congrArg (fun u : ZMod p =>c d*u)
      (sparseRawResidueDelta_as_pair hAdm hN hp2 hHsq hjH z hzp).symm
  rw [hactual 2,hactual 1,hactual 0] at hpair
  exact hpair

theorem sparse_combination_filtered_relation {P : Parameters} {N p k : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hN : 0<N) (hlarge : 1000000 ≤ p) (hHsq : P.H N<p^2)
    (hcut : 3*p+P.g N ≤ P.C N) (hhi : P.H N ≤ 4*p) (hH : 4<P.H N) (hk : k<P.n N)
    (c : Fin (P.g N) → ZMod p) (hc : sparseBadCoefficientMap P N p c=0)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    (∑ d,c d*sparseFilteredResidueDelta P p N 2 (d.val+1) k z)=
      (292/59:ZMod p)*(∑ d,c d*sparseFilteredResidueDelta P p N 1 (d.val+1) k z)-
      (3281/177:ZMod p)*(∑ d,c d*sparseFilteredResidueDelta P p N 0 (d.val+1) k z) :=by
  have hp2 : p≠2 :=by omega
  have hsum (a : ℕ) : (∑ d,c d*sparseFilteredResidueDelta P p N a (d.val+1) k z)=
      ∑ v ∈ Finset.range (P.q N+1),palindromicRatResidue p (filterCoeffRat P N v)*
        (∑ d,c d*sparseRawResidueDelta P p N a (d.val+1) (P.b N+k+v) z) :=by
    simp_rw [sparseFilteredResidueDelta_eq_sum hp2 hHsq hk z hzp,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hsum 2,hsum 1,hsum 0,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have hv' : v ≤ P.q N :=by have :=Finset.mem_range.mp hv; omega
  rw [sparse_combination_raw_relation hAdm hN hlarge hHsq hcut hhi hH
    (rawColumn_ge_b P N k v) (rawColumn_lt_L hk hv') c hc z hzp]
  ring

end
end CatalanMeasure.Parametric
