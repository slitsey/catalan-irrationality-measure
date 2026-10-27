module
public import CatalanCore.Uniform.NV.Corank
public import CatalanCore.Uniform.NV.KernelDimension
public import CatalanCore.Linalg.PrincipalDeletion.Rescue
@[expose] public section
open Polynomial Finset Module
open CatalanCore.Arith.Hybrid.FiniteFieldCorank
open CatalanCore.Rect.CharZeroNV
namespace CatalanCore.Uniform.NV
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- Visibility on arbitrary common nodes, using their actual jet equations. -/
theorem pair_eq_zero_of_common_values (L d c m : ℕ) (D A p q : K[X]) (f tau : K → K)
    (data : StepData L D A f tau) (a : K) (pole : IsolatedStepPole (L:K) a D A)
    (hd : 2 ≤ d) (hD : D.natDegree ≤ d) (hA : A.natDegree ≤ d-2)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z) (hC : C.card = c) (hZ : Z.card = c+2*m)
    (hn : 1 ≤ c+m) (hvis : componentCount Z L+d ≤ c+3)
    (hp : p.natDegree ≤ c+m-1) (hq : q.natDegree ≤ c+m-1)
    (hint : Hermite (fieldNodes Z) (fieldNodes C) f tau p q)
    (hz : ∀ x ∈ fieldNodes C, p.eval x = 0) : p = 0 := by
  let nodes : Finset K := fieldNodes C
  let DC := rootProduct nodes
  have hDC : DC.Monic := rootProduct_monic nodes
  have hdDC : DC.natDegree = c := by
    change (rootProduct nodes).natDegree = c
    rw [natDegree_rootProduct,card_fieldNodes,hC]
  have hzq : ∀ x ∈ nodes, q.eval x = 0 := by
    intro x hx
    rw [hint.value x (fieldNodes_mono hCZ hx),hz x hx,mul_zero]
  have hdp : DC ∣ p := by
    simpa using rootProduct_pow_dvd nodes 1 p (fun x hx => by
      simpa using (dvd_iff_isRoot.mpr (hz x hx) : X-Polynomial.C x ∣ p))
  have hdq : DC ∣ q := by
    simpa using rootProduct_pow_dvd nodes 1 q (fun x hx => by
      simpa using (dvd_iff_isRoot.mpr (hzq x hx) : X-Polynomial.C x ∣ q))
  obtain ⟨p0,hpf⟩ := hdp
  obtain ⟨q0,hqf⟩ := hdq
  by_contra hp0
  have hpn : p0 ≠ 0 := by intro h;simp [hpf,h] at hp0
  have hpm := natDegree_mul hDC.ne_zero hpn
  rw [← hpf,hdDC] at hpm
  have hm : 1 ≤ m := by omega
  have hpd : p0.natDegree ≤ m-1 := by omega
  have hqd : q0.natDegree ≤ m-1 := by
    by_cases hq0 : q0 = 0
    · simp [hq0]
    have hqm := natDegree_mul hDC.ne_zero hq0
    rw [← hqf,hdDC] at hqm
    omega
  have hvalues : ∀ x ∈ fieldNodes Z, q0.eval x = f x*p0.eval x := by
    intro x hx
    by_cases hxc : x ∈ nodes
    · have heD : DC.eval x = 0 := by
        change (rootProduct nodes).eval x = 0
        rw [rootProduct_factor nodes hxc]
        simp
      have heD' : DC.derivative.eval x ≠ 0 := by
        change (rootProduct nodes).derivative.eval x ≠ 0
        rw [rootProduct_factor nodes hxc,derivative_mul]
        simpa using punctured_eval_ne_zero nodes x
      have hj := hint.jet x hxc
      rw [hqf,hpf] at hj
      simp only [derivative_mul,eval_add,eval_mul,heD,zero_mul,add_zero] at hj
      apply mul_left_cancel₀ heD'
      linear_combination hj
    · have heD : DC.eval x ≠ 0 := rootProduct_eval_ne_zero nodes x hxc
      have hv := hint.value x hx
      rw [hqf,hpf,eval_mul,eval_mul] at hv
      apply mul_left_cancel₀ heD
      linear_combination hv
  have hshort := no_short_step_pair L d (m-1) D A p0 q0 f tau data a pole hd hD hA Z ∅
    (by simp) ⟨hvalues,by simp [fieldNodes]⟩ hpd hqd (by
      have hG := card_edges_add_components Z L
      have hempty : componentCount (∅ : Finset ℕ) L = 0 := by simp [componentCount,stepEnds]
      simp only [card_empty,hempty,Nat.sub_self,add_zero]
      omega)
  exact hpn hshort

/-- The actual common-coordinate evaluation map detects the whole pair space. -/
theorem commonEval_injective (G : NodeGeometry (K := K))
    (L d c m : ℕ) (D A : K[X]) (f tau : K → K)
    (data : StepData L D A f tau) (a : K) (pole : IsolatedStepPole (L:K) a D A)
    (hd : 2 ≤ d) (hD : D.natDegree ≤ d) (hA : A.natDegree ≤ d-2)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z) (hC : C.card = c) (hZ : Z.card = c+2*m)
    (hunion : G.rows ∪ G.cols = fieldNodes Z) (hinter : G.rows ∩ G.cols = fieldNodes C)
    (hrows : G.rows.card = c+m) (hn : 1 ≤ c+m)
    (hvis : componentCount Z L+d ≤ c+3) :
    Function.Injective (G.commonEval f tau) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hp0 : v.val.1 = 0 := pair_eq_zero_of_common_values L d c m D A v.val.1 v.val.2 f tau
    data a pole hd hD hA Z C hCZ hC hZ hn hvis
    (by simpa [hrows] using v.property.1) (by simpa [hrows] using v.property.2.1)
    (by simpa [hunion,hinter] using v.property.2.2) (by
      intro x hx
      exact congrFun hv ⟨x,hinter.symm ▸ hx⟩)
  have hsize : G.rows.card-1 < (G.rows ∪ G.cols).card := by
    have hh := Finset.card_le_card (Finset.subset_union_left : G.rows ⊆ G.rows ∪ G.cols)
    omega
  exact pairP_injective (G.rows ∪ G.cols) (G.rows ∩ G.cols) f tau _ hsize
    (show pairP _ _ _ _ _ v = pairP _ _ _ _ _ 0 from (by change v.val.1 = 0; exact hp0))

/-- Visibility produces a nonzero actual same-index common-node complement.
Both kernel coordinate families are the same evaluations times nonzero punctured
node factors; the existing complementary-minor theorem supplies the determinant. -/
theorem step_component_nv (G : NodeGeometry (K := K))
    (L d c m : ℕ) (D A : K[X]) (f tau : K → K)
    (data : StepData L D A f tau) (a : K) (pole : IsolatedStepPole (L:K) a D A)
    (hd : 2 ≤ d) (hD : D.natDegree ≤ d) (hA : A.natDegree ≤ d-2)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z) (hC : C.card = c) (hZ : Z.card = c+2*m)
    (hunion : G.rows ∪ G.cols = fieldNodes Z) (hinter : G.rows ∩ G.cols = fieldNodes C)
    (hrows : G.rows.card = c+m) (hn : 1 ≤ c+m)
    (hvis : componentCount Z L+d ≤ c+3) :
    ∃ s : Finset (G.rows ∩ G.cols : Finset K),
      s.card ≤ (d+componentCount Z L+componentCount C L-2)/2 ∧
      ((G.matrix f tau).submatrix
        (Subtype.val : {i // i ∉ s.image G.common} → G.rows) Subtype.val).det ≠ 0 := by
  let P := G.pairs f tau
  have hE := commonEval_injective G L d c m D A f tau data a pole hd hD hA
    Z C hCZ hC hZ hunion hinter hrows hn hvis
  letI : FiniteDimensional K P := FiniteDimensional.of_injective (G.commonEval f tau) hE
  have hdim : finrank K P ≤ (d+componentCount Z L+componentCount C L-2)/2 := by
    change finrank K (pairSpace (G.rows ∪ G.cols) (G.rows ∩ G.cols) f tau (G.rows.card-1)) ≤ _
    rw [hunion,hinter,hrows]
    apply step_pairSpace_finrank_bound L d (c+m) D A f tau data a pole hd hD hA Z C hCZ hn
    omega
  obtain ⟨s,hs,hdet⟩ := CatalanCore.Linalg.PrincipalDeletion.exists_principal_compl_ne_zero
    (G.matrix f tau) G.common G.common_injective
    (G.rightCoords f tau) (G.leftCoords f tau) (G.commonEval f tau)
    (fun i => ((punctured G.cols i.val).eval i.val)⁻¹)
    (fun i => ((punctured G.rows i.val).eval i.val)⁻¹)
    (fun i => inv_ne_zero (punctured_eval_ne_zero G.cols i.val))
    (fun i => inv_ne_zero (punctured_eval_ne_zero G.rows i.val))
    (G.rightCoords_onto_kernel f tau)
    (G.leftCoords_in_kernel f tau (by omega))
    (G.rightCoords_common f tau) (G.leftCoords_common f tau) hE
  exact ⟨s,hs ▸ hdim,hdet⟩

/-- Pure complementary-minor assembly, with the deletion size equal to the
actual corank. The visibility premise is supplied above by the step proof. -/
theorem common_deletion_exact (G : NodeGeometry (K := K)) (f tau : K → K)
    (hn : 1 ≤ G.rows.card) (hE : Function.Injective (G.commonEval f tau)) :
    ∃ s : Finset (G.rows ∩ G.cols : Finset K),
      s.card = finrank K (LinearMap.ker (G.matrix f tau).mulVecLin) ∧
      ((G.matrix f tau).submatrix
        (Subtype.val : {i // i ∉ s.image G.common} → G.rows) Subtype.val).det ≠ 0 := by
  letI : FiniteDimensional K (G.pairs f tau) := FiniteDimensional.of_injective (G.commonEval f tau) hE
  obtain ⟨s,hs,hdet⟩ := CatalanCore.Linalg.PrincipalDeletion.exists_principal_compl_ne_zero
    (G.matrix f tau) G.common G.common_injective
    (G.rightCoords f tau) (G.leftCoords f tau) (G.commonEval f tau)
    (fun i => ((punctured G.cols i.val).eval i.val)⁻¹)
    (fun i => ((punctured G.rows i.val).eval i.val)⁻¹)
    (fun i => inv_ne_zero (punctured_eval_ne_zero G.cols i.val))
    (fun i => inv_ne_zero (punctured_eval_ne_zero G.rows i.val))
    (G.rightCoords_onto_kernel f tau) (G.leftCoords_in_kernel f tau hn)
    (G.rightCoords_common f tau) (G.leftCoords_common f tau) hE
  exact ⟨s,hs.trans (G.pairSpace_finrank_eq_corank f tau hn),hdet⟩

#print axioms step_component_nv
#print axioms common_deletion_exact
end CatalanCore.Uniform.NV





