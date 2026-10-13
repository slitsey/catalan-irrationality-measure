module
public import CatalanMeasure.Parametric.SparseCombinationRelation
public import CatalanMeasure.Parametric.FiveSourceEmbedding
public import CatalanMeasure.Parametric.SparseModeGeometry
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix OAI.InternalCatalan
noncomputable section

theorem sparse_combination_residue_rank {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hN : 0<N) (hlarge : 1000000 ≤ p) (hHsq : P.H N<p^2)
    (hcut : 3*p+P.g N ≤ P.C N) (hhi : P.H N ≤ 4*p) (hH : 4<P.H N)
    (hgp : P.g N<p) (hfit : P.g N+2*p+P.g N<P.n N)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    let M : Matrix (Fin (P.n N)) (Fin (P.n N)) ℚ :=Matrix.of fun i j =>filteredEntryRat P z N i.val j.val
    (scaledResidueMatrix (p:=p) M).rank+(P.g N-(P.H N-3*p-P.b N)) ≤ P.n N :=by
  classical
  let M : Matrix (Fin (P.n N)) (Fin (P.n N)) ℚ :=Matrix.of fun i j =>filteredEntryRat P z N i.val j.val
  let R :=scaledResidueMatrix (p:=p) M
  let t : Fin (P.g N) → Fin (P.n N) :=fun d =>⟨P.g N+2*p+(d.val+1),by have :=d.isLt; omega⟩
  let s2 : Fin (P.g N) → Fin (P.n N) :=fun d =>boundedSource (t d) (P.g N+2*p-(d.val+1))
  let s1p : Fin (P.g N) → Fin (P.n N) :=fun d =>boundedSource (t d) (P.g N+p+(d.val+1))
  let s1m : Fin (P.g N) → Fin (P.n N) :=fun d =>boundedSource (t d) (P.g N+p-(d.val+1))
  let s0p : Fin (P.g N) → Fin (P.n N) :=fun d =>boundedSource (t d) (P.g N+(d.val+1))
  let s0m : Fin (P.g N) → Fin (P.n N) :=fun d =>boundedSource (t d) (P.g N-(d.val+1))
  have htval (d : Fin (P.g N)) : (t d).val=P.g N+2*p+(d.val+1) :=rfl
  have hsval (d : Fin (P.g N)) :
      (s2 d).val=P.g N+2*p-(d.val+1) ∧ (s1p d).val=P.g N+p+(d.val+1) ∧
      (s1m d).val=P.g N+p-(d.val+1) ∧ (s0p d).val=P.g N+(d.val+1) ∧ (s0m d).val=P.g N-(d.val+1) :=by
    refine ⟨?_,?_,?_,?_,?_⟩ <;> apply boundedSource_val <;> have :=d.isLt <;> omega
  have ht : Function.Injective t :=by
    intro d e heq
    apply Fin.ext
    have hh :=congrArg Fin.val heq
    rw [htval,htval] at hh
    omega
  have hsep (d e : Fin (P.g N)) :
      t d≠s2 e ∧ t d≠s1p e ∧ t d≠s1m e ∧ t d≠s0p e ∧ t d≠s0m e :=by
    have hv :=hsval e
    refine ⟨?_,?_,?_,?_,?_⟩ <;> intro heq <;> have hh :=congrArg Fin.val heq
    all_goals simp only [htval,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2] at hh
    all_goals have :=e.isLt
    all_goals omega
  let J :=fiveSourceEmbedding t s2 s1p s1m s0p s0m (292/59:ZMod p) (3281/177:ZMod p)
  have hJ : Function.Injective J :=fiveSourceEmbedding_injective _ _ _ _ _ _ _ _ ht hsep
  have hR (i j : Fin (P.n N)) : R i j=palindromicRatResidue p ((p:ℚ)^2*filteredEntryRat P z N i.val j.val) :=rfl
  have hker (c : Fin (P.g N) → ZMod p) (hc : sparseBadCoefficientMap P N p c=0) :
      R.transpose.mulVecLin (J c)=0 :=by
    funext j
    change R.transpose.mulVecLin (fiveSourceEmbedding t s2 s1p s1m s0p s0m
      (292/59:ZMod p) (3281/177:ZMod p) c) j=0
    rw [fiveSourceEmbedding_mulVec]
    have hrel :=sparse_combination_filtered_relation hAdm hN hlarge hHsq hcut hhi hH j.isLt c hc z hzp
    have hz :=weighted_sum_relation_zero
      (fun d =>sparseFilteredResidueDelta P p N 2 (d.val+1) j.val z)
      (fun d =>sparseFilteredResidueDelta P p N 1 (d.val+1) j.val z)
      (fun d =>sparseFilteredResidueDelta P p N 0 (d.val+1) j.val z)
      c (292/59:ZMod p) (3281/177:ZMod p) hrel
    have he (d : Fin (P.g N)) :
        R (t d) j-R (s2 d) j-(292/59:ZMod p)*(R (s1p d) j-R (s1m d) j)+
          (3281/177:ZMod p)*(R (s0p d) j-R (s0m d) j)=
        sparseFilteredResidueDelta P p N 2 (d.val+1) j.val z-
          (292/59:ZMod p)*sparseFilteredResidueDelta P p N 1 (d.val+1) j.val z+
          (3281/177:ZMod p)*sparseFilteredResidueDelta P p N 0 (d.val+1) j.val z :=by
      have hv :=hsval d
      simp only [hR,htval,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2,
        sparseFilteredResidueDelta,one_mul,zero_mul,add_zero]
    simpa only [he] using hz
  exact matrix_rank_le_of_kernel_embedding R (sparseBadCoefficientMap P N p) J hJ hker

theorem sparse_combination_determinant_valuation {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hN : 0<N) (hlarge : 1000000 ≤ p) (hHsq : P.H N<p^2)
    (hcut : 3*p+P.g N ≤ P.C N) (hhi : P.H N ≤ 4*p) (hH : 4<P.H N)
    (hgp : P.g N<p) (hfit : P.g N+2*p+P.g N<P.n N)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    -((2*P.n N-(P.g N-(P.H N-3*p-P.b N)):ℕ):ℤ) ≤ padicValRat p (determinantRat P z N) :=by
  let M : Matrix (Fin (P.n N)) (Fin (P.n N)) ℚ :=Matrix.of fun i j =>filteredEntryRat P z N i.val j.val
  have hh :=sparse_combination_residue_rank hAdm hN hlarge hHsq hcut hhi hH hgp hfit z hzp
  have hM (i j : Fin (P.n N)) : (((p:ℚ)^2*M i j).den : ZMod p)≠0 :=by
    exact (filteredEntry_scaled_residue_sum_general (by omega : p≠2) hHsq j.isLt z hzp).1
  have he : P.g N-(P.H N-3*p-P.b N) ≤ P.n N :=by omega
  have hr : (scaledResidueMatrix (p:=p) M).rank ≤ P.n N-(P.g N-(P.H N-3*p-P.b N)) :=by
    change (scaledResidueMatrix (p:=p) M).rank+(P.g N-(P.H N-3*p-P.b N)) ≤ P.n N at hh
    omega
  exact residue_rank_valuation_lower M hM he hr

end
end CatalanMeasure.Parametric
