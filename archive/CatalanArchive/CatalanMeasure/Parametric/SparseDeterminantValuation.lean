module
public import CatalanArchive.CatalanMeasure.Parametric.SparseModeGeometry
public import CatalanArchive.CatalanMeasure.Parametric.FiveSourceElimination
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix Finset OAI.InternalCatalan
noncomputable section

/-- Each admissible sparse mode saves a prime factor in the actual determinant.
No rank or nonvanishing assumption is added. -/
theorem sparse_determinant_valuation {P : Parameters} {p N e : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hN : 0<N) (hlarge : 1000000 ≤ p) (hHsq : P.H N<p^2)
    (heg : e ≤ P.g N) (hcut : 3*p+e ≤ P.C N) (hfit : P.g N+2*p+e<P.n N)
    (hhi : P.H N ≤ 4*p) (hH : 4<P.H N) (hwindow : P.H N ≤ 3*p+P.b N)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    -((2*P.n N-e:ℕ):ℤ) ≤ padicValRat p (determinantRat P z N) := by
  classical
  let S :=sparseTargetRows (P.n N) (P.g N) p e
  let d : Fin (P.n N) → ℕ :=sparseMode (P.g N) p
  let s2 : Fin (P.n N) → Fin (P.n N) :=fun i =>boundedSource i (P.g N+2*p-d i)
  let s1p : Fin (P.n N) → Fin (P.n N) :=fun i =>boundedSource i (P.g N+p+d i)
  let s1m : Fin (P.n N) → Fin (P.n N) :=fun i =>boundedSource i (P.g N+p-d i)
  let s0p : Fin (P.n N) → Fin (P.n N) :=fun i =>boundedSource i (P.g N+d i)
  let s0m : Fin (P.n N) → Fin (P.n N) :=fun i =>boundedSource i (P.g N-d i)
  have hsvals (i : Fin (P.n N)) (hi : i∈S) :
      (s2 i).val=P.g N+2*p-d i ∧ (s1p i).val=P.g N+p+d i ∧
      (s1m i).val=P.g N+p-d i ∧ (s0p i).val=P.g N+d i ∧ (s0m i).val=P.g N-d i :=by
    have hh :=sparseMode_sources_below hp.out.pos hi
    exact ⟨boundedSource_val i (hh.1.trans i.isLt),
      boundedSource_val i (hh.2.1.trans i.isLt),
      boundedSource_val i (hh.2.2.1.trans i.isLt),
      boundedSource_val i (hh.2.2.2.1.trans i.isLt),
      boundedSource_val i (hh.2.2.2.2.trans i.isLt)⟩
  have hs (i : Fin (P.n N)) (hi : i∈S) :
      s2 i < i ∧ s1p i < i ∧ s1m i < i ∧ s0p i < i ∧ s0m i < i :=by
    have hh :=sparseMode_sources_below hp.out.pos hi
    have hv :=hsvals i hi
    simpa only [Fin.lt_def,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2] using hh
  have hcast (m : ℕ) (hm0 : 0<m) (hm : m<p) : (m:ZMod p)≠0 :=by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hm0 hm) ((ZMod.natCast_eq_zero_iff m p).mp hz)
  have ha :=nat_fraction_reduced_residue (p:=p) 292 59 (hcast 59 (by decide) (by omega))
  have hb :=nat_fraction_reduced_residue (p:=p) 3281 177 (hcast 177 (by decide) (by omega))
  let M : Matrix (Fin (P.n N)) (Fin (P.n N)) ℚ :=Matrix.of fun i j =>filteredEntryRat P z N i.val j.val
  have hM (i j : Fin (P.n N)) : (((p:ℚ)^2*M i j).den : ZMod p)≠0 :=by
    exact (filteredEntry_scaled_residue_sum_general (by omega : p≠2) hHsq j.isLt z hzp).1
  have hrel (i : Fin (P.n N)) (hi : i∈S) (j : Fin (P.n N)) :
      palindromicRatResidue p ((p:ℚ)^2*M i j)-palindromicRatResidue p ((p:ℚ)^2*M (s2 i) j)=
      palindromicRatResidue p (292/59)*(palindromicRatResidue p ((p:ℚ)^2*M (s1p i) j)-
        palindromicRatResidue p ((p:ℚ)^2*M (s1m i) j))-
      palindromicRatResidue p (3281/177)*(palindromicRatResidue p ((p:ℚ)^2*M (s0p i) j)-
        palindromicRatResidue p ((p:ℚ)^2*M (s0m i) j)) :=by
    have hd :=sparseMode_bounds hi
    have hvals :=hsvals i hi
    have hrow :=sparse_filtered_residue_relation hAdm hN hlarge hHsq hd.1
      (hd.2.1.trans heg) (show 3*p+d i ≤ P.C N by change 3*p+sparseMode (P.g N) p i ≤ P.C N; omega)
      hhi hH hwindow j.isLt z hzp
    dsimp only [M,Matrix.of_apply]
    rw [hvals.1,hvals.2.1,hvals.2.2.1,hvals.2.2.2.1,hvals.2.2.2.2]
    change palindromicRatResidue p ((p:ℚ)^2*filteredEntryRat P z N i.val j.val)-
      palindromicRatResidue p ((p:ℚ)^2*filteredEntryRat P z N (P.g N+2*p-d i) j.val)=_
    rw [hd.2.2]
    rw [show palindromicRatResidue p (292/59)=(292/59:ZMod p) from ha.2,
      show palindromicRatResidue p (3281/177)=(3281/177:ZMod p) from hb.2]
    simpa only [sparseFilteredResidueDelta,one_mul,zero_mul,add_zero] using hrow
  have hh :=fiveSource_elimination_valuation M S s2 s1p s1m s0p s0m (292/59) (3281/177)
    hs ha.1 hb.1 hM hrel
  rw [sparseTargetRows_card hfit] at hh
  exact hh

theorem baseline_sparse_determinant_valuation {p N : ℕ} [hp : Fact p.Prime]
    (hN : 0<N) (hlarge : 1000000 ≤ p) (hlo : 58*N ≤ 3*p) (hhi : p ≤ 21*N)
    (hHsq : 65*N<p^2) (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    -((96*N-min (4*N) (63*N-3*p):ℕ):ℤ) ≤ padicValRat p (determinantRat baseline z N) := by
  have hn : baseline.n N=48*N :=rfl
  have hg : baseline.g N=4*N :=rfl
  have hb : baseline.b N=7*N :=rfl
  have hC : baseline.C N=63*N :=by
    unfold Parameters.C Parameters.L Parameters.n Parameters.b Parameters.q Parameters.g baseline
    dsimp
    omega
  have hH : baseline.H N=65*N :=by
    unfold Parameters.H
    rw [hC]
    change 63*N+2*N=65*N
    omega
  have hecut : 3*p+min (4*N) (63*N-3*p) ≤ 63*N :=by
    have :=Nat.min_le_right (4*N) (63*N-3*p)
    have hpp : 3*p ≤ 63*N :=by omega
    have :=Nat.sub_add_cancel hpp
    omega
  have hh :=sparse_determinant_valuation (P:=baseline) (e:=min (4*N) (63*N-3*p))
    baseline_admissible hN hlarge (by simpa only [hH] using hHsq)
    (by simpa only [hg] using Nat.min_le_left (4*N) (63*N-3*p))
    (by simpa only [hC] using hecut)
    (by simpa only [hg,hn] using baseline_sparse_modes_fit hN hhi)
    (by rw [hH]; omega) (by rw [hH]; omega) (by rw [hH,hb]; omega) z hzp
  simpa only [hn,show 2*(48*N)=96*N by omega] using hh

end
end CatalanMeasure.Parametric
