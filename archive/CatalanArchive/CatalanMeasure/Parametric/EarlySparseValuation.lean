module
public import CatalanMeasure.Parametric.SparseCombinationRank
public import CatalanArchive.CatalanMeasure.Parametric.BaselineBridge
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan
noncomputable section

theorem baseline_early_sparse_determinant_valuation {p N : ℕ} [hp : Fact p.Prime]
    (hN : 0<N) (hlarge : 1000000 ≤ p) (hlo : 18*N ≤ p) (hhi : 3*p ≤ 58*N)
    (hHsq : 65*N<p^2) (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    -((96*N-(3*p-54*N):ℕ):ℤ) ≤ padicValRat p (determinantRat baseline z N) :=by
  have hn : baseline.n N=48*N :=rfl
  have hg : baseline.g N=4*N :=rfl
  have hb : baseline.b N=7*N :=rfl
  have hC : baseline.C N=63*N :=by
    change 48*N+7*N+4*N+4*N=63*N
    omega
  have hH : baseline.H N=65*N :=by
    change 48*N+7*N+4*N+4*N+2*N=65*N
    omega
  have hh :=sparse_combination_determinant_valuation (P:=baseline)
    baseline_admissible hN hlarge (by simpa only [hH] using hHsq)
    (by rw [hg,hC]; omega) (by rw [hH]; omega) (by rw [hH]; omega)
    (by rw [hg]; omega) (by rw [hg,hn]; omega) z hzp
  have he : baseline.g N-(baseline.H N-3*p-baseline.b N)=3*p-54*N :=by
    rw [hg,hH,hb]
    omega
  simpa only [hn,he,show 2*(48*N)=96*N by omega] using hh

theorem determinantRat_early_sparse_prime_valuation {p N : ℕ} [hp : Fact p.Prime]
    (hN : 0<N) (hlarge : 1000000 ≤ p) (hlo : 18*N ≤ p) (hhi : 3*p ≤ 58*N)
    (hHsq : 65*N<p^2) (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    -((96*N-(3*p-54*N):ℕ):ℤ) ≤ padicValRat p (OAI.InternalCatalan.determinantRat z N) :=by
  rw [← baseline_determinantRat]
  exact baseline_early_sparse_determinant_valuation hN hlarge hlo hhi hHsq z hzp

end
end CatalanMeasure.Parametric
