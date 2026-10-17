module
public import CatalanMeasure.Parametric.SparseDeterminantValuation
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem baseline_parameter_values (N : ℕ) :
    baseline.n N=n N ∧ baseline.b N=b N ∧ baseline.q N=q N ∧ baseline.g N=g N ∧
      baseline.h N=h N ∧ baseline.C N=Cdegree N ∧ baseline.H N=H N :=by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · change 48*N+7*N+4*N+4*N=63*N
    omega
  · change 48*N+7*N+4*N+4*N+2*N=65*N
    omega

theorem baseline_rowP (N r : ℕ) : rowP baseline N r=OAI.InternalCatalan.rowP N r :=by
  have hpar :=baseline_parameter_values N
  unfold rowP OAI.InternalCatalan.rowP rowDistance rowOffset
    OAI.InternalCatalan.rowDistance OAI.InternalCatalan.rowOffset
  rw [hpar.2.2.2.2.1,hpar.2.2.2.2.2.1,hpar.2.2.2.1]

theorem baseline_rowD (N r : ℕ) : rowD baseline N r=OAI.InternalCatalan.rowD N r :=by
  have hpar :=baseline_parameter_values N
  unfold rowD OAI.InternalCatalan.rowD rowDistance rowOffset
    OAI.InternalCatalan.rowDistance OAI.InternalCatalan.rowOffset
  rw [hpar.2.2.2.2.1,hpar.2.2.2.2.2.1,hpar.2.2.2.1]

theorem baseline_rawEntryRat (z : ℚ) (N r j : ℕ) :
    rawEntryRat baseline z N r j=OAI.InternalCatalan.rawEntryRat z N r j :=by
  have hpar :=baseline_parameter_values N
  simp only [rawEntryRat,OAI.InternalCatalan.rawEntryRat,hpar.2.2.2.2.2.2,baseline_rowP,baseline_rowD]

theorem baseline_filteredEntryRat (z : ℚ) (N r k : ℕ) :
    filteredEntryRat baseline z N r k=OAI.InternalCatalan.filteredEntryRat z N r k :=by
  have hpar :=baseline_parameter_values N
  simp only [filteredEntryRat,OAI.InternalCatalan.filteredEntryRat,filterCoeffRat,
    OAI.InternalCatalan.filterCoeffRat,hpar.2.1,hpar.2.2.1,baseline_rawEntryRat]

theorem baseline_determinantRat (z : ℚ) (N : ℕ) :
    determinantRat baseline z N=OAI.InternalCatalan.determinantRat z N :=by
  have hn :=(baseline_parameter_values N).1
  unfold determinantRat OAI.InternalCatalan.determinantRat
  simp only [hn,baseline_filteredEntryRat]
  rfl

theorem determinantRat_sparse_prime_valuation {p N : ℕ} [hp : Fact p.Prime]
    (hN : 0<N) (hlarge : 1000000 ≤ p) (hlo : 58*N ≤ 3*p) (hhi : p ≤ 21*N)
    (hHsq : 65*N<p^2) (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    -((96*N-min (4*N) (63*N-3*p):ℕ):ℤ) ≤
      padicValRat p (OAI.InternalCatalan.determinantRat z N) :=by
  rw [← baseline_determinantRat]
  exact baseline_sparse_determinant_valuation hN hlarge hlo hhi hHsq z hzp

end
end CatalanMeasure.Parametric
