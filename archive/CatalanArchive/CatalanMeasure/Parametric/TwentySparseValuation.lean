module
public import CatalanMeasure.Parametric.TwentyParameters
public import CatalanArchive.CatalanMeasure.Parametric.SparseCombinationRank
public import CatalanArchive.CatalanMeasure.Parametric.SparseDeterminantValuation
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan
noncomputable section

theorem twenty_prime_ne_eight_mul {p N : ℕ} [hp : Fact p.Prime]
    (hlarge : 1000000 ≤ p) : p≠8*N :=by
  intro heq
  have hdiv : 2 ∣ p :=by rw [heq];exact ⟨4*N,by omega⟩
  have hh :=hp.out.eq_one_or_self_of_dvd 2 hdiv
  omega

/-- The earlier residue window saves 3p-22N prime valuations. -/
theorem twenty_early_sparse_valuation {p N : ℕ} [hp : Fact p.Prime]
    (hN : 0<N) (hlarge : 1000000 ≤ p) (hlo : 22*N ≤ 3*p) (hhi : 3*p ≤ 24*N)
    (hHsq : 27*N<p^2) (z : ℚ) (hzp : (((p:ℚ)*z).den:ZMod p)≠0) :
    -((40*N-(3*p-22*N):ℕ):ℤ) ≤ padicValRat p (determinantRat twenty z N) :=by
  have hn : twenty.n N=20*N :=rfl
  have hg : twenty.g N=2*N :=rfl
  have hb : twenty.b N=3*N :=rfl
  have hp8 :=twenty_prime_ne_eight_mul (N :=N) hlarge
  have hh :=sparse_combination_determinant_valuation (P :=twenty)
    twenty_admissible hN hlarge (by simpa only [twenty_H] using hHsq)
    (by rw [hg,twenty_C];omega) (by rw [twenty_H];omega)
    (by rw [twenty_H];omega) (by rw [hg];omega) (by rw [hg,hn];omega) z hzp
  have he : twenty.g N-(twenty.H N-3*p-twenty.b N)=3*p-22*N :=by
    rw [hg,twenty_H,hb]
    omega
  simpa only [hn,he,show 2*(20*N)=40*N by omega] using hh

/-- The upper residue window saves 26N-3p prime valuations. -/
theorem twenty_upper_sparse_valuation {p N : ℕ} [hp : Fact p.Prime]
    (hN : 0<N) (hlarge : 1000000 ≤ p) (hlo : 24*N ≤ 3*p) (hhi : 3*p ≤ 26*N)
    (hHsq : 27*N<p^2) (z : ℚ) (hzp : (((p:ℚ)*z).den:ZMod p)≠0) :
    -((40*N-(26*N-3*p):ℕ):ℤ) ≤ padicValRat p (determinantRat twenty z N) :=by
  have hn : twenty.n N=20*N :=rfl
  have hg : twenty.g N=2*N :=rfl
  have hb : twenty.b N=3*N :=rfl
  have hp8 :=twenty_prime_ne_eight_mul (N :=N) hlarge
  have hh :=sparse_determinant_valuation (P :=twenty) (e :=26*N-3*p)
    twenty_admissible hN hlarge (by simpa only [twenty_H] using hHsq)
    (by rw [hg];omega) (by rw [twenty_C];omega) (by rw [hg,hn];omega)
    (by rw [twenty_H];omega) (by rw [twenty_H];omega)
    (by rw [twenty_H,hb];omega) z hzp
  simpa only [hn,show 2*(20*N)=40*N by omega] using hh

end
end CatalanMeasure.Parametric
