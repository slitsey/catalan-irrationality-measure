import CatalanCore.Uniform.Bank.Lambda.RankBalance
import CatalanCore.Uniform.Bank.Chi3Rank.Fibre
import CatalanCore.Uniform.Content.RankProducer.Assignment
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankTools
open CatalanCore CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.RankProducer CatalanCore.Uniform.Bank.Chi3Rank
open scoped Classical
variable {p : ℕ} [Fact p.Prime] {B : ℕ} {f e : ℕ → ℚ}

/-- Complete physical realization survives global balancing; the retained kill
count is exactly the smaller of the two actual original kill counts. -/
theorem exists_balanced_realization (PS : PoleSplit p B f e) (r m : ℕ) (s : Finset (Fin r)) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes PS (rowsOf r m s) (colsOf r m s) x (cert x)) :
    ∃ bal : ZMod p → FibreCert,
      (∀ x, (bal x).Ok) ∧ (∀ x, (bal x).Integral p) ∧
      (∀ x, Realizes PS (rowsOf r m s) (colsOf r m s) x (bal x)) ∧
      (killRows (p := p) (rowsOf r m s) bal).card = min (killRows (p := p) (rowsOf r m s) cert).card (killCols (p := p) (colsOf r m s) cert).card ∧
      (killCols (p := p) (colsOf r m s) bal).card = min (killRows (p := p) (rowsOf r m s) cert).card (killCols (p := p) (colsOf r m s) cert).card := by
  let a := rowsOf r m s
  let b := colsOf r m s
  have ha : Function.Injective a := rows_inj r m s
  have hb : Function.Injective b := cols_inj r m s
  obtain ⟨KR, KC, hKR, hKC, hR, hC⟩ := exists_balanced_indices a b cert
  refine ⟨retainAssignment a b cert KR KC, retainAssignment_ok a b cert hOk KR KC hKR hKC,
    ?_, ?_, ?_, ?_⟩
  · intro x
    exact trim_integral (cert x) p (hInt x) _ _
  · intro x
    exact trim_realizes PS a b x (cert x) (hReal x) _ _
  · rw [retainAssignment_killRows a b ha]
    exact hR
  · rw [retainAssignment_killCols a b hb]
    exact hC

#print axioms exists_balanced_realization
end CatalanCore.Uniform.Bank.Lambda.RankTools
