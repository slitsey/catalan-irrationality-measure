import CatalanCore.Uniform.Bank.Lambda.Pipeline
import CatalanCore.Uniform.Bank.Lambda.Band
import CatalanCore.Uniform.Bank.Lambda.Assignment
import CatalanCore.Uniform.Bank.Lambda.MemberIdentity
import CatalanCore.Uniform.Content.RankProducer.LineMember
import CatalanCore.Rect.CommonMinor
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
open CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
open CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Bank.Chi3Rank
open scoped Classical

/-- Assemble the actual norm-one pipeline member from a balanced physical assignment. -/
noncomputable def rankMemberOfAssignment (a p r m : ℕ) [Fact p.Prime]
    (s : Finset (Fin r)) (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x))
    (hcard : (killRows (p := p) (rowsOf r m s) cert).card =
      (killCols (p := p) (colsOf r m s) cert).card)
    (w : RatFunc (ZMod p) × RatFunc (ZMod p)) (hw : w ≠ 0) :
    RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p := by
  have hc : ∀ j, (frameDigamma (pipelineFrame a ha) (u4 a) q4).c j ∈ S p := by
    intro j
    rw [pipeline_digamma]
    exact D4_coeff_mem a p j
  have hq : ∀ j, ¬ p ∣ (frameDigamma (pipelineFrame a ha) (u4 a) q4).q j := by
    intro j
    rw [pipeline_digamma]
    exact D4_den_units a p hp4 j
  have hbd : ∀ j, (frameDigamma (pipelineFrame a ha) (u4 a) q4).q j * (r + 2 * m) +
      (frameDigamma (pipelineFrame a ha) (u4 a) q4).u j ≤ p ^ 2 := by
    intro j
    rw [pipeline_digamma]
    exact D4_band a r m p ha hp29 hrp hm1 j
  apply RankMember.ofLine (pipelineFrame a ha) (u4 a) q4
    (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ))
    (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p (r + 2 * m)
    hc hq (by omega) hbd (q4_band r m p a ha hp29 hrp hm1).1
    (rows_le r m s) (cols_le r m s) (rows_inj r m s) (cols_inj r m s)
    cert hOk hInt ?_ hcard w hw
  intro x
  have htransport (D : DigammaFrame (Fin 2)) (hD : D = D4 a)
      (hcD : ∀ j, D.c j ∈ S p) (hqD : ∀ j, ¬ p ∣ D.q j)
      (hbD : ∀ j, D.q j * (r + 2 * m) + D.u j ≤ p ^ 2) :
      Realizes (D.poleSplit (r + 2 * m) hcD hqD (by omega) hbD)
        (rowsOf r m s) (colsOf r m s) x (cert x) := by
    subst D
    exact hReal x
  exact htransport _ (pipeline_digamma a ha) hc hq hbd

/-- The producer clears the actual common-minor polynomial of the pipeline. -/
theorem pipeline_rank_member_gle (a p r m : ℕ) [Fact p.Prime]
    (ha : a = 1 ∨ a = 3) (s : Finset (Fin r))
    (M : RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p) :
    GLE p M.price (commonMinorPoly (pipelineFrame a ha) r m s) := by
  apply RankMember.gle (pipelineFrame a ha) (u4 a) q4 (hu4 a ha) hq4
    (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ))
    (fun j : Fin m => r + 2 * (j : ℕ) + 1) Fin.val_injective
    ?_ ?_ ?_ s p M
  · intro i j
    have := j.2
    omega
  · intro i j
    have := j.2
    omega
  · intro i j
    omega

#print axioms rankMemberOfAssignment
#print axioms pipeline_rank_member_gle
end CatalanCore.Uniform.Bank.Lambda
