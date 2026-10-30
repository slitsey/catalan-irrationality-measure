import CatalanCore.Uniform.Bank.Sevenths.Normalisation
import CatalanCore.Uniform.Bank.Sevenths.Band
import CatalanCore.Uniform.Content.RankProducer.BalancedGeometry
import CatalanCore.Uniform.Bank.Sevenths.MemberIdentity
import CatalanCore.Uniform.Content.RankProducer.LineMember
import CatalanCore.Rect.CommonMinor
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
open CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
open CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Content.RankProducer.Geometry
open scoped Classical

/-- Assemble the actual norm-one pipeline member from a balanced physical assignment. -/
noncomputable def rankMemberOfAssignment (a : Fin 6) (p r m : ℕ) [Fact p.Prime]
    (s : Finset (Fin r)) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes (seventhsPoleSplit (seventhNumerator a) p r m (by dsimp [seventhNumerator]; omega) hp64 hp7 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x))
    (hcard : (killRows (p := p) (rowsOf r m s) cert).card =
      (killCols (p := p) (colsOf r m s) cert).card)
    (w : RatFunc (ZMod p) × RatFunc (ZMod p)) (hw : w ≠ 0) :
    RankMember (pipelineFrame a) (u7 a) q7 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p := by
  have hc : ∀ j, (frameDigamma (pipelineFrame a) (u7 a) q7).c j ∈ S p := by
    intro j
    rw [pipeline_digamma]
    exact D7Frame_coeff_mem (seventhNumerator a) p j
  have hq : ∀ j, ¬ p ∣ (frameDigamma (pipelineFrame a) (u7 a) q7).q j := by
    intro j
    rw [pipeline_digamma]
    exact D7Frame_den_units (seventhNumerator a) p hp7 j
  have hbd : ∀ j, (frameDigamma (pipelineFrame a) (u7 a) q7).q j * (r + 2 * m) +
      (frameDigamma (pipelineFrame a) (u7 a) q7).u j ≤ p ^ 2 := by
    intro j
    rw [pipeline_digamma]
    exact D7Frame_band (seventhNumerator a) r m p (by dsimp [seventhNumerator]; omega) hp64 hrp hm1 j
  apply RankMember.ofLine (pipelineFrame a) (u7 a) q7
    (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ))
    (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p (r + 2 * m)
    hc hq (by omega) hbd (by
      have h := D7Frame_band (seventhNumerator a) r m p (by dsimp [seventhNumerator]; omega) hp64 hrp hm1 (1 : Fin 2)
      change 1 * (r + 2 * m) + 1 ≤ p ^ 2 at h
      omega)
    (rows_le r m s) (cols_le r m s) (rows_inj r m s) (cols_inj r m s)
    cert hOk hInt ?_ hcard w hw
  intro x
  have htransport (D : DigammaFrame (Fin 2)) (hD : D = D7Frame (seventhNumerator a))
      (hcD : ∀ j, D.c j ∈ S p) (hqD : ∀ j, ¬ p ∣ D.q j)
      (hbD : ∀ j, D.q j * (r + 2 * m) + D.u j ≤ p ^ 2) :
      Realizes (D.poleSplit (r + 2 * m) hcD hqD (by omega) hbD)
        (rowsOf r m s) (colsOf r m s) x (cert x) := by
    subst D
    exact hReal x
  exact htransport _ (pipeline_digamma a) hc hq hbd

/-- The producer clears the actual common-minor polynomial of the pipeline. -/
theorem sevenths_pipeline_rank_member_gle (a : Fin 6) (p r m : ℕ) [Fact p.Prime]
    (s : Finset (Fin r))
    (M : RankMember (pipelineFrame a) (u7 a) q7 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p) :
    GLE p M.price (commonMinorPoly (pipelineFrame a) r m s) := by
  apply RankMember.gle (pipelineFrame a) (u7 a) q7 (hu7 a) hq7
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
#print axioms sevenths_pipeline_rank_member_gle
end CatalanCore.Uniform.Bank.Sevenths
