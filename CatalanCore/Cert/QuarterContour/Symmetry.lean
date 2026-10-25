module
public import CatalanCore.Cert.QuarterContour.Witness
@[expose] public section
namespace CatalanCore.Cert.QuarterContour

/-- Symmetric finite charges give a symmetric potential, independently of their count. -/
theorem Usig_conj_of_involution {K : ℕ} (rho : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ)
    (sigma : Fin K → Fin K) (hinv : Function.Involutive sigma)
    (hc : ∀ k, c (sigma k) = (starRingEnd ℂ) (c k))
    (hm : ∀ k, m (sigma k) = m k) (s : ℂ) :
    CatalanLambda.Decay.Usig rho c m ((starRingEnd ℂ) s) =
      CatalanLambda.Decay.Usig rho c m s := by
  unfold CatalanLambda.Decay.Usig
  have h : ∀ k, m k * CatalanLambda.Decay.krho rho ((starRingEnd ℂ) s) (c k) =
      m (sigma k) * CatalanLambda.Decay.krho rho s (c (sigma k)) := by
    intro k
    rw [hm, hc]
    unfold CatalanLambda.Decay.krho
    have hn : ‖(starRingEnd ℂ) s - c k‖ = ‖s - (starRingEnd ℂ) (c k)‖ := by
      rw [← Complex.norm_conj (s - (starRingEnd ℂ) (c k))]
      simp [map_sub]
    rw [hn]
  simp_rw [h]
  exact Equiv.sum_comp (Function.Involutive.toPerm sigma hinv)
    (fun j => m j * CatalanLambda.Decay.krho rho s (c j))

/-- Radius control of list-enumerated positions from an integer squared-norm check. -/
theorem positions_norm_le (pts : List CatalanCore.Cert.SigmaP6.Pt) (R : ℝ)
    (hR : 0 ≤ R) (k : Fin pts.length)
    (h : ((pointAt pts k).1 : ℝ) ^ 2 + ((pointAt pts k).2.1 : ℝ) ^ 2 ≤
      R ^ 2 * (2 ^ 40) ^ 2) : ‖positions pts k‖ ≤ R := by
  have hs : ‖positions pts k‖ ^ 2 ≤ R ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    unfold positions
    change (((pointAt pts k).1 : ℝ) / 2 ^ 40) * (((pointAt pts k).1 : ℝ) / 2 ^ 40) +
      (((pointAt pts k).2.1 : ℝ) / 2 ^ 40) * (((pointAt pts k).2.1 : ℝ) / 2 ^ 40) ≤ R ^ 2
    nlinarith [sq_nonneg (((pointAt pts k).1 : ℝ) / 2 ^ 40),
      sq_nonneg (((pointAt pts k).2.1 : ℝ) / 2 ^ 40)]
  nlinarith [norm_nonneg (positions pts k)]
end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.Usig_conj_of_involution
#print axioms CatalanCore.Cert.QuarterContour.positions_norm_le
