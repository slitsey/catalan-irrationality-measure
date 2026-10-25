module
public import CatalanCore.Cert.QuarterContour.Symmetry
@[expose] public section
namespace CatalanCore.Cert.QuarterContour

/-- Conjugation invariance of the hybrid node potential, for every border ratio. -/
theorem Unu_conj (alpha : ℝ) (s : ℂ) :
    CatalanCore.Decay.Unu alpha ((starRingEnd ℂ) s) = CatalanCore.Decay.Unu alpha s := by
  have hn (t : ℝ) : ‖(starRingEnd ℂ) s - (t : ℂ)‖ = ‖s - (t : ℂ)‖ := by
    rw [← Complex.norm_conj (s - (t : ℂ))]
    simp [map_sub]
  unfold CatalanCore.Decay.Unu CatalanCore.Decay.Uex CatalanLambda.Decay.Utau
    CatalanLambda.Decay.elog
  simp_rw [hn]

theorem gAlpha_conj_of_involution {K : ℕ} (rho epsilon alpha : ℝ)
    (c : Fin K → ℂ) (m : Fin K → ℝ) (sigma : Fin K → Fin K)
    (hinv : Function.Involutive sigma)
    (hc : ∀ k, c (sigma k) = (starRingEnd ℂ) (c k))
    (hm : ∀ k, m (sigma k) = m k) (s : ℂ) :
    CatalanCore.Cert.gAlpha rho epsilon c m alpha (CatalanCore.Decay.Unu alpha)
      ((starRingEnd ℂ) s) =
    CatalanCore.Cert.gAlpha rho epsilon c m alpha (CatalanCore.Decay.Unu alpha) s := by
  unfold CatalanCore.Cert.gAlpha
  rw [Usig_conj_of_involution rho c m sigma hinv hc hm, Unu_conj]
  simp
end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.Unu_conj
#print axioms CatalanCore.Cert.QuarterContour.gAlpha_conj_of_involution
