module
public import CatalanCore.Cert.SigmaQuarterContour.PointChecks
public import CatalanCore.Cert.QuarterContour.Symmetry
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
open CatalanCore.Cert.QuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem point_facts (k : Fin pts.length) :
    (ptAtC k).1 ^ 2 + (ptAtC k).2.1 ^ 2 ≤ (256 : ℤ) * (2 ^ 40) ^ 2 ∧
    conjugateIndex k < pts.length ∧
    (ptAtC (conjugateIndex k)).1 = (ptAtC k).1 ∧
    (ptAtC (conjugateIndex k)).2.1 = -(ptAtC k).2.1 ∧
    (ptAtC (conjugateIndex k)).2.2 = (ptAtC k).2.2 ∧
    conjugateIndex (conjugateIndex k) = k := by
  have h := List.all_eq_true.mp points_checked k.val (List.mem_range.mpr k.isLt)
  simp only [pointOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

def sigma (k : Fin pts.length) : Fin pts.length := ⟨conjugateIndex k, (point_facts k).2.1⟩

theorem sigma_involutive : Function.Involutive sigma := by
  intro k
  apply Fin.ext
  exact (point_facts k).2.2.2.2.2

theorem sigma_positions (k : Fin pts.length) :
    positions pts (sigma k) = (starRingEnd ℂ) (positions pts k) := by
  have h := point_facts k
  apply Complex.ext <;> simp only [positions, sigma, Complex.conj_re, Complex.conj_im]
  · change ((ptAtC (conjugateIndex k)).1 : ℝ) / 2^40 = ((ptAtC k).1 : ℝ) / 2^40
    rw [h.2.2.1]
  · change ((ptAtC (conjugateIndex k)).2.1 : ℝ) / 2^40 = -(((ptAtC k).2.1 : ℝ) / 2^40)
    rw [h.2.2.2.1]; push_cast; ring

theorem sigma_masses (k : Fin pts.length) : masses pts (sigma k) = masses pts k := by
  change ((ptAtC (conjugateIndex k)).2.2 : ℝ) / 2^32 = ((ptAtC k).2.2 : ℝ) / 2^32
  rw [(point_facts k).2.2.2.2.1]

theorem radius_le (k : Fin pts.length) : ‖positions pts k‖ ≤ 16 := by
  apply positions_norm_le pts 16 (by norm_num) k
  norm_num only [show (16 : ℝ)^2 = 256 by norm_num]
  exact_mod_cast (point_facts k).1

theorem Usig_conj (s : ℂ) :
    CatalanLambda.Decay.Usig (1/2048 : ℝ) (positions pts) (masses pts) ((starRingEnd ℂ) s) =
    CatalanLambda.Decay.Usig (1/2048 : ℝ) (positions pts) (masses pts) s :=
  Usig_conj_of_involution _ _ _ sigma sigma_involutive sigma_positions sigma_masses s
end CatalanCore.Cert.SigmaQuarterContour
#print axioms CatalanCore.Cert.SigmaQuarterContour.Usig_conj
#print axioms CatalanCore.Cert.SigmaQuarterContour.radius_le