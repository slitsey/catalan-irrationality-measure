module

public import CatalanCore.Cert.SigmaQuarter.EnergyDef
public import CatalanCore.Cert.SigmaQuarter.Bridge

@[expose] public section

namespace CatalanCore.Cert.SigmaQuarter

open CatalanCore.Cert.SigmaP6

set_option maxRecDepth 100000

lemma energyTot_eq : ∀ l : List Pt,
    (l.map (fun p => (pts.map (Jr p)).sum)).sum = -(energyTot l : ℝ) / 2 ^ 129 := by
  intro l
  induction l with
  | nil => simp [energyTot]
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih, row_eq]
    simp only [energyTot]
    push_cast
    ring

theorem I_le_of_energy (hEnergy : -(energyTot pts : ℝ) / 2 ^ 129 ≤ (1808029/1000000 : ℝ)) : CatalanLambda.Decay.Irho (1 / 2048 : ℝ) cQ mQ ≤ (1808029/1000000 : ℝ) := by
  have h1 : CatalanLambda.Decay.Irho (1 / 2048 : ℝ) cQ mQ ≤
      ∑ k : Fin pts.length, ∑ l : Fin pts.length, Jr (ptAtQ k) (ptAtQ l) := by
    unfold CatalanLambda.Decay.Irho
    refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
    have h := pair_le (ptAtQ k) (ptAtQ l)
    unfold mQ cQ
    exact h
  have h2 : (∑ k : Fin pts.length, ∑ l : Fin pts.length, Jr (ptAtQ k) (ptAtQ l)) =
      -(energyTot pts : ℝ) / 2 ^ 129 := by
    have e1 : ∀ k : Fin pts.length,
        ∑ l : Fin pts.length, Jr (ptAtQ k) (ptAtQ l) = (pts.map (Jr (ptAtQ k))).sum :=
      fun k => sum_sigmaQ (Jr (ptAtQ k))
    simp_rw [e1]
    rw [sum_sigmaQ (fun p => (pts.map (Jr p)).sum), energyTot_eq]
  exact h1.trans (h2.le.trans hEnergy)

end CatalanCore.Cert.SigmaQuarter