module

public import CatalanCore.Cert.SigmaThirds.IBoundA
public import CatalanCore.Cert.SigmaThirds.Bridge

@[expose] public section

open Real

namespace CatalanCore.Cert.SigmaThirds

open _root_.CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def cpt (p : Pt) : ℂ := ⟨(p.1 : ℝ) / 2 ^ 40, (p.2.1 : ℝ) / 2 ^ 40⟩

lemma qII_cast (p q : Pt) :
    (qII p q : ℝ) = ((p.1 : ℝ) - q.1) ^ 2 + ((p.2.1 : ℝ) - q.2.1) ^ 2 + 2 ^ 56 := by
  unfold qII
  push_cast [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  ring

lemma pair_le (p q : Pt) :
    ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) * CatalanLambda.Decay.krho (1 / 4096 : ℝ) (cpt p) (cpt q)
      ≤ Jr p q := by
  unfold CatalanLambda.Decay.krho cpt
  rw [norm_sq_mk]
  have hN : 0 < qII p q := by unfold qII; positivity
  have hq : ((p.1 : ℝ) / 2 ^ 40 - (q.1 : ℝ) / 2 ^ 40) ^ 2 + ((p.2.1 : ℝ) / 2 ^ 40 - (q.2.1 : ℝ) / 2 ^ 40) ^ 2
      + (1 / 4096 : ℝ) ^ 2 = (qII p q : ℝ) / 2 ^ 80 := by
    rw [qII_cast]; field_simp; ring
  rw [hq]
  have h1 := CatalanLambda.Cert.logLoS_spec hN
  have hn : (0 : ℝ) ≤ ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) := by positivity
  have h2 : -(1 / 2 : ℝ) * Real.log ((qII p q : ℝ) / 2 ^ 80) ≤ -(1 / 2) * ((CatalanLambda.Cert.logLoS (qII p q) : ℝ) / 2 ^ 64) := by
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn
  unfold Jr
  linarith

theorem Im_le : CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH mH ≤ -(ITOT : ℝ) / 2 ^ 129 := by
  have h1 : CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH mH ≤ ∑ k : Fin 2950, ∑ l : Fin 2950, Jr (ptAt k) (ptAt l) := by
    unfold CatalanLambda.Decay.Irho
    refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
    have := pair_le (ptAt k) (ptAt l)
    unfold mH cH
    exact this
  have h2 : ∑ k : Fin 2950, ∑ l : Fin 2950, Jr (ptAt k) (ptAt l) = -(iTri sigH : ℝ) / 2 ^ 129 := by
    have e1 : ∀ k : Fin 2950, ∑ l : Fin 2950, Jr (ptAt k) (ptAt l) = (sigH.map (Jr (ptAt k))).sum :=
      fun k => sum_sigma (Jr (ptAt k))
    simp_rw [e1]
    rw [sum_sigma (fun p => (sigH.map (Jr p)).sum), S_eq]
  rw [iTri_sigH] at h2
  exact h1.trans h2.le

theorem Irho_wt : CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH wtH
    = (64 / 81) * CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH mH := by
  unfold CatalanLambda.Decay.Irho
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold wtH
  ring

theorem I_ok_S : CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH wtH ≤ (IBOUNDS : ℝ) := by
  rw [Irho_wt]
  have h := Im_le
  have hX : (64 / 81 : ℝ) * (-(ITOT : ℝ) / 2 ^ 129) ≤ (IBOUNDS : ℝ) := by
    unfold ITOT IBOUNDS
    push_cast
    norm_num
  have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 64 / 81)
  exact this.trans hX

end CatalanCore.Cert.SigmaThirds
