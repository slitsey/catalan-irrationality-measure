module

public import CatalanCore.Cert.SigmaP6.IBoundData

@[expose] public section

/-!
# `I_ρ(σ) ≤ IBOUND` from the scaled-integer lower log bounds (`logLoS`)
-/

open Real

namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

set_option maxRecDepth 100000

noncomputable def Jr (p q : Pt) : ℝ :=
  -(1 / 2) * ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) * ((logLoS (qII p q) : ℝ) / 2 ^ 64)

lemma row_eq (p : Pt) : ∀ l : List Pt,
    (l.map (Jr p)).sum = -((p.2.2 : ℝ) * (iRow p l : ℝ)) / 2 ^ 129 := by
  intro l
  induction l with
  | nil => simp [iRow]
  | cons q qs ih =>
    simp only [List.map_cons, List.sum_cons, ih, iRow, Jr]
    push_cast
    ring

lemma tot_eq : ∀ l : List Pt,
    (l.map (fun p => (sigD.map (Jr p)).sum)).sum = -(iTot l : ℝ) / 2 ^ 129 := by
  intro l
  induction l with
  | nil => simp [iTot]
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih, row_eq]
    simp only [iTot]
    push_cast
    ring

noncomputable def cpt (p : Pt) : ℂ := ⟨(p.1 : ℝ) / 2 ^ 40, (p.2.1 : ℝ) / 2 ^ 40⟩

lemma qII_cast (p q : Pt) :
    (qII p q : ℝ) = ((p.1 : ℝ) - q.1) ^ 2 + ((p.2.1 : ℝ) - q.2.1) ^ 2 + 2 ^ 58 := by
  unfold qII
  push_cast [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  ring

lemma pair_le (p q : Pt) :
    ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) * CatalanLambda.Decay.krho (1 / 2048 : ℝ) (cpt p) (cpt q)
      ≤ Jr p q := by
  unfold CatalanLambda.Decay.krho cpt
  rw [norm_sq_mk]
  have hN : 0 < qII p q := by unfold qII; positivity
  have hq : ((p.1 : ℝ) / 2 ^ 40 - (q.1 : ℝ) / 2 ^ 40) ^ 2 + ((p.2.1 : ℝ) / 2 ^ 40 - (q.2.1 : ℝ) / 2 ^ 40) ^ 2
      + (1 / 2048 : ℝ) ^ 2 = (qII p q : ℝ) / 2 ^ 80 := by
    rw [qII_cast]; field_simp; ring
  rw [hq]
  have h1 := logLoS_spec hN
  have hn : (0 : ℝ) ≤ ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) := by positivity
  have h2 : -(1 / 2 : ℝ) * Real.log ((qII p q : ℝ) / 2 ^ 80) ≤ -(1 / 2) * ((logLoS (qII p q) : ℝ) / 2 ^ 64) := by
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn
  unfold Jr
  linarith

theorem I_ok : CatalanLambda.Decay.Irho (1 / 2048 : ℝ) cS mS ≤ (IBOUND : ℝ) := by
  have h1 : CatalanLambda.Decay.Irho (1 / 2048 : ℝ) cS mS ≤ ∑ k : Fin 699, ∑ l : Fin 699, Jr (ptAt k) (ptAt l) := by
    unfold CatalanLambda.Decay.Irho
    refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
    have := pair_le (ptAt k) (ptAt l)
    unfold mS cS
    exact this
  have h2 : ∑ k : Fin 699, ∑ l : Fin 699, Jr (ptAt k) (ptAt l) = -(iTot sigD : ℝ) / 2 ^ 129 := by
    have e1 : ∀ k : Fin 699, ∑ l : Fin 699, Jr (ptAt k) (ptAt l) = (sigD.map (Jr (ptAt k))).sum :=
      fun k => sum_sigma (Jr (ptAt k))
    simp_rw [e1]
    rw [sum_sigma (fun p => (sigD.map (Jr p)).sum), tot_eq]
  rw [iTot_sigD_val] at h2
  refine h1.trans (h2.le.trans ?_)
  unfold IBOUND
  push_cast
  try norm_num

end CatalanCore.Cert.SigmaP6
