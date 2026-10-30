module

public import CatalanLambda.Cert.IBoundData

@[expose] public section

/-!
# `I_ρ(σ) ≤ IBOUND` from the scaled-integer lower log bounds (`logLoS`)
-/

open Real

namespace CatalanLambda.Cert

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
    (l.map (fun p => (sigmaS.map (Jr p)).sum)).sum = -(iTot l : ℝ) / 2 ^ 129 := by
  intro l
  induction l with
  | nil => simp [iTot]
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih, row_eq]
    simp only [iTot]
    push_cast
    ring

lemma iTot_append (a b : List Pt) : iTot (a ++ b) = iTot a + iTot b := by
  induction a with
  | nil => simp [iTot]
  | cons p ps ih => simp only [List.cons_append, iTot, ih]; ring

noncomputable def cpt (p : Pt) : ℂ := ⟨(p.1 : ℝ) / 2 ^ 40, (p.2.1 : ℝ) / 2 ^ 40⟩

lemma qII_cast (p q : Pt) :
    (qII p q : ℝ) = ((p.1 : ℝ) - q.1) ^ 2 + ((p.2.1 : ℝ) - q.2.1) ^ 2 + 2 ^ 60 := by
  unfold qII
  push_cast [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  ring

lemma pair_le (p q : Pt) :
    ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) * Decay.krho (1 / 1024 : ℝ) (cpt p) (cpt q)
      ≤ Jr p q := by
  unfold Decay.krho cpt
  rw [norm_sq_mk]
  have hN : 0 < qII p q := by unfold qII; positivity
  have hq : ((p.1 : ℝ) / 2 ^ 40 - (q.1 : ℝ) / 2 ^ 40) ^ 2 + ((p.2.1 : ℝ) / 2 ^ 40 - (q.2.1 : ℝ) / 2 ^ 40) ^ 2
      + (1 / 1024 : ℝ) ^ 2 = (qII p q : ℝ) / 2 ^ 80 := by
    rw [qII_cast]; field_simp; ring
  rw [hq]
  have h1 := logLoS_spec hN
  have hn : (0 : ℝ) ≤ ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) := by positivity
  have h2 : -(1 / 2 : ℝ) * Real.log ((qII p q : ℝ) / 2 ^ 80) ≤ -(1 / 2) * ((logLoS (qII p q) : ℝ) / 2 ^ 64) := by
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn
  unfold Jr
  linarith

theorem I_ok : Decay.Irho (1 / 1024 : ℝ) cS mS ≤ (IBOUND : ℝ) := by
  have h1 : Decay.Irho (1 / 1024 : ℝ) cS mS ≤ ∑ k : Fin 300, ∑ l : Fin 300, Jr (ptAt k) (ptAt l) := by
    unfold Decay.Irho
    refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
    have := pair_le (ptAt k) (ptAt l)
    unfold mS cS
    exact this
  have h2 : ∑ k : Fin 300, ∑ l : Fin 300, Jr (ptAt k) (ptAt l) = -(iTot sigmaS : ℝ) / 2 ^ 129 := by
    have e1 : ∀ k : Fin 300, ∑ l : Fin 300, Jr (ptAt k) (ptAt l) = (sigmaS.map (Jr (ptAt k))).sum :=
      fun k => sum_sigma (Jr (ptAt k))
    simp_rw [e1]
    rw [sum_sigma (fun p => (sigmaS.map (Jr p)).sum), tot_eq]
  have hI : iTot sigmaS = iTot (iChunk 0) + iTot (iChunk 1) + iTot (iChunk 2) + iTot (iChunk 3)
      + iTot (iChunk 4) + iTot (iChunk 5) + iTot (iChunk 6) + iTot (iChunk 7) + iTot (iChunk 8)
      + iTot (iChunk 9) := by
    conv_lhs => rw [sigmaS_chunks]
    simp only [iTot_append]
    try ring
  rw [hI, iChunk_0, iChunk_1, iChunk_2, iChunk_3, iChunk_4, iChunk_5, iChunk_6, iChunk_7,
    iChunk_8, iChunk_9] at h2
  refine h1.trans (h2.le.trans ?_)
  unfold IBOUND
  push_cast
  try norm_num

end CatalanLambda.Cert
