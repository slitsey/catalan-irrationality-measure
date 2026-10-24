module

public import CatalanArchive.CatalanMeasure.Cert.ResidualField

/-!
# The existing residual certificate on the positive interval

The value and derivative certificates are unchanged. Only the covered interval
is [0,1], as needed for full-interval marked columns.
-/

@[expose] public section

namespace CatalanMeasure.Cert

open OAI.InternalCatalan Set

noncomputable section

def residualPositiveBracketOK (cs : List ℤ) (tail : List TailQ) (A Q : List ℚ) (M : ℚ)
    (p : Piece) : Bool :=
  !p.2.2 || (decide (0 < p.1) && decide (p.1 < p.2.1) && decide (p.2.1 < 1) &&
    bracketOK A Q (residualTwoApprox cs tail) M p)

theorem residual_positive_sup_of_checks {cs : List ℤ} {tail : List TailQ} {A Q : List ℚ}
    {ps : List Piece} {M : ℚ} (ht : tailsInDisk tail = true)
    (hAQ : fracSum (residualTwoFracs cs tail) = (A,Q))
    (hcover : coverFrom A [] 0 ps 1 = true) (hgaps : NoRootGaps A ps)
    (hbr : ps.all (residualPositiveBracketOK cs tail A Q M) = true)
    (hleft : residualTwoEndOK cs tail M 0 = true)
    (hright : residualTwoEndOK cs tail M 1 = true) :
    ∀ x ∈ Icc (0 : ℝ) 1, residualTwoField cs tail x ≤ (M : ℝ) := by
  have hend {x : ℚ} (hx : |(x : ℝ)| ≤ 1) (he : residualTwoEndOK cs tail M x = true) :
      residualTwoField cs tail x ≤ (M : ℝ) := by
    unfold residualTwoEndOK at he
    split at he
    · rename_i ve hv
      simp only [decide_eq_true_eq] at he
      have hh := residualTwoApprox_spec ht hx hv
      have hv' : (ve.1 : ℝ) + (ve.2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast he
      linarith [(abs_le.mp hh).2]
    · simp at he
  apply GlobalMaxReduction.le_on_Icc_of_critical_le (a := (0 : ℝ)) (b := (1 : ℝ))
    ((residualTwoField_continuousOn ht).mono (by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩))
    (by simpa using hend (by norm_num) hleft) (by simpa using hend (by norm_num) hright)
  intro x hx hzero
  have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1],hx.2⟩
  obtain ⟨hQ,hD⟩ := residualTwoField_hasDerivAt ht hx'
  rw [hAQ] at hQ hD
  have hA : lpEval A x = 0 := by
    rw [hD.deriv] at hzero
    exact (div_eq_zero_iff.mp hzero).resolve_right hQ
  rcases coverFrom_spec_of_noRoot hcover hgaps (by simpa using hx) hA with
    ⟨e,he,_⟩ | ⟨p,hp,hk,hxp⟩
  · simp at he
  have hbp := (List.all_eq_true.mp hbr) p hp
  simp only [residualPositiveBracketOK,hk,Bool.not_true,Bool.false_or,Bool.and_eq_true,
    decide_eq_true_eq] at hbp
  obtain ⟨⟨⟨hlo,hlt⟩,hhi⟩,hb⟩ := hbp
  apply bracketOK_spec hb hk hlt ?_ ?_ x hxp
  · intro v e hev
    have hlo' : (0 : ℝ) < p.1 := by exact_mod_cast hlo
    have hhi' : (p.1 : ℝ) ≤ 1 := by exact_mod_cast (lt_trans hlt hhi).le
    have hh := residualTwoApprox_spec ht (abs_le.mpr ⟨by linarith,hhi'⟩) hev
    linarith [(abs_le.mp hh).2]
  · intro y hy _
    have hlo' : (0 : ℝ) < p.1 := by exact_mod_cast hlo
    have hhi' : (p.2.1 : ℝ) < 1 := by exact_mod_cast hhi
    have hyy : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1],lt_of_le_of_lt hy.2 hhi'⟩
    have hh := (residualTwoField_hasDerivAt (cs := cs) ht hyy).2
    rw [hAQ] at hh
    exact hh

end

end CatalanMeasure.Cert
