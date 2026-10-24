module
public import CatalanMeasure.Cert.MarkedResidual
@[expose] public section
namespace CatalanMeasure.Cert
open OAI.InternalCatalan Set
noncomputable section

def markedResidualClosedBracketOK (cs : List ℤ) (tail : List TailQ)
    (A Q : List ℚ) (M : ℚ) (p : Piece) : Bool :=
  !p.2.2 || (decide (-1<p.1) && decide (p.1<p.2.1) && decide (p.2.1<1) &&
    bracketOK A Q (markedResidualApprox cs tail) M p)

/-- The same residual certificate on arbitrary closed subintervals of[-1,1].
This makes the physical atom gap an explicit domain parameter. -/
theorem markedResidual_closed_sup_of_checks {cs : List ℤ} {tail : List TailQ}
    {A Q : List ℚ} {a b M : ℚ} {ps : List Piece}
    (ha : -1≤a) (hab : a≤b) (hb : b≤1) (ht : tailsInDisk tail=true)
    (hAQ : fracSum (markedResidualFracs cs tail)=(A,Q))
    (hcover : coverFrom A [] a ps b=true) (hgaps : NoRootGaps A ps)
    (hbr : ps.all (markedResidualClosedBracketOK cs tail A Q M)=true)
    (hleft : markedResidualEndOK cs tail M a=true)
    (hright : markedResidualEndOK cs tail M b=true) :
    ∀ x ∈ Icc (a:ℝ) b, markedResidualField cs tail x ≤ (M:ℝ) := by
  have hend {x : ℚ} (hx : |(x:ℝ)|≤1) (he : markedResidualEndOK cs tail M x=true) :
      markedResidualField cs tail x ≤ (M:ℝ) := by
    unfold markedResidualEndOK at he
    split at he
    · rename_i ve hv
      have hh := markedResidualApprox_spec ht hx hv
      have hr : ((ve.1+ve.2:ℚ):ℝ) ≤ (M:ℝ) := by exact_mod_cast of_decide_eq_true he
      push_cast at hr
      linarith only [(abs_le.mp hh).2,hr]
    · simp at he
  have haR : (-1:ℝ)≤a := by exact_mod_cast ha
  have habR : (a:ℝ)≤b := by exact_mod_cast hab
  have hbR : (b:ℝ)≤1 := by exact_mod_cast hb
  apply GlobalMaxReduction.le_on_Icc_of_critical_le
    ((markedResidualField_continuousOn ht).mono (by
      intro x hx
      exact ⟨haR.trans hx.1,hx.2.trans hbR⟩))
    (by simpa using hend (abs_le.mpr ⟨haR,habR.trans hbR⟩) hleft)
    (by simpa using hend (abs_le.mpr ⟨haR.trans habR,hbR⟩) hright)
  intro x hx hz
  have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨lt_of_le_of_lt haR hx.1,lt_of_lt_of_le hx.2 hbR⟩
  obtain ⟨hQ,hD⟩ := markedResidualField_hasDerivAt ht hx'
  rw [hAQ] at hQ hD
  have hA : lpEval A x=0 := by
    rw [hD.deriv] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hQ
  rcases coverFrom_spec_of_noRoot hcover hgaps hx hA with ⟨e,he,_⟩ | ⟨p,hp,hk,hxp⟩
  · simp at he
  have hc := (List.all_eq_true.mp hbr) p hp
  simp only [markedResidualClosedBracketOK,hk,Bool.not_true,Bool.false_or,
    Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hlo,hlt⟩,hhi⟩,hc⟩ := hc
  apply bracketOK_spec hc hk hlt ?_ ?_ x hxp
  · intro v e hev
    have hloR : (-1:ℝ)<p.1 := by exact_mod_cast hlo
    have hhiR : (p.1:ℝ)<1 := by exact_mod_cast lt_trans hlt hhi
    have hh := markedResidualApprox_spec ht (abs_le.mpr ⟨hloR.le,hhiR.le⟩) hev
    linarith only [(abs_le.mp hh).2]
  · intro y hy _
    have hloR : (-1:ℝ)<p.1 := by exact_mod_cast hlo
    have hhiR : (p.2.1:ℝ)<1 := by exact_mod_cast hhi
    have hy' : y ∈ Ioo (-1:ℝ) 1 := ⟨lt_of_lt_of_le hloR hy.1,lt_of_le_of_lt hy.2 hhiR⟩
    have hd := (markedResidualField_hasDerivAt (cs := cs) ht hy').2
    rw [hAQ] at hd
    exact hd

end
end CatalanMeasure.Cert
