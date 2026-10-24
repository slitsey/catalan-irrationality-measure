module
public import CatalanMeasure.Cert.Cover
public import CatalanMeasure.Cert.IntegerGap
@[expose] public section
namespace CatalanMeasure.Cert
open OAI.InternalCatalan Set
noncomputable section

def residualTwoField (cs : List ℤ) (tail : List TailQ) (x : ℝ) : ℝ :=
  -(3/8:ℝ)*Real.log 2 -(89/96:ℝ)*Real.log (1+x^2) -
    2*barrierTrialT (trialSeq cs tail) x

def residualTwoFracs (cs : List ℤ) (tail : List TailQ) : List (List ℚ × List ℚ) :=
  [([0,-89/48],[1,0,1]),(lpSmul (-2) (finUPoly cs),[1])] ++
    tail.map (fun t => (lpSmul (-2) (tailTFrac t).1,(tailTFrac t).2))

theorem residualTwoField_hasDerivAt {cs : List ℤ} {tail : List TailQ}
    (ht : tailsInDisk tail=true) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    lpEval (fracSum (residualTwoFracs cs tail)).2 x ≠ 0 ∧
    HasDerivAt (residualTwoField cs tail)
      (lpEval (fracSum (residualTwoFracs cs tail)).1 x /
        lpEval (fracSum (residualTwoFracs cs tail)).2 x) x := by
  have hxa : |x|≤1 := abs_le.mpr ⟨hx.1.le,hx.2.le⟩
  have hd : 1+x^2≠0 := by positivity
  have htd := tailsInDisk_spec ht
  have hden : ∀ f ∈ residualTwoFracs cs tail,lpEval f.2 x≠0 := by
    intro f hf
    simp only [residualTwoFracs,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,List.mem_map] at hf
    rcases hf with (rfl|rfl)|⟨t,ht',rfl⟩
    · simpa [lpEval,pow_two] using hd
    · simp [lpEval]
    · exact (tailTFrac_spec t (htd _ (List.mem_map_of_mem ht')) hxa).1
  obtain ⟨hQ,hAQ⟩ := fracSum_spec _ x hden
  refine ⟨hQ,?_⟩
  rw [hAQ]
  obtain ⟨s1,s2⟩ := trialSeq_summable (cs := cs) ht
  have hT := barrierTrialT_hasDerivAt_series (barrierTrial cs (tail.map TailQ.toC)) s1 s2 hx
  rw [(barrierTrial_U_hasSum cs _ htd hxa).tsum_eq] at hT
  have hp : HasDerivAt (fun y:ℝ =>1+y^2) (2*x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (1:ℝ)
  have hall := ((hasDerivAt_const x (-(3/8:ℝ)*Real.log 2)).sub
    ((hp.log hd).const_mul (89/96:ℝ))).sub (hT.const_mul 2)
  unfold residualTwoField trialSeq
  refine hall.congr_deriv ?_
  have eT : (tail.map ((fun zr : ℂ × ℂ =>
      zr.2*zr.1/barrierTailQuadraticDen zr.1 x) ∘ TailQ.toC)).sum.re =
      (tail.map (fun t =>lpEval (tailTFrac t).1 x/lpEval (tailTFrac t).2 x)).sum := by
    rw [re_list_sum_map]
    congr 1
    apply List.map_congr_left
    intro t ht'
    exact (tailTFrac_spec t (htd _ (List.mem_map_of_mem ht')) hxa).2
  simp only [List.map_map] at hall ⊢
  rw [eT,← finUPoly_spec]
  have e2 : (tail.map (fun t =>lpEval (lpSmul (-2) (tailTFrac t).1) x /
      lpEval (tailTFrac t).2 x)).sum =
      -2*(tail.map (fun t =>lpEval (tailTFrac t).1 x/lpEval (tailTFrac t).2 x)).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [lpEval_smul]
    push_cast
    ring
  simp only [residualTwoFracs,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.map_map,Function.comp_apply]
  change _ = lpEval [0,-89/48] x/lpEval [1,0,1] x+
    (lpEval (lpSmul (-2) (finUPoly cs)) x/lpEval [1] x+0)+
    (tail.map (fun t =>lpEval (lpSmul (-2) (tailTFrac t).1) x/lpEval (tailTFrac t).2 x)).sum
  rw [e2]
  simp only [lpEval_smul,lpEval_cons,lpEval_nil]
  push_cast
  ring

def residualTwoTerms (tail : List TailQ) (x : ℚ) : List LogTerm :=
  [⟨-3/8,0,2,0⟩,⟨-89/96,0,1+x*x,0⟩] ++
    tail.map (fun t =>⟨t.rr,t.ri,(quadArg x t).1,(quadArg x t).2⟩)

def residualTwoRat (cs : List ℤ) (x : ℚ) : ℚ := -2*finTQ cs x

theorem residualTwoField_eq (cs : List ℤ) (tail : List TailQ)
    (ht : tailsInDisk tail=true) {x : ℚ} (hx : |(x:ℝ)|≤1) :
    residualTwoField cs tail x =
      ((residualTwoTerms tail x).map LogTerm.val).sum+(residualTwoRat cs x:ℝ) := by
  have hT : (tail.map (LogTerm.val ∘ fun t =>
      (⟨t.rr,t.ri,(quadArg x t).1,(quadArg x t).2⟩:LogTerm))).sum =
      (tail.map ((fun zr : ℂ × ℂ =>zr.2 *
        Complex.log (1-2*((x:ℝ):ℂ)*zr.1+zr.1^2)) ∘ TailQ.toC)).sum.re := by
    rw [re_list_sum,List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply,LogTerm.val]
    rw [quadArg_spec]
    rfl
  unfold residualTwoField trialSeq
  rw [barrierTrialT_eq_finite_log cs _ (tailsInDisk_spec ht) hx]
  simp only [residualTwoTerms,residualTwoRat,List.map_append,List.sum_append,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,List.map_map]
  have hd : (0:ℝ)<1+(x:ℝ)*x := by nlinarith [mul_self_nonneg (x:ℝ)]
  have hd' : ((1+x*x:ℚ):ℝ)≠0 := by push_cast; exact hd.ne'
  rw [realLogTerm _ _ (by norm_num : ((2:ℚ):ℝ)≠0),realLogTerm _ _ hd',hT]
  push_cast
  rw [finTQ_spec,abs_of_pos hd]
  push_cast
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  ring

def residualTwoApprox (cs : List ℤ) (tail : List TailQ) (x : ℚ) : Option (ℚ × ℚ) :=
  (sumLogs (residualTwoTerms tail x)).map (fun ve =>(ve.1+residualTwoRat cs x,ve.2))

theorem residualTwoApprox_spec {cs : List ℤ} {tail : List TailQ}
    (ht : tailsInDisk tail=true) {x v e : ℚ} (hx : |(x:ℝ)|≤1)
    (h : residualTwoApprox cs tail x=some (v,e)) :
    |residualTwoField cs tail x-(v:ℝ)|≤(e:ℝ) := by
  unfold residualTwoApprox at h
  cases he : sumLogs (residualTwoTerms tail x) with
  | none => simp [he] at h
  | some ve =>
    simp only [he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    rw [residualTwoField_eq cs tail ht hx]
    push_cast
    simpa using sumLogs_spec he

theorem residualTwoField_continuousOn {cs : List ℤ} {tail : List TailQ}
    (ht : tailsInDisk tail=true) : ContinuousOn (residualTwoField cs tail) (Icc (-1:ℝ) 1) := by
  have hl : Continuous (fun x:ℝ =>Real.log (1+x^2)) := by
    apply Continuous.log (continuous_const.add (continuous_id.pow 2))
    intro x
    exact ne_of_gt (by positivity : (0:ℝ)<1+x^2)
  have hT := barrierTrialT_continuousOn (trialSeq cs tail) (trialSeq_summable (cs := cs) ht).1
  exact (continuousOn_const.sub (hl.continuousOn.const_mul (89/96:ℝ))).sub (hT.const_mul 2)

def residualTwoEndOK (cs : List ℤ) (tail : List TailQ) (M x : ℚ) : Bool :=
  match residualTwoApprox cs tail x with
  | some ve =>decide (ve.1+ve.2≤M)
  | none =>false

def residualTwoBracketOK (cs : List ℤ) (tail : List TailQ) (A Q : List ℚ) (M : ℚ)
    (p : Piece) : Bool :=
  !p.2.2 || (decide (-1<p.1) && decide (p.1<p.2.1) && decide (p.2.1≤0) &&
    bracketOK A Q (residualTwoApprox cs tail) M p)

theorem residualTwo_sup_of_checks {cs : List ℤ} {tail : List TailQ} {A Q : List ℚ}
    {ps : List Piece} {M : ℚ} (ht : tailsInDisk tail=true)
    (hAQ : fracSum (residualTwoFracs cs tail)=(A,Q))
    (hcover : coverFrom A [] (-1) ps 0=true) (hgaps : NoRootGaps A ps)
    (hbr : ps.all (residualTwoBracketOK cs tail A Q M)=true)
    (hleft : residualTwoEndOK cs tail M (-1)=true)
    (hright : residualTwoEndOK cs tail M 0=true) :
    ∀ x ∈ Icc (-1:ℝ) 0,residualTwoField cs tail x≤(M:ℝ) := by
  have hend {x:ℚ} (hx : |(x:ℝ)|≤1) (he : residualTwoEndOK cs tail M x=true) :
      residualTwoField cs tail x≤(M:ℝ) := by
    unfold residualTwoEndOK at he
    split at he
    · rename_i ve hv
      simp only [decide_eq_true_eq] at he
      have hh := residualTwoApprox_spec ht hx hv
      have hv' : (ve.1:ℝ)+(ve.2:ℝ)≤(M:ℝ) := by exact_mod_cast he
      linarith [(abs_le.mp hh).2]
    · simp at he
  apply GlobalMaxReduction.le_on_Icc_of_critical_le (a := (-1:ℝ)) (b := (0:ℝ))
    ((residualTwoField_continuousOn ht).mono (by intro x hx;exact ⟨hx.1,by linarith [hx.2]⟩))
    (by simpa using hend (by norm_num) hleft) (by simpa using hend (by norm_num) hright)
  intro x hx hzero
  have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨hx.1,by linarith [hx.2]⟩
  obtain ⟨hQ,hD⟩ := residualTwoField_hasDerivAt ht hx'
  rw [hAQ] at hQ hD
  have hA : lpEval A x=0 := by
    rw [hD.deriv] at hzero
    exact (div_eq_zero_iff.mp hzero).resolve_right hQ
  rcases coverFrom_spec_of_noRoot hcover hgaps (by simpa using hx) hA with ⟨e,he,_⟩|⟨p,hp,hk,hxp⟩
  · simp at he
  have hbp := (List.all_eq_true.mp hbr) p hp
  simp only [residualTwoBracketOK,hk,Bool.not_true,Bool.false_or,Bool.and_eq_true,
    decide_eq_true_eq] at hbp
  obtain ⟨⟨⟨hlo,hlt⟩,hhi⟩,hb⟩ := hbp
  apply bracketOK_spec hb hk hlt ?_ ?_ x hxp
  · intro v e hev
    have hlo' : (-1:ℝ)<p.1 := by exact_mod_cast hlo
    have hhi' : (p.1:ℝ)≤0 := by exact_mod_cast (le_trans hlt.le hhi)
    have hh := residualTwoApprox_spec ht (abs_le.mpr ⟨hlo'.le,by linarith⟩) hev
    linarith [(abs_le.mp hh).2]
  · intro y hy _
    have hlo' : (-1:ℝ)<p.1 := by exact_mod_cast hlo
    have hhi' : (p.2.1:ℝ)≤0 := by exact_mod_cast hhi
    have hyy : y ∈ Ioo (-1:ℝ) 1 := ⟨lt_of_lt_of_le hlo' hy.1,by linarith [hy.2]⟩
    have hh := (residualTwoField_hasDerivAt (cs := cs) ht hyy).2
    rw [hAQ] at hh
    exact hh

end
end CatalanMeasure.Cert
