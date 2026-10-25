module
public import CatalanFrames.HybCommon.Numer
public import CatalanFrames.HybGen.ExtraAny
@[expose] public section
open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon
namespace CatalanFrames.HybGen
variable {Fr : Frame}
/-- Only the arithmetic hypotheses actually used by the pointwise tropical bound.
There is no L<=4, cm<=4, bad-prime cap, or outer-prime-range cap. -/
structure ArithmeticInfo (I : HybInst Fr) (Lc cm : ℕ) : Prop where
  L_eq : I.cd.L=Lc
  Ebd_le : ∀ N,I.Ebd N+N ≤ Ecub N
  cOf_le : ∀ p,cOf I p ≤ cm
theorem tropExp_le_arithmetic {I : HybInst Fr} {Lc cm : ℕ} (B : ArithmeticInfo I Lc cm) (r m p : ℕ) (hr : 1 ≤ r)
    (hp : p.Prime) :
    (tropExp I r m p : ℝ) ≤ (if p ∈ I.cd.bad then exBad cm r m else 0) +
      ((2 * (r + m) * cntG I r m p : ℕ) : ℝ) +
      (if p ∈ I.cd.bad then 0 else (tropVal (HW I.lev p r m) : ℝ)) := by
  have hn2 : (0 : ℝ) ≤ ((2 * (r + m) * cntG I r m p : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases hX : p ∈ I.cd.bad
  · have hb := tropExp_le_bad I r m p
    have hcB := cnt_bad_G I p r m hp.two_le
    have hlg : Nat.log 2 (I.Ebd (r + 2 * m) + (r + 2 * m)) ≤ Nat.log 2 (Ecub (r + 2 * m)) :=
      Nat.log_mono_right (B.Ebd_le _)
    have hc : cOf I p ≤ cm := B.cOf_le p
    have h1 : tropExp I r m p ≤ cm * (r + m) + 2 * (r + m) * Nat.log 2 (Ecub (r + 2 * m)) := by
      refine hb.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hc) ?_)
      exact Nat.mul_le_mul_left _ (hcB.trans hlg)
    have h1' : (tropExp I r m p : ℝ) ≤
        (cm : ℝ) * (r + m : ℕ) + 2 * (r + m : ℕ) * (Nat.log 2 (Ecub (r + 2 * m)) : ℕ) := by
      exact_mod_cast h1
    rw [if_pos hX, if_pos hX]
    unfold exBad
    push_cast at h1' hn2 ⊢
    nlinarith
  · have hb := tropExp_le I r m p hr hp hX
    rw [cOf_eq_zero I hp hX, zero_mul, zero_add] at hb
    rw [if_neg hX, if_neg hX]
    have hb' : (tropExp I r m p : ℝ) ≤
        ((tropVal (HW I.lev p r m) + 2 * (r + m) * cntG I r m p : ℕ) : ℝ) := by
      exact_mod_cast hb
    push_cast at hb' ⊢
    linarith


/-- Sum the three tropical contributions over an arbitrary finite prime cutoff. -/
theorem sum_le_arbitrary {I : HybInst Fr} {Lc cm : ℕ} {M : ℕ} [NeZero M]
    (Cs : Finset (ZMod M)) (R : ZMod M → ℕ) (r m Bd : ℕ) (T : ℕ → ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ p,0≤w p) (cnt : ℕ → ℕ)
    (hcnt_le : ∀ p,p.Prime → cnt p ≤ Nat.log 2 (Lc*(r+2*m)))
    (hcnt0 : ∀ p,p.Prime → Lc*(r+2*m)<p^2 → cnt p=0)
    (hT : ∀ p,p.Prime → (T p : ℝ) ≤ (if p∈I.cd.bad then exBad cm r m else 0)+
      ((2*(r+m)*cnt p : ℕ) : ℝ)+(if p∈I.cd.bad then 0 else w p))
    (hcls : ∀ p,p.Prime → p∉I.cd.bad → (p : ZMod M)∈Cs)
    (hRb : ∀ c∈Cs,∀ b∈I.cd.bad,(b : ZMod M)=c → b≤R c)
    (ht : ∀ c∈Cs,∀ p,p.Prime → p∉I.cd.bad → (p : ZMod M)=c → R c<p → w p=0) :
    ∑ p∈(Finset.range Bd).filter Nat.Prime,(T p : ℝ)*Real.log p ≤
      extraG Lc Ecub cm (badLog I) r m+∑ c∈Cs,clsSum M c w 0 (R c) := by
  set Q := Lc*(r+2*m) with hQ
  set P := (Finset.range Bd).filter Nat.Prime with hP
  have hpt : ∀ p∈P,(T p : ℝ)*Real.log p ≤
      (((2*(r+m)*cnt p : ℕ) : ℝ)*Real.log p)+
        ((if p∈I.cd.bad then exBad cm r m*Real.log p else 0)+
          (if p∈I.cd.bad then 0 else w p*Real.log p)) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hlog : 0≤Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hh := mul_le_mul_of_nonneg_right (hT p hpp) hlog
    by_cases hb : p∈I.cd.bad
    · simp only [hb,if_true] at hh ⊢;linarith
    · simp only [hb,if_false] at hh ⊢;linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  have hex : ∑ p∈P,((2*(r+m)*cnt p : ℕ) : ℝ)*Real.log p ≤
      ((Nat.sqrt Q : ℝ)+1)*
        (2*(r+m : ℝ)*(Nat.log 2 Q : ℕ)*Real.log ((Lc : ℝ)*(r+2*m)+5)) :=
    ex_sum_bound_any r m Bd Lc (fun p => 2*(r+m)*cnt p) (Nat.log 2 Q)
      (fun p hp => Nat.mul_le_mul_left _ (hcnt_le p hp))
      (fun p hp h => by simp [hcnt0 p hp h])
  have hbad : ∑ p∈P,(if p∈I.cd.bad then exBad cm r m*Real.log p else 0) ≤
      exBad cm r m*badLog I := by
    have hexnn : 0≤exBad cm r m := by unfold exBad;positivity
    rw [←Finset.sum_filter]
    unfold badLog
    rw [Finset.mul_sum]
    have hsub : P.filter (fun p => p∈I.cd.bad)⊆I.cd.bad := fun x hx => (Finset.mem_filter.mp hx).2
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ =>
      mul_nonneg hexnn (Real.log_nonneg (by exact_mod_cast (I.cd.bad_prime b hb).one_lt.le))
  have hg : ∑ p∈P,(if p∈I.cd.bad then 0 else w p*Real.log p) ≤
      ∑ c∈Cs,clsSum M c w 0 (R c) := by
    have hsub : P⊆(Finset.range (Bd+1)).filter Nat.Prime := by
      unfold P
      exact Finset.filter_subset_filter _ (Finset.range_mono (by omega))
    have hmono : ∑ p∈P,(if p∈I.cd.bad then 0 else w p*Real.log p) ≤
        ∑ p∈(Finset.range (Bd+1)).filter Nat.Prime,(if p∈I.cd.bad then 0 else w p*Real.log p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hw0 p)
          (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
    refine (hmono.trans (good_sum_le_cls Cs I.cd.bad w hw0 Bd hcls)).trans ?_
    refine Finset.sum_le_sum fun c hc => ?_
    refine clsSum_le_of_tail c w hw0 (B := Bd) (B' := R c) ?_
    intro p hp1 hpp hpc
    by_cases hb : p∈I.cd.bad
    · exact absurd (hRb c hc p hb hpc) (by omega)
    · exact ht c hc p hpp hb hpc hp1
  unfold extraG
  have e1 : (r+m : ℝ)*(cm+2*(Nat.log 2 (Ecub (r+2*m)) : ℝ))*badLog I =
      exBad cm r m*badLog I := rfl
  rw [e1]
  have e2 : ((Nat.sqrt (Lc*(r+2*m)) : ℝ)+1)*
      (2*(r+m : ℝ)*(Nat.log 2 (Lc*(r+2*m)) : ℝ)*Real.log ((Lc : ℝ)*(r+2*m)+5)) =
      ((Nat.sqrt Q : ℝ)+1)*
        (2*(r+m : ℝ)*(Nat.log 2 Q : ℕ)*Real.log ((Lc : ℝ)*(r+2*m)+5)) := rfl
  rw [e2]
  linarith
/-- Actual Dhyb cutoff is used directly: no false bound by LN+6 is required. -/
theorem log_Dhyb_le_arbitrary {I : HybInst Fr} {Lc cm : ℕ} (B : ArithmeticInfo I Lc cm)
    {M : ℕ} [NeZero M] (Cs : Finset (ZMod M)) (R : ZMod M → ℕ)
    (r m : ℕ) (hr : 1≤r) (w : ℕ → ℝ) (hw0 : ∀ p,0≤w p)
    (hw : ∀ p,p.Prime → (tropVal (HW I.lev p r m) : ℝ)≤w p)
    (hcls : ∀ p,p.Prime → p∉I.cd.bad → (p : ZMod M)∈Cs)
    (hRb : ∀ c∈Cs,∀ b∈I.cd.bad,(b : ZMod M)=c → b≤R c)
    (ht : ∀ c∈Cs,∀ p,p.Prime → p∉I.cd.bad → (p : ZMod M)=c → R c<p → w p=0) :
    Real.log (Dhyb I r m) ≤ extraG Lc Ecub cm (badLog I) r m+∑ c∈Cs,clsSum M c w 0 (R c) := by
  rw [log_Dhyb]
  refine sum_le_arbitrary (I := I) Cs R r m (Bnd I r m) (tropExp I r m) w hw0 (cntG I r m)
    (fun p hp => (cntG_le I r m p hp).trans (by rw [B.L_eq]))
    (fun p hp h => cntG_zero I r m p hp (by rw [B.L_eq];exact h)) (fun p hp => ?_) hcls hRb ht
  have hh := tropExp_le_arithmetic B r m p hr hp
  have hww := hw p hp
  by_cases hb : p∈I.cd.bad
  · simpa [hb] using hh
  · simp only [hb,if_false] at hh ⊢
    linarith
end CatalanFrames.HybGen
set_option pp.fullNames true
#print axioms CatalanFrames.HybGen.tropExp_le_arithmetic
#print axioms CatalanFrames.HybGen.sum_le_arbitrary
#print axioms CatalanFrames.HybGen.log_Dhyb_le_arbitrary
