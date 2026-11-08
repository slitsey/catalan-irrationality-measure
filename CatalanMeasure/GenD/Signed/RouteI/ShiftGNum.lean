module

public import CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
public import CatalanMeasure.GenD.Signed.RouteI.T4Instance
public import CatalanMeasure.GenD.Signed.RouteI.TrialC
public import CatalanMeasure.GenD.DesignInstance.FirstTrial

@[expose] public section

/-!
# G5 shiftG, numbers: the norm constants of the shift records and the inner products of design C

For a finite list-sequence `trialSeqOf l D` (entry `k` at index `k + 1`) the weighted inner products of
`barrierInner` are finite sums, and against a K590 base sequence `trialSeqS Pc P` (or `trialSeq Pc P`,
first population) they are `T4Instance.trial_sum` evaluations (`finPart + allTails`, exact rationals).

* second population (K = 40 trial `du40`, `dv40` over `2^24`):
  `cr2 = 4 <p₀, du> + <v₀, dv>`, `qd2 = 2 |du|² + |dv|²/2`;
* first population (K = 24 trial, doubled `du`): `cr1 = 2 <p₀, du> + <v₀, dv>`,
  `qd1 = |du|² + |dv|²/2`;
* signed family (K = 160, `TrialC.da0 …` over `2^40`): `Q₀₀, Q₀₁, Q₁₁` of `hQ00, hQ01, hQ11`.
-/

open Set Finset

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGNum
open CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.T4Instance
  CatalanMeasure.GenD.Signed.RouteI.CompletedGas CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan

noncomputable section

/-! ### Finite sums -/

theorem trialSeqOf_succ (l : List ℤ) (D : ℕ) (k : ℕ) :
    trialSeqOf l D (k + 1) = (l.getD k 0 : ℝ) / D := by simp [trialSeqOf]

theorem inner_trialSeqOf (u : ℕ → ℝ) (l : List ℤ) (D : ℕ) :
    barrierInner u (trialSeqOf l D) =
      ∑ i ∈ range l.length, ((l.getD i 0 : ℝ) / D / ((i + 1 : ℕ) : ℝ)) * u (i + 1) := by
  unfold barrierInner
  simp_rw [trialSeqOf_succ]
  rw [tsum_eq_sum (s := range l.length)]
  · refine sum_congr rfl fun i _ => ?_
    ring
  · intro k hk
    have hlen : l.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default l 0 hlen]
    simp

theorem normSq_trialSeqOf (l : List ℤ) (D : ℕ) :
    barrierTrialNormSq (trialSeqOf l D) =
      ∑ i ∈ range l.length, ((l.getD i 0 : ℝ) / D) ^ 2 / ((i + 1 : ℕ) : ℝ) := by
  unfold barrierTrialNormSq
  simp_rw [trialSeqOf_succ]
  rw [tsum_eq_sum (s := range l.length)]
  intro k hk
  have hlen : l.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default l 0 hlen]
  simp

theorem inner_two (a b : List ℤ) (D : ℕ) (h : a.length = b.length) :
    barrierInner (trialSeqOf a D) (trialSeqOf b D) =
      ∑ i ∈ range a.length, ((a.getD i 0 : ℝ) * (b.getD i 0 : ℝ)) / ((D : ℝ) ^ 2 * ((i + 1 : ℕ) : ℝ)) := by
  rw [inner_trialSeqOf, ← h]
  refine sum_congr rfl fun i _ => ?_
  rw [trialSeqOf_succ]
  by_cases hD : (D : ℝ) = 0
  · simp [hD]
  · field_simp

/-! ### The rational weights and the exact evaluation -/

/-- The weight list `l_i / (D (i+1))`. -/
def wQ (l : List ℤ) (D : ℕ) : List ℚ :=
  (List.range l.length).map fun i => (l.getD i 0 : ℚ) / D / ((i + 1 : ℕ) : ℚ)

theorem wQ_length (l : List ℤ) (D : ℕ) : (wQ l D).length = l.length := by simp [wQ]

theorem wQ_getD (l : List ℤ) (D : ℕ) {i : ℕ} (hi : i < l.length) :
    ((wQ l D).getD i 0 : ℝ) = (l.getD i 0 : ℝ) / D / ((i + 1 : ℕ) : ℝ) := by
  simp [wQ, List.getD_eq_getElem?_getD, hi]

/-- `<trialSeqS Pc P, trialSeqOf l D>` as an exact rational (`finPart + allTails`). -/
theorem innerS_eq (Pc : List ℤ) (tl : List TailQ) (l : List ℤ) (D : ℕ) :
    barrierInner (trialSeqS Pc tl) (trialSeqOf l D) =
      ((finPart Pc (wQ l D) 0 + allTails (wQ l D) tl : ℚ) : ℝ) := by
  rw [inner_trialSeqOf, ← trial_sum, wQ_length]
  refine sum_congr rfl fun i hi => ?_
  rw [wQ_getD l D (Finset.mem_range.mp hi)]

/-! ### The first population: scale `10^8` (`FirstStrongTrial`) -/

def finPart8 (Pc : List ℤ) : List ℚ → ℕ → ℚ
  | [], _ => 0
  | c :: cs, n => c * ((Pc.getD n 0 : ℚ) / 100000000) + finPart8 Pc cs (n + 1)

theorem finPart8_eq (Pc : List ℤ) (cs : List ℚ) : ∀ n : ℕ,
    ((finPart8 Pc cs n : ℚ) : ℝ) =
      ∑ i ∈ range cs.length, (cs.getD i 0 : ℝ) * ((Pc.getD (n + i) 0 : ℝ) / 100000000) := by
  induction cs with
  | nil => intro n; simp [finPart8]
  | cons c cs ih =>
    intro n
    simp only [finPart8, List.length_cons]
    rw [sum_range_succ']
    push_cast
    rw [ih (n + 1), add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    simp only [List.getD_cons_succ]
    rw [show n + 1 + i = n + (i + 1) by ring]

theorem trial_sum8 (Pc : List ℤ) (tl : List TailQ) (cs : List ℚ) :
    ∑ i ∈ range cs.length, (cs.getD i 0 : ℝ) * trialSeq Pc tl (i + 1) =
      ((finPart8 Pc cs 0 + allTails cs tl : ℚ) : ℝ) := by
  push_cast
  rw [finPart8_eq, allTails_eq, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [trialSeq, barrierTrial, barrierFiniteCoeff, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ite_false, Nat.add_sub_cancel, Nat.zero_add, List.map_map]
  ring

/-- `<trialSeq Pc P, trialSeqOf l D>` as an exact rational. -/
theorem innerT_eq (Pc : List ℤ) (tl : List TailQ) (l : List ℤ) (D : ℕ) :
    barrierInner (trialSeq Pc tl) (trialSeqOf l D) =
      ((finPart8 Pc (wQ l D) 0 + allTails (wQ l D) tl : ℚ) : ℝ) := by
  rw [inner_trialSeqOf, ← trial_sum8, wQ_length]
  refine sum_congr rfl fun i hi => ?_
  rw [wQ_getD l D (Finset.mem_range.mp hi)]

/-! ### Exact finite sums over `ℚ` -/

/-- `Σ_i a_i b_i / (D² (i+1))`. -/
def ipQ (a b : List ℤ) (D : ℕ) : ℚ :=
  ((List.range a.length).map fun i => (a.getD i 0 : ℚ) * (b.getD i 0 : ℚ) / ((D : ℚ) ^ 2 * ((i + 1 : ℕ) : ℚ))).sum

theorem lsum_range (f : ℕ → ℚ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem ipQ_eq' (a b : List ℤ) (D : ℕ) :
    ((ipQ a b D : ℚ) : ℝ) =
      ∑ i ∈ range a.length, ((a.getD i 0 : ℝ) * (b.getD i 0 : ℝ)) / ((D : ℝ) ^ 2 * ((i + 1 : ℕ) : ℝ)) := by
  unfold ipQ
  rw [lsum_range]
  push_cast
  rfl

theorem inner_two_Q (a b : List ℤ) (D : ℕ) (h : a.length = b.length) :
    barrierInner (trialSeqOf a D) (trialSeqOf b D) = ((ipQ a b D : ℚ) : ℝ) := by
  rw [inner_two a b D h, ipQ_eq']

theorem normSq_Q (a : List ℤ) (D : ℕ) :
    barrierTrialNormSq (trialSeqOf a D) = ((ipQ a a D : ℚ) : ℝ) := by
  rw [normSq_trialSeqOf, ipQ_eq']
  refine sum_congr rfl fun i _ => ?_
  by_cases hD : (D : ℝ) = 0
  · simp [hD]
  · field_simp


/-! ### The numbers -/

section Numbers
open CatalanMeasure.GenD.D58

/-- `cr2 = 4 <p₀, du> + <v₀, dv>` (second population, K = 40), exact. -/
def cr2Q : ℚ :=
  4 * (finPart Cert590.Pc (wQ du40 (2 ^ 24)) 0 + allTails (wQ du40 (2 ^ 24)) Cert590.P) +
    (finPart Cert590.Vc (wQ dv40 (2 ^ 24)) 0 + allTails (wQ dv40 (2 ^ 24)) Cert590.V)

/-- `qd2 = 2 |du|² + |dv|²/2`, exact. -/
def qd2Q : ℚ := 2 * ipQ du40 du40 (2 ^ 24) + ipQ dv40 dv40 (2 ^ 24) / 2

/-- `cr1 = 2 <p₀', du'> + <v₀', dv>` (first population, K = 24, doubled `du`), exact. -/
def cr1Q : ℚ :=
  2 * (2 * (finPart8 FirstStrongTrial.Pc (wQ du24 (2 ^ 23)) 0 + allTails (wQ du24 (2 ^ 23)) FirstStrongTrial.P)) +
    (finPart8 FirstStrongTrial.Vc (wQ dv24 (2 ^ 24)) 0 + allTails (wQ dv24 (2 ^ 24)) FirstStrongTrial.V)

/-- `qd1 = |du'|² + |dv|²/2`, exact. -/
def qd1Q : ℚ := ipQ du24 du24 (2 ^ 23) + ipQ dv24 dv24 (2 ^ 24) / 2

/-- The signed family: `Q₀₀, Q₀₁, Q₁₁` of `hQ00, hQ01, hQ11`, exact. -/
def q00Q : ℚ := ipQ TrialC.da0 TrialC.da0 (2 ^ 40) + ipQ TrialC.dv0 TrialC.dv0 (2 ^ 40) / 2
def q01Q : ℚ := ipQ TrialC.da0 TrialC.da1 (2 ^ 40) + ipQ TrialC.dv0 TrialC.dv1 (2 ^ 40) / 2
def q11Q : ℚ := ipQ TrialC.da1 TrialC.da1 (2 ^ 40) + ipQ TrialC.dv1 TrialC.dv1 (2 ^ 40) / 2

-- kcost: 14.6 s measured, 75 tails x 40 weights over Q (two lists)
theorem cr2_le : cr2Q ≤ (-117647903 : ℚ) / 1000000000 := by decide +kernel
-- kcost: 0.8 s measured, 80 rational terms
theorem qd2_le : qd2Q ≤ (5215061 : ℚ) / 1000000000 := by decide +kernel
-- kcost: 1.5 s measured, 8 tails x 24 weights over Q (two lists)
theorem cr1_le : cr1Q ≤ (-82834152 : ℚ) / 1000000000 := by decide +kernel
-- kcost: 2.5 s measured, 48 rational terms
theorem qd1_le : qd1Q ≤ (4096781 : ℚ) / 1000000000 := by decide +kernel
-- kcost: 1.5 s measured, 640 rational terms (three sums of 320)
theorem q00_le : q00Q ≤ (16623 : ℚ) / 100000000000 := by decide +kernel -- kcost: 1.5 s measured, 640 rational terms
theorem q01_le : q01Q ≤ (95232 : ℚ) / 100000000000 := by decide +kernel -- kcost: 1.5 s measured, 640 rational terms
theorem q11_le : q11Q ≤ (1002863 : ℚ) / 1000000000 := by decide +kernel -- kcost: 1.5 s measured, 640 rational terms

theorem len_TC : TrialC.da0.length = 160 ∧ TrialC.dv0.length = 160 ∧ TrialC.da1.length = 160 ∧
    TrialC.dv1.length = 160 := by
  exact ⟨TrialC.len_da0, TrialC.len_dv0, TrialC.len_da1, TrialC.len_dv1⟩

/-! ### The real statements -/

/-- The doubled-trial sequences and lists of the shift records. -/
def duS : ℕ → ℝ := trialSeqOf du40 (2 ^ 24)
def dvS : ℕ → ℝ := trialSeqOf dv40 (2 ^ 24)
def duF : ℕ → ℝ := trialSeqOf du24 (2 ^ 23)
def dvF : ℕ → ℝ := trialSeqOf dv24 (2 ^ 24)

theorem cr2_real : 4 * barrierInner (trialSeqS Cert590.Pc Cert590.P) duS +
    barrierInner (trialSeqS Cert590.Vc Cert590.V) dvS ≤ (-117647903 : ℝ) / 1000000000 := by
  have h := cr2_le
  have e : (cr2Q : ℝ) = 4 * barrierInner (trialSeqS Cert590.Pc Cert590.P) duS +
      barrierInner (trialSeqS Cert590.Vc Cert590.V) dvS := by
    unfold cr2Q duS dvS
    rw [innerS_eq, innerS_eq]
    push_cast
    ring
  have h' : (cr2Q : ℝ) ≤ ((-117647903 / 1000000000 : ℚ) : ℝ) := Rat.cast_le.mpr h
  rw [e] at h'
  push_cast at h'
  linarith

theorem qd2_real : 2 * barrierTrialNormSq duS + barrierTrialNormSq dvS / 2 ≤ (5215061 : ℝ) / 1000000000 := by
  have h := qd2_le
  have e : (qd2Q : ℝ) = 2 * barrierTrialNormSq duS + barrierTrialNormSq dvS / 2 := by
    unfold qd2Q duS dvS
    rw [normSq_Q, normSq_Q]
    push_cast
    ring
  have h' : (qd2Q : ℝ) ≤ ((5215061 / 1000000000 : ℚ) : ℝ) := Rat.cast_le.mpr h
  rw [e] at h'
  push_cast at h'
  linarith

theorem cr1_real : 2 * barrierInner D58.firstP duF + barrierInner D58.firstV dvF ≤
    (-82834152 : ℝ) / 1000000000 := by
  have h := cr1_le
  have hp : barrierInner D58.firstP (trialSeqOf du24 (2 ^ 23)) =
      2 * barrierInner (trialSeq FirstStrongTrial.Pc FirstStrongTrial.P) (trialSeqOf du24 (2 ^ 23)) := by
    unfold barrierInner D58.firstP
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring
  have e : (cr1Q : ℝ) = 2 * barrierInner D58.firstP duF + barrierInner D58.firstV dvF := by
    unfold cr1Q duF dvF
    rw [hp, D58.firstV, innerT_eq, innerT_eq]
    push_cast
    ring
  have h' : (cr1Q : ℝ) ≤ ((-82834152 / 1000000000 : ℚ) : ℝ) := Rat.cast_le.mpr h
  rw [e] at h'
  push_cast at h'
  linarith

theorem qd1_real : barrierTrialNormSq duF + barrierTrialNormSq dvF / 2 ≤ (4096781 : ℝ) / 1000000000 := by
  have h := qd1_le
  have e : (qd1Q : ℝ) = barrierTrialNormSq duF + barrierTrialNormSq dvF / 2 := by
    unfold qd1Q duF dvF
    rw [normSq_Q, normSq_Q]
    push_cast
    ring
  have h' : (qd1Q : ℝ) ≤ ((4096781 / 1000000000 : ℚ) : ℝ) := Rat.cast_le.mpr h
  rw [e] at h'
  push_cast at h'
  linarith

/-- `hQ00`, `hQ01`, `hQ11` of `NearData` at the frozen lists. -/
theorem hQ00_real : barrierInner (trialSeqOf TrialC.da0 (2 ^ 40)) (trialSeqOf TrialC.da0 (2 ^ 40)) +
    barrierInner (trialSeqOf TrialC.dv0 (2 ^ 40)) (trialSeqOf TrialC.dv0 (2 ^ 40)) / 2 ≤
      (16623 : ℝ) / 100000000000 := by
  have h := q00_le
  rw [inner_two_Q _ _ _ (by rw [TrialC.len_da0]), inner_two_Q _ _ _ (by rw [TrialC.len_dv0])]
  have h' : (q00Q : ℝ) ≤ ((16623 / 100000000000 : ℚ) : ℝ) := Rat.cast_le.mpr h
  unfold q00Q at h'
  push_cast at h' ⊢
  linarith

theorem hQ01_real : barrierInner (trialSeqOf TrialC.da0 (2 ^ 40)) (trialSeqOf TrialC.da1 (2 ^ 40)) +
    barrierInner (trialSeqOf TrialC.dv0 (2 ^ 40)) (trialSeqOf TrialC.dv1 (2 ^ 40)) / 2 ≤
      (95232 : ℝ) / 100000000000 := by
  have h := q01_le
  rw [inner_two_Q _ _ _ (by rw [TrialC.len_da0, TrialC.len_da1]),
    inner_two_Q _ _ _ (by rw [TrialC.len_dv0, TrialC.len_dv1])]
  have h' : (q01Q : ℝ) ≤ ((95232 / 100000000000 : ℚ) : ℝ) := Rat.cast_le.mpr h
  unfold q01Q at h'
  push_cast at h' ⊢
  linarith

theorem hQ11_real : barrierInner (trialSeqOf TrialC.da1 (2 ^ 40)) (trialSeqOf TrialC.da1 (2 ^ 40)) +
    barrierInner (trialSeqOf TrialC.dv1 (2 ^ 40)) (trialSeqOf TrialC.dv1 (2 ^ 40)) / 2 ≤
      (1002863 : ℝ) / 1000000000 := by
  have h := q11_le
  rw [inner_two_Q _ _ _ (by rw [TrialC.len_da1]), inner_two_Q _ _ _ (by rw [TrialC.len_dv1])]
  have h' : (q11Q : ℝ) ≤ ((1002863 / 1000000000 : ℚ) : ℝ) := Rat.cast_le.mpr h
  unfold q11Q at h'
  push_cast at h' ⊢
  linarith

/-! ### The phase-test values and the near-field slope of the base trial -/

theorem p1_num : (90753 / 500000 : ℚ) ≤ finPart Cert590.Pc [1] 0 + allTails [1] Cert590.P := by
  decide +kernel

theorem p1_num' : (1031 / 6250 : ℚ) ≤
    finPart Cert590.Pc [1] 0 + allTails [1] Cert590.P + (du40.getD 0 0 : ℚ) / 2 ^ 24 := by
  decide +kernel

theorem p1_lower : (90753 / 500000 : ℝ) ≤ trialSeqS Cert590.Pc Cert590.P 1 := by
  have h := trial_sum Cert590.Pc Cert590.P [1]
  have h2 : (((90753 / 500000 : ℚ)) : ℝ) ≤
      ((finPart Cert590.Pc [1] 0 + allTails [1] Cert590.P : ℚ) : ℝ) := Rat.cast_le.mpr p1_num
  rw [← h] at h2
  simp [sum_range_succ] at h2
  norm_num at h2 ⊢
  exact h2

theorem p1_lower' : (1031 / 6250 : ℝ) ≤ trialSeqS Cert590.Pc Cert590.P 1 + duS 1 := by
  have h := trial_sum Cert590.Pc Cert590.P [1]
  have h2 : (((1031 / 6250 : ℚ)) : ℝ) ≤
      ((finPart Cert590.Pc [1] 0 + allTails [1] Cert590.P + (du40.getD 0 0 : ℚ) / 2 ^ 24 : ℚ) : ℝ) :=
    Rat.cast_le.mpr p1_num'
  push_cast at h2
  have h3 : (∑ i ∈ range [1].length, (([1] : List ℚ).getD i 0 : ℝ) * trialSeqS Cert590.Pc Cert590.P (i + 1)) =
      ((finPart Cert590.Pc [1] 0 + allTails [1] Cert590.P : ℚ) : ℝ) := h
  simp [sum_range_succ] at h3
  unfold duS
  rw [trialSeqOf_succ]
  push_cast at h3
  norm_num at h2 ⊢
  linarith

end Numbers

end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGNum

#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGNum.innerS_eq
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGNum.innerT_eq
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGNum.inner_two_Q
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGNum.normSq_Q
