module

public import CatalanMeasure.GenD.Signed.RouteI.G16
public import CatalanMeasure.GenD.Signed.RouteI.ChordPairData
public import CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance

@[expose] public section
set_option Elab.async false

/-!
# Route I `ChordPair`: the three open items of the residual pair cover (ledger G16, G32)

For `Cert590.residual_pair` (`PositiveCert.RCoverPair`):

* `hdh_table`: the chord hypothesis `hdh` with `dh = δc = pwl 865 kt vt` of `ChordTableData`, from the cell data
  `ChordPairData.pair_chord`;
* `qSum_aDu_eq`: `qSum aDuList 1 x = barrierTrialT (trialSeqOf du40 2^24) x`;
* `hG_window`: the window of `Gd` restricted to `401/2500 ≤ |x|` in the form `residual_pair` asks for;
* `residual_pair_Gd`: `residual_pair` for the window `G = Gd ∧ 401/2500 ≤ |x|` and `dh = δc`, with the trial
  in `barrierTrialT` form.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.ChordPair

open CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.ChordTable
  CatalanMeasure.GenD.Signed.RouteI.ChordTableData CatalanMeasure.GenD.Signed.RouteI.ChordLine
  CatalanMeasure.GenD.Signed.RouteI.ChordPairData CatalanMeasure.GenD.Signed.RouteI.TerminalC
  CatalanMeasure.GenD.Signed.RouteI.G16 CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.CellCert
  CatalanMeasure.GenD.Cert.TrialCell CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
  CatalanMeasure.Signed.ChebSquare OAI.InternalCatalan Set

noncomputable section

theorem TT_real : ((TT : ℤ) : ℝ) = 1099511627776 := by norm_num [CellCert.TT]

/-- **`hdh`**: `δ̂(2y/(1+y²))/58 ≤ ddTab` on every cell of the pair cover. -/
theorem hdh_table : ∀ b ∈ blocksP, ∀ c ∈ b.cells, ∀ y : ℝ, |y - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT →
    δc (2 * y / (1 + y ^ 2)) / 58 ≤ (tabGet ddTab c.1 : ℝ) := by
  intro b hb c hc y hy
  have h1 := List.all_eq_true.mp pair_chord b hb
  have h2 := List.all_eq_true.mp h1 c hc
  unfold pairChk at h2
  cases hl : lookupCC pairTab c.1 with
  | none => rw [hl] at h2; simp at h2
  | some cc =>
    rw [hl] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨hy', hdd⟩ := h2
    have hdd' : (0 : ℝ) ≤ (tabGet ddTab c.1 : ℝ) := by exact_mod_cast hdd
    rw [TT_real] at hy
    have hab := abs_le.mp hy
    by_cases hh : kt 0 ≤ 2 * y / (1 + y ^ 2) ∧ 2 * y / (1 + y ^ 2) ≤ kt 865
    · have := yChk_sound hy' (y := y) (by push_cast; linarith) (by push_cast; linarith)
        hh.1 hh.2
      push_cast at this
      have h' : δc (2 * y / (1 + y ^ 2)) ≤
          58 * ((tabGet ddTab c.1 : ℚ) : ℝ) + 0 * (2 * y / (1 + y ^ 2)) := this
      rw [div_le_iff₀ (by norm_num)]
      linarith
    · have h0 : δc (2 * y / (1 + y ^ 2)) = 0 := by
        apply pwl_zero_outside kt_lt
        by_contra hn
        push Not at hn
        exact hh hn
      rw [h0]
      simpa using hdd'

/-! ### The trial term -/

theorem qSum_eq_sum (l : List ℚ) : ∀ (k : ℕ) (x : ℝ),
    qSum l k x = ∑ i ∈ Finset.range l.length, (l.getD i 0 : ℝ) * basis (k + i) x := by
  induction l with
  | nil => intro k x; simp
  | cons a t ih =>
    intro k x
    rw [qSum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show k + (i + 1) = k + 1 + i by omega]

theorem duL_eq : duL = du40 := by decide +kernel

theorem aDu_getD (i : ℕ) (hi : i < 40) :
    (aDuList.getD i 0 : ℝ) = ((du40.getD i 0 : ℤ) : ℝ) / 16777216 / ((i : ℝ) + 1) := by
  have : aDuList.getD i 0 = ((duL.getD i 0 : ℤ) : ℚ) / 16777216 / ((i + 1 : ℕ) : ℚ) := by
    unfold aDuList
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    simp
  rw [this, duL_eq]
  push_cast
  rfl

theorem aDuList_length : aDuList.length = 40 := by
  unfold aDuList; simp

/-- **The trial identity**: the Chebyshev list `aDuList` of the pair cover is the trial `du40`. -/
theorem qSum_aDu_eq (x : ℝ) :
    qSum aDuList 1 x = barrierTrialT (trialSeqOf du40 (2 ^ 24)) x := by
  rw [trialT_eq_sum, qSum_eq_sum, aDuList_length, len_du40]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < 40 := Finset.mem_range.mp hi
  rw [aDu_getD i hi']
  unfold basis
  rw [add_comm 1 i]
  push_cast
  field_simp

/-! ### The window -/

theorem hG_window : ∀ x : ℝ, (Gd x ∧ (401 / 2500 : ℝ) ≤ |x|) →
    (-9636 / 10000 : ℝ) ≤ x ∧ x ≤ 99942 / 100000 ∧ (401 / 2500 : ℝ) ≤ |x| :=
  fun _ h => ⟨(gd_window h.1).1, (gd_window h.1).2, h.2⟩

/-- **`residual_pair` for the design window**, `dh = δc`, trial in `barrierTrialT` form. -/
theorem residual_pair_Gd (τ : Fin 2) :
    ∀ x ∈ Icc (-1 : ℝ) 1, 401 / 2500 ≤ |x| → Gd x →
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x -
          2 * (τ.val : ℝ) * barrierTrialT (trialSeqOf du40 (2 ^ 24)) x +
          δc (2 * x / (1 + x ^ 2)) / 58 ≤ (if τ.val = 0 then (7 / 1000 : ℝ) else (-268 / 10000 : ℝ)) := by
  intro x hx h401 hG
  have := residual_pair (fun x => Gd x ∧ (401 / 2500 : ℝ) ≤ |x|) δc hG_window hdh_table τ x hx ⟨hG, h401⟩
  rw [qSum_aDu_eq] at this
  exact this

end

end CatalanMeasure.GenD.Signed.RouteI.ChordPair

#print axioms CatalanMeasure.GenD.Signed.RouteI.ChordPair.hdh_table
#print axioms CatalanMeasure.GenD.Signed.RouteI.ChordPair.qSum_aDu_eq
#print axioms CatalanMeasure.GenD.Signed.RouteI.ChordPair.residual_pair_Gd
