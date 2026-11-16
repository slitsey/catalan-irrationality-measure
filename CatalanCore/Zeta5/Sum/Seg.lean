module

public import CatalanCore.Zeta5.Sum.OuterCell

@[expose] public section

/-!
# Segments: one kernel declaration per chunk of a cut list

`SegInt H l e v` says `∫_l^e H(t) t⁻³ dt = v` (with integrability and `0 < l`). A chunk of a cut
list is certified by one Boolean (`segR`, `segG`, `segE`, `segH`: cell test, value and end point
of `Profile.chain`), and chunks are glued by `SegInt.trans`. This is the one-value-per-declaration
pattern of the lean-efficient skill (§3.2): the generic soundness theorems `chain_sound` are
proved once in `Profile`/`OuterCell`, each chunk is a small `decide +kernel`.
-/

open Set MeasureTheory

namespace CatalanCore.Zeta5.Sum

open CatalanCore.Zeta5.Profile

/-- `∫_l^e H(t) t⁻³ dt = v`, with integrability and `0 < l`. -/
def SegInt (H : ℝ → ℝ) (l e v : ℚ) : Prop :=
  0 < l ∧ IntervalIntegrable (fun t => H t / t ^ 3) volume (l : ℝ) (e : ℝ) ∧
    ∫ t in (l : ℝ)..(e : ℝ), H t / t ^ 3 = (v : ℝ)

theorem SegInt.trans {H : ℝ → ℝ} {a b c v w : ℚ} (h1 : SegInt H a b v) (h2 : SegInt H b c w) :
    SegInt H a c (v + w) := by
  obtain ⟨ha, hi1, hv1⟩ := h1
  obtain ⟨hb, hi2, hv2⟩ := h2
  refine ⟨ha, hi1.trans hi2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hv1, hv2]
  push_cast; ring

/-- Soundness of one chunk, generic in the evaluator. -/
theorem seg_sound {H : ℝ → ℝ} {h : ℚ → ℚ} (hh : ∀ q : ℚ, H q = h q)
    {ok : ℚ → List ℚ → Bool}
    (hok : ∀ (ts : List ℚ) (l : ℚ), ok l ts = true →
      okChain (fun l r => ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, H t = A * t + B) l ts)
    {l : ℚ} {ts : List ℚ} {v e : ℚ}
    (hc : (decide (0 < l) && ok l ts && decide (chain h l ts = v) && decide (endpt l ts = e)) = true) :
    SegInt H l e v := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hl, hok'⟩, hv⟩, he⟩ := hc
  obtain ⟨hi, hval⟩ := chain_sound hh ts l hl (hok ts l hok')
  rw [he] at hi hval
  rw [hv] at hval
  exact ⟨hl, hi, hval⟩

/-- A chunk of the cut list of `R`. -/
def segR (l : ℚ) (ts : List ℚ) (v e : ℚ) : Bool :=
  decide (0 < l) && chainOK l ts && decide (chain Rg l ts = v) && decide (endpt l ts = e)

theorem segR_sound {l : ℚ} {ts : List ℚ} {v e : ℚ} (h : segR l ts v e = true) :
    SegInt Rg l e v :=
  seg_sound (H := (Rg : ℝ → ℝ)) (h := (Rg : ℚ → ℚ)) (fun q => (Rg_cast q).symm)
    (ok := chainOK) okChain_of_chainOK h

/-- A chunk of the cut list of `g_ref`. -/
def segG (l : ℚ) (ts : List ℚ) (v e : ℚ) : Bool :=
  decide (0 < l) && chainOKg l ts && decide (chain gref l ts = v) && decide (endpt l ts = e)

theorem segG_sound {l : ℚ} {ts : List ℚ} {v e : ℚ} (h : segG l ts v e = true) :
    SegInt gref l e v :=
  seg_sound (H := (gref : ℝ → ℝ)) (h := (gref : ℚ → ℚ)) (fun q => (gref_cast q).symm)
    (ok := chainOKg) okChain_of_chainOKg h

/-- A chunk of the cut list of `x T₀(1/x)`. -/
def segE (l : ℚ) (ts : List ℚ) (v e : ℚ) : Bool :=
  decide (0 < l) && chainOKE l ts && decide (chain Ex l ts = v) && decide (endpt l ts = e)

theorem segE_sound {l : ℚ} {ts : List ℚ} {v e : ℚ} (h : segE l ts v e = true) :
    SegInt Ex l e v :=
  seg_sound (H := (Ex : ℝ → ℝ)) (h := (Ex : ℚ → ℚ)) (fun q => (Ex_cast q).symm)
    (ok := chainOKE) okChain_of_chainOKE h

/-- A chunk of the cut list of the outer saving `[x T₀(1/x) − R(x)]₊`. -/
def segH (l : ℚ) (ts : List ℚ) (v e : ℚ) : Bool :=
  decide (0 < l) && chainOKH l ts && decide (chain Hp l ts = v) && decide (endpt l ts = e)

theorem segH_sound {l : ℚ} {ts : List ℚ} {v e : ℚ} (h : segH l ts v e = true) :
    SegInt (fun t : ℝ => max 0 (Ex t - Rg t)) l e v :=
  seg_sound (H := fun t : ℝ => max 0 (Ex t - Rg t)) (h := Hp) (fun q => (Hp_cast q).symm)
    (ok := chainOKH) okChain_of_chainOKH h

end CatalanCore.Zeta5.Sum
