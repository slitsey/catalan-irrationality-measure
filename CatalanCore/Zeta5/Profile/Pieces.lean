module

public import Mathlib.Tactic
public import Mathlib.Data.Rat.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-!
# ZC33: the piece evaluator (generic)

For a function `H : ℝ → ℝ` that is affine between the consecutive points of a list of rational
cut points, `∫_{c₀}^{cₙ} H(t) t⁻³ dt` is a finite sum of explicit rationals (the trisection rule
of CONTENT-LEDGER ZC30):
`∫_l^r (A t + B) t⁻³ dt = A (1/l − 1/r) + (B/2)(1/l² − 1/r²)`, where `A, B` are recovered from
the values of `H` at the trisection points `(2l+r)/3`, `(l+2r)/3`.

* `cellVal h l r`   : the value of one piece, computed from the rational function `h` only.
* `chain h l ts`    : the sum over the cut list `l, ts₀, ts₁, …` (structural recursion).
* `okChain P l ts`  : every consecutive pair `l < r` satisfies the cell predicate `P l r`.
* `chain_sound`     : soundness, proved once for every `H` that agrees with `h` on `ℚ`.
-/

open Set MeasureTheory

namespace CatalanCore.Zeta5.Profile

/-- One piece: `A(1/l − 1/r) + B/2 (1/l² − 1/r²)` with `A, B` from the trisection values. -/
def cellVal (h : ℚ → ℚ) (l r : ℚ) : ℚ :=
  let x := (2 * l + r) / 3
  let y := (l + 2 * r) / 3
  let A := 3 * (h y - h x) / (r - l)
  let B := h x - A * x
  A * (1 / l - 1 / r) + B * (1 / l ^ 2 - 1 / r ^ 2) / 2

/-- Sum of the pieces over the cut list `l, ts₀, ts₁, …`. -/
def chain (h : ℚ → ℚ) : ℚ → List ℚ → ℚ
  | _, [] => 0
  | l, r :: t => cellVal h l r + chain h r t

/-- The last point of the cut list. -/
def endpt : ℚ → List ℚ → ℚ
  | l, [] => l
  | _, r :: t => endpt r t

/-- All consecutive pairs are increasing and satisfy the cell predicate `P`. -/
def okChain (P : ℚ → ℚ → Prop) : ℚ → List ℚ → Prop
  | _, [] => True
  | l, r :: t => l < r ∧ P l r ∧ okChain P r t

lemma endpt_append (ts1 ts2 : List ℚ) :
    ∀ l : ℚ, endpt l (ts1 ++ ts2) = endpt (endpt l ts1) ts2 := by
  induction ts1 with
  | nil => intro l; simp [endpt]
  | cons r t ih => intro l; simp [endpt, ih]

/-- Chunking: the value of a long cut list is the sum of the values of its chunks (so each chunk
can be one kernel declaration). -/
lemma chain_append (h : ℚ → ℚ) (ts1 ts2 : List ℚ) :
    ∀ l : ℚ, chain h l (ts1 ++ ts2) = chain h l ts1 + chain h (endpt l ts1) ts2 := by
  induction ts1 with
  | nil => intro l; simp [chain, endpt]
  | cons r t ih => intro l; simp [chain, endpt, ih]; ring

lemma cell_integral {H : ℝ → ℝ} {l r A B : ℝ} (hl : 0 < l) (hlr : l < r)
    (h : ∀ t ∈ Ioo l r, H t = A * t + B) :
    IntervalIntegrable (fun t => H t / t ^ 3) MeasureTheory.volume l r ∧
      ∫ t in l..r, H t / t ^ 3 = A * (1 / l - 1 / r) + B * (1 / l ^ 2 - 1 / r ^ 2) / 2 := by
  have heq : Set.EqOn (fun t => H t / t ^ 3) (fun t => (A * t + B) / t ^ 3) (Set.uIoo l r) := by
    intro t ht
    rw [Set.uIoo_of_le hlr.le] at ht
    simp only [h t ht]
  have hcont : ContinuousOn (fun t : ℝ => (A * t + B) / t ^ 3) (Set.uIcc l r) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    rw [Set.uIcc_of_le hlr.le] at ht
    exact pow_ne_zero _ (by linarith [ht.1])
  have hint : IntervalIntegrable (fun t : ℝ => (A * t + B) / t ^ 3) MeasureTheory.volume l r :=
    hcont.intervalIntegrable
  refine ⟨hint.congr_uIoo heq.symm, ?_⟩
  rw [intervalIntegral.integral_congr_uIoo heq]
  have hd : ∀ t ∈ Set.uIcc l r,
      HasDerivAt (fun t : ℝ => -A / t - B / (2 * t ^ 2)) ((A * t + B) / t ^ 3) t := by
    intro t ht
    rw [Set.uIcc_of_le hlr.le] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have d1 := (hasDerivAt_const t (-A)).div (hasDerivAt_id t) h0
    have d2 := (hasDerivAt_const t B).div ((hasDerivAt_pow 2 t).const_mul 2) (by positivity)
    have := d1.sub d2
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have hl0 : l ≠ 0 := hl.ne'
  have hr0 : r ≠ 0 := (lt_trans hl hlr).ne'
  field_simp
  ring

lemma cellVal_cast {H : ℝ → ℝ} {h : ℚ → ℚ} (hh : ∀ q : ℚ, H q = h q) {l r : ℚ} {A B : ℝ}
    (hlr : l < r) (hA : ∀ t ∈ Ioo (l : ℝ) r, H t = A * t + B) :
    ((cellVal h l r : ℚ) : ℝ) = A * (1 / (l : ℝ) - 1 / r) + B * (1 / (l : ℝ) ^ 2 - 1 / (r : ℝ) ^ 2) / 2 := by
  have hlr' : (l : ℝ) < r := by exact_mod_cast hlr
  have hx : H (((2 * l + r) / 3 : ℚ) : ℝ) = A * ((2 * l + r) / 3 : ℚ) + B := by
    apply hA; push_cast; constructor <;> linarith
  have hy : H (((l + 2 * r) / 3 : ℚ) : ℝ) = A * ((l + 2 * r) / 3 : ℚ) + B := by
    apply hA; push_cast; constructor <;> linarith
  rw [hh] at hx hy
  unfold cellVal
  simp only []
  push_cast
  push_cast at hx hy
  rw [hx, hy]
  have hne : (r : ℝ) - l ≠ 0 := by linarith
  field_simp
  ring

/-- **Soundness of the evaluator**: if `H` is affine on every cell of the cut list and agrees with
the rational function `h` on `ℚ`, then `∫ H(t) t⁻³` over the whole list is `chain h`. -/
theorem chain_sound {H : ℝ → ℝ} {h : ℚ → ℚ} (hh : ∀ q : ℚ, H q = h q) :
    ∀ (ts : List ℚ) (l : ℚ), 0 < l →
      okChain (fun l r => ∃ A B : ℝ, ∀ t ∈ Ioo (l : ℝ) r, H t = A * t + B) l ts →
      IntervalIntegrable (fun t => H t / t ^ 3) MeasureTheory.volume (l : ℝ) (endpt l ts : ℚ) ∧
        ∫ t in (l : ℝ)..(endpt l ts : ℚ), H t / t ^ 3 = ((chain h l ts : ℚ) : ℝ) := by
  intro ts
  induction ts with
  | nil =>
    intro l _ _
    simp [endpt, chain]
  | cons r t ih =>
    intro l hl hok
    obtain ⟨hlr, ⟨A, B, hA⟩, hrest⟩ := hok
    have hlr' : (l : ℝ) < r := by exact_mod_cast hlr
    have hl' : (0 : ℝ) < l := by exact_mod_cast hl
    have hr : 0 < r := lt_trans hl hlr
    obtain ⟨hi1, hv1⟩ := cell_integral hl' hlr' hA
    obtain ⟨hi2, hv2⟩ := ih r hr hrest
    simp only [endpt, chain]
    refine ⟨hi1.trans hi2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hv1, hv2]
    push_cast
    rw [cellVal_cast hh hlr hA]

end CatalanCore.Zeta5.Profile
