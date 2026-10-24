module

public import CatalanMeasure.GenD.PrimeGrowth

@[expose] public section

/-!
# Parity: the generic engine reproduces the P20 content areas (instance file)

The P20 ledger (proof-lemma0-div, section 2.5) has three cells, each used once:
`U6g` on `[4, 9/2]` with profile `(x-4)/2`, area `1/16`; the secondary tent on `[52/9, 44/7]`,
area `16/63`; tent + U3 on `[22/3, 9]` (`3x-22` up to `x = 8`, then `18-2x`), area `5/3`.
Total `1/16 + 16/63 + 5/3 = 1.98313...` per `N²`.  Only numerals appear here.
-/

namespace CatalanMeasure.GenD
namespace Parity

open Filter PL PrimeGrowth
open scoped Topology BigOperators

noncomputable section

def sixth : Prof := ⟨0, 0, [(1/2, 4)]⟩
def secTent : Prof := ⟨0, 0, [(9/2, 52/9), (-8, 6), (7/2, 44/7)]⟩
def tentU3 : Prof := ⟨0, 0, [(3, 22/3), (-5, 8), (2, 9)]⟩

theorem sixth_area : sixth.area 4 (9/2) = 1/16 := by
  norm_num [Prof.area, sixth, hingeInt, ramp, max_def]

theorem secTent_area : secTent.area (52/9) (44/7) = 16/63 := by
  norm_num [Prof.area, secTent, hingeInt, ramp, max_def]

theorem tentU3_area : tentU3.area (22/3) 9 = 5/3 := by
  norm_num [Prof.area, tentU3, hingeInt, ramp, max_def]

/-- Segment check with the generic affine lemma: the rise of the tent+U3 cell. -/
theorem tentU3_rise {x : ℝ} (hx : 22/3 ≤ x ∧ x ≤ 8) : tentU3.eval x = 3 * x - 22 := by
  have h := Prof.eval_affine tentU3 hx (by
    intro wt hwt
    simp only [tentU3, List.mem_cons, List.not_mem_nil, or_false] at hwt
    rcases hwt with rfl | rfl | rfl <;> norm_num)
  rw [h]
  norm_num [tentU3, hingeSlope, hingeIntercept]
  ring

theorem tentU3_fall {x : ℝ} (hx : 8 ≤ x ∧ x ≤ 9) : tentU3.eval x = 18 - 2 * x := by
  have h := Prof.eval_affine tentU3 hx (by
    intro wt hwt
    simp only [tentU3, List.mem_cons, List.not_mem_nil, or_false] at hwt
    rcases hwt with rfl | rfl | rfl <;> norm_num)
  rw [h]
  norm_num [tentU3, hingeSlope, hingeIntercept]
  ring

def p20Segs : List Seg :=
  [⟨4, 9/2, sixth.eval⟩, ⟨52/9, 44/7, secTent.eval⟩, ⟨22/3, 9, tentU3.eval⟩]

theorem p20_totalArea : totalArea p20Segs = 1/16 + 16/63 + 5/3 := by
  have e1 : Seg.area ⟨4, 9/2, sixth.eval⟩ = 1/16 := by
    unfold Seg.area; rw [sixth.integral_eval (by norm_num), sixth_area]
  have e2 : Seg.area ⟨52/9, 44/7, secTent.eval⟩ = 16/63 := by
    unfold Seg.area; rw [secTent.integral_eval (by norm_num), secTent_area]
  have e3 : Seg.area ⟨22/3, 9, tentU3.eval⟩ = 5/3 := by
    unfold Seg.area; rw [tentU3.integral_eval (by norm_num), tentU3_area]
  simp only [totalArea, p20Segs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [e1, e2, e3]; ring

/-- The generic engine at P20: every rate below `1/16 + 16/63 + 5/3` is eventually supplied by
the content `∏ p^(segExp)` over primes up to `27 N` (the P20 value of `H/N`). -/
theorem p20_growth {c : ℝ} (hc : c < 1/16 + 16/63 + 5/3) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ 2 ≤
      ∑ p ∈ (Finset.Ioc 0 (27 * N)).filter Nat.Prime,
        (segExp p20Segs N p : ℝ) * Real.log p := by
  refine growth_segExp p20Segs ?_ ?_ (fun N => (Finset.Ioc 0 (27 * N)).filter Nat.Prime) ?_
    (by rw [p20_totalArea]; exact hc)
  · intro s hs
    simp only [p20Segs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨by norm_num, by norm_num, sixth.continuous.continuousOn⟩
    · exact ⟨by norm_num, by norm_num, secTent.continuous.continuousOn⟩
    · exact ⟨by norm_num, by norm_num, tentU3.continuous.continuousOn⟩
  · simp only [p20Segs, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    norm_num
  · intro N s hs p hp h1 h2
    simp only [p20Segs, List.mem_cons, List.not_mem_nil, or_false] at hs
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hb : (p : ℝ) ≤ 27 * N := by
      rcases hs with rfl | rfl | rfl <;> simp only at h2 <;> nlinarith
    have hp27 : p ≤ 27 * N := by exact_mod_cast hb
    have hpos : 0 < p := hp.pos
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpos, hp27⟩, hp⟩

end
end Parity
end CatalanMeasure.GenD
