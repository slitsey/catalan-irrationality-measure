module

public import CatalanMeasure.GenD.P20.Kap
public import CatalanMeasure.GenD.DenomGrowth2

@[expose] public section

/-!
# P20: the normalizer and the growth of its denominator (instance file)

`Znorm` is `normalizerOf` for `twenty` (nullity bound `kap = segExp segs - 1`), with
`log D_N ≤ (gD20 + ε) N²`, `gD20 = 42 log 2 + 40 + 2777/4 - 1999/1008`.
-/

namespace CatalanMeasure.GenD
namespace P20

open PrimeGrowth CatalanMeasure.Parametric Filter

noncomputable section

def kapP20 (N p : ℕ) : ℕ := segExp segs N p - 1

theorem odd_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.mp (hp.odd_of_ne_two hp2)

/-- The nullity lower bound of P20. -/
def lb : NullityLB design :=
  NullityLB.ofFam design design_admissible kapP20
    (fun N p hN hp hp2 _ => by
      have := segExp_le_famKap hN (odd_of_prime hp hp2)
      unfold kapP20
      omega)

theorem lb_kap (N p : ℕ) : lb.kap N p = segExp segs N p - 1 := rfl

theorem segExp_zero_outside {N p : ℕ} (hN : 0 < N) (h : p ≤ 4 * N ∨ 9 * N < p) :
    segExp segs N p = 0 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : segExp segs N p ≤ 0 := by
    apply segExp_le
    intro s hs hc
    simp only [segs, profSegs, cellProfs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    obtain ⟨hc1, hc2⟩ := hc
    rcases h with h | h
    · have h' : (p : ℝ) ≤ 4 * N := by exact_mod_cast h
      exfalso
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> dsimp only at hc1 <;> nlinarith
    · have h' : (9 : ℝ) * N < p := by exact_mod_cast h
      exfalso
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> dsimp only at hc2 <;> nlinarith
  omega

theorem segs_bounds : ∀ s ∈ segs, 4 ≤ s.a ∧ s.b ≤ 9 := by
  intro s hs
  simp only [segs, profSegs, cellProfs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> constructor <;> norm_num

theorem rec_ok_p20 : ∀ N q : ℕ, 28 ≤ N → q.Prime → N < q → q ≤ 2 * N →
    2 * design.n N ≤ OddProfile.oddLossNat design N q ∧ lb.kap N q = 0 := by
  intro N q hN hq hNq hqN
  have hN0 : 0 < N := by omega
  refine ⟨?_, ?_⟩
  · unfold OddProfile.oddLossNat
    rw [design_H, if_pos (by omega), lower_eq (by omega)]
    unfold lossNat
    rw [if_pos (by omega)]
    simp only [Parameters.n, design, twenty]
    omega
  · rw [lb_kap, segExp_zero_outside hN0 (Or.inl (by omega))]

theorem hloss_p20 {N p : ℕ} (hN : 0 < N) (hp : p ≤ design.H N) :
    (OddProfile.oddLossNat design N p : ℝ) = N * f20.eval ((p : ℝ) / N) := by
  rw [design_H] at hp
  unfold OddProfile.oddLossNat
  rw [design_H]
  by_cases h : 2 * p ≤ 27 * N
  · rw [if_pos h, lower_eq h]
    exact lossNat_cast hN hp
  · rw [if_neg h, upper_eq (by omega) hp]
    exact lossNat_cast hN hp

theorem hf0_p20 (x : ℝ) (hx : x ≤ 1) : f20.eval x = 40 := by
  simp only [PL.Prof.eval, f20, PL.hinges_cons, PL.hinges_nil]
  rw [PL.ramp_of_le (by linarith : x ≤ 10), PL.ramp_of_le (by linarith : x ≤ 12),
    PL.ramp_of_le (by linarith : x ≤ 27 / 2), PL.ramp_of_le (by linarith : x ≤ 14),
    PL.ramp_of_le (by linarith : x ≤ 16), PL.ramp_of_le (by linarith : x ≤ 24),
    PL.ramp_of_le (by linarith : x ≤ 27)]
  ring

theorem hgain_p20 : ∀ N p : ℕ, 0 < N → p.Prime → design.H N < p ^ 2 → p ≤ design.H N →
    lb.kap N p ≤ OddProfile.oddLossNat design N p ∧
      (0 < lb.kap N p → 2 * design.n N ≤ OddProfile.oddLossNat design N p) := by
  intro N p hN hp hH hpH
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    rw [design_H] at hH
    omega
  have hk : lb.kap N p ≤ design.n N := by
    have h := lb.ok N p hN hp hp2 hH
    haveI : Fact p.Prime := ⟨hp⟩
    exact h.trans (Nat.sub_le _ _)
  have hn : design.n N = 20 * N := by simp [Parameters.n, design, twenty]
  have hloss : 0 < lb.kap N p → OddProfile.oddLossNat design N p = 40 * N := by
    intro hpos
    have hs : 2 ≤ segExp segs N p := by rw [lb_kap] at hpos; omega
    have hout : ¬ (p ≤ 4 * N ∨ 9 * N < p) := by
      intro h
      rw [segExp_zero_outside hN h] at hs
      omega
    push Not at hout
    unfold OddProfile.oddLossNat
    rw [design_H, if_pos (by omega), lower_eq (by omega)]
    unfold lossNat
    rw [if_pos (by omega)]
  constructor
  · by_cases h0 : lb.kap N p = 0
    · rw [h0]; exact Nat.zero_le _
    · rw [hloss (Nat.pos_of_ne_zero h0)]; omega
  · intro hpos
    rw [hloss hpos, hn]; omega

theorem hgood_p20 : ∀ s ∈ segs, Seg.Good (fun N p => lb.kap N p + 1) s := by
  intro s hs
  have hs' := hs
  unfold segs profSegs at hs'
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs'
  have hb := segs_bounds _ hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hb.1; dsimp only at this ⊢; linarith
  · simp only [cellProfs, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · exact t.2.2.continuous.continuousOn
  · intro N p hN hp h1 h2
    have := segExp_ge hs h1 h2
    have h' : segExp segs N p ≤ segExp segs N p - 1 + 1 := by omega
    have h'' : ((segExp segs N p : ℕ) : ℝ) ≤ ((segExp segs N p - 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast h'
    refine this.trans (h''.trans (le_of_eq ?_))
    rfl

theorem hord_p20 : segs.Pairwise (fun s t => s.b ≤ t.a) := by
  simp only [segs, profSegs, cellProfs, List.map_cons, List.map_nil, List.pairwise_cons,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil,
    and_true]
  norm_num

theorem hsq_aux {N p : ℕ} (hN : 0 < N) (h1 : 4 * N < p) (h2 : 2 * p ≤ 9 * N ∨ 5 * N < p) :
    27 * N < p ^ 2 := by
  rcases h2 with h | h
  · have hN2 : 2 ≤ N := by omega
    have : (4 * N + 1) * (4 * N + 1) ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
    nlinarith [Nat.mul_le_mul_left N hN2]
  · have : (5 * N + 1) * (5 * N + 1) ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
    nlinarith [Nat.mul_le_mul_left N hN]

theorem hwin_p20 : ∀ s ∈ segs, ∀ N p : ℕ, 0 < N → p.Prime → s.a * (N : ℝ) < p →
    (p : ℝ) ≤ s.b * N → p ≠ 2 ∧ design.H N < p ^ 2 ∧ p ≤ design.H N := by
  intro s hs N p hN hp h1 h2
  simp only [segs, profSegs, cellProfs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rw [design_H]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> dsimp only at h1 h2
  · have a1 : 4 * N < p := by exact_mod_cast (by linarith : (4 : ℝ) * N < p)
    have a2 : 2 * p ≤ 9 * N := by exact_mod_cast (by linarith : (2 : ℝ) * p ≤ 9 * N)
    exact ⟨by omega, hsq_aux hN a1 (Or.inl a2), by omega⟩
  all_goals
    have a1 : 5 * N < p := by exact_mod_cast (by linarith : (5 : ℝ) * N < p)
    have a2 : p ≤ 9 * N := by exact_mod_cast (by linarith : (p : ℝ) ≤ 9 * N)
    exact ⟨by omega, hsq_aux hN (by omega) (Or.inr a1), by omega⟩

/-- The normalizer of P20. -/
def Znorm : Normalizer design :=
  normalizerOf design design_admissible lb 28 (by rw [design_H]; norm_num)
    (fun N p hN h => side_of hN h) rec_ok_p20

/-- The loss integral: `∫_1^27 f20 = 2777/4`. -/
theorem integral_f20 : ∫ x in (1 : ℝ)..27, f20.eval x = 2777 / 4 := by
  rw [PL.Prof.integral_eval f20 (by norm_num)]
  simp only [PL.Prof.area, f20, PL.hingeInt_cons, PL.hingeInt_nil]
  rw [PL.ramp_of_ge (by norm_num : (10 : ℝ) ≤ 27), PL.ramp_of_ge (by norm_num : (12 : ℝ) ≤ 27),
    PL.ramp_of_ge (by norm_num : (27 / 2 : ℝ) ≤ 27), PL.ramp_of_ge (by norm_num : (14 : ℝ) ≤ 27),
    PL.ramp_of_ge (by norm_num : (16 : ℝ) ≤ 27), PL.ramp_of_ge (by norm_num : (24 : ℝ) ≤ 27),
    PL.ramp_of_ge (by norm_num : (27 : ℝ) ≤ 27),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 10), PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 12),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 27 / 2), PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 14),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 16), PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 24),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 27)]
  norm_num

/-- Growth constant of the denominator in the design's own unit. -/
def gD20 : ℝ := 42 * Real.log 2 + 40 + 2777 / 4 - 1999 / 1008

/-- **Growth of the denominator.** -/
theorem Znorm_growth {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (Znorm.D N : ℝ) ≤ (gD20 + ε) * (N : ℝ) ^ 2 := by
  have hH27 : ((design.H 1 : ℕ) : ℝ) = 27 := by
    rw [design_H]; norm_num
  have h := denom_growth design design_admissible lb f20 segs 40 1
    (fun N p hN hp => hloss_p20 hN hp) hf0_p20
    (by rw [design_H]; norm_num) hgain_p20 hgood_p20 hord_p20 hwin_p20 hε
  rw [hH27, integral_f20, segs_totalArea] at h
  have hA : TwoAdic.A2 (design.n0 : ℝ) (27 : ℝ) (design.b0 : ℝ) = 42 := by
    simp only [TwoAdic.A2, design, twenty]
    norm_num
  rw [hA] at h
  have e : gD20 + ε = 42 * Real.log 2 + (40 + 2777 / 4) - 1999 / 1008 + ε := by
    unfold gD20; ring
  rw [e]
  exact h

end

end P20
end CatalanMeasure.GenD
