module

public import CatalanMeasure.GenD.KapHelpers
public import CatalanArchive.CatalanMeasure.GenD.P20.Ramps
public import CatalanArchive.CatalanMeasure.GenD.P20.OddProfile

@[expose] public section

/-!
# P20: the nullity lower bound `kap` as the ramp list (instance file)

`segExp segs N p ≤ famKap twenty N p + 1`: cell 0 is U6g, cells 1-2 are S, cell 3 is T, cell 4 is U.
Each comparison is a linear (`omega`) statement, exactly as in `D58.Kap`.
-/

namespace CatalanMeasure.GenD
namespace P20

open PrimeGrowth CatalanMeasure.Parametric

noncomputable section

macro "p20_unfold" : tactic =>
  `(tactic| simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h, design, twenty])

theorem cell0 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 4 * N < p) (h2 : 2 * p ≤ 9 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk (-2) (1 / 2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap design N p + 1 := by
  have happ : U6App design N p := by
    unfold U6App uM0
    p20_unfold
    omega
  have hv := u6Val_le_famKap happ
  have hf := floor_aux (N := N) (p := p) (v := u6Val design N p) (d := 2) (A := -4) (B := 1)
    hN (by norm_num) (by unfold u6Val uM1 uM0 sE; p20_unfold; omega) (c0 := -2) (c1 := 1 / 2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem sApp_p20 {N p : ℕ} (h1 : 4 * N ≤ p) : SApp design N p := by
  unfold SApp
  p20_unfold
  omega

theorem cell1 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 52 * N < 9 * p) (h2 : p ≤ 6 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk (-26) (9 / 2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap design N p + 1 := by
  have hv := sVal_le_famKap (sApp_p20 (N := N) (p := p) (by omega))
  have hf := floor_aux (N := N) (p := p) (v := sVal design N p) (d := 2) (A := -52) (B := 9)
    hN (by norm_num) (by unfold sVal sM1 sM0 sE; p20_unfold; omega) (c0 := -26) (c1 := 9 / 2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem cell2 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 6 * N < p) (h2 : 7 * p ≤ 44 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk 22 (-7 / 2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap design N p + 1 := by
  have hv := sVal_le_famKap (sApp_p20 (N := N) (p := p) (by omega))
  have hf := floor_aux (N := N) (p := p) (v := sVal design N p) (d := 2) (A := 44) (B := -7)
    hN (by norm_num) (by unfold sVal sM1 sM0 sE; p20_unfold; omega) (c0 := 22) (c1 := -7 / 2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem tApp_p20 {N p : ℕ} (hN : 0 < N) (h1 : 22 * N < 3 * p) (h2 : p ≤ 8 * N) :
    TApp design N p := by
  unfold TApp tentD
  p20_unfold
  omega

theorem cell3 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 22 * N < 3 * p) (h2 : p ≤ 8 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk (-22) 3 []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap design N p + 1 := by
  have hv := tVal_le_famKap (tApp_p20 hN h1 h2)
  have hf := floor_aux (N := N) (p := p) (v := tVal design N p) (d := 1) (A := -22) (B := 3)
    hN (by norm_num) (by unfold tVal tentD; p20_unfold; omega) (c0 := -22) (c1 := 3)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem uApp_p20 {N p : ℕ} (h1 : 8 * N < p) (h2 : p ≤ 9 * N) : UApp design N p := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> p20_unfold <;> omega

theorem cell4 {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) (h1 : 8 * N < p) (h2 : p ≤ 9 * N) :
    ⌊(N : ℝ) * ((PL.Prof.mk 18 (-2) []).eval ((p : ℝ) / N))⌋₊ ≤
      famKap design N p + 1 := by
  have hv := uVal_le_famKap (uApp_p20 h1 h2)
  have hf := floor_aux (N := N) (p := p) (v := uVal design N p) (d := 1) (A := 18) (B := -2)
    hN (by norm_num) (by unfold uVal uStar; p20_unfold; omega) (c0 := 18) (c1 := -2)
    (by norm_num) (by norm_num)
  rw [prof_eval_nil]
  omega

theorem segExp_le_famKap {N p : ℕ} (hN : 0 < N) (hodd : p % 2 = 1) :
    segExp segs N p ≤ famKap design N p + 1 := by
  apply segExp_le
  intro s hs hc
  simp only [segs, profSegs, cellProfs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨hc1, hc2⟩ := hc <;> dsimp only at hc1 hc2 ⊢
  · exact cell0 hN hodd (by exact_mod_cast (by linarith : (4 : ℝ) * N < p))
      (by exact_mod_cast (by linarith : (2 : ℝ) * p ≤ 9 * N))
  · exact cell1 hN hodd (by exact_mod_cast (by linarith : (52 : ℝ) * N < 9 * p))
      (by exact_mod_cast (by linarith : (p : ℝ) ≤ 6 * N))
  · exact cell2 hN hodd (by exact_mod_cast (by linarith : (6 : ℝ) * N < p))
      (by exact_mod_cast (by linarith : (7 : ℝ) * p ≤ 44 * N))
  · exact cell3 hN hodd (by exact_mod_cast (by linarith : (22 : ℝ) * N < 3 * p))
      (by exact_mod_cast (by linarith : (p : ℝ) ≤ 8 * N))
  · exact cell4 hN hodd (by exact_mod_cast (by linarith : (8 : ℝ) * N < p))
      (by exact_mod_cast (by linarith : (p : ℝ) ≤ 9 * N))

end

end P20
end CatalanMeasure.GenD
