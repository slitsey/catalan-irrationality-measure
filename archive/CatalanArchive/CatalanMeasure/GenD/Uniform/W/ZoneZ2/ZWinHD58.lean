module
public import CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZWinH
public import CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZWinD58
@[expose] public section
set_option Elab.async false

/-!
# Law_H(4) window certificates at the design `D58` (G2h)

`zH_winCert_cap` (cap window, `15.15 < x ≤ 15.5`, `L ≤ 5p`): profile `FzHcap x = (7/2) x - 53`.
`zH_winCert_nc` (no cap, `15.6 < x ≤ 16.6`): profile
`FzHnc x = 25 - (3/2) x + min 0 (min (48 - 3x) (x/2 - 5)) + min 0 (69 - 4x)`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.Parametric Filter
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.LedgerW
  CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
noncomputable section

def FzHcap (x : ℝ) : ℝ := 7 / 2 * x - 53
def FzHnc (x : ℝ) : ℝ := 25 - 3 / 2 * x + min 0 (min (48 - 3 * x) (x / 2 - 5)) + min 0 (69 - 4 * x)

theorem ZcH6_pos : 0 < ZcH6 := by
  unfold ZcH6 ZcH'
  exact Nat.lcm_pos (Nat.lcm_pos (by unfold ZcH; decide +kernel)
    (Nat.lcm_pos (by exact Nat.pos_of_ne_zero (by simpa using DqU_num_ne))
      (by exact Nat.pos_of_ne_zero (by simpa using DqY_num_ne)))) (by norm_num)

theorem ZcH'_pos : 0 < ZcH' := by
  unfold ZcH'
  exact Nat.lcm_pos (by unfold ZcH; decide +kernel)
    (Nat.lcm_pos (by exact Nat.pos_of_ne_zero (by simpa using DqU_num_ne))
      (by exact Nat.pos_of_ne_zero (by simpa using DqY_num_ne)))

theorem zHAppCap_d58 {N p : ℕ} (hZ : ZcH6 < p) (h1 : 1515 * N < 100 * p) (h2 : 2 * p ≤ 31 * N)
    (hodd : p % 2 = 1) (hN : 25 ≤ N) :
    zHAppCap design N p ∧ 7 * p + 1 ≤ 2 * zHvalCap design N p + 106 * N := by
  have hnd : ¬ p ∣ ZcH6 := fun h => absurd (Nat.le_of_dvd ZcH6_pos h) (by omega)
  constructor
  · refine ⟨hnd, ?_⟩
    simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
      Parameters.g, Parameters.h, design, D58.Odd.design]
    omega
  · unfold zHvalCap
    simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
      Parameters.g, Parameters.h, design, D58.Odd.design]
    omega

theorem zHApp_d58 {N p : ℕ} (hZ : ZcH' < p) (h1 : 156 * N < 10 * p) (h2 : 10 * p ≤ 166 * N)
    (hodd : p % 2 = 1) (hN : 25 ≤ N) : zHApp design N p := by
  have hnd : ¬ p ∣ ZcH' := fun h => absurd (Nat.le_of_dvd ZcH'_pos h) (by omega)
  refine ⟨hnd, ?_⟩
  simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
    Parameters.g, Parameters.h, design, D58.Odd.design]
  omega

theorem min3_shift (u v u' v' : ℝ) (h1 : u ≤ u' + 1) (h2 : v ≤ v' + 1) :
    min 0 (min u v) ≤ min 0 (min u' v') + 1 := by
  have e : min 0 (min u' v') + 1 = min 1 (min (u' + 1) (v' + 1)) := by
    rw [← min_add_add_right, ← min_add_add_right]; simp
  rw [e]
  exact le_min (le_trans (min_le_left _ _) zero_le_one)
    (le_min (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h1))
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h2)))

theorem zH_winCert_cap {a b c0 c1 : ℝ} (ha : (1515 / 100 : ℝ) ≤ a) (hb : b ≤ 31 / 2)
    (hlin : ∀ x : ℝ, a ≤ x → x ≤ b → c0 + c1 * x ≤ FzHcap x) :
    WinCert (zHLB design D58.Odd.design_admissible) (cw a b c0 c1) := by
  unfold WinCert
  filter_upwards [eventually_ge_atTop (ZcH6 + 25)] with N hN p hp haN hbN
  change a * (N : ℝ) < p at haN
  change (p : ℝ) ≤ b * N at hbN
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have h1r : (1515 : ℝ) * N < 100 * p := by nlinarith
  have h2r : (2 : ℝ) * p ≤ 31 * N := by nlinarith
  have h1 : 1515 * N < 100 * p := by exact_mod_cast h1r
  have h2 : 2 * p ≤ 31 * N := by exact_mod_cast h2r
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  obtain ⟨hA, hv⟩ := zHAppCap_d58 (by omega) h1 h2 hodd (by omega)
  have key := zHLB_kap_ge_cap D58.Odd.design_admissible hA
  refine ⟨?_, pool_cert a b hN0 (by omega)⟩
  have hev : (N : ℝ) * (cw a b c0 c1).K.eval ((p : ℝ) / N) = c0 * N + c1 * p := by
    simp only [cw, PL.Prof.eval, PL.hinges_nil]
    field_simp
    ring
  rw [hev]
  have hx := hlin ((p : ℝ) / N) (by rw [le_div_iff₀ hNr]; exact haN.le)
    (by rw [div_le_iff₀ hNr]; exact hbN)
  have hxN : c0 * N + c1 * p ≤ (N : ℝ) * FzHcap ((p : ℝ) / N) := by
    have := mul_le_mul_of_nonneg_left hx hNr.le
    have e : (N : ℝ) * (c0 + c1 * ((p : ℝ) / N)) = c0 * N + c1 * p := by
      field_simp
    linarith
  have hF : (N : ℝ) * FzHcap ((p : ℝ) / N) = 7 / 2 * p - 53 * N := by
    unfold FzHcap; field_simp
  have hk : (7 * p + 1 : ℤ) ≤ 2 * (((zHLB design D58.Odd.design_admissible).kap N p : ℕ) : ℤ) + 106 * N := by
    have h3 : (zHvalCap design N p : ℤ) ≤ ((zHLB design D58.Odd.design_admissible).kap N p : ℤ) := by
      exact_mod_cast key
    have h4 : (7 * p + 1 : ℤ) ≤ 2 * (zHvalCap design N p : ℤ) + 106 * N := by exact_mod_cast hv
    omega
  have hkR : (7 * p + 1 : ℝ) ≤ 2 * (((zHLB design D58.Odd.design_admissible).kap N p : ℕ) : ℝ) + 106 * N := by
    exact_mod_cast hk
  linarith

theorem zH_winCert_nc {a b c0 c1 : ℝ} (ha : (156 / 10 : ℝ) ≤ a) (hb : b ≤ 166 / 10)
    (hlin : ∀ x : ℝ, a ≤ x → x ≤ b → c0 + c1 * x ≤ FzHnc x) :
    WinCert (zHLB design D58.Odd.design_admissible) (cw a b c0 c1) := by
  unfold WinCert
  filter_upwards [eventually_ge_atTop (ZcH' + 25)] with N hN p hp haN hbN
  change a * (N : ℝ) < p at haN
  change (p : ℝ) ≤ b * N at hbN
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have h1r : (156 : ℝ) * N < 10 * p := by nlinarith
  have h2r : (10 : ℝ) * p ≤ 166 * N := by nlinarith
  have h1 : 156 * N < 10 * p := by exact_mod_cast h1r
  have h2 : 10 * p ≤ 166 * N := by exact_mod_cast h2r
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hA := zHApp_d58 (by omega) h1 h2 hodd (by omega)
  have key := zHLB_kap_ge_nc D58.Odd.design_admissible hodd hA
  refine ⟨?_, pool_cert a b hN0 (by omega)⟩
  have hev : (N : ℝ) * (cw a b c0 c1).K.eval ((p : ℝ) / N) = c0 * N + c1 * p := by
    simp only [cw, PL.Prof.eval, PL.hinges_nil]
    field_simp
    ring
  rw [hev]
  have hx := hlin ((p : ℝ) / N) (by rw [le_div_iff₀ hNr]; exact haN.le)
    (by rw [div_le_iff₀ hNr]; exact hbN)
  have hxN : c0 * N + c1 * p ≤ (N : ℝ) * FzHnc ((p : ℝ) / N) := by
    have := mul_le_mul_of_nonneg_left hx hNr.le
    have e : (N : ℝ) * (c0 + c1 * ((p : ℝ) / N)) = c0 * N + c1 * p := by
      field_simp
    linarith
  have hF : (N : ℝ) * FzHnc ((p : ℝ) / N) =
      25 * N - 3 / 2 * p + min 0 (min (48 * N - 3 * (p : ℝ)) ((p : ℝ) / 2 - 5 * N)) +
        min 0 (69 * N - 4 * (p : ℝ)) := by
    unfold FzHnc
    have e1 : (N : ℝ) * min 0 (min (48 - 3 * ((p : ℝ) / N)) (((p : ℝ) / N) / 2 - 5)) =
        min 0 (min (48 * N - 3 * (p : ℝ)) ((p : ℝ) / 2 - 5 * N)) := by
      rw [mul_min_of_nonneg _ _ hNr.le, mul_min_of_nonneg _ _ hNr.le, mul_zero]
      congr 2 <;> field_simp
    have e2 : (N : ℝ) * min 0 (69 - 4 * ((p : ℝ) / N)) = min 0 (69 * N - 4 * (p : ℝ)) := by
      rw [mul_min_of_nonneg _ _ hNr.le, mul_zero]
      congr 1; field_simp
    have e0 : (N : ℝ) * (25 - 3 / 2 * ((p : ℝ) / N)) = 25 * N - 3 / 2 * p := by
      field_simp
    calc (N : ℝ) * (25 - 3 / 2 * ((p : ℝ) / N) +
          min 0 (min (48 - 3 * ((p : ℝ) / N)) (((p : ℝ) / N) / 2 - 5)) + min 0 (69 - 4 * ((p : ℝ) / N)))
        = (N : ℝ) * (25 - 3 / 2 * ((p : ℝ) / N)) +
          (N : ℝ) * min 0 (min (48 - 3 * ((p : ℝ) / N)) (((p : ℝ) / N) / 2 - 5)) +
          (N : ℝ) * min 0 (69 - 4 * ((p : ℝ) / N)) := by ring
      _ = _ := by rw [e0, e1, e2]
  -- integer bound
  have dn : design.n N = 58 * N := by simp only [Parameters.n, design, D58.Odd.design]
  have dg : design.g N = 5 * N := by simp only [Parameters.g, design, D58.Odd.design]
  have dh : design.h N = 3 * N := by simp only [Parameters.h, design, D58.Odd.design]
  have dq : design.q N = 3 * N := by simp only [Parameters.q, design, D58.Odd.design]
  have db : design.b N = 9 * N := by simp only [Parameters.b, design, D58.Odd.design]
  have dH : design.H N = 78 * N := by
    simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
      Parameters.g, Parameters.h, design, D58.Odd.design]; omega
  rw [dn, dg, dh, dq, db, dH] at key
  have hpo2 : 2 * ((p - 1) / 2) + 1 = p := by omega
  generalize (p - 1) / 2 = hq at key hpo2
  set k : ℕ := (zHLB design D58.Odd.design_admissible).kap N p with hk
  have key' : -3 * (p : ℤ) + 1 + 50 * N +
      2 * (min 0 (min (53 * (N : ℤ) - 1 - 3 * p - 5 * N) (hq - 5 * N)) + min 0 (69 * (N : ℤ) - 4 * p))
        ≤ 2 * (k : ℤ) := by
    push_cast at key
    omega
  have hkR : -3 * (p : ℝ) + 1 + 50 * N +
      2 * (min 0 (min (53 * (N : ℝ) - 1 - 3 * p - 5 * N) (hq - 5 * N)) + min 0 (69 * (N : ℝ) - 4 * p))
        ≤ 2 * (k : ℝ) := by
    exact_mod_cast key'
  have hpo : (hq : ℝ) = ((p : ℝ) - 1) / 2 := by
    have h' : (2 : ℝ) * (hq : ℝ) + 1 = p := by exact_mod_cast hpo2
    linarith
  rw [hpo] at hkR
  have m3 := min3_shift (48 * N - 3 * (p : ℝ)) ((p : ℝ) / 2 - 5 * N)
    (53 * (N : ℝ) - 1 - 3 * p - 5 * N) (((p : ℝ) - 1) / 2 - 5 * N) (by linarith) (by linarith)
  have hgoal : c0 * N + c1 * p - 2 ≤ (k : ℝ) := by
    linarith [hxN, hF, hkR, m3]
  exact hgoal

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
