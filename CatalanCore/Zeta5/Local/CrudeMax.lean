module

public import CatalanCore.Zeta5.Local.SmallPrimeTau

@[expose] public section

/-!
# Row ZC07 (second half): (I8) with the exact exponent `⌊log_p max(2K, d+1)⌋`

`crude_tauX` (ported) is stated for `2K ≤ d` with exponent `⌊log_p (d+1)⌋`.  `crude_tauX_max`
covers every `d` with the ledger exponent: for `d < 2K` the polynomial part vanishes.
-/

open Finset Polynomial

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

/-- **ZC07, (I8)**: `A` integer-valued of degree `≤ d`, `K ≥ 1`,
`v_p^G(τ_X((K!)² A / ∏_{0<|r|≤K}(x - r))) ≥ -6 ⌊log_p max(2K, d+1)⌋ - v_p(24)`. -/
theorem crude_tauX_max {K d : ℕ} (hK : 1 ≤ K) (A : ℚ[X]) (hA : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0) :
    GV p (tauX (C ((K.factorial : ℚ) ^ 2) * A) (PlK K))
      (-6 * (Nat.log p (max (2 * K) (d + 1)) : ℚ) - padicValNat p 24) := by
  rcases le_or_gt (2 * K) d with h | h
  · rw [max_eq_right (by omega)]
    exact crude_tauX hK h A hA hint
  · rw [max_eq_left (by omega)]
    set g := C ((K.factorial : ℚ) ^ 2) * A with hg
    set L : ℚ := (Nat.log p (2 * K) : ℚ) with hL
    have hL0 : (0 : ℚ) ≤ L := by positivity
    have hv24 : (0 : ℚ) ≤ padicValNat p 24 := by positivity
    have hgdeg : g.natDegree ≤ d := (natDegree_C_mul_le _ _).trans hA
    have hP0 : polyPart g (PlK K) = 0 := by
      unfold polyPart
      rw [divByMonic_eq_zero_iff (piPl_monic _), degree_eq_natDegree (piPl_monic _).ne_zero,
        natDegree_piPl, card_PlK]
      refine (degree_le_natDegree).trans_lt ?_
      exact_mod_cast (by omega : g.natDegree < 2 * K)
    have hres : ∀ r ∈ PlK K, VG p (resP g (PlK K) r) (-L) := by
      intro r hr
      unfold resP
      rw [hg, eval_mul, eval_C, mul_comm, mul_div_assoc]
      simpa using (hint r).mul (VG_res_factor hr)
    unfold tauX
    rw [hP0]
    refine GV.add (GV.C ?_) (GV.sum _ fun r hr => ?_)
    · left; simp [tau, Lb]
    · obtain ⟨j, hj, ε, hε, hrj⟩ := mem_PlK_iff hr
      have hj' := Finset.mem_Icc.mp hj
      have hdd : dd r ≤ 2 * K := by
        rw [hrj]; rcases hε with rfl | rfl
        · rw [one_mul, dd_nat]; omega
        · rw [neg_one_mul, dd_neg hj'.1]; omega
      have hH : GV p (C (H5 (dd r)) - X) (-5 * L) :=
        (GV.C ((VG_H5_log (p := p) (dd r)).mono (by
          have : (Nat.log p (dd r) : ℚ) ≤ L := log_mono hdd
          linarith))).sub (GV.X.mono (by linarith))
      refine (GV.C_mul (hres r hr) hH).mono ?_
      linarith

end Apery
