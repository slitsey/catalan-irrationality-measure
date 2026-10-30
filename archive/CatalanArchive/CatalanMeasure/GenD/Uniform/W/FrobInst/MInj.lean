module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MSetup
@[expose] public section
set_option Elab.async false

/-!
# Theorem M: row-level independence of the `C` coordinates

If `tRows y + hRows ρ = 0` (three `C` centres `0, p, 2p`, two `H+` blocks), then `y = 0`:
at the rows `(k) p ± s` the coordinates satisfy `y_{s-1,k} + ρ_{s,k} = 0` and
`-y_{s-1,k} + ρ_{s,k-1} = 0`, which chain from `k = 2` down to `k = 0`.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem prof_eq_zero_of_rows (hp2 : p ≠ 2) (hW : MWin P N p)
    (y : Fin (0 + R0 P N p) → Fin 3 → ZMod p)
    (ρ : Fin ((p - 1) / 2 + 1) → Fin 2 → ZMod p)
    (h : ∀ r, tRows P N p 3 (0 + R0 P N p) 0 y r + hRows P N p 2 ((p - 1) / 2 + 1) 0 ρ r = 0) :
    y = 0 := by
  have hodd := native_half_identity hp2
  have hRn : R0 P N p ≤ P.n N - P.g N - 2 * p - 1 := min_le_right _ _
  have hn := hW.hn
  have hR := hW.hR
  have hp1 : (0 : ℤ) < p := by
    have := (Fact.out : p.Prime).pos; exact_mod_cast this
  funext d k
  have hd := d.isLt
  have hDle : 0 + R0 P N p ≤ (p - 1) / 2 := by omega
  have hs : (d : ℕ) + 1 < (p - 1) / 2 + 1 := by omega
  have hRle : (d : ℕ) + 1 ≤ R0 P N p := by omega
  have hRn' : R0 P N p + 2 * p + 1 + P.g N ≤ P.n N := by omega
  have hdp : (d : ℕ) + 1 ≤ p := by omega
  have iR : (((d : ℕ) : ℤ) + 1) ≤ ((R0 P N p : ℕ) : ℤ) := by exact_mod_cast hRle
  have iN : ((R0 P N p : ℕ) : ℤ) + 2 * (p : ℤ) + 1 + (P.g N : ℤ) ≤ (P.n N : ℤ) := by
    exact_mod_cast hRn'
  have iP : ((d : ℕ) : ℤ) + 1 ≤ (p : ℤ) := by exact_mod_cast hdp
  have i0 : (0 : ℤ) ≤ ((d : ℕ) : ℤ) := by positivity
  have ig : (0 : ℤ) ≤ (P.g N : ℤ) := by positivity
  obtain ⟨r2p, h2p⟩ := exists_row (P := P) (N := N) (2 * (p : ℤ) + (((d : ℕ) : ℤ) + 1))
    (by omega) (by omega)
  obtain ⟨r2m, h2m⟩ := exists_row (P := P) (N := N) (2 * (p : ℤ) - (((d : ℕ) : ℤ) + 1))
    (by omega) (by omega)
  obtain ⟨r1p, h1p⟩ := exists_row (P := P) (N := N) ((p : ℤ) + (((d : ℕ) : ℤ) + 1))
    (by omega) (by omega)
  obtain ⟨r1m, h1m⟩ := exists_row (P := P) (N := N) ((p : ℤ) - (((d : ℕ) : ℤ) + 1))
    (by omega) (by omega)
  obtain ⟨r0p, h0p⟩ := exists_row (P := P) (N := N) (((d : ℕ) : ℤ) + 1)
    (by omega) (by omega)
  -- C-part evaluations
  have c2p := pair_eval (P := P) (N := N) hp2 hDle 0 y d (2 : Fin 3) r2p (by
    rw [h2p]; simp [cen])
  have c2m := pair_eval_minus (P := P) (N := N) hp2 hDle 0 y d (2 : Fin 3) r2m (by
    rw [h2m]; simp [cen])
  have c1p := pair_eval (P := P) (N := N) hp2 hDle 0 y d (1 : Fin 3) r1p (by
    rw [h1p]; simp [cen])
  have c1m := pair_eval_minus (P := P) (N := N) hp2 hDle 0 y d (1 : Fin 3) r1m (by
    rw [h1m]; simp [cen])
  have c0p := pair_eval (P := P) (N := N) hp2 hDle 0 y d (0 : Fin 3) r0p (by
    rw [h0p]; simp [cen])
  -- H-part evaluations
  have e2p := hRows_eval_plus (P := P) (N := N) hp2 le_rfl 0 ρ ((d : ℕ) + 1) hs (by omega) 2 r2p
    (by rw [h2p]; push_cast; ring)
  have e2m := hRows_eval_minus (P := P) (N := N) hp2 le_rfl 0 ρ ((d : ℕ) + 1) hs (by omega) 2 r2m
    (by rw [h2m]; push_cast; ring)
  have e1p := hRows_eval_plus (P := P) (N := N) hp2 le_rfl 0 ρ ((d : ℕ) + 1) hs (by omega) 1 r1p
    (by rw [h1p]; push_cast; ring)
  have e1m := hRows_eval_minus (P := P) (N := N) hp2 le_rfl 0 ρ ((d : ℕ) + 1) hs (by omega) 1 r1m
    (by rw [h1m]; push_cast; ring)
  have e0p := hRows_eval_plus (P := P) (N := N) hp2 le_rfl 0 ρ ((d : ℕ) + 1) hs (by omega) 0 r0p
    (by rw [h0p]; push_cast; ring)
  have t2p := h r2p
  have t2m := h r2m
  have t1p := h r1p
  have t1m := h r1m
  have t0p := h r0p
  rw [c2p, e2p] at t2p
  rw [c2m, e2m] at t2m
  rw [c1p, e1p] at t1p
  rw [c1m, e1m] at t1m
  rw [c0p, e0p] at t0p
  simp at t2p t2m t1p t1m t0p
  fin_cases k
  · show y d 0 = 0
    linear_combination t0p - t1m - t1p + t2m + t2p
  · show y d 1 = 0
    linear_combination t1p - t2m - t2p
  · show y d 2 = 0
    exact t2p

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
