module

public import CatalanCore.Cert.SigmaP6.Final
public import CatalanCore.Cert.SigmaHyb.HSymm
public import CatalanCore.Decay.Rect.Decompose

@[expose] public section

/-!
# The P6 hybrid measure `σ_h = (σ_P6 + λ)/(9/8)` (P6DECAY)

`σ_P6` is the 699-atom square measure `(cS, mS)` (`ρ = 1/2048`), `λ` the 32 real atoms
`t_k = 1 + k/128 - 1/2048` of weight `1/256` (formula, no table).  `α = 1/8`.
The hybrid function `gH = (1+α) U^{σ_h} - U^ν + (1-ε) π |Im|` decomposes as the square
`gfun` plus `h = U^λ - U^{ex}_{2α}` (`Decompose.hyb_g_decomp`).
-/

open Real

namespace CatalanCore.Cert.SigmaP6H

open CatalanLambda.Decay CatalanCore.Decay
open CatalanCore.Cert.SigmaP6 (cS mS mS_sum pos_bounds g_conj_cert)

/-- The 32 real correction atoms `t_k = 1 + k/128 - ρ`, `ρ = 1/2048`. -/
noncomputable def lamC : Fin 32 → ℂ := fun k => (((1 : ℝ) + ((k : ℕ) : ℝ) / 128 - 1 / 2048 : ℝ) : ℂ)

noncomputable def lamW : Fin 32 → ℝ := fun _ => 1 / 256

noncomputable def cH : Fin (699 + 32) → ℂ := Fin.append cS lamC

noncomputable def wtH : Fin (699 + 32) → ℝ := fun k => Fin.append mS lamW k / (1 + 1 / 8)

/-- The hybrid function. -/
noncomputable def gH (s : ℂ) : ℝ :=
  (1 + 1 / 8) * Usig (1 / 2048) cH wtH s - Unu (1 / 8) s + (1 - 1 / 1000) * Real.pi * |s.im|

theorem lamW_sum : ∑ k, lamW k = 1 / 8 := by
  simp [lamW]; norm_num

theorem wtH_sum : ∑ k, wtH k = 1 := by
  unfold wtH
  rw [← Finset.sum_div, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [mS_sum, lamW_sum]
  norm_num

theorem wtH_nonneg (k : Fin (699 + 32)) : 0 ≤ wtH k := by
  unfold wtH
  refine div_nonneg ?_ (by norm_num)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left]; unfold mS; positivity
  · rw [Fin.append_right]; unfold lamW; norm_num

theorem cH_norm (k : Fin (699 + 32)) : ‖cH k‖ ≤ 4 := by
  unfold cH
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left]
    obtain ⟨a, b, c, d⟩ := pos_bounds i
    have h := Complex.norm_le_abs_re_add_abs_im (cS i)
    rw [abs_of_nonpos b] at h
    have : |(cS i).im| ≤ 14 / 5 := abs_le.2 ⟨by linarith, d⟩
    linarith
  · rw [Fin.append_right]
    unfold lamC
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : ((i : ℕ) : ℝ) ≤ 31 := by exact_mod_cast Nat.lt_succ_iff.1 i.2
    have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> linarith

/-- `gH = gfun + h`, `h = U^λ - U^ex_{2α}`. -/
theorem gH_decomp (s : ℂ) :
    gH s = gfun (1 / 2048) (1 / 1000) cS mS s
      + (Usig (1 / 2048) lamC lamW s - Uex (2 * (1 / 8)) s) := by
  have h := hyb_g_decomp (1 / 2048 : ℝ) (1 / 1000 : ℝ) (1 / 8 : ℝ) (by norm_num) cS mS lamC lamW s
  have e : (fun k : Fin (699 + 32) => (Fin.append mS lamW k) / (1 + (1 / 8 : ℝ))) = wtH := rfl
  rw [e] at h
  unfold gH gfun
  exact h

theorem Usig_lam_conj (s : ℂ) : Usig (1 / 2048) lamC lamW ((starRingEnd ℂ) s)
    = Usig (1 / 2048) lamC lamW s := by
  unfold Usig
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold krho lamC
  congr 3
  have : (starRingEnd ℂ) s - (((1 : ℝ) + ((k : ℕ) : ℝ) / 128 - 1 / 2048 : ℝ) : ℂ)
      = (starRingEnd ℂ) (s - (((1 : ℝ) + ((k : ℕ) : ℝ) / 128 - 1 / 2048 : ℝ) : ℂ)) := by
    rw [map_sub, Complex.conj_ofReal]
  rw [this, Complex.norm_conj]

theorem gH_conj (s : ℂ) : gH ((starRingEnd ℂ) s) = gH s := by
  rw [gH_decomp, gH_decomp, g_conj_cert, Usig_lam_conj, SigmaHyb.Uex_conj]

end CatalanCore.Cert.SigmaP6H
