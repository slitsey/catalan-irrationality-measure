module
public import CatalanCore.Uniform.Decay.Nodes.EnergySmall
public import CatalanCore.Uniform.Decay.SignedNodes.EnergyGeomSigned
@[expose] public section

/-!
# The all-common-deletion energy bound for signed trial densities (lane D, package D8)

`BlockGeom.energy_geom_small_signed`: `energy_geom_small` for a signed trial measure with
`∑ wt = 1`, `∑ |wt| ≤ V`.  The conclusion is the same `-(D_0 - δ) r² + c r (N - k)`; the
signed loss `V · (…)` only enters the threshold `R0` (through `V · rowConst` and `Lp ρ`).
The positive theorem is the case `V = 1` (`energy_geom_small_of_signed`).
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

namespace BlockGeom

set_option maxHeartbeats 8000000 in
theorem energy_geom_small_signed (G : BlockGeom) {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (hρ : 0 < ρ) {V : ℝ} (hV : ∑ k, |wt k| ≤ V) (hm : ∑ k, wt k = 1) {Rc : ℝ} (hc : ∀ k, ‖c k‖ ≤ Rc)
    (g : ℂ → ℝ)
    (hg : ∀ s : ℂ, g s = (G.totalMass : ℝ) * Usig ρ c wt s - G.nodePot s +
      (1 - ε) * Real.pi * |s.im|)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) {a0 : ℝ} (ha1 : 1 ≤ a0)
    {e Cl mp ℓ cB Ibd Scap Cdef : ℝ}
    (hε : 0 < ε) (he0 : 0 < e) (heε : e < ε) (hCl : 0 ≤ Cl)
    (hIb : Irho ρ c wt ≤ Ibd) (hcB : 2 * (mp - ℓ) ≤ cB) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R0 : ℕ, ∀ {r N nc : ℕ}, R0 ≤ r → 0 < N → ∀ (E : NodeEnum G r N nc) {k : ℕ}
      (z : Fin k → ℂ), Function.Injective z → (∀ l, m0 ≤ -(z l).re) →
      (∀ l, ‖z l‖ ≤ a0 * r + 2 * |(z l).im|) →
      ∀ (s : Fin k → Fin N), Function.Injective s →
      (∀ b : Fin N, nc ≤ (b : ℕ) → ∃ i, s i = b) →
      ∀ (q : Fin k → ℝ), (∀ l, Real.log (q l) ≤ (1 - e) * (Cl - 2 * Real.pi * |(z l).im|)) →
      (k : ℝ) * mp + r * Scap - Cdef ≤ ∑ l, g (z l / r) →
      (∀ b : Fin N, (b : ℕ) < nc → ℓ ≤ g ((E.nR b : ℂ) / r)) →
      ∑ l, Real.log (q l) +
          (1 / 2) * (Real.log (‖cexpr z (fun i => ((E.nR (s i) : ℕ) : ℂ))‖ ^ 2) +
            Real.log (‖cexpr z (fun i => ((E.nQ (s i) : ℕ) : ℂ))‖ ^ 2))
        ≤ -((r : ℝ) ^ 2 * (2 * (G.totalMass : ℝ) * mp + 2 * Scap -
              (G.totalMass : ℝ) ^ 2 * Ibd + G.nodeEnergy - δ)) + cB * r * ((N : ℝ) - k) := by
  have hM := G.totalMass_nonneg'
  have hV1 : (1 : ℝ) ≤ V := CatalanCore.Decay.one_le_V hm hV
  have hV0 : (0 : ℝ) ≤ V := by linarith
  have hLp := CatalanCore.Decay.Lp_nonneg ρ
  have hKc0 : (0 : ℝ) ≤ G.rowConst := Nat.cast_nonneg _
  have hKc : (0 : ℝ) ≤ (V * (G.rowConst : ℝ)) := mul_nonneg hV0 hKc0
  have hRc : 0 ≤ Rc := by
    by_cases hK : Nonempty (Fin K)
    · obtain ⟨k0⟩ := hK; exact (norm_nonneg _).trans (hc k0)
    · exfalso; simp at hK; subst hK; simp at hm
  set Af : ℝ := a0 + Rc + ρ + CatalanCore.Decay.Lp ρ with hAf
  set Ab : ℝ := Bd + Rc + ρ + CatalanCore.Decay.Lp ρ with hAb
  have hAf0 : 0 ≤ Af := by positivity
  have hAb0 : 0 ≤ Ab := by positivity
  set Nb : ℝ := (G.totalMass : ℝ) + G.rowConst with hNb
  have hNb0 : 0 ≤ Nb := by positivity
  set A : ℝ := 2 * |Cdef| + 2 * (V * (G.rowConst : ℝ)) * |mp| + (2 * (G.totalMass : ℝ) * (V * (G.rowConst : ℝ)) +
      (V * (G.rowConst : ℝ)) ^ 2) * |Ibd| + (|1 - e| * Cl + 2 * (V * (G.rowConst : ℝ)) * Af + 2 * (V * (G.rowConst : ℝ)) * Ab +
        G.C3 Bd + G.C1 Bd a0 m0 + |Real.log ρ|) * Nb + G.C4 Bd / 2 with hA
  have hC1 : 0 ≤ G.C1 Bd a0 m0 := by
    have hl : 0 ≤ Real.log (1 + (a0 + Bd)) := Real.log_nonneg (by linarith)
    unfold C1; positivity
  have hC3 : 0 ≤ G.C3 Bd := by
    have hl : 0 ≤ Real.log (1 + Bd) := Real.log_nonneg (by linarith)
    unfold C3; positivity
  have hC4 := G.C4_nonneg Bd hBd0
  have hA0 : 0 ≤ A := by
    have : 0 ≤ 1 - e → True := fun _ => trivial
    rw [hA]; positivity
  obtain ⟨R1, hR1⟩ := eventually_le_sq A δ hA0 hδ
  have hπε : 0 < 2 * Real.pi * (ε - e) := by
    have := Real.pi_pos; nlinarith
  obtain ⟨R2, hR2⟩ := exists_nat_ge ((4 * (V * (G.rowConst : ℝ)) + G.E2) / (2 * Real.pi * (ε - e)))
  refine ⟨max (max R1 R2) 1, ?_⟩
  intro r N nc hR hN E k z hzi hre hnorm s hs hkeep q hq hcap hℓ
  have hr1n : 1 ≤ r := le_trans (le_max_right _ _) hR
  have hr : 0 < r := hr1n
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr1n
  have hRR1 : R1 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRR2 : R2 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hmargin : 4 * (V * (G.rowConst : ℝ)) + G.E2 ≤ 2 * Real.pi * (ε - e) * r := by
    have h1 : ((4 * (V * (G.rowConst : ℝ)) + G.E2) / (2 * Real.pi * (ε - e))) ≤ r :=
      hR2.trans (by exact_mod_cast hRR2)
    have := (div_le_iff₀ hπε).mp h1
    linarith
  have hmain := G.energy_geom_signed hρ hV hm hc g hg hr hN E hBd0 hBc hBr hBq hm0 z hzi hre ha1
    hnorm s hs hkeep hε he0 heε hCl q hq hIb hcap hℓ hcB hmargin
  -- bound the error
  have hNM : |(N : ℝ) - (G.totalMass : ℝ) * r| ≤ (G.rowConst : ℝ) := by
    have := G.card_rows_bound r
    rw [G.rows_card_eq_N E] at this
    exact this
  have hNbd : (N : ℝ) ≤ Nb * r := by
    have := (abs_le.mp hNM).2
    rw [hNb]; nlinarith
  have hkN : k ≤ N := by simpa using Fintype.card_le_of_injective s hs
  have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hL0 : 0 ≤ Real.log (1 + (r : ℝ)) := Real.log_nonneg (by linarith)
  have herr := err_arith (r := r) (u := 1 + Real.log (1 + r)) (N := N) (k := k)
    (M := (G.totalMass : ℝ)) (Kc := (V * (G.rowConst : ℝ))) (e := e) (Cl := Cl) (mp := mp)
    (Ibd := Ibd) (Cdef := Cdef) (Af := Af) (Ab := Ab) (E1 := G.E1 r Bd a0 m0)
    (E3 := G.E3 r Bd) (E4 := G.E4 r Bd) (lρ := Real.log ρ) (Nb := Nb) (C1 := G.C1 Bd a0 m0)
    (C3 := G.C3 Bd) (C4 := G.C4 Bd) hr1 (by linarith) (Nat.cast_nonneg k) hkN' hNbd hNb0 hM hKc
    hCl hAf0 hAb0 (G.E1_nonneg hr hBd0 ha1) (G.E1_le hr hBd0 ha1) (G.E3_nonneg hr hBd0)
    (G.E3_le hr hBd0) (G.E4_le hr E hBd0) hC4
  have hsmall := hR1 r hRR1
  rw [hA] at hsmall
  have hfin := herr.trans hsmall
  rw [hAf, hAb] at hfin
  linarith [hmain, hfin]

end BlockGeom

end CatalanCore.Uniform
