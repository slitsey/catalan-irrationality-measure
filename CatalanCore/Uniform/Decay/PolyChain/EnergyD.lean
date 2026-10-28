module

public import CatalanCore.Uniform.Decay.Nodes.EnergySmall

@[expose] public section

/-!
# The Part 1 energy step with a distance hypothesis (lane D, package D7)

Copies of D3's `energy_block`, `BlockGeom.ps_hyp`, `BlockGeom.energy_geom` and
`BlockGeom.energy_geom_small` in which the straight-ray hypothesis `m0 ≤ -Re z` on the free
points is replaced by the contour-free hypothesis

`∀ t ≥ 0, m0 ≤ ‖z - t‖`  (distance at least `m0 > 0` from the node half-line `[0, ∞)`).

This is all the original proofs use (`Re z < 0` only served to separate `z` from the nodes, and
`dist(z, [0, Bd r]) ≥ m0`, `‖z‖ ≥ m0` are the two distance facts of `ps_hyp`).  Points of a
polygon contour need not lie in `Re < 0`; D4's `path_node_dist` gives the distance hypothesis.
The statements and proofs are otherwise unchanged.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Finset CatalanLambda.Decay

set_option maxHeartbeats 8000000 in
/-- **The block-node energy step.** -/
theorem energy_block_d {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (hρ : 0 < ρ) (hw0 : ∀ k, 0 ≤ wt k) (hm : ∑ k, wt k = 1) {Rc : ℝ} (hc : ∀ k, ‖c k‖ ≤ Rc)
    {M : ℝ} (hM : 0 ≤ M) (g U : ℂ → ℝ)
    (hg : ∀ s : ℂ, g s = M * Usig ρ c wt s - U s + (1 - ε) * Real.pi * |s.im|)
    {r N nc : ℕ} (hr : 0 < r) (hN : 0 < N) {Kc : ℝ} (hKc : 0 ≤ Kc)
    (hNM : |(N : ℝ) - M * r| ≤ Kc)
    (nR nQ : Fin N → ℕ) (hRi : Function.Injective nR) (hQi : Function.Injective nQ)
    (hcom : ∀ b : Fin N, (b : ℕ) < nc → nR b = nQ b)
    {Bd : ℝ} (hBd : ∀ b : Fin N, (b : ℕ) < nc → (nR b : ℝ) ≤ Bd * r) (hBd0 : 0 ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) {k : ℕ} (z : Fin k → ℂ) (hzi : Function.Injective z)
    (hdist : ∀ l (t : ℝ), 0 ≤ t → m0 ≤ ‖z l - (t : ℂ)‖)
    {a0 : ℝ} (ha0 : 0 ≤ a0) (hnorm : ∀ l, ‖z l‖ ≤ a0 * r + 2 * |(z l).im|)
    (s : Fin k → Fin N) (hs : Function.Injective s)
    (hkeep : ∀ b : Fin N, nc ≤ (b : ℕ) → ∃ i, s i = b)
    {e Cl mp ℓ cB Ibd Scap Cdef J E1 E2 E3 E4 : ℝ}
    (hε : 0 < ε) (he0 : 0 < e) (heε : e < ε) (hCl : 0 ≤ Cl)
    (q : Fin k → ℝ) (hq : ∀ l, Real.log (q l) ≤ (1 - e) * (Cl - 2 * Real.pi * |(z l).im|))
    (hIb : Irho ρ c wt ≤ Ibd)
    (hcap : (k : ℝ) * mp + r * Scap - Cdef ≤ ∑ l, g (z l / r))
    (hℓ : ∀ b : Fin N, (b : ℕ) < nc → ℓ ≤ g ((nR b : ℂ) / r)) (hcB : 2 * (mp - ℓ) ≤ cB)
    (hPS : ∀ l, (∑ b, elog (z l / r) ((nR b : ℂ) / r)) + (∑ b, elog (z l / r) ((nQ b : ℂ) / r))
      ≤ 2 * (r * U (z l / r)) + E1 + E2 * |(z l).im| / r)
    (hRS : ∀ b : Fin N, (b : ℕ) < nc →
      (∑ b', elog ((nR b : ℂ) / r) ((nR b' : ℂ) / r)) +
        (∑ b', elog ((nQ b : ℂ) / r) ((nQ b' : ℂ) / r)) ≤ 2 * (r * U ((nR b : ℂ) / r)) + E3)
    (hAS : 2 * (r : ℝ) ^ 2 * J - E4 ≤
      (∑ b, ∑ b', elog ((nR b : ℂ) / r) ((nR b' : ℂ) / r)) +
        (∑ b, ∑ b', elog ((nQ b : ℂ) / r) ((nQ b' : ℂ) / r)))
    (hmargin : 4 * Kc + E2 ≤ 2 * Real.pi * (ε - e) * r) :
    ∑ l, Real.log (q l) +
        (1 / 2) * (Real.log (‖cexpr z (fun i => ((nR (s i) : ℕ) : ℂ))‖ ^ 2) +
          Real.log (‖cexpr z (fun i => ((nQ (s i) : ℕ) : ℂ))‖ ^ 2))
      ≤ -((r : ℝ) ^ 2 * (2 * M * mp + 2 * Scap - M ^ 2 * Ibd + J)) + cB * r * ((N : ℝ) - k)
        + (2 * r * Cdef + 2 * r * Kc * |mp| + (2 * M * r * Kc + Kc ^ 2) * |Ibd|
          + (1 - e) * k * Cl + 2 * Kc * k * (a0 + Rc + ρ + |Real.log ρ|)
          + 2 * Kc * ((N : ℝ) - k) * (Bd + Rc + ρ + |Real.log ρ|) + ((N : ℝ) - k) * E3
          + k * E1 + E4 / 2 + N * |Real.log ρ|) := by
  classical
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hkN : k ≤ N := by simpa using Fintype.card_le_of_injective s hs
  have hkN' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set σ : Fin k → ℂ := fun l => z l / r with hσ
  set τR : Fin N → ℂ := fun b => (nR b : ℂ) / r with hτR
  set τQ : Fin N → ℂ := fun b => (nQ b : ℂ) / r with hτQ
  have hσre : ∀ l, (σ l).re = (z l).re / r := fun l => by simp [hσ, Complex.div_natCast_re]
  have hσim : ∀ l, (σ l).im = (z l).im / r := fun l => by simp [hσ, Complex.div_natCast_im]
  have hzne : ∀ l (n : ℕ), z l ≠ (n : ℂ) := fun l n e' => by
    have h1 := hdist l (n : ℝ) (Nat.cast_nonneg n)
    have h2 : z l - (((n : ℝ)) : ℂ) = 0 := by rw [e']; push_cast; ring
    rw [h2, norm_zero] at h1; linarith
  have hτRre : ∀ b, 0 ≤ (τR b).re := fun b => by
    simp only [hτR, Complex.div_natCast_re, Complex.natCast_re]; positivity
  have hτQre : ∀ b, 0 ≤ (τQ b).re := fun b => by
    simp only [hτQ, Complex.div_natCast_re, Complex.natCast_re]; positivity
  have hσi : Function.Injective σ := by
    intro a b hab
    exact hzi ((div_left_inj' hrC).1 hab)
  have hτRi : Function.Injective τR := by
    intro a b hab
    exact hRi (Nat.cast_injective (R := ℂ) ((div_left_inj' hrC).1 hab))
  have hτQi : Function.Injective τQ := by
    intro a b hab
    exact hQi (Nat.cast_injective (R := ℂ) ((div_left_inj' hrC).1 hab))
  have hστR : ∀ l b, σ l ≠ τR b := fun l b e' => hzne l (nR b) ((div_left_inj' hrC).1 e')
  have hστQ : ∀ l b, σ l ≠ τQ b := fun l b e' => hzne l (nQ b) ((div_left_inj' hrC).1 e')
  have hpiR : Function.Injective (Sum.elim σ τR) := by
    intro x y hxy
    rcases x with l | b <;> rcases y with l' | b'
    · simp only [Sum.elim_inl] at hxy; rw [hσi hxy]
    · simp only [Sum.elim_inl, Sum.elim_inr] at hxy; exact absurd hxy (hστR _ _)
    · simp only [Sum.elim_inl, Sum.elim_inr] at hxy; exact absurd hxy.symm (hστR _ _)
    · simp only [Sum.elim_inr] at hxy; rw [hτRi hxy]
  -- row / column Cauchy expressions
  set rowC : Fin k → ℂ := fun i => ((nR (s i) : ℕ) : ℂ) with hrowC
  set colC : Fin k → ℂ := fun i => ((nQ (s i) : ℕ) : ℂ) with hcolC
  have hrowi : Function.Injective rowC := by
    intro a b hab
    exact hs (hRi (Nat.cast_injective (R := ℂ) hab))
  have hcoli : Function.Injective colC := by
    intro a b hab
    exact hs (hQi (Nat.cast_injective (R := ℂ) hab))
  have hzrow : ∀ l i, z l ≠ rowC i := fun l i => hzne l (nR (s i))
  have hzcol : ∀ l i, z l ≠ colC i := fun l i => hzne l (nQ (s i))
  have hX : -Real.log (‖cexpr z rowC‖ ^ 2) =
      EscB σ (fun i => τR (s i)) + 2 * k * Real.log r :=
    neg_log_cexpr_scaledB hr z rowC hzi hrowi hzrow
  have hY : -Real.log (‖cexpr z colC‖ ^ 2) =
      EscB σ (fun i => τQ (s i)) + 2 * k * Real.log r :=
    neg_log_cexpr_scaledB hr z colC hzi hcoli hzcol
  -- masks
  have hmsk01 : ∀ b, rmask s b = 0 ∨ rmask s b = 1 := rmask_cases s
  have hmskr : ∀ b : Fin N, nc ≤ (b : ℕ) → rmask s b = 0 := by
    intro b hb
    obtain ⟨i, hi⟩ := hkeep b hb
    unfold rmask
    rw [if_pos (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)]
  have hmsum : ∑ b, rmask s b = (N : ℝ) - k := by
    have h1 := sum_mask s hs (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_sub_distrib] at h1
    linarith
  have hmsk1 : ∀ b : Fin N, rmask s b ≠ 0 → (b : ℕ) < nc ∧ rmask s b = 1 := by
    intro b hb
    refine ⟨?_, (hmsk01 b).resolve_left hb⟩
    by_contra h; exact hb (hmskr b (not_lt.1 h))
  have hτeq : ∀ b : Fin N, rmask s b ≠ 0 → τR b = τQ b := by
    intro b hb
    simp only [hτR, hτQ, hcom b (hmsk1 b hb).1]
  have hDX := Hsc_decomp σ τR s hs
  have hDY := Hsc_decomp σ τQ s hs
  have hBeq : BexpB σ τR (rmask s) = BexpB σ τQ (rmask s) := BexpB_congr σ τR τQ _ hτeq
  have hBX : 2 * (N : ℝ) * (∑ l, Usig ρ c wt (σ l) + ∑ b, rmask s b * Usig ρ c wt (τR b))
      - (N : ℝ) ^ 2 * Irho ρ c wt + (N : ℝ) * Real.log ρ ≤ BexpB σ τR (rmask s) :=
    energy_B hN hρ c wt hm σ τR (rmask s) hmsk01 hmsum hpiR
  -- sums
  set SI : ℝ := ∑ l, |(z l).im| with hSI
  have hSI0 : 0 ≤ SI := Finset.sum_nonneg (fun l _ => abs_nonneg _)
  set SIr : ℝ := SI / r with hSIr
  have hSIeq : SI = r * SIr := by rw [hSIr]; field_simp
  set SY : ℝ := ∑ l, Usig ρ c wt (σ l) with hSY
  set SYb : ℝ := ∑ b, rmask s b * Usig ρ c wt (τR b) with hSYb
  set SU : ℝ := ∑ l, U (σ l) with hSU
  set SUb : ℝ := ∑ b, rmask s b * U (τR b) with hSUb
  set Sg : ℝ := ∑ l, g (σ l) with hSg
  -- identity layer
  set PSR : ℝ := ∑ l, ∑ b, elog (σ l) (τR b) with hPSR
  set PSQ : ℝ := ∑ l, ∑ b, elog (σ l) (τQ b) with hPSQ
  set ASR : ℝ := ∑ b, ∑ b', elog (τR b) (τR b') with hASR
  set ASQ : ℝ := ∑ b, ∑ b', elog (τQ b) (τQ b') with hASQ
  set RSR : ℝ := ∑ b, ∑ b', rmask s b * elog (τR b) (τR b') with hRSR
  set RSQ : ℝ := ∑ b, ∑ b', rmask s b * elog (τQ b) (τQ b') with hRSQ
  have hEX : EscB σ (fun i => τR (s i)) = BexpB σ τR (rmask s) + ASR - 2 * PSR - 2 * RSR := by
    have := hDX
    unfold EscB BexpB
    linarith
  have hEY : EscB σ (fun i => τQ (s i)) = BexpB σ τQ (rmask s) + ASQ - 2 * PSQ - 2 * RSQ := by
    have := hDY
    unfold EscB BexpB
    linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hLHS : ∑ l, Real.log (q l) +
        (1 / 2) * (Real.log (‖cexpr z rowC‖ ^ 2) + Real.log (‖cexpr z colC‖ ^ 2))
      ≤ ∑ l, Real.log (q l) - BexpB σ τR (rmask s) - (ASR + ASQ) / 2 + (PSR + PSQ) +
        (RSR + RSQ) := by
    have hk2 : 0 ≤ 2 * (k : ℝ) * Real.log r := by positivity
    linarith [hX, hY, hEX, hEY, hk2, hBeq]
  -- node-sum discrepancies
  have hPSs : PSR + PSQ ≤ 2 * r * SU + k * E1 + E2 * SIr := by
    have h1 : ∑ l, ((∑ b, elog (σ l) (τR b)) + (∑ b, elog (σ l) (τQ b))) ≤
        ∑ l, (2 * (r * U (σ l)) + E1 + E2 * |(z l).im| / r) := Finset.sum_le_sum (fun l _ => hPS l)
    rw [Finset.sum_add_distrib] at h1
    have e1 : ∑ l, (2 * ((r : ℝ) * U (σ l)) + E1 + E2 * |(z l).im| / r) =
        2 * r * SU + k * E1 + E2 * SIr := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hSU, hSIr, hSI]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      ring
    rw [e1] at h1
    exact h1
  have hRSs : RSR + RSQ ≤ 2 * r * SUb + ((N : ℝ) - k) * E3 := by
    have eR : RSR = ∑ b, rmask s b * ∑ b', elog (τR b) (τR b') := by
      rw [hRSR]; exact Finset.sum_congr rfl (fun b _ => (Finset.mul_sum _ _ _).symm)
    have eQ : RSQ = ∑ b, rmask s b * ∑ b', elog (τQ b) (τQ b') := by
      rw [hRSQ]; exact Finset.sum_congr rfl (fun b _ => (Finset.mul_sum _ _ _).symm)
    have h1 : RSR + RSQ = ∑ b, rmask s b *
        ((∑ b', elog (τR b) (τR b')) + (∑ b', elog (τQ b) (τQ b'))) := by
      rw [eR, eQ, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    have h2 : ∑ b, rmask s b * ((∑ b', elog (τR b) (τR b')) + (∑ b', elog (τQ b) (τQ b'))) ≤
        ∑ b, rmask s b * (2 * (r * U (τR b)) + E3) := by
      refine Finset.sum_le_sum (fun b _ => ?_)
      by_cases hb : rmask s b = 0
      · simp [hb]
      · obtain ⟨hb1, hb2⟩ := hmsk1 b hb
        rw [hb2, one_mul, one_mul]
        exact hRS b hb1
    have h3 : ∑ b, rmask s b * (2 * (r * U (τR b)) + E3) =
        2 * r * SUb + ((N : ℝ) - k) * E3 := by
      have : ∀ b, rmask s b * (2 * ((r : ℝ) * U (τR b)) + E3) =
          2 * r * (rmask s b * U (τR b)) + rmask s b * E3 := fun b => by ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hmsum]
    linarith
  have hASs : 2 * (r : ℝ) ^ 2 * J - E4 ≤ ASR + ASQ := hAS
  -- pointwise g-bounds
  have hfreeSum : 2 * r * Sg - 2 * (1 - ε) * Real.pi * SI -
      2 * Kc * (k * (a0 + Rc + ρ + |Real.log ρ|) + 2 * SIr) ≤ 2 * N * SY - 2 * r * SU := by
    have hpt : ∀ l, 2 * r * g (σ l) - 2 * (1 - ε) * Real.pi * |(z l).im| -
        2 * Kc * ((a0 + Rc + ρ + |Real.log ρ|) + 2 * |(z l).im| / r) ≤
        2 * N * Usig ρ c wt (σ l) - 2 * r * U (σ l) := by
      intro l
      have hnl : ‖σ l‖ ≤ a0 + 2 * |(z l).im| / r := by
        show ‖z l / (r : ℂ)‖ ≤ _
        rw [norm_div, Complex.norm_natCast, div_le_iff₀ hr']
        have := hnorm l
        have e : (a0 + 2 * |(z l).im| / r) * r = a0 * r + 2 * |(z l).im| := by field_simp
        rw [e]; exact this
      have hY := abs_Usig_le hρ c wt hw0 hm hc (σ l)
      have hY' : |Usig ρ c wt (σ l)| ≤ (a0 + Rc + ρ + |Real.log ρ|) + 2 * |(z l).im| / r := by
        linarith
      have hgl : g (σ l) = M * Usig ρ c wt (σ l) - U (σ l) +
          (1 - ε) * Real.pi * |(z l).im| / r := by
        rw [hg (σ l), hσim, abs_div, abs_of_pos hr']; ring
      exact pt_block hr' hNM hY' hgl
    have h1 := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) => hpt l)
    have e2 : ∑ l : Fin k, 2 * |(z l).im| / (r : ℝ) = 2 * SIr := by
      rw [hSIr, hSI, ← Finset.sum_div, ← Finset.mul_sum]
      ring
    have hlhs : ∑ l, (2 * (r : ℝ) * g (σ l) - 2 * (1 - ε) * Real.pi * |(z l).im| -
        2 * Kc * ((a0 + Rc + ρ + |Real.log ρ|) + 2 * |(z l).im| / r)) =
        2 * r * Sg - 2 * (1 - ε) * Real.pi * SI -
          2 * Kc * (k * (a0 + Rc + ρ + |Real.log ρ|) + 2 * SIr) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, e2, hSg, hSI]
      ring
    have hrhs : ∑ l, (2 * (N : ℝ) * Usig ρ c wt (σ l) - 2 * r * U (σ l)) =
        2 * N * SY - 2 * r * SU := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hSY, hSU]
    rw [hlhs, hrhs] at h1
    exact h1
  have hlineSum : ((N : ℝ) - k) *
      (2 * r * ℓ - 2 * Kc * (Bd + Rc + ρ + |Real.log ρ|)) ≤ 2 * N * SYb - 2 * r * SUb := by
    have hpt : ∀ b : Fin N, rmask s b * (2 * r * ℓ - 2 * Kc * (Bd + Rc + ρ + |Real.log ρ|)) ≤
        rmask s b * (2 * N * Usig ρ c wt (τR b) - 2 * r * U (τR b)) := by
      intro b
      by_cases hb : rmask s b = 0
      · simp [hb]
      · obtain ⟨hb1, hb2⟩ := hmsk1 b hb
        rw [hb2, one_mul, one_mul]
        have hnb : ‖τR b‖ ≤ Bd := by
          show ‖(nR b : ℂ) / (r : ℂ)‖ ≤ Bd
          simp only [norm_div, Complex.norm_natCast]
          rw [div_le_iff₀ hr']
          exact hBd b hb1
        have hY := abs_Usig_le hρ c wt hw0 hm hc (τR b)
        have hY' : |Usig ρ c wt (τR b)| ≤ Bd + Rc + ρ + |Real.log ρ| := by linarith
        have hgb : g (τR b) = M * Usig ρ c wt (τR b) - U (τR b) +
            (1 - ε) * Real.pi * |(0 : ℝ)| / r := by
          rw [hg (τR b)]
          have : (τR b).im = 0 := by simp [hτR, Complex.div_natCast_im]
          rw [this]; simp
        have hpb := pt_block hr' hNM hY' hgb
        have hl := hℓ b hb1
        simp only [abs_zero, mul_zero, sub_zero] at hpb
        have := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 2 * r)
        linarith
    have h1 := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin N))) => hpt b)
    rw [← Finset.sum_mul, hmsum] at h1
    have h2 : ∑ b, rmask s b * (2 * (N : ℝ) * Usig ρ c wt (τR b) - 2 * r * U (τR b)) =
        2 * N * SYb - 2 * r * SUb := by
      have : ∀ b, rmask s b * (2 * (N : ℝ) * Usig ρ c wt (τR b) - 2 * r * U (τR b)) =
          2 * N * (rmask s b * Usig ρ c wt (τR b)) - 2 * r * (rmask s b * U (τR b)) :=
        fun b => by ring
      simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hSYb, hSUb]
    rw [h2] at h1
    exact h1
  have hq_sum : ∑ l, Real.log (q l) ≤ (1 - e) * k * Cl - 2 * (1 - e) * Real.pi * SI := by
    have h1 := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) => hq l)
    have h2 : ∀ l : Fin k, (1 - e) * (Cl - 2 * Real.pi * |(z l).im|) =
        (1 - e) * Cl - (2 * (1 - e) * Real.pi) * |(z l).im| := fun l => by ring
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    rw [hSI]
    linarith
  have hRc : 0 ≤ Rc := by
    by_cases hK : Nonempty (Fin K)
    · obtain ⟨k0⟩ := hK; exact (norm_nonneg _).trans (hc k0)
    · exfalso; simp at hK; subst hK; simp at hm
  have hAf : 0 ≤ a0 + Rc + ρ + |Real.log ρ| := by positivity
  have hAb : 0 ≤ Bd + Rc + ρ + |Real.log ρ| := by positivity
  have key := block_arith (r := r) (N := N) (k := k) (M := M) (Kc := Kc) (e := e) (ε := ε)
    (Cl := Cl) (mp := mp) (ℓ := ℓ) (cB := cB) (Ibd := Ibd) (Irho := Irho ρ c wt)
    (Scap := Scap) (Cdef := Cdef) (J := J) (E1 := E1) (E2 := E2) (E3 := E3) (E4 := E4)
    (Af := a0 + Rc + ρ + |Real.log ρ|) (Ab := Bd + Rc + ρ + |Real.log ρ|)
    (lρ := Real.log ρ) (P := Real.pi) (SI := SI) (SIr := SIr)
    (Slq := ∑ l, Real.log (q l)) (SY := SY) (SYb := SYb) (SU := SU) (SUb := SUb) (Sg := Sg)
    (Bexp := BexpB σ τR (rmask s)) (ASs := ASR + ASQ) (PSs := PSR + PSQ) (RSs := RSR + RSQ)
    (LHS := ∑ l, Real.log (q l) +
      (1 / 2) * (Real.log (‖cexpr z rowC‖ ^ 2) + Real.log (‖cexpr z colC‖ ^ 2)))
    hr' hk0 hkN' hNM hM hKc hCl Real.pi_pos.le heε.le hSI0 hSIeq hAf hAb hLHS hBX hPSs hRSs hASs
    hfreeSum hlineSum hcap hq_sum hIb hcB hmargin
  exact key


end CatalanCore.Uniform.Decay.Nodes

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

namespace BlockGeom

/-- **Free-point hypothesis** of `energy_block`. -/
theorem ps_hyp_d (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd m0 a0 : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    (hm0 : 0 < m0) (ha1 : 1 ≤ a0) (z : ℂ) (hdist : ∀ t : ℝ, 0 ≤ t → m0 ≤ ‖z - (t : ℂ)‖)
    (hnorm : ‖z‖ ≤ a0 * r + 2 * |z.im|) :
    (∑ j ∈ (G.geometry r).rows, elog (z / r) ((j : ℂ) / r)) +
        (∑ j ∈ (G.geometry r).cols, elog (z / r) ((j : ℂ) / r)) ≤
      2 * (r * G.nodePot (z / r)) + G.E1 r Bd a0 m0 + G.E2 * |z.im| / r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hb : 0 ≤ Bd * r := by positivity
  set M : ℝ := ‖z‖ + Bd * r with hM
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), m0 ≤ ‖z - (t : ℂ)‖ := fun t ht => hdist t ht.1
  have hMM : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), ‖z - (t : ℂ)‖ ≤ M := by
    intro t ht
    have h1 := norm_sub_le z (t : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] at h1
    linarith [ht.2]
  have hnz : m0 ≤ ‖z‖ := by
    have := hdist 0 le_rfl
    simpa using this
  have hMge : m0 ≤ M := by rw [hM]; have : 0 ≤ Bd * r := hb; linarith
  have hlogM : |Real.log M| ≤ Real.log (1 + M) + |Real.log m0| := by
    by_cases h1 : 1 ≤ M
    · rw [abs_of_nonneg (Real.log_nonneg h1)]
      have := Real.log_le_log (by linarith) (show M ≤ 1 + M by linarith)
      have := abs_nonneg (Real.log m0)
      linarith
    · push Not at h1
      have : Real.log m0 ≤ Real.log M := Real.log_le_log hm0 hMge
      have h2 : Real.log M ≤ 0 := Real.log_nonpos (by linarith) h1.le
      rw [abs_of_nonpos h2]
      have : 0 ≤ Real.log (1 + M) := Real.log_nonneg (by linarith)
      have := neg_abs_le (Real.log m0)
      linarith
  have hlog1M : Real.log (1 + M) ≤ Real.log (1 + (a0 + Bd) * r) + 2 * |z.im| / r := by
    have hx : 0 < 1 + (a0 + Bd) * r := by positivity
    have hle : 1 + M ≤ (1 + (a0 + Bd) * r) + 2 * |z.im| := by
      rw [hM]; nlinarith [hnorm]
    have h1 := Real.log_le_log (by linarith [norm_nonneg z, hb]) hle
    have h2 := log_add_le' hx (by positivity : 0 ≤ 2 * |z.im|)
    have h3 : 2 * |z.im| / (1 + (a0 + Bd) * r) ≤ 2 * |z.im| / r := by
      apply div_le_div_of_nonneg_left (by positivity) hr'
      nlinarith
    linarith
  -- generic bound for one side
  have side : ∀ D : ℝ, 0 ≤ D → D * (|kern z (Bd * r)| + 2 * (Real.log M - Real.log m0)) ≤
      D * (6 * |Real.log m0| + 3 * Real.log (1 + (a0 + Bd) * r) + 6 * |z.im| / r) := by
    intro D hD
    refine mul_le_mul_of_nonneg_left ?_ hD
    have hbm : Bd * r ∈ Set.Icc (0 : ℝ) (Bd * r) := ⟨hb, le_rfl⟩
    have k1 := kern_le hb hm0 hd hbm
    have k2 := ge_kern hb hm0 hd hMM hbm
    have hk : |kern z (Bd * r)| ≤ |Real.log M| + |Real.log m0| := by
      rw [abs_le]
      constructor
      · have := le_abs_self (Real.log M); have := abs_nonneg (Real.log m0); linarith
      · have := neg_le_abs (Real.log m0); have := abs_nonneg (Real.log M); linarith
    have e1 : Real.log M - Real.log m0 ≤ |Real.log M| + |Real.log m0| := by
      have := le_abs_self (Real.log M); have := neg_le_abs (Real.log m0); linarith
    have : 6 * |z.im| / r = 3 * (2 * |z.im| / r) := by ring
    nlinarith [hlogM, hlog1M, hk, e1, abs_nonneg (Real.log m0)]
  have hrow := G.rows_ps_scaled hr z hBd0 hBc hBr hm0 hd hMM
  have hcol := G.cols_ps_scaled hr z hBd0 hBc hBq hm0 hd hMM
  have hsr := side (G.rowConstR : ℝ) (Nat.cast_nonneg _)
  have hsc := side (G.colConstR : ℝ) (Nat.cast_nonneg _)
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  have hrow' := (abs_le.mp hrow).2
  have hcol' := (abs_le.mp hcol).2
  unfold nodePot E1 E2
  have e3 : ((G.rowConstR : ℝ) + G.colConstR) * (6 * |z.im| / r) =
      (6 * ((G.rowConstR : ℝ) + G.colConstR)) * |z.im| / r := by ring
  nlinarith [hrow', hcol', hsr, hsc, e3]

set_option maxHeartbeats 8000000 in
/-- **Energy step for a block geometry.** -/
theorem energy_geom_d (G : BlockGeom) {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (hρ : 0 < ρ) (hw0 : ∀ k, 0 ≤ wt k) (hm : ∑ k, wt k = 1) {Rc : ℝ} (hc : ∀ k, ‖c k‖ ≤ Rc)
    (g : ℂ → ℝ)
    (hg : ∀ s : ℂ, g s = (G.totalMass : ℝ) * Usig ρ c wt s - G.nodePot s +
      (1 - ε) * Real.pi * |s.im|)
    {r N nc : ℕ} (hr : 0 < r) (hN : 0 < N) (E : NodeEnum G r N nc)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) {k : ℕ} (z : Fin k → ℂ) (hzi : Function.Injective z)
    (hdist : ∀ l (t : ℝ), 0 ≤ t → m0 ≤ ‖z l - (t : ℂ)‖)
    {a0 : ℝ} (ha1 : 1 ≤ a0) (hnorm : ∀ l, ‖z l‖ ≤ a0 * r + 2 * |(z l).im|)
    (s : Fin k → Fin N) (hs : Function.Injective s)
    (hkeep : ∀ b : Fin N, nc ≤ (b : ℕ) → ∃ i, s i = b)
    {e Cl mp ℓ cB Ibd Scap Cdef : ℝ}
    (hε : 0 < ε) (he0 : 0 < e) (heε : e < ε) (hCl : 0 ≤ Cl)
    (q : Fin k → ℝ) (hq : ∀ l, Real.log (q l) ≤ (1 - e) * (Cl - 2 * Real.pi * |(z l).im|))
    (hIb : Irho ρ c wt ≤ Ibd)
    (hcap : (k : ℝ) * mp + r * Scap - Cdef ≤ ∑ l, g (z l / r))
    (hℓ : ∀ b : Fin N, (b : ℕ) < nc → ℓ ≤ g ((E.nR b : ℂ) / r)) (hcB : 2 * (mp - ℓ) ≤ cB)
    (hmargin : 4 * (G.rowConst : ℝ) + G.E2 ≤ 2 * Real.pi * (ε - e) * r) :
    ∑ l, Real.log (q l) +
        (1 / 2) * (Real.log (‖cexpr z (fun i => ((E.nR (s i) : ℕ) : ℂ))‖ ^ 2) +
          Real.log (‖cexpr z (fun i => ((E.nQ (s i) : ℕ) : ℂ))‖ ^ 2))
      ≤ -((r : ℝ) ^ 2 * (2 * (G.totalMass : ℝ) * mp + 2 * Scap -
            (G.totalMass : ℝ) ^ 2 * Ibd + G.nodeEnergy)) + cB * r * ((N : ℝ) - k)
        + (2 * r * Cdef + 2 * r * (G.rowConst : ℝ) * |mp|
          + (2 * (G.totalMass : ℝ) * r * G.rowConst + (G.rowConst : ℝ) ^ 2) * |Ibd|
          + (1 - e) * k * Cl + 2 * (G.rowConst : ℝ) * k * (a0 + Rc + ρ + |Real.log ρ|)
          + 2 * (G.rowConst : ℝ) * ((N : ℝ) - k) * (Bd + Rc + ρ + |Real.log ρ|)
          + ((N : ℝ) - k) * G.E3 r Bd
          + k * G.E1 r Bd a0 m0 + G.E4 r Bd / 2 + N * |Real.log ρ|) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hM0 : (0 : ℝ) ≤ (G.totalMass : ℝ) := by
    have : 0 ≤ G.totalMass := by
      unfold BlockGeom.totalMass BlockGeom.gamma BlockGeom.beta
      have := G.common_pos
      have h2 : 0 ≤ G.row.mass := by
        unfold BlockCollection.mass
        exact Finset.sum_nonneg (fun i _ => (G.row.block i).mass_pos.le)
      linarith
    exact_mod_cast this
  have hcardN := G.rows_card_eq_N E
  have hNM : |(N : ℝ) - (G.totalMass : ℝ) * r| ≤ (G.rowConst : ℝ) := by
    have := G.card_rows_bound r
    rw [hcardN] at this
    exact this
  have hbd : ∀ b : Fin N, (b : ℕ) < nc → (E.nR b : ℝ) ≤ Bd * r := by
    intro b hb
    have hmem : E.nR b ∈ (G.geometry r).rows := by
      rw [← E.imgR]; exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
    rcases G.mem_rows_cases r _ hmem with h | h
    · exact node_lt_bound G.common r _ hBc h
    · exact node_lt_bound G.row r _ hBr h
  refine energy_block_d hρ hw0 hm hc hM0 g G.nodePot hg hr hN (Nat.cast_nonneg _) hNM
    E.nR E.nQ E.injR E.injQ E.commonAgree hbd hBd0 hm0 z hzi hdist (by linarith) hnorm s hs hkeep
    hε he0 heε hCl q hq hIb hcap hℓ hcB ?_ ?_ ?_ hmargin
  · -- free-point hypothesis
    intro l
    have h := G.ps_hyp_d hr hBd0 hBc hBr hBq hm0 ha1 (z l) (hdist l) (hnorm l)
    rw [sum_fin_eq E.nR E.injR _ E.imgR (fun j => elog (z l / r) ((j : ℂ) / r)),
      sum_fin_eq E.nQ E.injQ _ E.imgQ (fun j => elog (z l / r) ((j : ℂ) / r))]
    exact h
  · -- punctured hypothesis
    intro b hb
    have hq' := E.commonAgree b hb
    have hCm := E.commonMem b hb
    have har : E.nR b ∈ (G.geometry r).rows := by
      unfold Rect.Geometry.rows; exact Finset.mem_union_left _ hCm
    have hac : E.nR b ∈ (G.geometry r).cols := by
      unfold Rect.Geometry.cols; exact Finset.mem_union_left _ hCm
    have h := G.rs_hyp hr hBd0 hBc hBr hBq har hac
    rw [← hq']
    rw [sum_fin_eq E.nR E.injR _ E.imgR (fun j => elog ((E.nR b : ℂ) / r) ((j : ℂ) / r)),
      sum_fin_eq E.nQ E.injQ _ E.imgQ (fun j => elog ((E.nR b : ℂ) / r) ((j : ℂ) / r))]
    exact h
  · -- self-energy hypothesis
    have h := G.as_hyp hr hBd0 hBc hBr hBq
    have e1 : ∑ b : Fin N, ∑ b' : Fin N, elog ((E.nR b : ℂ) / r) ((E.nR b' : ℂ) / r) =
        ∑ a ∈ (G.geometry r).rows, ∑ b ∈ (G.geometry r).rows,
          elog ((a : ℂ) / r) ((b : ℂ) / r) := by
      have inner : ∀ b : Fin N, ∑ b' : Fin N, elog ((E.nR b : ℂ) / r) ((E.nR b' : ℂ) / r) =
          ∑ j ∈ (G.geometry r).rows, elog ((E.nR b : ℂ) / r) ((j : ℂ) / r) := fun b =>
        sum_fin_eq E.nR E.injR _ E.imgR (fun j => elog ((E.nR b : ℂ) / r) ((j : ℂ) / r))
      simp_rw [inner]
      exact sum_fin_eq E.nR E.injR _ E.imgR
        (fun a => ∑ j ∈ (G.geometry r).rows, elog ((a : ℂ) / r) ((j : ℂ) / r))
    have e2 : ∑ b : Fin N, ∑ b' : Fin N, elog ((E.nQ b : ℂ) / r) ((E.nQ b' : ℂ) / r) =
        ∑ a ∈ (G.geometry r).cols, ∑ b ∈ (G.geometry r).cols,
          elog ((a : ℂ) / r) ((b : ℂ) / r) := by
      have inner : ∀ b : Fin N, ∑ b' : Fin N, elog ((E.nQ b : ℂ) / r) ((E.nQ b' : ℂ) / r) =
          ∑ j ∈ (G.geometry r).cols, elog ((E.nQ b : ℂ) / r) ((j : ℂ) / r) := fun b =>
        sum_fin_eq E.nQ E.injQ _ E.imgQ (fun j => elog ((E.nQ b : ℂ) / r) ((j : ℂ) / r))
      simp_rw [inner]
      exact sum_fin_eq E.nQ E.injQ _ E.imgQ
        (fun a => ∑ j ∈ (G.geometry r).cols, elog ((a : ℂ) / r) ((j : ℂ) / r))
    rw [e1, e2]
    exact h

set_option maxHeartbeats 8000000 in
theorem energy_geom_small_d (G : BlockGeom) {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (hρ : 0 < ρ) (hw0 : ∀ k, 0 ≤ wt k) (hm : ∑ k, wt k = 1) {Rc : ℝ} (hc : ∀ k, ‖c k‖ ≤ Rc)
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
      (z : Fin k → ℂ), Function.Injective z → (∀ l (t : ℝ), 0 ≤ t → m0 ≤ ‖z l - (t : ℂ)‖) →
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
  have hKc : (0 : ℝ) ≤ G.rowConst := Nat.cast_nonneg _
  have hRc : 0 ≤ Rc := by
    by_cases hK : Nonempty (Fin K)
    · obtain ⟨k0⟩ := hK; exact (norm_nonneg _).trans (hc k0)
    · exfalso; simp at hK; subst hK; simp at hm
  set Af : ℝ := a0 + Rc + ρ + |Real.log ρ| with hAf
  set Ab : ℝ := Bd + Rc + ρ + |Real.log ρ| with hAb
  have hAf0 : 0 ≤ Af := by positivity
  have hAb0 : 0 ≤ Ab := by positivity
  set Nb : ℝ := (G.totalMass : ℝ) + G.rowConst with hNb
  have hNb0 : 0 ≤ Nb := by positivity
  set A : ℝ := 2 * |Cdef| + 2 * G.rowConst * |mp| + (2 * (G.totalMass : ℝ) * G.rowConst +
      (G.rowConst : ℝ) ^ 2) * |Ibd| + (|1 - e| * Cl + 2 * G.rowConst * Af + 2 * G.rowConst * Ab +
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
  obtain ⟨R2, hR2⟩ := exists_nat_ge ((4 * (G.rowConst : ℝ) + G.E2) / (2 * Real.pi * (ε - e)))
  refine ⟨max (max R1 R2) 1, ?_⟩
  intro r N nc hR hN E k z hzi hdist hnorm s hs hkeep q hq hcap hℓ
  have hr1n : 1 ≤ r := le_trans (le_max_right _ _) hR
  have hr : 0 < r := hr1n
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr1n
  have hRR1 : R1 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRR2 : R2 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hmargin : 4 * (G.rowConst : ℝ) + G.E2 ≤ 2 * Real.pi * (ε - e) * r := by
    have h1 : ((4 * (G.rowConst : ℝ) + G.E2) / (2 * Real.pi * (ε - e))) ≤ r :=
      hR2.trans (by exact_mod_cast hRR2)
    have := (div_le_iff₀ hπε).mp h1
    linarith
  have hmain := G.energy_geom_d hρ hw0 hm hc g hg hr hN E hBd0 hBc hBr hBq hm0 z hzi hdist ha1
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
    (M := (G.totalMass : ℝ)) (Kc := (G.rowConst : ℝ)) (e := e) (Cl := Cl) (mp := mp)
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
