module
public import CatalanCore.Uniform.Decay.Nodes.EnergyAux
public import CatalanCore.Uniform.Decay.Nodes.EnergyArith
@[expose] public section

/-!
# The block-node energy step (Part 1, Lemma `general-energy`), Frame-free

`energy_block`: for ANY injective row/column node lists `nR, nQ : Fin N → ℕ` that agree on the
first `nc` (common) positions, every retained pattern `s` (all non-common nodes kept, so the
removed nodes are common), every admissible free configuration `z`, and weights `q`:

`∑ log q + (1/2) (log ‖C(z, rows)‖² + log ‖C(z, cols)‖²) ≤ -(D r² ...) + c r (N - k) + Err`.

The three node-sum discrepancies (`hPS`, `hRS`, `hAS`: proved for block geometries in
`PotentialPS`, `PotentialRS`, `SelfScaled`), the cap-sum (`hcap`, the output of `lemmaBG`), the
free-point norm control and the common-support bound are hypotheses.  No Frame appears.
The final determinant bound is `Frame.theoremN_rect` applied to this inequality
(`RectEnergy`), outside this file.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Finset CatalanLambda.Decay

lemma elog_scaleB {c : ℝ} (hc : 0 < c) (u v : ℂ) :
    elog ((c : ℂ) * u) ((c : ℂ) * v) = elog u v - (if u = v then 0 else Real.log c) := by
  by_cases huv : u = v
  · subst huv; simp [elog_self]
  · rw [if_neg huv]
    unfold elog
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le,
      Real.log_mul hc.ne' (norm_ne_zero_iff.2 (sub_ne_zero.2 huv))]
    ring

lemma sum_offdiag_constB (a : ℝ) (k : ℕ) :
    ∑ l : Fin k, ∑ l' : Fin k, (if l = l' then (0 : ℝ) else a) = k * (k - 1) * a := by
  have h1 : ∀ l : Fin k, ∑ l' : Fin k, (if l = l' then (0 : ℝ) else a) = (k - 1) * a := by
    intro l
    have : ∀ l' : Fin k, (if l = l' then (0 : ℝ) else a) = a - (if l = l' then a else 0) := by
      intro l'; split_ifs <;> simp
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The two-list energy `Esc` of a free configuration against a node list. -/
noncomputable def EscB {k : ℕ} (σ ω : Fin k → ℂ) : ℝ :=
  ∑ l, ∑ l', elog (σ l) (σ l') + ∑ i, ∑ i', elog (ω i) (ω i')
    - 2 * ∑ l, ∑ i, elog (σ l) (ω i)

/-- Scale-`r` form of the Cauchy determinant energy identity. -/
theorem neg_log_cexpr_scaledB {k r : ℕ} (hr : 0 < r) (z w : Fin k → ℂ)
    (hzi : Function.Injective z) (hwi : Function.Injective w) (hzw : ∀ l i, z l ≠ w i) :
    -Real.log (‖cexpr z w‖ ^ 2)
      = EscB (fun l => z l / r) (fun i => w i / r) + 2 * k * Real.log r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h0 := neg_log_cexpr_sq z w hzi hwi hzw
  set σ : Fin k → ℂ := fun l => z l / r with hσ
  set ω : Fin k → ℂ := fun i => w i / r with hω
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hzσ : ∀ l, z l = (r : ℂ) * σ l := fun l => by simp only [hσ]; field_simp
  have hwω : ∀ i, w i = (r : ℂ) * ω i := fun i => by simp only [hω]; field_simp
  have hσi : Function.Injective σ := fun a b h => hzi (by rw [hzσ a, hzσ b, h])
  have hωi : Function.Injective ω := fun a b h => hwi (by rw [hwω a, hwω b, h])
  have hσω : ∀ l i, σ l ≠ ω i := fun l i e => hzw l i (by rw [hzσ l, hwω i, e])
  have S1 : ∑ l, ∑ l', elog (z l) (z l')
      = ∑ l, ∑ l', elog (σ l) (σ l') - k * (k - 1) * Real.log r := by
    have : ∀ l l', elog (z l) (z l') = elog (σ l) (σ l') - (if l = l' then 0 else Real.log r) := by
      intro l l'
      rw [hzσ l, hzσ l']
      have := elog_scaleB (c := (r : ℝ)) hr' (σ l) (σ l')
      simp only [Complex.ofReal_natCast] at this
      rw [this]
      congr 2
      simp only [hσi.eq_iff]
    simp_rw [this, Finset.sum_sub_distrib]
    rw [sum_offdiag_constB]
  have S2 : ∑ i, ∑ i', elog (w i) (w i')
      = ∑ i, ∑ i', elog (ω i) (ω i') - k * (k - 1) * Real.log r := by
    have : ∀ i i', elog (w i) (w i') = elog (ω i) (ω i') - (if i = i' then 0 else Real.log r) := by
      intro i i'
      rw [hwω i, hwω i']
      have := elog_scaleB (c := (r : ℝ)) hr' (ω i) (ω i')
      simp only [Complex.ofReal_natCast] at this
      rw [this]
      congr 2
      simp only [hωi.eq_iff]
    simp_rw [this, Finset.sum_sub_distrib]
    rw [sum_offdiag_constB]
  have S3 : ∑ l, ∑ i, elog (z l) (w i) = ∑ l, ∑ i, elog (σ l) (ω i) - k * k * Real.log r := by
    have : ∀ l i, elog (z l) (w i) = elog (σ l) (ω i) - Real.log r := by
      intro l i
      rw [hzσ l, hwω i]
      have := elog_scaleB (c := (r : ℝ)) hr' (σ l) (ω i)
      simp only [Complex.ofReal_natCast] at this
      rw [this, if_neg (hσω _ _)]
    simp_rw [this, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [h0, S1, S2, S3]
  unfold EscB
  ring

/-- The `B`-expression of the restored-node energy. -/
noncomputable def BexpB {k N : ℕ} (σ : Fin k → ℂ) (τ : Fin N → ℂ) (msk : Fin N → ℝ) : ℝ :=
  ∑ l, ∑ l', elog (σ l) (σ l') + 2 * ∑ l, ∑ b, msk b * elog (σ l) (τ b)
    + ∑ b, ∑ b', msk b * msk b' * elog (τ b) (τ b')

lemma BexpB_congr {k N : ℕ} (σ : Fin k → ℂ) (τ τ' : Fin N → ℂ) (msk : Fin N → ℝ)
    (h : ∀ b, msk b ≠ 0 → τ b = τ' b) : BexpB σ τ msk = BexpB σ τ' msk := by
  unfold BexpB
  have h1 : ∀ l b, msk b * elog (σ l) (τ b) = msk b * elog (σ l) (τ' b) := by
    intro l b
    by_cases hb : msk b = 0
    · simp [hb]
    · rw [h b hb]
  have h2 : ∀ b b', msk b * msk b' * elog (τ b) (τ b') = msk b * msk b' * elog (τ' b) (τ' b') := by
    intro b b'
    by_cases hb : msk b = 0
    · simp [hb]
    · by_cases hb' : msk b' = 0
      · simp [hb']
      · rw [h b hb, h b' hb']
  simp only [h1, h2]

set_option maxHeartbeats 8000000 in
/-- **The block-node energy step.** -/
theorem energy_block {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (hρ : 0 < ρ) (hw0 : ∀ k, 0 ≤ wt k) (hm : ∑ k, wt k = 1) {Rc : ℝ} (hc : ∀ k, ‖c k‖ ≤ Rc)
    {M : ℝ} (hM : 0 ≤ M) (g U : ℂ → ℝ)
    (hg : ∀ s : ℂ, g s = M * Usig ρ c wt s - U s + (1 - ε) * Real.pi * |s.im|)
    {r N nc : ℕ} (hr : 0 < r) (hN : 0 < N) {Kc : ℝ} (hKc : 0 ≤ Kc)
    (hNM : |(N : ℝ) - M * r| ≤ Kc)
    (nR nQ : Fin N → ℕ) (hRi : Function.Injective nR) (hQi : Function.Injective nQ)
    (hcom : ∀ b : Fin N, (b : ℕ) < nc → nR b = nQ b)
    {Bd : ℝ} (hBd : ∀ b : Fin N, (b : ℕ) < nc → (nR b : ℝ) ≤ Bd * r) (hBd0 : 0 ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) {k : ℕ} (z : Fin k → ℂ) (hzi : Function.Injective z)
    (hre : ∀ l, m0 ≤ -(z l).re)
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
  have hzneg : ∀ l, (z l).re < 0 := fun l => by linarith [hre l]
  have hσneg : ∀ l, (σ l).re < 0 := fun l => by
    rw [hσre]; exact div_neg_of_neg_of_pos (hzneg l) hr'
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
  have hστR : ∀ l b, σ l ≠ τR b := fun l b e' => by
    have := congrArg Complex.re e'; linarith [hσneg l, hτRre b]
  have hστQ : ∀ l b, σ l ≠ τQ b := fun l b e' => by
    have := congrArg Complex.re e'; linarith [hσneg l, hτQre b]
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
  have hzrow : ∀ l i, z l ≠ rowC i := fun l i e' => by
    have h1 := congrArg Complex.re e'
    simp only [hrowC, Complex.natCast_re] at h1
    have : (0 : ℝ) ≤ ((nR (s i) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith [hzneg l]
  have hzcol : ∀ l i, z l ≠ colC i := fun l i e' => by
    have h1 := congrArg Complex.re e'
    simp only [hcolC, Complex.natCast_re] at h1
    have : (0 : ℝ) ≤ ((nQ (s i) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith [hzneg l]
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
