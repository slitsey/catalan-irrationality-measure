module

public import CatalanCore.Decay.Rect.Energy3
public import CatalanCore.Decay.Rect.IntegR
public import CatalanCore.Decay.Rect.Asymp2
public import CatalanCore.Rect.Family

@[expose] public section

/-!
# The shared core of the rectangular decay theorems (DECAYDEDUP)

`decay_core` is the window-independent part of `decay_of_certG_rect` (DecayRect.lean) and
`decay_top_of_certG_rect` (DecayTop.lean): it fixes the constants, builds the energy hypothesis
`Frame.RectEnergy` for the patterns `(r, m)` and (when `m + 1 ≤ α r + 1`) `(r, m+1)`, and shows
that the resulting window exponents are below `-(D - δ) r²`.  The two decay theorems then only
apply their own window lemma (`window_rect` / `window_rect_top`).
-/

open Filter Topology
open CatalanLambda.Decay (Usig Utau Irho cexpr)

namespace CatalanCore

open Decay

theorem eventually_goodG {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} (Fr : Frame)
    (F : Cert.CertCoreG K ρ ε c wt) :
    ∀ᶠ r : ℕ in atTop, Fr.n0off ≤ ⌊(F.r0 : ℝ) * r⌋₊ ∧
      (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * r := by
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  have hW0 : (0 : ℝ) < F.W := by exact_mod_cast F.W_pos
  have h1 : ∀ᶠ h : ℕ in atTop, (Fr.n0off : ℝ) + 1 + Fr.xs ≤ F.W * h := by
    have : Tendsto (fun h : ℕ => (F.W : ℝ) * h) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hW0
    exact this.eventually_ge_atTop _
  have h2 : ∀ᶠ h : ℕ in atTop, (Fr.n0off : ℝ) ≤ F.r0 * h := by
    have : Tendsto (fun h : ℕ => (F.r0 : ℝ) * h) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hr0
    exact this.eventually_ge_atTop _
  filter_upwards [h1, h2] with h hh1 hh2
  exact ⟨Nat.le_floor hh2, hh1⟩

set_option maxHeartbeats 4000000 in
theorem decay_core {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOK') (F : Cert.CertCoreG K ρ ε c wt) {α : ℚ} (hα : 0 < α)
    (hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|)
    (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) {D : ℚ} (hD : D ≤ F.Dof Fr.d α Inu) :
    ∃ e m0 κ B0 : ℝ, 0 < e ∧ e < 1 ∧ 0 < m0 ∧ m0 ≤ Fr.xs ∧ (∀ i, m0 ≤ Fr.μ i) ∧ κ = Real.log (4 * (1 + 1 / m0)) ∧
      B0 = Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1 ∧
      ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m : ℕ, N₀ ≤ r → (α : ℝ) * r ≤ m → (m : ℝ) ≤ α * r + 1 →
        1 ≤ r ∧ (((⌊(F.r0 : ℝ) * r⌋₊ - Fr.n0off : ℕ)) : ℝ) ≤ (F.r0 : ℝ) * r ∧
        (∃ T0 : ℝ,
          (∀ (k : ℕ) (s : Fin k → Fin (r + m)), Function.Injective s →
            (∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s i = b) →
            Frame.RectEnergy Fr (⌊(F.r0 : ℝ) * r⌋₊ - Fr.n0off) k e m0 (max (Real.log Fr.Aco) 0)
              (T0 + r * (((r : ℝ) + m) - k) * (F.ccert : ℝ))
              (fun i => xnode r (s i)) (fun i => ynode r (s i))) ∧
          T0 + ((r : ℝ) + m) * Real.log (Fr.Wabs * ((F.r0 : ℝ) * r) + B0) + r * Real.log 2
            ≤ -((D : ℝ) - δ) * (r : ℝ) ^ 2) ∧
        ((m : ℝ) + 1 ≤ α * r + 1 → ∃ T1 : ℝ,
          (∀ (k : ℕ) (s : Fin k → Fin (r + m + 1)), Function.Injective s →
            (∀ b : Fin (r + m + 1), r ≤ (b : ℕ) → ∃ i, s i = b) →
            Frame.RectEnergy Fr (⌊(F.r0 : ℝ) * r⌋₊ - Fr.n0off) k e m0 (max (Real.log Fr.Aco) 0)
              (T1 + r * (((r : ℝ) + m + 1) - k) * (F.ccert : ℝ))
              (fun i => xnode r (s i)) (fun i => ynode r (s i))) ∧
          T1 + ((r : ℝ) + m + 1) * (Real.log (Fr.Wabs * ((F.r0 : ℝ) * r) + B0) + κ)
            + r * Real.log 2 ≤ -((D : ℝ) - δ) * (r : ℝ) ^ 2) := by
  classical
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  have hε0 := F.hε0
  have hε1 := F.hε1
  obtain ⟨m0, hm0, hm0xs, hm0μ⟩ := Frame.exists_m0 Fr hFr.contour.xs_pos
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ε / 2 := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  have he1 : e < 1 := by rw [he]; linarith
  have heε : e < ε := by rw [he]; linarith
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hFr.contour.xs_pos
  have hr0q : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  -- constants
  obtain ⟨Γd, hΓd⟩ : ∃ Γd : ℝ, Γd = Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0 := ⟨_, rfl⟩
  obtain ⟨A0, hA0def⟩ : ∃ A0 : ℝ, A0 = (F.r0 : ℝ) + Fr.xs + Rc + ρ + 1 := ⟨_, rfl⟩
  obtain ⟨Cl, hClDef⟩ : ∃ Cl : ℝ, Cl = max (Real.log Fr.Aco) 0 := ⟨_, rfl⟩
  have hΓ : 0 ≤ Γd := by
    rw [hΓd]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => le_max_right _ _))
  have hA0 : 0 ≤ A0 := by rw [hA0def]; have := F.hρ; positivity
  have hCl0 : 0 ≤ Cl := by rw [hClDef]; exact le_max_right _ _
  obtain ⟨B0, hB0def⟩ : ∃ B0 : ℝ, B0 = Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
      + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1 := ⟨_, rfl⟩
  have hAp := Frame.Aco_pos hFr.contour
  have hbe := Frame.betaE_pos he0
  have hW0 := Fr.Wabs_nonneg
  have hB01 : 1 ≤ B0 := by
    rw [hB0def]
    have : (0 : ℝ) ≤ Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by positivity
    have : (0 : ℝ) ≤ 2 * (Fr.Aco ^ e / Frame.betaE e) := by positivity
    linarith
  obtain ⟨L0, hL0def⟩ : ∃ L0 : ℝ, L0 = Real.log (Fr.Wabs * F.r0 + B0) := ⟨_, rfl⟩
  have hDreal : (D : ℝ) ≤ 2 * ((1 + (α : ℝ)) * F.mprime + Fr.d * F.Sbase)
      - (1 + (α : ℝ)) ^ 2 * F.Ibound + Inu := by
    have h1 : ((D : ℚ) : ℝ) ≤ ((F.Dof Fr.d α Inu : ℚ) : ℝ) := by exact_mod_cast hD
    unfold Cert.CertCoreG.Dof at h1
    push_cast at h1
    exact h1
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.log (4 * (1 + 1 / m0)) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    refine Real.log_nonneg ?_
    have : 0 ≤ 1 / m0 := by positivity
    linarith
  refine ⟨e, m0, κ, B0, he0, he1, hm0, hm0xs, hm0μ, hκdef, hB0def, ?_⟩
  intro δ hδ
  obtain ⟨r0, hr0⟩ := asymp_main (α := (α : ℝ)) (m' := F.mprime) (dS := Fr.d * F.Sbase)
    (Ib := F.Ibound) (Inu := Inu) (Γd := Γd) (A0 := A0) (ρ := ρ) (m0 := m0) (Cl := Cl)
    (L0 := L0 + κ) (D := D) hαR hm0 hΓ hA0 hCl0 hInu hDreal hδ
  obtain ⟨r1, hr1⟩ := Filter.eventually_atTop.1 (eventually_goodG Fr F)
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℕ, ∀ r : ℕ, r2 ≤ r → 2 ≤ Real.pi * (ε - e) * r := by
    have hpe : 0 < Real.pi * (ε - e) := by
      have := Real.pi_pos
      have : 0 < ε - e := by linarith
      positivity
    refine ⟨⌈2 / (Real.pi * (ε - e))⌉₊, fun r hr => ?_⟩
    have h1 : 2 / (Real.pi * (ε - e)) ≤ r :=
      (Nat.le_ceil _).trans (by exact_mod_cast hr)
    rw [div_le_iff₀ hpe] at h1
    linarith
  refine ⟨max (max r0 r1) (max r2 1), ?_⟩
  intro r m hrN hαr hαr'
  have hr0' : r0 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hrN
  have hr1' : r1 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hrN
  have hr2' : r2 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hrN
  have hrpos : 1 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hrN
  have hr' : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m := by
      have : (0 : ℝ) < α * r := by positivity
      linarith
    exact_mod_cast this
  obtain ⟨hgood1, hgood2⟩ := hr1 r hr1'
  have hN0 : (⌊(F.r0 : ℝ) * r⌋₊ - Fr.n0off) + Fr.n0off = ⌊(F.r0 : ℝ) * r⌋₊ := by omega
  have hR : (((⌊(F.r0 : ℝ) * r⌋₊ - Fr.n0off : ℕ)) : ℝ) ≤ (F.r0 : ℝ) * r := by
    have h1 := Nat.floor_le (show (0 : ℝ) ≤ F.r0 * r by positivity)
    have h2 : (((⌊(F.r0 : ℝ) * r⌋₊ - Fr.n0off : ℕ)) : ℝ) ≤ ⌊(F.r0 : ℝ) * r⌋₊ :=
      Nat.cast_le.2 (Nat.sub_le _ _)
    linarith
  -- the energy hypothesis for every kept-node pattern
  obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ, T0 = -(2 * r * ((r : ℝ) + m) * F.mprime
      + 2 * (r : ℝ) ^ 2 * (Fr.d * F.Sbase) - ((r : ℝ) + m) ^ 2 * F.Ibound + Alow r m)
      + RerrR Γd A0 ρ m0 Cl α r m := ⟨_, rfl⟩
  have hEn : ∀ (k : ℕ) (s : Fin k → Fin (r + m)), Function.Injective s →
      (∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s i = b) →
      Frame.RectEnergy Fr (⌊(F.r0 : ℝ) * r⌋₊ - Fr.n0off) k e m0 (max (Real.log Fr.Aco) 0)
        (T0 + r * (((r : ℝ) + m) - k) * (F.ccert : ℝ))
        (fun i => xnode r (s i)) (fun i => ynode r (s i)) := by
    intro k s hs hkeep x hxi hx hre q hq
    have h := energy_rect (Fr := Fr) hFr.toDecayOK F (α := (α : ℝ)) hαR hg hw0 hRc hc hrpos hmpos
      hαr hαr' hN0 hgood2 hm0 x hxi hx hre s hs hkeep he0 heε (hr2 r hr2') q
      (Cl := max (Real.log Fr.Aco) 0) (le_max_right _ _) hq
    have hT0' : T0 = -(2 * r * ((r : ℝ) + m) * F.mprime + 2 * (r : ℝ) ^ 2 * (Fr.d * F.Sbase)
        - ((r : ℝ) + m) ^ 2 * F.Ibound + Alow r m)
        + RerrR (Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0)
          ((F.r0 : ℝ) + Fr.xs + Rc + ρ + 1) ρ m0 (max (Real.log Fr.Aco) 0) α r m := by
      rw [hT0, hΓd, hA0def, hClDef]
    rw [hT0']
    linarith [h]
  have hlogM : Real.log (Fr.Wabs * ((F.r0 : ℝ) * r) + B0) ≤ L0 + Real.log r := by
    have h := log_lin_le (Fr.Wabs * F.r0) B0 (by positivity) hB01 hrpos
    rw [hL0def]
    have e1 : Fr.Wabs * ((F.r0 : ℝ) * r) = Fr.Wabs * F.r0 * r := by ring
    rw [e1]; exact h
  have hNnn : (0 : ℝ) ≤ (r : ℝ) + m := by positivity
  have hNnn1 : (0 : ℝ) ≤ (r : ℝ) + m + 1 := by positivity
  refine ⟨hrpos, hR, ⟨T0, hEn, ?_⟩, ?_⟩
  · have hasym0 := hr0 r m hr0' hαr hαr'
    have hlm0 := mul_le_mul_of_nonneg_left hlogM hNnn
    have hκm0 := mul_nonneg hNnn hκ0
    rw [hT0]
    nlinarith [hasym0, hlm0, hκm0]
  intro hm1
  have hαr1 : (α : ℝ) * r ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hαr1' : ((m + 1 : ℕ) : ℝ) ≤ α * r + 1 := by push_cast; linarith
  obtain ⟨T1, hT1⟩ : ∃ T1 : ℝ, T1 = -(2 * r * ((r : ℝ) + ((m + 1 : ℕ) : ℝ)) * F.mprime
      + 2 * (r : ℝ) ^ 2 * (Fr.d * F.Sbase) - ((r : ℝ) + ((m + 1 : ℕ) : ℝ)) ^ 2 * F.Ibound
      + Alow r (m + 1)) + RerrR Γd A0 ρ m0 Cl α r (m + 1) := ⟨_, rfl⟩
  have hEn1 : ∀ (k : ℕ) (s : Fin k → Fin (r + m + 1)), Function.Injective s →
      (∀ b : Fin (r + m + 1), r ≤ (b : ℕ) → ∃ i, s i = b) →
      Frame.RectEnergy Fr (⌊(F.r0 : ℝ) * r⌋₊ - Fr.n0off) k e m0 (max (Real.log Fr.Aco) 0)
        (T1 + r * (((r : ℝ) + m + 1) - k) * (F.ccert : ℝ))
        (fun i => xnode r (s i)) (fun i => ynode r (s i)) := by
    intro k s hs hkeep x hxi hx hre q hq
    have h := energy_rect (Fr := Fr) hFr.toDecayOK F (α := (α : ℝ)) hαR hg hw0 hRc hc hrpos
      (Nat.succ_pos m) hαr1 hαr1' hN0 hgood2 hm0 x hxi hx hre s hs hkeep he0 heε (hr2 r hr2') q
      (Cl := max (Real.log Fr.Aco) 0) (le_max_right _ _) hq
    have hT1' : T1 = -(2 * r * ((r : ℝ) + ((m + 1 : ℕ) : ℝ)) * F.mprime
        + 2 * (r : ℝ) ^ 2 * (Fr.d * F.Sbase) - ((r : ℝ) + ((m + 1 : ℕ) : ℝ)) ^ 2 * F.Ibound
        + Alow r (m + 1))
        + RerrR (Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0)
          ((F.r0 : ℝ) + Fr.xs + Rc + ρ + 1) ρ m0 (max (Real.log Fr.Aco) 0) α r (m + 1) := by
      rw [hT1, hΓd, hA0def, hClDef]
    rw [hT1']
    push_cast at h ⊢
    linarith [h]
  refine ⟨T1, hEn1, ?_⟩
  have hasym1 := hr0 r (m + 1) hr0' hαr1 hαr1'
  push_cast at hasym1
  have hlm1 := mul_le_mul_of_nonneg_left (add_le_add_right hlogM κ) hNnn1
  have hT1c := hT1
  push_cast at hT1c
  have hκm1 := mul_nonneg hNnn1 hκ0
  rw [hT1c]
  nlinarith [hasym1, hlm1, hκm1]

end CatalanCore
