module

public import CatalanCore.Uniform.Decay.Nodes.Window

@[expose] public section

/-!
# D5 adapter, part 2: from the explicit all-common-deletion bound to the window

Part 2's `Lemma allJ` (all common deletions) produces, for every common deletion `J₀` with
`j = |J₀|` nodes removed, a bound of the shape

`|det Φ_r(ξ)[R∖J₀, Q∖J₀]| ≤ exp(-D' r² + c r j + K r (log (r+1) + 1))`

(`D' = D - 2Mζ`, `c ≥ 2(m₀-ℓ)`, `K` a fixed constant collecting the logarithmic growth errors).
This module absorbs the `K r log r` loss into an arbitrarily small `δ r²` and states the result as
the `HasAllMinorDecay` provider consumed by D3's `BlockGeom.hasScaledDecay_of_allMinor`
(the Part 1 transfer from all common deletions to the window is `Deletion`/`Window`, already
accepted).

* `eventually_rlog_le` : `K r (log (r+1) + 1) ≤ δ r²` for large `r`;
* `hasAllMinorDecay_of_bound` : the bound above, for `r ≥ R₁` and every common subset `S`,
  gives `NodeFamily.HasAllMinorDecay G Fr D' c`;
* `HasAllMinorDecay.mono` : decay may be weakened (`D'' ≤ D`, `c ≤ c'`);
* `BlockGeom.hasScaledDecay_of_energy_bound` : composite to `HasScaledDecay` of the block family.
-/

namespace CatalanCore.Uniform
open Finset Filter

theorem eventually_rlog_le {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → K * r * (Real.log (r + 1) + 1) ≤ δ * (r : ℝ) ^ 2 := by
  set ε : ℝ := δ / (4 * K + 4) with hε
  have hε0 : 0 < ε := by positivity
  have h := Real.isLittleO_log_id_atTop.def hε0
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 h
  refine ⟨max (max ⌈X⌉₊ 1) ⌈2 * K / δ⌉₊, fun r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := by
    have : (1 : ℕ) ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hr)
    exact_mod_cast this
  have hrX : X ≤ (r : ℝ) + 1 := by
    have : ⌈X⌉₊ ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
    have h2 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h3 : (⌈X⌉₊ : ℝ) ≤ r := by exact_mod_cast this
    linarith
  have hr2 : 2 * K / δ ≤ (r : ℝ) := by
    have : ⌈2 * K / δ⌉₊ ≤ r := (le_max_right _ _).trans hr
    have h2 : 2 * K / δ ≤ (⌈2 * K / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈2 * K / δ⌉₊ : ℝ) ≤ r := by exact_mod_cast this
    linarith
  have hlog := hX ((r : ℝ) + 1) hrX
  simp only [id, Real.norm_eq_abs] at hlog
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) + 1)] at hlog
  have hlog' : Real.log ((r : ℝ) + 1) ≤ ε * ((r : ℝ) + 1) := (le_abs_self _).trans hlog
  have hKr : 2 * K ≤ δ * r := by
    rw [div_le_iff₀ hδ] at hr2; linarith
  have hKε : K * ε ≤ δ / 4 := by
    rw [hε]
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hr0 : (0 : ℝ) ≤ r := by linarith
  calc K * r * (Real.log (r + 1) + 1) ≤ K * r * (ε * ((r : ℝ) + 1) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK hr0)
    _ = (K * ε) * (r : ℝ) ^ 2 + (K * ε) * r + K * r := by ring
    _ ≤ (δ / 4) * (r : ℝ) ^ 2 + (δ / 4) * (r : ℝ) ^ 2 + (δ / 2) * (r : ℝ) ^ 2 := by
        have a1 : (K * ε) * (r : ℝ) ^ 2 ≤ (δ / 4) * (r : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hKε (by positivity)
        have a2 : (K * ε) * r ≤ (δ / 4) * (r : ℝ) ^ 2 := by
          calc (K * ε) * r ≤ (δ / 4) * r := mul_le_mul_of_nonneg_right hKε hr0
            _ ≤ (δ / 4) * (r : ℝ) ^ 2 := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                nlinarith
        have a3 : K * r ≤ (δ / 2) * (r : ℝ) ^ 2 := by
          have : K * r ≤ (δ * r / 2) * r := mul_le_mul_of_nonneg_right (by linarith) hr0
          nlinarith
        linarith
    _ = δ * (r : ℝ) ^ 2 := by ring

namespace NodeFamily

/-- **From the explicit all-common-deletion bound to `HasAllMinorDecay`.** -/
theorem hasAllMinorDecay_of_bound (G : NodeFamily) (Fr : Frame) {D c K : ℝ} (hc : 0 ≤ c)
    (hK : 0 ≤ K) (R1 : ℕ)
    (hb : ∀ r : ℕ, R1 ≤ r → ∀ S : Finset (G r).C,
      |(Rect.FullN Fr (fun a : S => ((a.1 : (G r).C) : ℕ))
        (G r).xs (G r).ys Fr.const).det| ≤
        Real.exp (-D * (r : ℝ) ^ 2 + c * r * (((G r).C.card - S.card : ℕ) : ℝ)
          + K * r * (Real.log (r + 1) + 1))) :
    G.HasAllMinorDecay Fr D c := by
  intro δ hδ
  obtain ⟨R2, hR2⟩ := eventually_rlog_le hK hδ
  refine ⟨max R1 R2, fun r hr S => ?_⟩
  refine (hb r ((le_max_left _ _).trans hr) S).trans (Real.exp_le_exp.2 ?_)
  have := hR2 r ((le_max_right _ _).trans hr)
  nlinarith

/-- Decay may be weakened in both parameters. -/
theorem HasAllMinorDecay.mono {G : NodeFamily} {Fr : Frame} {D D' c c' : ℝ} (hc : 0 ≤ c)
    (hD : D' ≤ D) (hcc : c ≤ c') (h : G.HasAllMinorDecay Fr D c) :
    G.HasAllMinorDecay Fr D' c' := by
  intro δ hδ
  obtain ⟨R0, hR0⟩ := h (δ) hδ
  refine ⟨R0, fun r hr S => (hR0 r hr S).trans (Real.exp_le_exp.2 ?_)⟩
  have h1 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ (r : ℝ) * (((G r).C.card - S.card : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  nlinarith

end NodeFamily

/-- **Composite**: the explicit all-common-deletion bound gives the bounded-selector window
(`HasScaledDecay`) of the block family. -/
theorem BlockGeom.hasScaledDecay_of_energy_bound (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    {D c K : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) (R1 : ℕ)
    (hb : ∀ r : ℕ, R1 ≤ r → ∀ S : Finset (G.geometry r).C,
      |(Rect.FullN Fr (fun a : S => ((a.1 : (G.geometry r).C) : ℕ))
        (G.geometry r).xs (G.geometry r).ys Fr.const).det| ≤
        Real.exp (-D * (r : ℝ) ^ 2 + c * r * ((((G.geometry r).C.card - S.card : ℕ)) : ℝ)
          + K * r * (Real.log (r + 1) + 1))) :
    HasScaledDecay (G.family Fr depth) G.scale D c :=
  G.hasScaledDecay_of_allMinor Fr depth hc
    (NodeFamily.hasAllMinorDecay_of_bound G.geometry Fr hc hK R1 hb)

end CatalanCore.Uniform
