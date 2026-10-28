module

public import CatalanCore.Uniform.Content.Wire.Output
public import CatalanCore.Uniform.Content.Shape.Reindex
public import CatalanCore.Uniform.Measure.BlockNV

@[expose] public section

/-!
# Content and measure on a scale predicate `P` (lane H7)

The H5/H6 layers (`Wire.Output`) are valid only where `HybShape` holds, i.e. at even scale for
the alternating geometry.  Here the H5 assembler is re-run for the family restricted to the scales
satisfying `P` (all covering hypotheses are needed only for `P r`), and the measure theorem is
derived for the restricted family by the even-scale reindexing `measure_of_family_nv0_even`.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire

namespace CatalanCore.Uniform.Content.Shape

variable {M : ℕ} [NeZero M]

/-- `hasContent_blockGeom` for the family restricted to the scales satisfying `P`. -/
theorem hasContent_blockGeom_on (G : BlockGeom) (Fr : Frame) (depth : ℕ) (P : ℕ → Prop)
    (CC : ContentCover ((G.family Fr depth).restrictAdm (fun i => P i.1)) G.scale M) :
    HasContent ((G.family Fr depth).restrictAdm (fun i => P i.1))
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M CC.tmpl) := by
  have hmass : (0 : ℝ) < G.common.mass := by exact_mod_cast G.common_pos
  refine ContentCover.hasContent_of_cover CC
    (fun i => NodeFamily.family_degree Fr G.geometry depth i)
    (γ := (G.common.mass : ℝ)⁻¹) (γ' := (G.common.mass : ℝ))
    (K0 := ((G.common.n : ℝ) + depth) / G.common.mass) (K1 := G.common.n)
    (inv_nonneg.2 hmass.le) hmass (by positivity) (Nat.cast_nonneg _) ?_ ?_
  · intro i hi
    have hc := (G.card_common i.1).1
    have hc' : (G.common.mass : ℝ) * i.1 - G.common.n ≤ ((G.geometry i.1).C.card : ℝ) := by
      exact_mod_cast hc
    have hAdm : (G.geometry i.1).C.card - i.2.card ≤ depth := hi.1
    have hle : i.2.card ≤ (G.geometry i.1).C.card := by simpa using Finset.card_le_univ i.2
    have hdep : ((G.geometry i.1).C.card : ℝ) ≤ i.2.card + depth := by
      have : (G.geometry i.1).C.card ≤ i.2.card + depth := by omega
      exact_mod_cast this
    have hdeg : (G.family Fr depth).deg i = i.2.card := rfl
    show (i.1 : ℝ) ≤ (G.common.mass : ℝ)⁻¹ * ((G.family Fr depth).deg i : ℝ) +
      ((G.common.n : ℝ) + depth) / G.common.mass
    rw [hdeg]
    rw [inv_mul_eq_div, ← add_div, le_div_iff₀ hmass]
    nlinarith
  · intro i _
    exact G.degree_bound Fr depth i

/-- **H5's `hasContent_of_debitLayers`, restricted to the scales satisfying `P`.** -/
theorem hasContent_of_debitLayers_on (G : BlockGeom) (Fr : Frame) (depth : ℕ) (P : ℕ → Prop)
    {k : ℕ} (L : Fin (k + 1) → DebitLayer G Fr depth) (h0 : ∀ r p, P r → (L 0).valid r p)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (tail : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p → ∃ j, (L j).valid r p ∧ (L j).eff r p = 0)
    (pre : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ (tmpl c).α0 * r)
    (cov : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ Q ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊Q.s * r⌋₊ < p → p ≤ ⌊Q.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, P r → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ K * r) :
    HasContent ((G.family Fr depth).restrictAdm (fun i => P i.1))
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) := by
  classical
  let w : Fin (k + 1) → NodeFamily.Index G.geometry → ℕ → ℕ := fun j i p =>
    if (L j).valid i.1 p then (L j).base i.1 p + (L j).debit * delCount G i
    else (L 0).base i.1 p + (L 0).debit * delCount G i
  have hw_le : ∀ j (i : NodeFamily.Index G.geometry), (G.family Fr depth).Adm i → ∀ p,
      (L j).valid i.1 p → w j i p ≤ (L j).eff i.1 p := by
    intro j i hi p hv
    have hd := delCount_le G Fr depth i hi
    simp only [w, if_pos hv, DebitLayer.eff]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hd) _
  have hw_le_real : ∀ j (i : NodeFamily.Index G.geometry), (G.family Fr depth).Adm i → ∀ p,
      (L j).valid i.1 p → (w j i p : ℝ) ≤ (((L j).eff i.1 p : ℕ) : ℝ) := by
    intro j i hi p hv
    exact_mod_cast hw_le j i hi p hv
  let CC : ContentCover ((G.family Fr depth).restrictAdm (fun i => P i.1)) G.scale M :=
    ContentCover.ofLayers (Fam := (G.family Fr depth).restrictAdm (fun i => P i.1))
      (sc := G.scale) tmpl w K hK
      (by
        intro j i hi p hp
        by_cases hv : (L j).valid i.1 p
        · simp only [w, if_pos hv]
          exact (L j).gle i hi.1 p hv
        · simp only [w, if_neg hv]
          exact (L 0).gle i hi.1 p (h0 _ _ hi.2))
      (by
        intro i hi c hc p hp hpc hlt
        obtain ⟨j, hv, he⟩ := tail i.1 hi.2 c hc p hp hpc hlt
        exact ⟨j, Nat.le_zero.1 (he ▸ hw_le j i hi.1 p hv)⟩)
      (by
        intro i hi c hc p h1 hp hpc
        obtain ⟨j, hv, he⟩ := pre i.1 hi.2 c hc p h1 hp hpc
        exact ⟨j, (hw_le_real j i hi.1 p hv).trans he⟩)
      (by
        intro i hi c hc Q hQ p h1 h2 hp hpc
        obtain ⟨j, hv, he⟩ := cov i.1 hi.2 c hc Q hQ p h1 h2 hp hpc
        exact ⟨j, (hw_le_real j i hi.1 p hv).trans he⟩)
      (by
        intro i hi p hp hpd
        obtain ⟨j, hv, he⟩ := exc i.1 hi.2 p hp hpd
        exact ⟨j, (hw_le_real j i hi.1 p hv).trans he⟩)
  exact hasContent_blockGeom_on G Fr depth P CC

end CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.BlockGeom

/-- **Measure theorem on the even-scale subfamily.**  Content and decay are needed only for the
members of even scale; nonvanishing comes from the complete `HasNV0` (members at every scale).
The exponent `γ c / (D - Λ)` is the same as for the full family. -/
theorem measure_of_providers_even (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    {Λ D c : ℝ}
    (hΛ : HasScaledContent
      ((G.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) G.scale Λ)
    (hminor : NodeFamily.HasAllMinorDecay G.geometry Fr D c)
    (hnv : HasNV0 (G.family Fr depth) G.scale)
    (hη : Λ < D) (hc : 0 < c) :
    (G.family Fr depth).MeasureLB ((G.common.mass : ℝ) * c / (D - Λ)) := by
  have hD := G.hasScaledDecay Fr depth hc.le hminor
  have h := measure_of_family_nv0_even
    ((G.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) G.scale
    (γ := G.common.mass) (K := G.common.n) hΛ
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) hη hc
    (by exact_mod_cast G.common_pos) (Nat.cast_nonneg _)
    (fun n hn => G.degree_bound Fr depth n)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := hnv
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : G.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  exact h

end CatalanCore.Uniform.BlockGeom
