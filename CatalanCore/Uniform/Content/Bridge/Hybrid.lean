module

public import CatalanCore.Uniform.Content.Bridge.Scale
public import CatalanCore.Uniform.Content.Shape.Wrap

@[expose] public section

/-!
# End-to-end hybrid: H5/H6 content + D-decay + NV0 give `MeasureLB` (lane H, bridge)

Chain: `hasContent_twoTerm_on` (degree units, even scales) -> `hasScaledContent_of_hasContent`
(scale units, `Λ = mass² Λ_deg = contentConstant`) -> `measure_of_family_nv0_even`.
The window contract `HasScaledDecay` is a hypothesis (output of `hasScaledDecay_of_check`).
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.BlockGeom

/-- Scale-unit content of the even-scale block family from degree-unit content. -/
theorem hasScaledContent_restricted (G : BlockGeom) (Fr : Frame) (depth : ℕ) (P : ℕ → Prop)
    {Λd : ℝ} (hΛd : 0 ≤ Λd) (h : HasContent ((G.family Fr depth).restrictAdm (fun i => P i.1)) Λd) :
    HasScaledContent ((G.family Fr depth).restrictAdm (fun i => P i.1)) G.scale
      ((G.common.mass : ℝ) ^ 2 * Λd) := by
  have hmass : (0 : ℝ) < G.common.mass := by exact_mod_cast G.common_pos
  refine hasScaledContent_of_hasContent ((G.family Fr depth).restrictAdm (fun i => P i.1)) G.scale (K0 := ((G.common.n : ℝ) + depth) / G.common.mass)
    (K1 := G.common.n) h hΛd hmass (Nat.cast_nonneg _)
    (fun i _ => (G.degree_bound Fr depth i : _)) ?_
  intro i hi
  have hc := (G.card_common i.1).1
  have hc' : (G.common.mass : ℝ) * i.1 - G.common.n ≤ ((G.geometry i.1).C.card : ℝ) := by
    exact_mod_cast hc
  have hAdm : (G.geometry i.1).C.card - i.2.card ≤ depth := hi.1
  have hdep : ((G.geometry i.1).C.card : ℝ) ≤ i.2.card + depth := by
    have : (G.geometry i.1).C.card ≤ i.2.card + depth := by omega
    exact_mod_cast this
  have hdeg : ((G.family Fr depth).deg i : ℝ) = i.2.card := rfl
  show (i.1 : ℝ) ≤ (G.common.mass : ℝ)⁻¹ * (((G.family Fr depth).deg i : ℕ) : ℝ) +
    ((G.common.n : ℝ) + depth) / G.common.mass
  rw [hdeg, inv_mul_eq_div, ← add_div, le_div_iff₀ hmass]
  nlinarith

/-- **Hybrid, content as hypothesis.**  Even-scale scaled content `Λ = contentConstant`
(from `Λ_deg = mass⁻² Λ`), window decay `D, c` on the whole family, and `HasNV0`. -/
theorem measure_of_content_even (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    {M : ℕ} [NeZero M] (tmpl : ZMod M → Template) {D c : ℝ}
    (hC : HasContent ((G.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0))
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl))
    (hD : HasScaledDecay (G.family Fr depth) G.scale D c)
    (hnv : HasNV0 (G.family Fr depth) G.scale)
    (hη : contentConstant M tmpl < D) (hc : 0 < c) :
    (G.family Fr depth).MeasureLB ((G.common.mass : ℝ) * c / (D - contentConstant M tmpl)) := by
  have hmass : (0 : ℝ) < G.common.mass := by exact_mod_cast G.common_pos
  have hΛd : 0 ≤ ((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl :=
    mul_nonneg (by positivity) (contentConstant_nonneg M tmpl)
  have hS := hasScaledContent_restricted G Fr depth (fun r => r % 2 = 0) hΛd hC
  have heq : (G.common.mass : ℝ) ^ 2 * (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl)
      = contentConstant M tmpl := by field_simp
  rw [heq] at hS
  exact measure_of_family_nv0_even
    ((G.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) G.scale
    (γ := G.common.mass) (K := G.common.n) hS
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) hη hc hmass (Nat.cast_nonneg _)
    (fun n _ => G.degree_bound Fr depth n)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := hnv
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : G.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)

variable {G : BlockGeom} {Fr : Frame} {depth e : ℕ} {M : ℕ} [NeZero M]

/-- **End-to-end hybrid (two-term layers).**  All remaining hypotheses are the covering data
of `hasContent_twoTerm_on` at even `r`, the window contract `hD` (e.g. from
`hasScaledDecay_of_check`), the selector data of `BlockGeom.hasNV0`, and `Λ < D`, `0 < c`. -/
theorem measure_of_twoTerm_even {D c : ℝ}
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ) (q o : ℕ) (kf jf : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (tail : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p = 0)
    (pre : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
            : ℝ) ≤ (tmpl c).α0 * r)
    (cov : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ Q ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊Q.s * r⌋₊ < p → p ≤ ⌊Q.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
            : ℝ) ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, r % 2 = 0 → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
        (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
          : ℝ) ≤ K * r)
    (hD : HasScaledDecay (G.family Fr depth) G.scale D c)
    (L : ℕ) (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hCd : ∀ i, (G.common.block i).d ∣ L)
    (hXd : ∀ i, (G.row.block i).d ∣ L)
    (hYd : ∀ i, (G.column.block i).d ∣ L)
    (hdepth : G.selectionDepth Fr L ≤ depth)
    (hη : contentConstant M tmpl < D) (hc : 0 < c) :
    (G.family Fr depth).MeasureLB ((G.common.mass : ℝ) * c / (D - contentConstant M tmpl)) :=
  measure_of_content_even G Fr depth tmpl
    (hasContent_twoTerm_on (P := fun r => r % 2 = 0) W hrat a b q o kf jf ext tmpl K hK
      tail pre cov exc)
    hD (G.hasNV0 Fr L depth hL hd hw hCd hXd hYd hdepth) hη hc

end CatalanCore.Uniform.BlockGeom
