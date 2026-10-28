module

public import CatalanCore.Uniform.Content.SmallPrimes.Cover
public import CatalanCore.Uniform.Content.Member.HasContent
public import CatalanCore.Uniform.Content.Shape.Even

@[expose] public section

/-!
# Debit layers with a small-prime budget (lane H14)

The assembler `ContentCoverB` lifted to the per-prime minimum of the debit layers, the BlockGeom
families and their restriction to a scale predicate `P`.  Each theorem is the namesake in
`Member` / `Shape` with the prefix hypothesis `eff ≤ alpha0 * r` replaced by
`eff ≤ alpha0 * r + B.X r p` for a `SmallBudget B`.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire

namespace CatalanCore.Uniform.Content.SmallPrimes

variable {Fam : PolyFamily} {sc : Fam.ι → ℕ} {M : ℕ} [NeZero M]

/-- **The cover from layers.**  Layers `w j i p` (`j ≤ k`) are valid per-prime prices of the
members; the price is their per-prime minimum, and the cover hypotheses ask only that at each
prime some layer lies under the class template. -/
noncomputable def ContentCoverB.ofLayers {k : ℕ} (tmpl : ZMod M → Template)
    (w : Fin (k + 1) → Fam.ι → ℕ → ℕ) (K : ℝ) (hK : 0 ≤ K) (B : SmallBudget)
    (gle : ∀ j i, Fam.Adm i → ∀ (p : ℕ) [Fact p.Prime], GLE p (w j i p) (Fam.Q i))
    (tail : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * sc i⌋₊ < p → ∃ j, w j i p = 0)
    (pre : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * sc i⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (w j i p : ℝ) ≤ (tmpl c).α0 * sc i + B.X (sc i) p)
    (cov : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ P ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊P.s * sc i⌋₊ < p → p ≤ ⌊P.t * sc i⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (w j i p : ℝ) ≤ P.α * sc i + P.β * p + P.C)
    (exc : ∀ i, Fam.Adm i → ∀ p : ℕ, p.Prime → p ∣ M → ∃ j, (w j i p : ℝ) ≤ K * sc i) :
    ContentCoverB Fam sc M where
  tmpl := tmpl
  price := fun i p => layerMin (fun j => w j i p)
  K := K
  hK := hK
  B := B
  gle := fun i hi p _ => gle_layerMin (fun j => gle j i hi p)
  tail := fun i hi c hc p hp hpc hlt => layerMin_eq_zero_of_exists (tail i hi c hc p hp hpc hlt)
  pre := fun i hi c hc p h1 hp hpc => layerMin_le_of_exists (pre i hi c hc p h1 hp hpc)
  cov := fun i hi c hc P hP p h1 h2 hp hpc =>
    layerMin_le_of_exists (cov i hi c hc P hP p h1 h2 hp hpc)
  exc := fun i hi p hp hpd => layerMin_le_of_exists (exc i hi p hp hpd)


/-- **`HasContent` for the BlockGeom common-deletion family.** -/
theorem hasContent_blockGeomB (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    (CC : ContentCoverB (G.family Fr depth) G.scale M) :
    HasContent (G.family Fr depth)
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M CC.tmpl) := by
  have hmass : (0 : ℝ) < G.common.mass := by exact_mod_cast G.common_pos
  refine ContentCoverB.hasContent_of_cover CC (fun i => NodeFamily.family_degree Fr G.geometry depth i)
    (γ := (G.common.mass : ℝ)⁻¹) (γ' := (G.common.mass : ℝ))
    (K0 := ((G.common.n : ℝ) + depth) / G.common.mass) (K1 := G.common.n)
    (inv_nonneg.2 hmass.le) hmass (by positivity) (Nat.cast_nonneg _) ?_ ?_
  · intro i hi
    have hc := (G.card_common i.1).1
    have hc' : (G.common.mass : ℝ) * i.1 - G.common.n ≤ ((G.geometry i.1).C.card : ℝ) := by
      exact_mod_cast hc
    have hAdm : (G.geometry i.1).C.card - i.2.card ≤ depth := hi
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


/-- **Main theorem (lane H5).**  `HasContent` for the BlockGeom common-deletion family from a
finite list of debit layers (layer `0` is global) and the class templates covering their
per-prime minimum. -/
theorem hasContent_of_debitLayersB (G : BlockGeom) (Fr : Frame) (depth : ℕ) {k : ℕ}
    (L : Fin (k + 1) → DebitLayer G Fr depth) (h0 : ∀ r p, (L 0).valid r p)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K) (B : SmallBudget)
    (tail : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p → ∃ j, (L j).valid r p ∧ (L j).eff r p = 0)
    (pre : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ (tmpl c).α0 * r + B.X r p)
    (cov : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ P ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊P.s * r⌋₊ < p → p ≤ ⌊P.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ P.α * r + P.β * p + P.C)
    (exc : ∀ r p : ℕ, p.Prime → p ∣ M →
      ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ K * r) :
    HasContent (G.family Fr depth)
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
  let CC : ContentCoverB (G.family Fr depth) G.scale M :=
    ContentCoverB.ofLayers (Fam := G.family Fr depth) (sc := G.scale) tmpl w K hK B
      (by
        intro j i hi p hp
        by_cases hv : (L j).valid i.1 p
        · simp only [w, if_pos hv]
          exact (L j).gle i hi p hv
        · simp only [w, if_neg hv]
          exact (L 0).gle i hi p (h0 _ _))
      (by
        intro i hi c hc p hp hpc hlt
        obtain ⟨j, hv, he⟩ := tail i.1 c hc p hp hpc hlt
        exact ⟨j, Nat.le_zero.1 (he ▸ hw_le j i hi p hv)⟩)
      (by
        intro i hi c hc p h1 hp hpc
        obtain ⟨j, hv, he⟩ := pre i.1 c hc p h1 hp hpc
        exact ⟨j, (hw_le_real j i hi p hv).trans he⟩)
      (by
        intro i hi c hc P hP p h1 h2 hp hpc
        obtain ⟨j, hv, he⟩ := cov i.1 c hc P hP p h1 h2 hp hpc
        exact ⟨j, (hw_le_real j i hi p hv).trans he⟩)
      (by
        intro i hi p hp hpd
        obtain ⟨j, hv, he⟩ := exc i.1 p hp hpd
        exact ⟨j, (hw_le_real j i hi p hv).trans he⟩)
  exact hasContent_blockGeomB G Fr depth CC


/-- `hasContent_blockGeom` for the family restricted to the scales satisfying `P`. -/
theorem hasContent_blockGeom_onB (G : BlockGeom) (Fr : Frame) (depth : ℕ) (P : ℕ → Prop)
    (CC : ContentCoverB ((G.family Fr depth).restrictAdm (fun i => P i.1)) G.scale M) :
    HasContent ((G.family Fr depth).restrictAdm (fun i => P i.1))
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M CC.tmpl) := by
  have hmass : (0 : ℝ) < G.common.mass := by exact_mod_cast G.common_pos
  refine ContentCoverB.hasContent_of_cover CC
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
theorem hasContent_of_debitLayers_onB (G : BlockGeom) (Fr : Frame) (depth : ℕ) (P : ℕ → Prop)
    {k : ℕ} (L : Fin (k + 1) → DebitLayer G Fr depth) (h0 : ∀ r p, P r → (L 0).valid r p)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K) (B : SmallBudget)
    (tail : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p → ∃ j, (L j).valid r p ∧ (L j).eff r p = 0)
    (pre : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ (tmpl c).α0 * r + B.X r p)
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
  let CC : ContentCoverB ((G.family Fr depth).restrictAdm (fun i => P i.1)) G.scale M :=
    ContentCoverB.ofLayers (Fam := (G.family Fr depth).restrictAdm (fun i => P i.1))
      (sc := G.scale) tmpl w K hK B
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
  exact hasContent_blockGeom_onB G Fr depth P CC


end CatalanCore.Uniform.Content.SmallPrimes
