module

public import CatalanCore.Uniform.Content.SmallPrimes.Output
public import CatalanCore.Uniform.Content.Shape.Alt

@[expose] public section

/-!
# Discharging the small-prime budget for hybrid geometries (lane H14)

`SmallBudget.sqrtLog L C` is a data-free budget.  For a hybrid frame the tropical price of the
whole matrix at `(r, p)` is `tropVal` of the entry valuations `W r p`; if `W` exceeds a leading
table `U` by at most `e0 (log_2 r + 1)` per entry, and only at primes with `p^2 <= L r` (higher
levels: `p^k` for `k >= 2` does not divide anything beyond), then
`tropVal W <= tropVal U + card * e0 (log_2 r + 1)` (`tropVal_le_add_card`).  The card of the index
set is at most `kap * r` (`altGeom_card_le`: `kap = 2 + c/2` for the alternating geometry), so the
excess is `<= X r p` for `X = SmallBudget.sqrtLog L C` as soon as `kap * e0 <= C`
(`trop_le_budget_card`).  The remaining `pre` data is only the *leading* table bound
`tropVal (U r p) <= alpha0 * r`, as in the old `Dhyb` route.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.Content.SmallPrimes


section Trop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A uniform entrywise excess `E` raises the tropical value by at most `card * E`. -/
theorem tropVal_le_add_card (W U : ι → ι → ℕ) (E : ℕ)
    (h : ∀ a b, W a b ≤ U a b + E) :
    tropVal W ≤ tropVal U + Fintype.card ι * E := by
  refine tropVal_le_of_forall (fun σ => ?_)
  calc ∑ b, W (σ b) b ≤ ∑ b, (U (σ b) b + E) := Finset.sum_le_sum (fun b _ => h _ _)
    _ = ∑ b, U (σ b) b + Fintype.card ι * E := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ tropVal U + Fintype.card ι * E := Nat.add_le_add_right (le_tropVal U σ) _

/-- **Budget discharge.**  Leading table `U` with `tropVal U ≤ al * r`, entrywise excess of at most
`e0 (log_2 r + 1)` at the primes with `p^2 ≤ L r`, index set of size `≤ kap * r`,
`kap * e0 ≤ C`: the whole tropical price is `≤ al * r + X r p` for `X = sqrtLog L C`. -/
theorem trop_le_budget_card {r p : ℕ} (Wt Ut : ι → ι → ℕ) (kap : ℝ)
    (hcard : (Fintype.card ι : ℝ) ≤ kap * r) (L C e0 : ℕ)
    (hC : kap * e0 ≤ C) {al : ℝ} (hU : (tropVal Ut : ℝ) ≤ al * r)
    (hexc : ∀ x y, Wt x y ≤ Ut x y + (if p * p ≤ L * r then e0 * (Nat.log 2 r + 1) else 0)) :
    (tropVal Wt : ℝ) ≤ al * r + (SmallBudget.sqrtLog L C).X r p := by
  have h := tropVal_le_add_card Wt Ut _ hexc
  have hX0 := (SmallBudget.sqrtLog L C).nonneg r p
  by_cases hp : p * p ≤ L * r
  · rw [SmallBudget.sqrtLog_X_of L C r p hp]
    simp only [if_pos hp] at h
    have hh : (tropVal Wt : ℝ) ≤ tropVal Ut + Fintype.card ι * (e0 * (Nat.log 2 r + 1)) := by
      exact_mod_cast h
    have hl1 : (0 : ℝ) < (Nat.log 2 r : ℝ) + 1 := by positivity
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have he0 : (0 : ℝ) ≤ e0 := Nat.cast_nonneg _
    calc (tropVal Wt : ℝ) ≤ tropVal Ut + Fintype.card ι * (e0 * ((Nat.log 2 r : ℝ) + 1)) := by
          exact_mod_cast hh
      _ ≤ al * r + (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
          have h1 : (Fintype.card ι : ℝ) * (e0 * ((Nat.log 2 r : ℝ) + 1)) ≤
              (kap * r) * (e0 * ((Nat.log 2 r : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
          have h2 : (kap * r) * (e0 * ((Nat.log 2 r : ℝ) + 1)) =
              (kap * e0) * (r * ((Nat.log 2 r : ℝ) + 1)) := by ring
          have h3 : (kap * e0) * (r * ((Nat.log 2 r : ℝ) + 1)) ≤
              (C : ℝ) * (r * ((Nat.log 2 r : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hC (by positivity)
          nlinarith
  · simp only [if_neg hp, mul_zero, add_zero] at h
    have : (tropVal Wt : ℝ) ≤ tropVal Ut := by exact_mod_cast h
    linarith

end Trop

section Alt

variable (c : ℚ) (hc : 0 < c)

/-- The index set of the alternating geometry at an even scale has at most `(2 + c/2) r` elements. -/
theorem altGeom_card_le {r : ℕ} (hr : r % 2 = 0) :
    (Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) : ℝ) ≤
      (2 + (c : ℝ) / 2) * r := by
  have hf : Function.Injective (fun i : ℕ => r + 2 * i) := fun a b h => by simp at h; omega
  have hk : ((altGeom c hc).geometry r).k = (altGeom c hc).borderSize r := by
    show ((altGeom c hc).geometry r).X'.card = _
    rw [altGeom_X c hc hr, Finset.card_image_of_injective _ hf, Finset.card_range]
  have h1 : Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) =
      r + (altGeom c hc).borderSize r := by
    rw [Fintype.card_sum, Fintype.card_coe, altGeom_C c hc r, Finset.card_range,
      Fintype.card_fin, hk]
  have hb : (altGeom c hc).borderSize r ≤ ⌈(c * r / 2)⌉₊ := by
    rw [altGeom_borderSize c hc hr]; exact min_le_left _ _
  have hcpos : (0 : ℚ) ≤ c * r / 2 := by
    have := hc.le
    positivity
  have hceil : ((⌈(c * r / 2)⌉₊ : ℕ) : ℝ) < (c : ℝ) * r / 2 + 1 := by
    have := Nat.ceil_lt_add_one hcpos
    exact_mod_cast this
  rw [h1]
  push_cast
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    have h00 : (altGeom c hc).borderSize 0 = 0 := by simpa using hb
    simp [h00]
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h0
    have hbR : ((altGeom c hc).borderSize r : ℝ) ≤ ((⌈(c * r / 2)⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast hb
    have hcR : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc.le
    nlinarith

end Alt

theorem tropGlobal_eff {G : BlockGeom} {Fr : Frame} {depth : ℕ}
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (r p : ℕ) : (tropGlobal (depth := depth) W hrat).eff r p = tropVal (W r p) := by
  simp [DebitLayer.eff, tropGlobal, DebitLayer.tropRat, DebitLayer.trop]

variable {G : BlockGeom} {Fr : Frame} {depth e : ℕ} {M : ℕ} [NeZero M]

theorem hasContent_multiTerm_hyb  (P : ℕ → Prop)
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k → (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (U : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k → (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ) (L C e0 : ℕ)
    (kap : ℝ) (hcard : ∀ r : ℕ, P r → (Fintype.card ((G.geometry r).C ⊕ Fin (G.geometry r).k) : ℝ) ≤ kap * r)
    (hC : kap * e0 ≤ C)
    (tail : ∀ r : ℕ, P r → ∀ cl : ZMod M, IsUnit cl → ∀ p : ℕ, p.Prime →
      (p : ZMod M) = cl → ⌊(tmpl cl).tend * r⌋₊ < p →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧ (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p = 0)
    (preU : ∀ r : ℕ, P r → ∀ cl : ZMod M, IsUnit cl → ∀ p : ℕ,
      p ≤ ⌊(tmpl cl).t1 * r⌋₊ → p.Prime → (p : ZMod M) = cl →
        (tropVal (U r p) : ℝ) ≤ (tmpl cl).α0 * r)
    (hexc : ∀ r : ℕ, P r → ∀ p : ℕ, p.Prime → ∀ x y,
      W r p x y ≤ U r p x y + (if p * p ≤ L * r then e0 * (Nat.log 2 r + 1) else 0))
    (cov : ∀ r : ℕ, P r → ∀ cl : ZMod M, IsUnit cl → ∀ Q ∈ (tmpl cl).l, ∀ p : ℕ,
      ⌊ Q.s * r⌋₊ < p → p ≤ ⌊ Q.t * r⌋₊ → p.Prime → (p : ZMod M) = cl →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ) ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, P r → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧ (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ) ≤ K * r) :
    HasContent ((G.family Fr depth).restrictAdm (fun i => P i.1))
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) :=
  hasContent_multiTerm_on' P W hrat a b ext tmpl K hK (SmallBudget.sqrtLog L C) tail
    (fun r hr cl hcl p h1 hp hpc => ⟨0, tropGlobal_valid W hrat r p, by
      show (((tropGlobal (depth := depth) W hrat).eff r p : ℕ) : ℝ) ≤ _
      rw [tropGlobal_eff]
      exact trop_le_budget_card (W r p) (U r p) _ (hcard r hr) L C e0 hC
        (preU r hr cl hcl p h1 hp hpc) (hexc r hr p hp)⟩) cov exc

theorem hasContent_twoTerm_hyb  (P : ℕ → Prop)
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k → (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ) (q o : ℕ) (kf jf : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (U : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k → (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ) (L C e0 : ℕ)
    (kap : ℝ) (hcard : ∀ r : ℕ, P r → (Fintype.card ((G.geometry r).C ⊕ Fin (G.geometry r).k) : ℝ) ≤ kap * r)
    (hC : kap * e0 ≤ C)
    (tail : ∀ r : ℕ, P r → ∀ cl : ZMod M, IsUnit cl → ∀ p : ℕ, p.Prime →
      (p : ZMod M) = cl → ⌊(tmpl cl).tend * r⌋₊ < p →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧ (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p = 0)
    (preU : ∀ r : ℕ, P r → ∀ cl : ZMod M, IsUnit cl → ∀ p : ℕ,
      p ≤ ⌊(tmpl cl).t1 * r⌋₊ → p.Prime → (p : ZMod M) = cl →
        (tropVal (U r p) : ℝ) ≤ (tmpl cl).α0 * r)
    (hexc : ∀ r : ℕ, P r → ∀ p : ℕ, p.Prime → ∀ x y,
      W r p x y ≤ U r p x y + (if p * p ≤ L * r then e0 * (Nat.log 2 r + 1) else 0))
    (cov : ∀ r : ℕ, P r → ∀ cl : ZMod M, IsUnit cl → ∀ Q ∈ (tmpl cl).l, ∀ p : ℕ,
      ⌊ Q.s * r⌋₊ < p → p ≤ ⌊ Q.t * r⌋₊ → p.Prime → (p : ZMod M) = cl →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ) : ℝ) ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, P r → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧ (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ) : ℝ) ≤ K * r) :
    HasContent ((G.family Fr depth).restrictAdm (fun i => P i.1))
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) :=
  hasContent_twoTerm_on' P W hrat a b q o kf jf ext tmpl K hK (SmallBudget.sqrtLog L C) tail
    (fun r hr cl hcl p h1 hp hpc => ⟨0, tropGlobal_valid W hrat r p, by
      show (((tropGlobal (depth := depth) W hrat).eff r p : ℕ) : ℝ) ≤ _
      rw [tropGlobal_eff]
      exact trop_le_budget_card (W r p) (U r p) _ (hcard r hr) L C e0 hC
        (preU r hr cl hcl p h1 hp hpc) (hexc r hr p hp)⟩) cov exc

end CatalanCore.Uniform.Content.SmallPrimes
