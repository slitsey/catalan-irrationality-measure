module

public import CatalanCore.Uniform.Content.UFMoments.NodeBridge
public import CatalanCore.Uniform.Content.UFMoments.Transport

@[expose] public section

/-!
# UF moments: the second-order function on one joint type (steps (a)+(b) assembled)

A representative node `t₀` (border vector `σ₀`, `B₀ = res(1 - Σ g₀) ≠ 0`) and a direction `d`
killing its own-fiber moment (`hz`; e.g. `d = (ℓ_{t₀} - g₀·ℓ)/(1 - Σ g₀)`) are fixed.  A node `t`
of the same joint type comes with a chain equivalence `e` (own fiber of `t` ≃ own fiber of `t₀`)
under which core entries and border entries agree modulo `π²` and prefixes are shifted by
`κ = ℓ_t - ℓ_{t₀} = π κ₁`.  Then (`jtype_node`) there is `Φ` with

  `momB = momA (π u d + π² Φ)`,   `res Φ = res u · (res κ₁ - Σ_c m(c) (c - t̄)⁻¹)`,

with ONE fiber-moment function `m = fibMom (ℓ - d)` for the whole type.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

theorem dot_sub_const {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (g ℓ : ι → R) (d : R) :
    g ⬝ᵥ (fun a => ℓ a - d) = g ⬝ᵥ ℓ - d * ∑ j, g j := by
  simp only [dotProduct, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Cauchy form of the reduced cross sum. -/
theorem cross_cauchy (m : ZMod p → RatFunc (ZMod p)) (τ : ZMod p) :
    (∑ c' : ZMod p, if c' = τ then 0 else m c' / (rfH p c' - rfH p τ)) =
      ∑ c' : ZMod p, m c' * rfH p (c' - τ)⁻¹ := by
  refine Finset.sum_congr rfl fun c' _ => ?_
  by_cases h : c' = τ
  · simp [h]
  · rw [if_neg h, map_inv₀, map_sub, div_eq_mul_inv]

/-- **One node of a joint type.** -/
theorem jtype_node (D : PoleData Fr p N) (c : ι → ℕ) (hc : ∀ a, c a < N)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, a ≠ b → nL p Fr * (nd p (c b) - nd p (c a)) * Q a b =
      PF p Fr (c b) - PF p Fr (c a))
    (hdet : phiP p Q.det ≠ 0)
    (t0 : ℕ) (σ0 : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hz : (ellL p Fr t0 - d) -
      (sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a) - d) = 0)
    (hB0 : res p (1 - ∑ j, (sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) j) ≠ 0)
    (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (c a) - nd p t) * σ a = PF p Fr (c a) - PF p Fr t)
    (momA momB : (LocRing p)[X])
    (hA : algebraMap _ (GaussLoc p) momA = (Q.map (algebraMap _ (GaussLoc p))).det *
      (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)))
    (hB : algebraMap _ (GaussLoc p) momB = piL p * ((Q.map (algebraMap _ (GaussLoc p))).det *
      (algebraMap _ (GaussLoc p) (PF1 p Fr t) - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
          fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (c a))))))
    (e : {a // colOf (p := p) c a = ((t : ℕ) : ZMod p)} ≃
      {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)})
    (hDD : ∀ i j : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      algebraMap _ (GaussLoc p) (Q (e.symm i).1 (e.symm j).1) =
        algebraMap _ (GaussLoc p) (Q i.1 j.1) + piL p ^ 2 * x)
    (hss : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      algebraMap _ (GaussLoc p) (σ (e.symm i).1) =
        algebraMap _ (GaussLoc p) (σ0 i.1) + piL p ^ 2 * x)
    (hℓ : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      ellL p Fr (c (e.symm i).1) = ellL p Fr (c i.1) + (ellL p Fr t - ellL p Fr t0) +
        piL p ^ 2 * x)
    (κ₁ : GaussLoc p) (hκ : ellL p Fr t - ellL p Fr t0 = piL p * κ₁) :
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) momB = algebraMap _ (GaussLoc p) momA *
        (piL p * (algebraMap _ (GaussLoc p) (nL p Fr) * d) +
          piL p ^ 2 * Φ) ∧
      res p Φ = res p (algebraMap _ (GaussLoc p) (nL p Fr)) *
        (res p κ₁ - ∑ c' : ZMod p,
          fibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d) c' *
            rfH p (c' - ((t : ℕ) : ZMod p))⁻¹) := by
  have hDu := isUnit_Dmat_det D c hc Q hQ hdet
  have hb : ∀ a b, colOf (p := p) c a ≠ colOf c b → Dmat c Q a b = 0 := by
    intro a b h; simp [Dmat, h]
  have hs : ∀ a, colOf (p := p) c a ≠ ((t : ℕ) : ZMod p) → sOwn c t σ a = 0 := by
    intro a h; simp [sOwn, h]
  have hs0 : ∀ a, colOf (p := p) c a ≠ ((t0 : ℕ) : ZMod p) → sOwn c t0 σ0 a = 0 := by
    intro a h; simp [sOwn, h]
  have hDD' : ∀ i j : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      Dmat c Q (e.symm i).1 (e.symm j).1 = Dmat c Q i.1 j.1 + piL p ^ 2 * x := by
    intro i j
    obtain ⟨x, hx⟩ := hDD i j
    refine ⟨x, ?_⟩
    have h1 : colOf (p := p) c (e.symm i).1 = colOf c (e.symm j).1 :=
      ((e.symm i).2).trans ((e.symm j).2).symm
    have h2 : colOf (p := p) c i.1 = colOf c j.1 := i.2.trans j.2.symm
    simp only [Dmat, Matrix.of_apply, h1, h2, ↓reduceIte]
    exact hx
  have hss' : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      sOwn c t σ (e.symm i).1 = sOwn c t0 σ0 i.1 + piL p ^ 2 * x := by
    intro i
    obtain ⟨x, hx⟩ := hss i
    refine ⟨x, ?_⟩
    simp only [sOwn, (e.symm i).2, i.2, ↓reduceIte]
    exact hx
  obtain ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ := transport (piL p) (Dmat c Q) (colOf c) hDu hb _ _ e
    (sOwn c t σ) (sOwn c t0 σ0) (fun a => ellL p Fr (c a)) hs hs0 (ellL p Fr t0)
    (ellL p Fr t - ellL p Fr t0) d hDD' hss' hℓ
  set g0 := sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹
  set G₁ := κ₁ * (1 - ∑ j, g0 j) + piL p * x
  have hG : (ellL p Fr t - d) - (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a) - d) = piL p * G₁ := by
    have e1 : ellL p Fr t = ellL p Fr t0 + (ellL p Fr t - ellL p Fr t0) := by ring
    rw [e1, hx, hz, hκ]
    simp only [G₁]
    ring
  have hBt : res p (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j) = res p (1 - ∑ j, g0 j) := by
    rw [hx']
    simp only [map_sub, map_add, map_mul, map_pow, res_piL, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, add_zero]
  obtain ⟨Φ, h1, h2⟩ := node_bridge D c hc Q hQ hdet t ht σ hσ momA momB hA hB d G₁ hG
    (by rw [hBt]; exact hB0)
  refine ⟨Φ, h1, ?_⟩
  rw [h2, hBt, cross_cauchy]
  have hG1 : res p G₁ = res p κ₁ * res p (1 - ∑ j, g0 j) := by
    simp only [G₁, map_add, map_mul, res_piL, zero_mul, add_zero]
  rw [hG1, mul_div_assoc, div_self hB0, mul_one]

end CatalanCore.Uniform.Content.UFMoments
