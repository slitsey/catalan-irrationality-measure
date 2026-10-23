module
public import CatalanCore.Arith.Hybrid.ShiftRow
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid
open ChainClasses

/-! # N1 reduced to a one-node formula

For a cell, fix a reference row and put `a = α(x₀)`, `b = pβ(x₀)` (exact polynomials).  For a node
`x` of the cell the leading parts agree (`α(x) ≡ a`, `pβ(x) ≡ b` modulo `p`), so
`Γ(x) = (a pβ(x) - b α(x)) / p` is integral, and the exact displacement identity
`g n (y - z) · pT_zy = α_z (pβ'_y) - (pβ_z) α'_y` becomes

  `g n (y - z) T_zy ≡ Γ(y) - Γ(z)   (mod p)`.

So `T` is determined by the single-node function `Γ`, and the weighted congruence N1 is equivalent to
the one-node formula `GammaFormula` (a Cauchy transform of the weight). -/

section Generic
variable {p : ℕ} [Fact p.Prime]

lemma gle0_Cp : GLE p 0 (C (p : ℚ)) := gle0_C_nat p

lemma Cp_ne_zero : (C (p : ℚ) : ℚ[X]) ≠ 0 := by
  rw [Ne, Polynomial.C_eq_zero]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma redI_Cp_mul {u : ℚ[X]} (hu : GLE p 0 u) : redI p (C (p : ℚ) * u) = 0 := by
  rw [redI_mul gle0_Cp hu, redI_C_nat, ZMod.natCast_self]
  simp [rfC]

/-- Integral polynomials with the same reduction differ by `p` times an integral polynomial. -/
lemma exists_div_of_redI_eq {f f' : ℚ[X]} (hf : GLE p 0 f) (hf' : GLE p 0 f')
    (h : redI p f = redI p f') : ∃ u : ℚ[X], GLE p 0 u ∧ f = f' + C (p : ℚ) * u := by
  obtain ⟨a, rfl⟩ := exists_lift0 p hf
  obtain ⟨b, rfl⟩ := exists_lift0 p hf'
  rw [redI_toQ, redI_toQ] at h
  have h0 : phiP p (a - b) = 0 := by rw [map_sub, h, sub_self]
  rw [phiP_eq_zero_iff] at h0
  obtain ⟨c, hc⟩ := h0
  have hCp : toQ p (C ((p : ℕ) : LocRing p)) = C (p : ℚ) := by simp [toQ]
  refine ⟨toQ p c, gle0_toQ p c, ?_⟩
  have : toQ p a = toQ p b + toQ p (C ((p : ℕ) : LocRing p) * c) := by
    rw [← map_add]; congr 1; rw [← hc]; ring
  rw [this, map_mul, hCp]

/-- `Γ(x) = (a · pβ(x) - b · α(x)) / p`. -/
noncomputable def gamF (p : ℕ) (a b α β : ℚ[X]) : ℚ[X] := C ((p : ℚ)⁻¹) * (a * β - b * α)

lemma gamF_eq {a b α β u v : ℚ[X]} (hα : α = a + C (p : ℚ) * u) (hβ : β = b + C (p : ℚ) * v) :
    gamF p a b α β = a * v - b * u := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hCC : (C ((p : ℚ)⁻¹) : ℚ[X]) * C (p : ℚ) = 1 := by rw [← map_mul]; simp [hp0]
  unfold gamF
  rw [hα, hβ]
  calc C ((p : ℚ)⁻¹) * (a * (b + C (p : ℚ) * v) - b * (a + C (p : ℚ) * u))
      = (C ((p : ℚ)⁻¹) * C (p : ℚ)) * (a * v - b * u) := by ring
    _ = a * v - b * u := by rw [hCC, one_mul]

/-- **The Wronskian reduction.**  If `g D (p T) = α₁ β₂ - β₁ α₂` and the four moments are
congruent to the constants `a, b` modulo `p`, then `g D T ≡ Γ₂ - Γ₁` in `𝔽_p(X)`. -/
theorem redI_wronskian {g D T a b α₁ β₁ α₂ β₂ : ℚ[X]}
    (hg : GLE p 0 g) (hD : GLE p 0 D) (hT : GLE p 0 T) (ha : GLE p 0 a) (hb : GLE p 0 b)
    (h₁ : GLE p 0 α₁) (h₂ : GLE p 0 β₁) (h₃ : GLE p 0 α₂) (h₄ : GLE p 0 β₂)
    (hid : g * D * (C (p : ℚ) * T) = α₁ * β₂ - β₁ * α₂)
    (c₁ : redI p α₁ = redI p a) (c₂ : redI p β₁ = redI p b)
    (c₃ : redI p α₂ = redI p a) (c₄ : redI p β₂ = redI p b) :
    redI p g * redI p D * redI p T = redI p (gamF p a b α₂ β₂) - redI p (gamF p a b α₁ β₁) := by
  obtain ⟨u₁, hu₁, e₁⟩ := exists_div_of_redI_eq h₁ ha c₁
  obtain ⟨v₁, hv₁, f₁⟩ := exists_div_of_redI_eq h₂ hb c₂
  obtain ⟨u₂, hu₂, e₂⟩ := exists_div_of_redI_eq h₃ ha c₃
  obtain ⟨v₂, hv₂, f₂⟩ := exists_div_of_redI_eq h₄ hb c₄
  rw [gamF_eq e₁ f₁, gamF_eq e₂ f₂]
  have key : g * D * T = (a * v₂ - b * u₂) - (a * v₁ - b * u₁) +
      C (p : ℚ) * (u₁ * v₂ - v₁ * u₂) := by
    apply mul_left_cancel₀ (Cp_ne_zero (p := p))
    calc C (p : ℚ) * (g * D * T) = g * D * (C (p : ℚ) * T) := by ring
      _ = α₁ * β₂ - β₁ * α₂ := hid
      _ = _ := by rw [e₁, e₂, f₁, f₂]; ring
  have hA : GLE p 0 ((a * v₂ - b * u₂) - (a * v₁ - b * u₁)) :=
    gle0_of_int1 (((int1_of_gle0 (gle0_mul ha hv₂)).sub (int1_of_gle0 (gle0_mul hb hu₂))).sub
      ((int1_of_gle0 (gle0_mul ha hv₁)).sub (int1_of_gle0 (gle0_mul hb hu₁))))
  have hB : GLE p 0 (u₁ * v₂ - v₁ * u₂) :=
    gle0_of_int1 ((int1_of_gle0 (gle0_mul hu₁ hv₂)).sub (int1_of_gle0 (gle0_mul hv₁ hu₂)))
  have hBp : GLE p 0 (C (p : ℚ) * (u₁ * v₂ - v₁ * u₂)) := gle0_mul gle0_Cp hB
  have := congrArg (redI p) key
  rw [redI_mul (gle0_mul hg hD) hT, redI_mul hg hD, redI_add hA hBp, redI_Cp_mul hB,
    redI_sub (gle0_mul ha hv₂ |> fun h => gle0_of_int1 ((int1_of_gle0 h).sub
      (int1_of_gle0 (gle0_mul hb hu₂)))) (gle0_of_int1 ((int1_of_gle0 (gle0_mul ha hv₁)).sub
      (int1_of_gle0 (gle0_mul hb hu₁))))] at this
  simpa using this

end Generic

section Model
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N) (hy : ∀ y, ys y<N)

omit hx hy in
include hL in
lemma gle0_D (z y : Z) : GLE p 0 (C Fr.norm * (C (ys y : ℚ) - C (xs z : ℚ))) := by
  have hCn : GLE p 0 (C Fr.norm) := by
    rw [hL.norm_eq]; simpa using gle0_C_nat (p := p) 16
  have hd : GLE p 0 (C (ys y : ℚ) - C (xs z : ℚ)) :=
    gle0_of_int1 ((int1_of_gle0 (gle0_C_nat (p := p) (ys y))).sub
      (int1_of_gle0 (gle0_C_nat (p := p) (xs z))))
  exact gle0_mul hCn hd

omit hx hy in
include hL in
lemma redI_D (z y : Z) : redI p (C Fr.norm * (C (ys y : ℚ) - C (xs z : ℚ))) =
    rfC p 16 * (rfC p (ys y : ZMod p) - rfC p (xs z : ZMod p)) := by
  have hn : redI p (C Fr.norm) = rfC p 16 := by
    have := redI_C_nat (p := p) 16
    rw [hL.norm_eq]
    simpa using this
  have hCn : GLE p 0 (C Fr.norm) := by
    rw [hL.norm_eq]; simpa using gle0_C_nat (p := p) 16
  have hd' : redI p (C (ys y : ℚ) - C (xs z : ℚ)) =
      rfC p (ys y : ZMod p) - rfC p (xs z : ZMod p) := by
    rw [redI_sub (gle0_C_nat _) (gle0_C_nat _), redI_C_nat, redI_C_nat]
  have hd : GLE p 0 (C (ys y : ℚ) - C (xs z : ℚ)) :=
    gle0_of_int1 ((int1_of_gle0 (gle0_C_nat (p := p) (ys y))).sub
      (int1_of_gle0 (gle0_C_nat (p := p) (xs z))))
  rw [redI_mul hCn hd, hn, hd']

include hL hp hN hr hk hx hy

/-- **`T` from the one-node function `Γ`.**  For a row `z`, a column `y` and a reference row `z₀`
with the same source moments (one cell), every lift `T'` of the scaled Schur entry satisfies
`det · 16 (y - z) · T̄ = Γ(y) - Γ(z)` in `𝔽_p(X)`, `Γ(x) = (a pβ(x) - b α(x))/p`,
`a = α(z₀)`, `b = pβ(z₀)`. -/
theorem zoneT_gamma (z₀ z y : Z) (hz₀ : r ≤ xs z₀) (hxz : r ≤ xs z) (hyy : r ≤ ys y)
    (hzA : sourceA Fr p o (fun j : ChainIndex p r (xs z) => (chainNode j).val) (xs z) =
        sourceA Fr p o (fun j : ChainIndex p r (xs z₀) => (chainNode j).val) (xs z₀))
    (hzB : sourceB Fr p o (fun j : ChainIndex p r (xs z) => (chainNode j).val) (xs z) =
        sourceB Fr p o (fun j : ChainIndex p r (xs z₀) => (chainNode j).val) (xs z₀))
    (hyA : sourceA Fr p o (fun j : ChainIndex p r (ys y) => (chainNode j).val) (ys y) =
        sourceA Fr p o (fun j : ChainIndex p r (xs z₀) => (chainNode j).val) (xs z₀))
    (hyB : sourceB Fr p o (fun j : ChainIndex p r (ys y) => (chainNode j).val) (ys y) =
        sourceB Fr p o (fun j : ChainIndex p r (xs z₀) => (chainNode j).val) (xs z₀))
    (T' : (LocRing p)[X])
    (hT' : toQ p T' = LemmaE.Tscaled (ChainModel.Q Fr p r xs ys).det
      (ChainModel.full Fr p r xs ys).toBlocks₁₁ (ChainModel.full Fr p r xs ys).toBlocks₁₂
      (ChainModel.full Fr p r xs ys).toBlocks₂₁ (ChainModel.full Fr p r xs ys).toBlocks₂₂
      (ChainModel.Nm Fr p r xs ys) z y) :
    redI p (ChainModel.Q Fr p r xs ys).det *
        (rfC p 16 * (rfC p (ys y : ZMod p) - rfC p (xs z : ZMod p))) * phiP p T' =
      redI p (gamF p (ChainModel.aR Fr p r xs ys z₀) (ChainModel.bR Fr p r xs ys z₀)
        (ChainModel.aC Fr p r xs ys y) (ChainModel.bC Fr p r xs ys y)) -
      redI p (gamF p (ChainModel.aR Fr p r xs ys z₀) (ChainModel.bR Fr p r xs ys z₀)
        (ChainModel.aR Fr p r xs ys z) (ChainModel.bR Fr p r xs ys z)) := by
  have W := redI_wronskian (p := p) (g := (ChainModel.Q Fr p r xs ys).det)
    (D := C Fr.norm * (C (ys y : ℚ) - C (xs z : ℚ))) (T := toQ p T')
    (a := ChainModel.aR Fr p r xs ys z₀) (b := ChainModel.bR Fr p r xs ys z₀)
    (α₁ := ChainModel.aR Fr p r xs ys z) (β₁ := ChainModel.bR Fr p r xs ys z)
    (α₂ := ChainModel.aC Fr p r xs ys y) (β₂ := ChainModel.bC Fr p r xs ys y)
    (ChainModel.gle0_det hL hp hN hr) (gle0_D hL z y) (gle0_toQ p T')
    (gle0_of_int1 (ChainModel.int1_aR hL hp hN hr hx hy z₀))
    (gle0_of_int1 (ChainModel.int1_bR hL hp hN hr hx hy z₀))
    (gle0_of_int1 (ChainModel.int1_aR hL hp hN hr hx hy z))
    (gle0_of_int1 (ChainModel.int1_bR hL hp hN hr hx hy z))
    (gle0_of_int1 (ChainModel.int1_aC hL hp hN hr hx hy y))
    (gle0_of_int1 (ChainModel.int1_bC hL hp hN hr hx hy y))
    (by rw [hT']; exact ChainModel.T_lead_identity (Fr := Fr) (p := p) (r := r) (xs := xs) (ys := ys) z y)
    (by rw [redI_aR hL hp hN hr hk hx hy z hxz, redI_aR hL hp hN hr hk hx hy z₀ hz₀, hzB])
    (by rw [redI_bR hL hp hN hr hk hx hy z hxz, redI_bR hL hp hN hr hk hx hy z₀ hz₀, hzA])
    (by rw [redI_aC hL hp hN hr hk hx hy y hyy, redI_aR hL hp hN hr hk hx hy z₀ hz₀, hyB])
    (by rw [redI_bC hL hp hN hr hk hx hy y hyy, redI_bR hL hp hN hr hk hx hy z₀ hz₀, hyA])
  rw [redI_D hL, redI_toQ] at W
  exact W

end Model

#print axioms zoneT_gamma
end CatalanCore.Arith.Hybrid
