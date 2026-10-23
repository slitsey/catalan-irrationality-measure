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

section Assembly
open ChainModel
variable {Fr : Frame} {p o r m : ℕ} [Fact p.Prime]

lemma noCut_of_interval {a b : ℕ}
    (hcut : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (min (x : ℤ) y) (max (x : ℤ) y))
    {x y : ℕ} (hx : a ≤ x ∧ x < b) (hy : a ≤ y ∧ y < b) (hxy : x ≤ y) :
    NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (x : ℤ) (y : ℤ) := by
  have := hcut x y hx.1 hx.2 hy.1 hy.2
  rwa [min_eq_left (by exact_mod_cast hxy), max_eq_right (by exact_mod_cast hxy)] at this

/-- Two nodes of one cut-free interval have the same source moments. -/
lemma sourceAB_cell (hL : LamData Fr o) {x x' : ℕ}
    (h1 : x ≤ x' → NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (x : ℤ) (x' : ℤ))
    (h2 : x' ≤ x → NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (x' : ℤ) (x : ℤ)) :
    sourceA Fr p o (fun j : ChainIndex p r x' => (chainNode j).val) x' =
        sourceA Fr p o (fun j : ChainIndex p r x => (chainNode j).val) x ∧
      sourceB Fr p o (fun j : ChainIndex p r x' => (chainNode j).val) x' =
        sourceB Fr p o (fun j : ChainIndex p r x => (chainNode j).val) x := by
  rcases le_total x x' with h | h
  · exact sourceAB_chainTransport hL h (h1 h)
  · have := sourceAB_chainTransport hL h (h2 h)
    exact ⟨this.1.symm, this.2.symm⟩

/-- `Γ` at a row node of the zone, with reference row `z₀`. -/
noncomputable def zoneGamR (Fr : Frame) (p r m : ℕ) [Fact p.Prime] (z₀ z : Fin m) : ℚ[X] :=
  gamF p (aR Fr p r (zoneX r m) (zoneY r m) z₀) (bR Fr p r (zoneX r m) (zoneY r m) z₀)
    (aR Fr p r (zoneX r m) (zoneY r m) z) (bR Fr p r (zoneX r m) (zoneY r m) z)

/-- `Γ` at a column node of the zone. -/
noncomputable def zoneGamC (Fr : Frame) (p r m : ℕ) [Fact p.Prime] (z₀ y : Fin m) : ℚ[X] :=
  gamF p (aR Fr p r (zoneX r m) (zoneY r m) z₀) (bR Fr p r (zoneX r m) (zoneY r m) z₀)
    (aC Fr p r (zoneX r m) (zoneY r m) y) (bC Fr p r (zoneX r m) (zoneY r m) y)

/-- **The one-node formula** (the real content of N1): for the cell `[a,b)` with reference row
`z₀`, the reduction of `Γ(x)` is, up to a constant, `det Q · 16` times the Cauchy transform of the
weight `w(c) = α (c̄_C - c̄(c)) + β 1_S(c)` at the node `x`. -/
def GammaFormula (Fr : Frame) (p o r m a b h : ℕ) [Fact p.Prime] (z₀ : Fin m) : Prop :=
  ∃ α β c0 : RatFunc (ZMod p),
    (∀ z ∈ cellRows r m a b, redI p (zoneGamR Fr p r m z₀ z) =
      c0 + redI p (Q Fr p r (zoneX r m) (zoneY r m)).det * rfC p 16 *
        ∑ c : ZMod p, zoneWeight Fr p o r h (r + 2 * z₀.val) α β c *
          rfC p ((c - ((zoneX r m z : ℕ) : ZMod p))⁻¹)) ∧
    (∀ y ∈ cellCols r m a b, redI p (zoneGamC Fr p r m z₀ y) =
      c0 + redI p (Q Fr p r (zoneX r m) (zoneY r m)).det * rfC p 16 *
        ∑ c : ZMod p, zoneWeight Fr p o r h (r + 2 * z₀.val) α β c *
          rfC p ((c - ((zoneY r m y : ℕ) : ZMod p))⁻¹))

/-- **N1 follows from the one-node formula.** -/
theorem weightedSameCell_of_gamma (hL : LamData Fr o) (hp : 5 ≤ p) (hm : 2 * m < p)
    (hN : 4 * (r + 2 * m) < p * p) {k : ℕ} (hk : (4 : ZMod p) * k = (o : ZMod p))
    {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p)) {a b : ℕ}
    (hcut : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (min (x : ℤ) y) (max (x : ℤ) y))
    (z0 : Fin m) (hz0 : a ≤ r + 2 * z0.val ∧ r + 2 * z0.val < b)
    (hlong : ∀ k, a ≤ k → k < b → r ≤ k → k < r + 2 * m → ((k : ℕ) : ZMod p) ∉ shortArc p h)
    (hG : GammaFormula Fr p o r m a b h z0) :
    WeightedSameCell Fr p o r m a b h (r + 2 * z0.val) := by
  classical
  obtain ⟨α, β, c0, hR, hC⟩ := hG
  refine ⟨α, β, ?_⟩
  intro z hz y hy
  have hzm := hz
  have hym := hy
  rw [mem_cellRows] at hz
  rw [mem_cellCols] at hy
  have hr0 : r ≤ r + 2 * m := by omega
  have hxz : r ≤ zoneX r m z := by simp only [zoneX]; omega
  have hyy : r ≤ zoneY r m y := by simp only [zoneY]; omega
  have hz0r : r ≤ zoneX r m z0 := by simp only [zoneX]; omega
  have hd : ((zoneY r m y : ℕ) : ZMod p) - ((zoneX r m z : ℕ) : ZMod p) ≠ 0 :=
    zone_dist_ne (r := r) hm z.isLt y.isLt
  have hint := zoneT_gle_one hL hp hm hN hk z y
  have hnc₁ : zoneX r m z ≤ zoneY r m y →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (zoneX r m z : ℤ) (zoneY r m y : ℤ) :=
    fun hle => noCut_of_interval hcut hz hy hle
  have hnc₂ : zoneY r m y ≤ zoneX r m z →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (zoneY r m y : ℤ) (zoneX r m z : ℤ) :=
    fun hle => noCut_of_interval hcut hy hz hle
  obtain ⟨T', hT'⟩ := T_integral_same_cell (Fr := Fr) (p := p) (r := r) (N := r + 2 * m) (o := o)
    (k := k) (xs := zoneX r m) (ys := zoneY r m) hL hp hN hr0 hk (fun z => zoneX_lt z)
    (fun y => zoneY_lt y) z y hxz hyy hnc₁ hnc₂ hd hint
  refine ⟨T', hT', ?_⟩
  -- source moments are constant on the cell
  have hZ := sourceAB_cell (Fr := Fr) (r := r) hL
    (x := zoneX r m z0) (x' := zoneX r m z)
    (fun hle => noCut_of_interval hcut hz0 hz hle) (fun hle => noCut_of_interval hcut hz hz0 hle)
  have hY := sourceAB_cell (Fr := Fr) (r := r) hL
    (x := zoneX r m z0) (x' := zoneY r m y)
    (fun hle => noCut_of_interval hcut hz0 hy hle) (fun hle => noCut_of_interval hcut hy hz0 hle)
  have G : redI p (Q Fr p r (zoneX r m) (zoneY r m)).det *
        (rfC p 16 * (rfC p ((zoneY r m y : ℕ) : ZMod p) - rfC p ((zoneX r m z : ℕ) : ZMod p))) *
        phiP p T' = redI p (zoneGamC Fr p r m z0 y) - redI p (zoneGamR Fr p r m z0 z) :=
    zoneT_gamma (Fr := Fr) (p := p) (r := r) (N := r + 2 * m) (o := o) (k := k)
      (xs := zoneX r m) (ys := zoneY r m) hL hp hN hr0 hk (fun z => zoneX_lt z)
      (fun y => zoneY_lt y) z0 z y hz0r hxz hyy hZ.1 hZ.2 hY.1 hY.2 T' hT'
  rw [hC y hym, hR z hzm] at G
  -- the finite-field Cauchy identity
  set zb : ZMod p := ((zoneX r m z : ℕ) : ZMod p) with hzb
  set yb : ZMod p := ((zoneY r m y : ℕ) : ZMod p) with hyb
  set w := zoneWeight Fr p o r h (r + 2 * z0.val) α β with hw
  have hwz : w zb = 0 :=
    zoneWeight_zero_of_cell hL hp hm hN hh hroot hcut z0 hz0 hlong α β hxz
      (by have := z.isLt; simp only [zoneX]; omega) hz.1 hz.2
  have hwy : w yb = 0 :=
    zoneWeight_zero_of_cell hL hp hm hN hh hroot hcut z0 hz0 hlong α β hyy
      (by have := y.isLt; simp only [zoneY]; omega) hy.1 hy.2
  have hsub : rfC p yb - rfC p zb = rfC p (yb - zb) := by
    simp only [← rfCHom_apply, map_sub]
  have hterm : ∀ c : ZMod p, w c * (rfC p ((c - yb)⁻¹) - rfC p ((c - zb)⁻¹)) =
      rfC p (yb - zb) * (rfC p ((c - zb)⁻¹) * w c * rfC p ((c - yb)⁻¹)) := by
    intro c
    by_cases hcz : c = zb
    · rw [hcz, hwz]; ring
    by_cases hcy : c = yb
    · rw [hcy, hwy]; ring
    have h1 : c - zb ≠ 0 := sub_ne_zero.2 hcz
    have h2 : c - yb ≠ 0 := sub_ne_zero.2 hcy
    have e : ((c - yb)⁻¹ - (c - zb)⁻¹ : ZMod p) = (yb - zb) * ((c - zb)⁻¹ * (c - yb)⁻¹) := by
      field_simp
      ring
    have e' := congrArg (rfCHom p) e
    simp only [rfCHom_apply, map_sub, map_mul] at e'
    calc w c * (rfC p ((c - yb)⁻¹) - rfC p ((c - zb)⁻¹))
        = w c * (rfC p (yb - zb) * (rfC p ((c - zb)⁻¹) * rfC p ((c - yb)⁻¹))) := by
          rw [e', hsub]
      _ = _ := by ring
  have hK : redI p (Q Fr p r (zoneX r m) (zoneY r m)).det * rfC p 16 ≠ 0 := by
    have h16 : (rfC p 16 : RatFunc (ZMod p)) ≠ 0 := by
      apply rfC_ne_zero'
      have h4 := four_ne_zmod p hp
      have : (16 : ZMod p) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero h4 h4
    exact mul_ne_zero (redI_det_ne_zero hL hp hN hr0 (xs := zoneX r m) (ys := zoneY r m)) h16
  have hdz : rfC p (yb - zb) ≠ 0 := rfC_ne_zero' hd
  rw [hsub] at G
  apply mul_left_cancel₀ (mul_ne_zero hK hdz)
  have hsum : ∑ c : ZMod p, w c * (rfC p ((c - yb)⁻¹) - rfC p ((c - zb)⁻¹)) =
      rfC p (yb - zb) * ∑ c : ZMod p, rfC p ((c - zb)⁻¹) * w c * rfC p ((c - yb)⁻¹) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => hterm c
  calc redI p (Q Fr p r (zoneX r m) (zoneY r m)).det * rfC p 16 * rfC p (yb - zb) * phiP p T'
      = redI p (Q Fr p r (zoneX r m) (zoneY r m)).det * (rfC p 16 * rfC p (yb - zb)) * phiP p T' := by
        ring
    _ = (c0 + redI p (Q Fr p r (zoneX r m) (zoneY r m)).det * rfC p 16 *
          ∑ c : ZMod p, w c * rfC p ((c - yb)⁻¹)) -
        (c0 + redI p (Q Fr p r (zoneX r m) (zoneY r m)).det * rfC p 16 *
          ∑ c : ZMod p, w c * rfC p ((c - zb)⁻¹)) := G
    _ = redI p (Q Fr p r (zoneX r m) (zoneY r m)).det * rfC p 16 *
          ∑ c : ZMod p, w c * (rfC p ((c - yb)⁻¹) - rfC p ((c - zb)⁻¹)) := by
        simp only [mul_sub, Finset.sum_sub_distrib]; ring
    _ = _ := by rw [hsum]; ring

end Assembly

#print axioms weightedSameCell_of_gamma
end CatalanCore.Arith.Hybrid
