module

public import CatalanCore.Arith.Hybrid.DefBFinal
public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# Bordered Theorem B (MEM2C): `defHypTop_B`

Copies of the final assembly lines of `gleAt_B`, `gleAt_B_lam`, `defHypT_B` with
`gle_full_of_rank` replaced by `gle_fullTop_of_rank'` (conclusions for `afterTop r m`, extra cost
`topC`).  All internal lemmas are reused from `DefBC5`, `DefBFinal`.
-/

open Finset Polynomial CatalanCore CatalanCore.Rect CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {Fr : Frame} (I : HybInst Fr) (r m : ℕ) (p : ℕ) [Fact p.Prime]

/-- Bordered twin of `gleAt_B`. -/
theorem gleAt_Btop {B0 B1 X Y D : Type} [Fintype B0] [Fintype B1] [Fintype X] [Fintype Y]
    [Fintype D] [DecidableEq B0] [DecidableEq B1] [DecidableEq X] [DecidableEq Y]
    [DecidableEq D]
    (hB0 : Fintype.card B1 + Fintype.card B0 = r) (_hX : Fintype.card X = m)
    (hY : Fintype.card Y = m) (hdm : Fintype.card D ≤ m)
    (e : Fin r ⊕ Fin m ≃ (B0 ⊕ X) ⊕ B1) (e' : Fin r ⊕ Fin m ≃ (B0 ⊕ Y) ⊕ B1)
    (u v : Fin r ⊕ Fin m → ℕ)
    (A0 : Matrix B0 B0 (RatFunc (ZMod p))) (V : Matrix B0 B1 (RatFunc (ZMod p)))
    (π s0 κ lam σ : RatFunc (ZMod p)) (hπ : π ≠ 0) (hs0 : s0 ≠ 0) (E : Matrix B0 D (RatFunc (ZMod p)))
    (hS : A0 - π⁻¹ • (V * Vᵀ) = s0 • (1 : Matrix B0 B0 _) - κ • (E * Eᵀ))
    (Gx : Matrix X B0 (RatFunc (ZMod p))) (Gy : Matrix B0 Y (RatFunc (ZMod p)))
    (lowX : X → Prop) (lowY : Y → Prop) [DecidablePred lowX] [DecidablePred lowY]
    (iX : X → D) (iY : Y → D) (cX : X → B0) (cY : Y → B0)
    (hGx : ∀ x w, Gx x w = if lowX x then -lam * E w (iX x) else (if w = cX x then σ else 0))
    (hGy : ∀ w y, Gy w y = if lowY y then -lam * E w (iY y) else (if w = cY y then σ else 0))
    (hdisj : ∀ x y, lowX x → lowY y → iX x ≠ iY y)
    (hc : ∀ x y, ¬ lowX x → ¬ lowY y → cX x ≠ cY y)
    (hred : ∀ a b, ∃ g : (LocRing p)[X],
      toQ p g = C ((p : ℚ) ^ (u a + v b)) * fullEntry Fr r m a b ∧
        phiP p g = BbarB A0 V π Gx Gy (e a) (e' b)) :
    GLE p (∑ a, u a + ∑ b, v b - (m - Fintype.card D) + topC I r m p)
      ((afterTop r m).fullPolyG Fr) := by
  have hrank := rank_BbarB_le A0 V π s0 κ lam σ hπ hs0 E hS Gx Gy lowX lowY iX iY cX cY hGx hGy
    hdisj hc
  refine gle_fullTop_of_rank' I r m p u v ((BbarB A0 V π Gx Gy).submatrix e e') hred
    (m - Fintype.card D) ?_
  rw [Matrix.rank_submatrix _ e e']
  omega

end

section

variable {p : ℕ} [Fact p.Prime] {r m j k : ℕ}

/-- **Bordered Theorem B at a prime** (member 2, `afterTop`; cost `topC`): with `τ' = ∑u + ∑v` the
value of the D4 potentials, `p^{τ' - (r + m - p)} · det Full(X)` is `ℤ_(p)`-integral.  No
primal optimality is needed. -/
theorem gleAt_Btop_lam {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr)
    (S : BSetup p r m j k) (hpm : p < r + m) :
    GLE p (∑ a, uPot p r k (Frame.hybRow r m a) + ∑ b, uPot p r k (Frame.hybCol r m b) -
      (m - (p - r)) + topC I r m p) ((afterTop r m).fullPolyG Fr) := by
  have hrp := S.hrp
  have hp5 := S.p5
  have hk0 := S.hk0
  have hkr := S.hkr
  have h2mk := S.h2mk
  obtain ⟨d, hd⟩ : ∃ d, d = p - r := ⟨_, rfl⟩
  have hrd : r + d = p := by omega
  have hd0 : 0 < d := by omega
  have hdm : d ≤ m := by omega
  have hk4 : (4 : ZMod p) * (k : ZMod p) = 1 := by
    have : ((4 * k : ℕ) : ZMod p) = ((j * p + 1 : ℕ) : ZMod p) := by rw [S.hk]
    push_cast at this
    simpa [ZMod.natCast_self] using this
  have hjz : ((j : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt S.hj0 S.hjp
  have hpi : piL p j ≠ 0 := by
    unfold piL; rw [rfC_eq]
    exact (map_ne_zero (rfCH p)).2 (pow_ne_zero 2 (inv_ne_zero hjz))
  have hs0 : s0L p k ≠ 0 := by
    unfold s0L rfX rfC
    rw [← map_add]
    exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))).2
      (Polynomial.X_add_C_ne_zero _)
  let z0 : Blk0 r k := ⟨⟨0, by omega⟩, hk0⟩
  let cXf : ℕ → Blk0 r k := fun z =>
    if h : z - p < k then ⟨⟨z - p, by omega⟩, h⟩ else z0
  have cXf_val : ∀ z, p ≤ z → z < r + 2 * m → (cXf z).1.val = z - p := by
    intro z hz1 hz2
    have h : z - p < k := by omega
    simp only [cXf, dif_pos h]
  have hGx : ∀ (x : Fin m) (w : Blk0 r k), GxL p r m j k x w =
      if r + 2 * (x : ℕ) < p then -(rfC p (-(4 * ((j : ℕ) : ZMod p))⁻¹)) *
        EL p r k d w ⟨(p - (r + 2 * (x : ℕ)) - 1) % d, Nat.mod_lt _ hd0⟩
      else if w = cXf (r + 2 * (x : ℕ)) then
        rfC p ((16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1)) else 0 := by
    intro x w
    have hx := x.2
    simp only [GxL, Matrix.of_apply]
    refine zone_shape S hd hd0 (by omega) (by omega) w (cXf (r + 2 * (x : ℕ))) ?_
    by_cases h : r + 2 * (x : ℕ) < p
    · exact Or.inl h
    · exact Or.inr (cXf_val _ (by omega) (by omega))
  have hGy : ∀ (w : Blk0 r k) (y : Fin m), GyL p r m j k w y =
      if r + 2 * (y : ℕ) + 1 < p then -(rfC p (-(4 * ((j : ℕ) : ZMod p))⁻¹)) *
        EL p r k d w ⟨(p - (r + 2 * (y : ℕ) + 1) - 1) % d, Nat.mod_lt _ hd0⟩
      else if w = cXf (r + 2 * (y : ℕ) + 1) then
        rfC p ((16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1)) else 0 := by
    intro w y
    have hy := y.2
    simp only [GyL, Matrix.of_apply]
    rw [Tfull_symm]
    refine zone_shape S hd hd0 (by omega) (by omega) w (cXf (r + 2 * (y : ℕ) + 1)) ?_
    by_cases h : r + 2 * (y : ℕ) + 1 < p
    · exact Or.inl h
    · exact Or.inr (cXf_val _ (by omega) (by omega))
  have key := gleAt_Btop (Fr := Fr) I r m p (B0 := Blk0 r k) (B1 := Blk1 r k) (X := Fin m) (Y := Fin m)
    (D := Fin d) (by have := card_blk r k; omega) (Fintype.card_fin m) (Fintype.card_fin m)
    (by simpa using hdm) (eB r m k) (eB r m k)
    (fun a => uPot p r k (Frame.hybRow r m a)) (fun b => uPot p r k (Frame.hybCol r m b))
    (A0L p r j k) (VL p r j k) (piL p j) (s0L p k) (κL p)
    (rfC p (-(4 * ((j : ℕ) : ZMod p))⁻¹))
    (rfC p ((16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1))) hpi hs0 (EL p r k d)
    (hS_L p r j k hp5 hk4 hjz hrd hkr) (GxL p r m j k) (GyL p r m j k)
    (fun x : Fin m => r + 2 * (x : ℕ) < p) (fun y : Fin m => r + 2 * (y : ℕ) + 1 < p)
    (fun x : Fin m => ⟨(p - (r + 2 * (x : ℕ)) - 1) % d, Nat.mod_lt _ hd0⟩)
    (fun y : Fin m => ⟨(p - (r + 2 * (y : ℕ) + 1) - 1) % d, Nat.mod_lt _ hd0⟩)
    (fun x : Fin m => cXf (r + 2 * (x : ℕ))) (fun y : Fin m => cXf (r + 2 * (y : ℕ) + 1))
    hGx hGy ?_ ?_ ?_
  · simpa [hd] using key
  · intro x y hx hy
    have hx' := x.2
    have hy' := y.2
    intro h
    have h2 := congrArg Fin.val h
    simp only at h2
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
    omega
  · intro x y hx hy
    have hx' := x.2
    have hy' := y.2
    intro h
    have h1 := cXf_val (r + 2 * (x : ℕ)) (by omega) (by omega)
    have h2 := cXf_val (r + 2 * (y : ℕ) + 1) (by omega) (by omega)
    have h3 := congrArg (fun t : Blk0 r k => t.1.val) h
    omega
  · intro a b
    obtain ⟨g, h1, h2⟩ := hred_B hL S a b
    exact ⟨g, h1, h2.trans (BT_eq p r m j k hkr a b).symm⟩

end

open Classical in
/-- **Bordered Theorem B as a `DefHypTop` family** (twin of `defHypT_B`, same hypotheses). -/
theorem defHypTop_B {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr) (r m : ℕ) (T : ℕ → ℕ)
    (W : ℕ → Prop) (hW : ∀ p, W p → p < r + m)
    (hSet : ∀ p : ℕ, p.Prime → W p → ∃ j k, BSetup p r m j k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → ∀ j k, BSetup p r m j k →
      ∑ a, uPot p r k (Frame.hybRow r m a) + ∑ b, uPot p r k (Frame.hybCol r m b) ≤ T p) :
    DefHypTop I r m T (fun p => if W p then m - (p - r) else 0) := by
  refine defHypTop_of_local T _ hT W (fun p hp => by simp [hp]) ?_
  intro p hp hb hWp
  obtain ⟨j, k, S⟩ := hSet p hp hWp
  haveI : Fact p.Prime := ⟨hp⟩
  have hd := hTd p hp hWp j k S
  have h1 := uPot_sum_ge (p := p) (r := r) (m := m) (k := k) S.hrp
  have hg := gleAt_Btop_lam I hL S (hW p hWp)
  simp only [if_pos hWp]
  exact fun [Fact p.Prime] => hg.mono (show _ ≤ T p - (m - (p - r)) + topC I r m p by omega)

end CatalanCore.Arith.Hybrid
