module

public import CatalanCore.Arith.Hybrid.DefBSchur

@[expose] public section

/-!
# Theorem B for a λ-like frame, at a prime `r < p < r + m`

`defAt_B_lam` : the additive deficit `m - (p - r) = r + m - p` at the prime `p`, relative to any
weights `(u, v)` that are tropically optimal for `hybW` (hypothesis `hopt`).  Everything else
(entries of `Full(X)` reduce to the block matrix `B̄`, the scalar Schur complement, the shape of the
zone rows, the rank count) is proved in `LamEntries`, `DefBLam`, `DefBSchur`, `DefB`, `DefBC5`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {r m j k : ℕ}

lemma Tfull_zone (S : BSetup p r m j k) {z w : ℕ} (hz : r ≤ z) (hw : w < k) :
    Tfull p j k z w = if z < p then (16 * ((z : ZMod p) - w))⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹))
      else if z - w = p then (16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1) else 0 := by
  have := S.hkr
  have hwz : w < z := by omega
  unfold Tfull TB
  rw [if_neg (by omega), if_pos hwz, if_neg (by omega), if_pos hw]

lemma card_blk (r k : ℕ) : Fintype.card (Blk0 r k) + Fintype.card (Blk1 r k) = r := by
  have := Fintype.card_congr (Equiv.sumCompl (fun c : Fin r => (c : ℕ) < k))
  rw [Fintype.card_sum, Fintype.card_fin] at this
  exact this

/-- The shape of a zone row/column `z ≥ r` against `w ∈ B0` (generic in the label `z`). -/
lemma zone_shape (S : BSetup p r m j k) {d : ℕ} (hd : d = p - r) (hd0 : 0 < d) {z : ℕ}
    (hz : r ≤ z) (hzN : z < r + 2 * m) (w : Blk0 r k)
    (cz : Blk0 r k) (hcz : z < p ∨ (cz.1.val = z - p)) :
    rfC p (Tfull p j k z w.1.val) =
      if z < p then -(rfC p (-(4 * ((j : ℕ) : ZMod p))⁻¹)) *
          EL p r k d w ⟨(p - z - 1) % d, Nat.mod_lt _ hd0⟩
      else if w = cz then rfC p ((16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1)) else 0 := by
  have hp5 := S.p5
  have h4 := four_ne_zmod p hp5
  rw [Tfull_zone S hz w.2]
  by_cases hlow : z < p
  · rw [if_pos hlow, if_pos hlow]
    have hmod : (p - z - 1) % d = p - z - 1 := Nat.mod_eq_of_lt (by omega)
    simp only [EL, Matrix.of_apply, hmod]
    have hcast : ((p - z - 1 + 1 : ℕ) : ZMod p) = -((z : ℕ) : ZMod p) := by
      have : p - z - 1 + 1 = p - z := by omega
      rw [this, Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    rw [hcast]
    have : -(rfC p (-(4 * ((j : ℕ) : ZMod p))⁻¹)) *
        rfC p ((((w.1 : ℕ) : ZMod p) + -((z : ℕ) : ZMod p))⁻¹) =
        rfC p ((4 * ((j : ℕ) : ZMod p))⁻¹ * (((w.1 : ℕ) : ZMod p) + -((z : ℕ) : ZMod p))⁻¹) := by
      simp only [rfC_eq, map_mul, map_neg]; ring
    rw [this]
    congr 1
    have h16 : (16 : ZMod p) ≠ 0 := by
      have : (16 : ZMod p) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero h4 h4
    have : ((w.1 : ℕ) : ZMod p) + -((z : ℕ) : ZMod p) = -(((z : ℕ) : ZMod p) - ((w.1 : ℕ) : ZMod p)) := by
      ring
    rw [this, inv_neg, mul_inv, mul_inv]
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]
    field_simp
  · rw [if_neg hlow, if_neg hlow]
    have hczv : cz.1.val = z - p := hcz.resolve_left hlow
    by_cases hw : w = cz
    · have : z - (w.1 : ℕ) = p := by
        have := congrArg (fun t : Blk0 r k => t.1.val) hw
        have hw2 := w.2
        omega
      rw [if_pos this, if_pos hw]
    · have : ¬ z - (w.1 : ℕ) = p := by
        intro h
        apply hw
        apply Subtype.ext; apply Fin.ext
        omega
      rw [if_neg this, if_neg hw, rfC_zero]

/-- **Theorem B at a prime** `r < p < r + m` (λ-like frame): deficit `m - (p - r) = r + m - p`,
relative to tropically optimal weights `uPot` (hypothesis `hopt`). -/
theorem defAt_B_lam {Fr : Frame} (I : HybInst Fr) (hL : LamData Fr)
    (S : BSetup p r m j k) (hpm : p < r + m)
    (hopt : ∑ a, uPot p r k (Frame.hybRow r m a) + ∑ b, uPot p r k (Frame.hybCol r m b) ≤
      tropExp I r m p)
    (hk' : m - (p - r) ≤ ∑ a, uPot p r k (Frame.hybRow r m a) +
      ∑ b, uPot p r k (Frame.hybCol r m b)) :
    m - (p - r) ≤ tropExp I r m p ∧
      GLE p (tropExp I r m p - (m - (p - r))) (Fr.fullPoly r m) := by
  classical
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
  have key := defAt_B I r m p (B0 := Blk0 r k) (B1 := Blk1 r k) (X := Fin m) (Y := Fin m)
    (D := Fin d) (by have := card_blk r k; omega) (Fintype.card_fin m) (Fintype.card_fin m)
    (by simpa using hdm) (eB r m k) (eB r m k)
    (fun a => uPot p r k (Frame.hybRow r m a)) (fun b => uPot p r k (Frame.hybCol r m b))
    hopt (by rw [Fintype.card_fin, hd]; exact hk') (A0L p r j k) (VL p r j k) (piL p j) (s0L p k) (κL p)
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

end CatalanCore.Arith.Hybrid
