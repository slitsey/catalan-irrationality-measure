module

public import CatalanCore.Uniform.Content.Smith.LP2Schur

@[expose] public section

/-!
# Theorem LP2 for a general two-term frame `ψ(z+1) - ψ(z+a/q)`

**Theorem `LP2Hyp.gle`.**  Let `Fr` be a two-term frame (`TwoTermData Fr q o`, any norm unit mod `p`),
`p ≥ 5` a prime with `r < p < r + m`, `k ≤ r` the first index with `p ∣ q k - o` (`q k = j p + o`),
`r + 2m ≤ p + k`, and `p² ∤ q t - o` for `1 ≤ t < r + 2m` (the corrected PoleData condition).  Then,
with `τ' = Σ u + Σ v` the value of the D4 potentials `uPot`,

  `GLE p (τ' - (m - (p - r))) (Fr.fullPoly r m)`,

i.e. the saving is `r + m - p`.  `LP2Hyp.gleAt` gives the underlying `HasRankWit`; for members
(deleted rows and columns) see `HasRankWit.gle_sub`, which applies to any index type.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix
  CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m k j : ℕ}

lemma Tsym_zone {nr v : ZMod p} {z w : ℕ} (hz : r ≤ z) (hkr : k ≤ r) (hw : w < k) :
    Tsym p k nr v z w =
      if z < p then nr⁻¹ * (((z : ZMod p) - w)⁻¹ * v)
      else if z - w = p then nr⁻¹ * (v + 1) else 0 := by
  unfold Tsym
  rw [if_neg (by omega), if_pos (by omega)]
  unfold Tg
  rw [if_neg (by omega), if_pos hw]

lemma zone_shape_g {nr v : ZMod p} (hkr : k ≤ r) {d : ℕ} (hd : d = p - r) (hd0 : 0 < d) {z : ℕ}
    (hz : r ≤ z) (w : Blk0 r k)
    (cz : Blk0 r k) (hcz : z < p ∨ (cz.1.val = z - p)) :
    rfC p (Tsym p k nr v z w.1.val) =
      if z < p then -(rfC p (nr⁻¹ * v)) *
          EL p r k d w ⟨(p - z - 1) % d, Nat.mod_lt _ hd0⟩
      else if w = cz then rfC p (nr⁻¹ * (v + 1)) else 0 := by
  have hwk : w.1.val < k := w.2
  rw [Tsym_zone hz hkr hwk]
  by_cases hlow : z < p
  · rw [if_pos hlow, if_pos hlow]
    have hmod : (p - z - 1) % d = p - z - 1 := Nat.mod_eq_of_lt (by omega)
    simp only [EL, Matrix.of_apply, hmod]
    have hcast : ((p - z - 1 + 1 : ℕ) : ZMod p) = -((z : ℕ) : ZMod p) := by
      have : p - z - 1 + 1 = p - z := by omega
      rw [this, Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    rw [hcast]
    have e1 : (((w.1 : ℕ) : ZMod p) + -((z : ℕ) : ZMod p)) =
        -(((z : ℕ) : ZMod p) - ((w.1 : ℕ) : ZMod p)) := by ring
    rw [e1, inv_neg]
    simp only [rfC_eq, map_mul, map_neg]
    ring
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

/-- **Theorem LP2, rank witness.**  The reduction `B̄` of `Full(X)` under the D4 potentials has
`rank B̄ ≤ p`, i.e. a saving of `r + m - p`. -/
theorem LP2Hyp.gleAt (H : LP2Hyp Fr p q o r m k j) (hpm : p < r + m) :
    HasRankWit Fr p r m (fun a => uPot p r k (Frame.hybRow r m a))
      (fun b => uPot p r k (Frame.hybCol r m b)) (m - (p - r)) := by
  have C := H.cfg
  have hrp := H.hrp
  have hp5 := H.p5
  have hk0 := C.sg.hk0
  have hkr := H.hkr
  have hNk := C.sg.hNk
  have hnr : red p Fr.norm ≠ 0 := C.hnm0
  have hv : vk p q j ≠ 0 := C.sg.vk_ne C.tt
  obtain ⟨d, hd⟩ : ∃ d, d = p - r := ⟨_, rfl⟩
  have hrd : r + d = p := by omega
  have hd0 : 0 < d := by omega
  have hdm : d ≤ m := by omega
  have hpi : piG p (red p Fr.norm) (vk p q j) ≠ 0 := by
    unfold piG; rw [rfC_eq]
    exact (map_ne_zero (rfCH p)).2 (mul_ne_zero (inv_ne_zero hnr) (pow_ne_zero 2 hv))
  have hs0 : s0g k (red p Fr.norm) ≠ 0 := by
    unfold s0g rfX rfC
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
  have hGx : ∀ (x : Fin m) (w : Blk0 r k), GxG p r m k (red p Fr.norm) (vk p q j) x w =
      if r + 2 * (x : ℕ) < p then -(rfC p ((red p Fr.norm)⁻¹ * vk p q j)) *
        EL p r k d w ⟨(p - (r + 2 * (x : ℕ)) - 1) % d, Nat.mod_lt _ hd0⟩
      else if w = cXf (r + 2 * (x : ℕ)) then
        rfC p ((red p Fr.norm)⁻¹ * (vk p q j + 1)) else 0 := by
    intro x w
    have hx := x.2
    simp only [GxG, Matrix.of_apply]
    have := zone_shape_g (nr := red p Fr.norm) (v := vk p q j) hkr hd hd0
      (z := r + 2 * (x : ℕ)) (by omega) w (cXf (r + 2 * (x : ℕ))) ?_
    · exact this
    · by_cases h : r + 2 * (x : ℕ) < p
      · exact Or.inl h
      · exact Or.inr (cXf_val _ (by omega) (by omega))
  have hGy : ∀ (w : Blk0 r k) (y : Fin m), GyG p r m k (red p Fr.norm) (vk p q j) w y =
      if r + 2 * (y : ℕ) + 1 < p then -(rfC p ((red p Fr.norm)⁻¹ * vk p q j)) *
        EL p r k d w ⟨(p - (r + 2 * (y : ℕ) + 1) - 1) % d, Nat.mod_lt _ hd0⟩
      else if w = cXf (r + 2 * (y : ℕ) + 1) then
        rfC p ((red p Fr.norm)⁻¹ * (vk p q j + 1)) else 0 := by
    intro w y
    have hy := y.2
    simp only [GyG, Matrix.of_apply]
    rw [Tsym_symm]
    have := zone_shape_g (nr := red p Fr.norm) (v := vk p q j) hkr hd hd0
      (z := r + 2 * (y : ℕ) + 1) (by omega) w (cXf (r + 2 * (y : ℕ) + 1)) ?_
    · exact this
    · by_cases h : r + 2 * (y : ℕ) + 1 < p
      · exact Or.inl h
      · exact Or.inr (cXf_val _ (by omega) (by omega))
  have key := gleAt_B (Fr := Fr) r m p (B0 := Blk0 r k) (B1 := Blk1 r k) (X := Fin m)
    (Y := Fin m) (D := Fin d) (by have := card_blk r k; omega) (Fintype.card_fin m)
    (Fintype.card_fin m) (by simpa using hdm) (eB r m k) (eB r m k)
    (fun a => uPot p r k (Frame.hybRow r m a)) (fun b => uPot p r k (Frame.hybCol r m b))
    (A0g p r k (red p Fr.norm) (vk p q j)) (Vg p r k (red p Fr.norm) (vk p q j))
    (piG p (red p Fr.norm) (vk p q j)) (s0g k (red p Fr.norm)) (κg (red p Fr.norm))
    (rfC p ((red p Fr.norm)⁻¹ * vk p q j))
    (rfC p ((red p Fr.norm)⁻¹ * (vk p q j + 1))) hpi hs0 (EL p r k d)
    (hS_g r k (red p Fr.norm) (vk p q j) hp5 hrd hkr hnr hv)
    (GxG p r m k (red p Fr.norm) (vk p q j)) (GyG p r m k (red p Fr.norm) (vk p q j))
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
    obtain ⟨g, h1, h2⟩ := H.hred a b
    exact ⟨g, h1, h2.trans (BTg_eq p r m k _ _ hkr a b).symm⟩

/-- **Theorem LP2.**  `p^{τ' - (r + m - p)} · det Full(X)` is `ℤ_(p)`-integral. -/
theorem LP2Hyp.gle (H : LP2Hyp Fr p q o r m k j) (hpm : p < r + m) :
    GLE p (∑ a, uPot p r k (Frame.hybRow r m a) + ∑ b, uPot p r k (Frame.hybCol r m b) -
      (m - (p - r))) (Fr.fullPoly r m) :=
  (H.gleAt hpm).gle

end CatalanCore.Uniform.Content.Smith
