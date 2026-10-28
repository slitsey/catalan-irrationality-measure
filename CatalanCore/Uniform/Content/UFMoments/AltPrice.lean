module

public import CatalanCore.Uniform.Content.UFMoments.S7Count

@[expose] public section

/-!
# The price of the `S7` Smith datum of the alternating geometry (transport count)

`altSmithJKDatum_S7_price`: with `σ = |Jr| + |Jc| - m` (`Jr`, `Jc` the border rows/columns in the
window `[t₀, t_max]`) and any transport window `[t₀, t_v]` (`t_v - t₀ < p`, same arc and chain
length, `t_v < r + p`, `t_v < N`; virtual nodes allowed), the retained count is at most
`p - (t_v - t₀ + 1)`, so

  `price ≤ 2(|C| + m) - (m + σ + (σ - (p - (t_v - t₀ + 1))))`.

This is the transport part of Theorem UF's `s_J` (top extensions not yet credited).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.Content.UFMoments

variable (c : ℚ) (hc : 0 < c) {r : ℕ}

theorem card_window_residues {p : ℕ} [Fact p.Prime] (t0 tv : ℕ) (h : tv - t0 < p) :
    ((Finset.Icc t0 tv).image (fun t : ℕ => ((t : ℕ) : ZMod p))).card = tv + 1 - t0 := by
  rw [Finset.card_image_of_injOn, Nat.card_Icc]
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  have := (ZMod.natCast_eq_natCast_iff' a b p).1 hab
  rcases le_total a b with h1 | h1
  · have h2 : b - a < p := by omega
    have : (b - a) % p = 0 := by
      have := Nat.sub_mod_eq_zero_of_mod_eq this.symm; exact this
    have : b - a = 0 := by
      rw [Nat.mod_eq_of_lt h2] at this; exact this
    omega
  · have h2 : a - b < p := by omega
    have : (a - b) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq this
    have : a - b = 0 := by rw [Nat.mod_eq_of_lt h2] at this; exact this
    omega

theorem altSmithJKDatum_S7_price (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ} [Fact p.Prime]
    (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0)
    (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (hp : 2 * (altGeom c hc).borderSize r ≤ p) (hp2 : p ≠ 2)
    (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (t0 tmax : ℕ) (hrt : r ≤ t0) (htm : tmax < r + p) (hdiv : tmax / p = t0 / p)
    (hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tmax - t0)) (hB0)
    (tv : ℕ) (htv0 : t0 ≤ tv) (htv : tv < r + p) (htvN : tv < N) (htvd : tv / p = t0 / p)
    (htvp : tv - t0 < p)
    (hwv : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tv - t0)) :
    (altSmithJKDatum_S7 c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax hrt htm hdiv hw
        hB0).price ≤
      2 * Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) -
        (Fintype.card (Fin ((altGeom c hc).geometry r).k) +
          (((winRows (r := r) c hc t0 tmax).card + (winCols (r := r) c hc t0 tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k)) +
            (((winRows (r := r) c hc t0 tmax).card + (winCols (r := r) c hc t0 tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k)) - (p - (tv + 1 - t0))))) := by
  classical
  have hC := altGeom_C c hc r
  have hS : ∀ t, t0 ≤ t → t ≤ tmax →
      ShiftData (twoTermPoleData T hNp.le hsq hnorm hnorm0)
        (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0 t := by
    intro t h1 h2
    obtain ⟨Δ, rfl⟩ : ∃ Δ, t = t0 + Δ := ⟨t - t0, by omega⟩
    exact alt_shiftData T hNp.le hsq hnorm hnorm0 _ hC t0 Δ hrt (by omega)
      (div_eq_of_between h1 h2 hdiv) (fun k hk1 hk2 => hw k hk1 (by omega))
  obtain ⟨h1, h2, h3⟩ := s7_twoTerm_fields T hNp.le hsq hnorm hnorm0 hNp hp2 ho hq
    (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
    ((altGeom c hc).geometry r).ys (alt_hc' c hc hrN) (alt_hx' c hc hr hrN)
    (alt_hy' c hc hr hrN) (alt_hdist c hc hr hp) t0 hB0 (winRows (r := r) c hc t0 tmax)
    (winCols (r := r) c hc t0 tmax)
    (fun z hz => by
        simp only [winRows, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        exact hS _ hz.1 hz.2)
    (fun y hy => by
        simp only [winCols, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hS _ hy.1 hy.2)
  have hcount := card_retOf_le (vS7 p q o Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
      (sLift (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
        ((altGeom c hc).geometry r).ys (hint_of_poleData (twoTermPoleData T hNp.le hsq hnorm
          hnorm0) hNp (alt_hc' c hc hrN) (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN))).toBlocks₁₁
      t0) ((Finset.Icc t0 tv).image (fun t : ℕ => ((t : ℕ) : ZMod p))) (by
    intro c' hc'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc'
    obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 ht
    obtain ⟨Δ, rfl⟩ : ∃ Δ, t = t0 + Δ := ⟨t - t0, by omega⟩
    exact vS7_zero T hNp.le hsq hnorm hnorm0 hNp hp2 ho hq _ _ _ (alt_hc' c hc hrN)
      (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 (t0 + Δ) (by omega)
      (alt_shiftData T hNp.le hsq hnorm hnorm0 _ hC t0 Δ hrt (by omega)
        (div_eq_of_between (by omega) ht2 htvd) (fun k hk1 hk2 => hwv k hk1 (by omega))))
  rw [card_window_residues t0 tv htvp] at hcount
  have eR : (altSmithJKDatum_S7 c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax hrt htm
      hdiv hw hB0).J.Jr = winRows (r := r) c hc t0 tmax := h1
  have eC : (altSmithJKDatum_S7 c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax hrt htm
      hdiv hw hB0).J.Jc = winCols (r := r) c hc t0 tmax := h2
  have eS : (altSmithJKDatum_S7 c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax hrt htm
      hdiv hw hB0).J.sJ ≤ p - (tv + 1 - t0) := h3 ▸ hcount
  unfold SmithJKDatum.price
  rw [eR, eC]
  omega

end CatalanCore.Uniform.Content.UFMoments
