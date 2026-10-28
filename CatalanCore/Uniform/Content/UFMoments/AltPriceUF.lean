module

public import CatalanCore.Uniform.Content.UFMoments.TopExt2

@[expose] public section

/-!
# The UF price of the alternating geometry: transport AND top-extension residues credited

`altSmithJKDatum_UF_priceTE`: with the transport window `[t₀, t_v]` and the top-extension window
`[t₀ - δ₂, t₀ - δ₁]` (core nodes `t₀ - δ < r` whose chains are `J`'s chain plus the image of `t₀`),

  `price ≤ 2(|C| + m) - (m + σ + (σ - s))`,   `s = p - (t_v + 1 - t₀) - (δ₂ + 1 - δ₁)`,

i.e. Theorem UF's `s_J = #(ℤ/p \ I_J)` with `I_J` = transport ∪ top extensions (before kills).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.Content.UFMoments

variable (c : ℚ) (hc : 0 < c) {r : ℕ}

theorem card_residues_sub {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (a b : ℕ) (hs : s ⊆ Finset.Icc a b)
    (h : b - a < p) : (s.image (fun t : ℕ => ((t : ℕ) : ZMod p))).card = s.card := by
  rw [Finset.card_image_of_injOn]
  intro x hx y hy hxy
  have hx' := Finset.mem_Icc.1 (hs hx)
  have hy' := Finset.mem_Icc.1 (hs hy)
  have := (ZMod.natCast_eq_natCast_iff' x y p).1 hxy
  rcases le_total x y with h1 | h1
  · have : (y - x) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq this.symm
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  · have : (x - y) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega

theorem altSmithJKDatum_UF_priceTE (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ} [Fact p.Prime]
    (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0)
    (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (hp : 2 * (altGeom c hc).borderSize r ≤ p) (hp2 : p ≠ 2)
    (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (t0 tmax : ℕ) (ht0N : t0 < N) (hrt : r ≤ t0) (htm : tmax < r + p)
    (hdiv : tmax / p = t0 / p)
    (hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tmax - t0))
    (tv : ℕ) (htv0 : t0 ≤ tv) (htv : tv < r + p) (htvN : tv < N) (htvd : tv / p = t0 / p)
    (hwv : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tv - t0))
    (δ₁ δ₂ : ℕ) (hδ12 : δ₁ ≤ δ₂) (hδ2 : δ₂ ≤ t0) (hlt : t0 - δ₁ < r) (hr3 : r ≤ t0 - δ₂ + p)
    (hqd : (t0 - δ₂) / p = t0 / p)
    (hwd : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) (t0 - δ₂) δ₂)
    (hspan : tv - (t0 - δ₂) < p) :
    (altSmithJKDatum_UF c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax ht0N hrt htm hdiv
        hw).price ≤
      2 * Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) -
        (Fintype.card (Fin ((altGeom c hc).geometry r).k) +
          (((winRows (r := r) c hc t0 tmax).card + (winCols (r := r) c hc t0 tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k)) +
            (((winRows (r := r) c hc t0 tmax).card + (winCols (r := r) c hc t0 tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k)) -
                (p - ((tv + 1 - t0) + (t0 - δ₁ + 1 - (t0 - δ₂))))))) := by
  classical
  have hC := altGeom_C c hc r
  have hS : ∀ t, t0 ≤ t → t ≤ tmax →
      ShiftData (twoTermPoleData T hNp.le hsq hnorm hnorm0)
        (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0 t := by
    intro t h1 h2
    obtain ⟨Δ, rfl⟩ : ∃ Δ, t = t0 + Δ := ⟨t - t0, by omega⟩
    exact alt_shiftData T hNp.le hsq hnorm hnorm0 _ hC t0 Δ hrt (by omega)
      (div_eq_of_between h1 h2 hdiv) (fun k hk1 hk2 => hw k hk1 (by omega))
  have hB0 := hB0_auto (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp _ _ _ (alt_hc' c hc hrN)
    (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 ht0N
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
  set Tn : Finset ℕ := Finset.Icc t0 tv ∪ Finset.Icc (t0 - δ₂) (t0 - δ₁)
  have hTn : Tn.card = (tv + 1 - t0) + (t0 - δ₁ + 1 - (t0 - δ₂)) := by
    rw [Finset.card_union_of_disjoint, Nat.card_Icc, Nat.card_Icc]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have := Finset.mem_Icc.1 hx1
    have := Finset.mem_Icc.1 hx2
    omega
  have hTsub : Tn ⊆ Finset.Icc (t0 - δ₂) tv := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · have := Finset.mem_Icc.1 h
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · have := Finset.mem_Icc.1 h
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hcount := card_retOf_le (vS7 p q o Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
      (sLift (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
        ((altGeom c hc).geometry r).ys (hint_of_poleData (twoTermPoleData T hNp.le hsq hnorm
          hnorm0) hNp (alt_hc' c hc hrN) (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN))).toBlocks₁₁
      t0) (Tn.image (fun t : ℕ => ((t : ℕ) : ZMod p))) (by
    intro c' hc'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc'
    rcases Finset.mem_union.1 ht with ht | ht
    · obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 ht
      obtain ⟨Δ, rfl⟩ : ∃ Δ, t = t0 + Δ := ⟨t - t0, by omega⟩
      exact vS7_zero T hNp.le hsq hnorm hnorm0 hNp hp2 ho hq _ _ _ (alt_hc' c hc hrN)
        (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 (t0 + Δ) (by omega)
        (alt_shiftData T hNp.le hsq hnorm hnorm0 _ hC t0 Δ hrt (by omega)
          (div_eq_of_between (by omega) ht2 htvd) (fun k hk1 hk2 => hwv k hk1 (by omega)))
    · obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 ht
      obtain ⟨δ, hδt, rfl⟩ : ∃ δ, δ ≤ t0 ∧ t = t0 - δ := ⟨t0 - t, by omega, by omega⟩
      have hδ1 : δ₁ ≤ δ := by omega
      have hδ2' : δ ≤ δ₂ := by omega
      refine vS7_topext T hNp.le hsq hnorm hnorm0 hNp ho hq _ hC _ _ (alt_hc' c hc hrN)
        (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 δ ht0N hrt (by omega) (by omega)
        (by omega) (by omega) ?_ ?_
      · exact le_antisymm (Nat.div_le_div_right (by omega)) (hqd ▸ Nat.div_le_div_right (by omega))
      · intro k hk1 hk2
        exact hwd k (by omega) (by omega))
  rw [card_residues_sub Tn (t0 - δ₂) tv hTsub hspan, hTn] at hcount
  have eR : (altSmithJKDatum_UF c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax ht0N hrt
      htm hdiv hw).J.Jr = winRows c hc t0 tmax := h1
  have eC : (altSmithJKDatum_UF c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax ht0N hrt
      htm hdiv hw).J.Jc = winCols c hc t0 tmax := h2
  have eS : (altSmithJKDatum_UF c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax ht0N hrt
      htm hdiv hw).J.sJ ≤ p - ((tv + 1 - t0) + (t0 - δ₁ + 1 - (t0 - δ₂))) := h3 ▸ hcount
  unfold SmithJKDatum.price
  rw [eR, eC]
  omega

end CatalanCore.Uniform.Content.UFMoments
