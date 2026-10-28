module

public import CatalanCore.Uniform.Content.UFMoments.AltShift

@[expose] public section

/-!
# The non-empty `SmithJKDatum` of the alternating geometry from (S7-Lean)

`altSmithJKDatum_S7`: for a two-term frame at even `r`, a window `[t₀, t_max]` of border nodes with
`r ≤ t₀`, `t_max < r + p`, `⌊t_max/p⌋ = ⌊t₀/p⌋` and no singular index in `(t₀, t_max]` (one arc, one
chain length), and `B₀ ≠ 0` at `t₀`, the Smith datum whose `J`-block is `s7_twoTerm` on the border
rows/columns inside the window (`Jr`, `Jc` = `winRows`, `winCols`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.Content.UFMoments

variable (c : ℚ) (hc : 0 < c) {r : ℕ}

theorem alt_hc' {N : ℕ} (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N) :
    ∀ a : ((altGeom c hc).geometry r).C, (a : ℕ) < N := fun a => by
  have := alt_core_lt c hc a; omega

theorem alt_hx' (hr : r % 2 = 0) {N : ℕ} (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N) :
    ∀ i, ((altGeom c hc).geometry r).xs i < N := fun i => by
  obtain ⟨a, ha, he⟩ := alt_xs_eq c hc hr i; omega

theorem alt_hy' (hr : r % 2 = 0) {N : ℕ} (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N) :
    ∀ j, ((altGeom c hc).geometry r).ys j < N := fun j => by
  obtain ⟨b, hb, he⟩ := alt_ys_eq c hc hr j; omega

/-- Border rows inside the window `[t₀, t_max]`. -/
noncomputable def winRows (t0 tmax : ℕ) : Finset (Fin ((altGeom c hc).geometry r).k) := by
  classical exact univ.filter fun i => t0 ≤ ((altGeom c hc).geometry r).xs i ∧
    ((altGeom c hc).geometry r).xs i ≤ tmax

/-- Border columns inside the window `[t₀, t_max]`. -/
noncomputable def winCols (t0 tmax : ℕ) : Finset (Fin ((altGeom c hc).geometry r).k) := by
  classical exact univ.filter fun i => t0 ≤ ((altGeom c hc).geometry r).ys i ∧
    ((altGeom c hc).geometry r).ys i ≤ tmax

theorem div_eq_of_between {p a t b : ℕ} (h1 : a ≤ t) (h2 : t ≤ b) (h : b / p = a / p) :
    t / p = a / p :=
  le_antisymm (h ▸ Nat.div_le_div_right h2) (Nat.div_le_div_right h1)

/-- **The `S7` Smith datum of the alternating geometry.** -/
noncomputable def altSmithJKDatum_S7 (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ} [Fact p.Prime]
    (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0)
    (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (hp : 2 * (altGeom c hc).borderSize r ≤ p) (hp2 : p ≠ 2)
    (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (t0 tmax : ℕ) (hrt : r ≤ t0) (htm : tmax < r + p) (hdiv : tmax / p = t0 / p)
    (hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tmax - t0))
    (hB0 : res p (1 - ∑ j, (sOwn (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0
      (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0) ᵥ*
      (Dmat (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (sLift (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
          ((altGeom c hc).geometry r).xs ((altGeom c hc).geometry r).ys
          (hint_of_poleData (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp
            (alt_hc' c hc hrN) (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN))).toBlocks₁₁)⁻¹) j) ≠
      0) :
    SmithJKDatum (altGeom c hc) Fr r p := by
  classical
  have hC := altGeom_C c hc r
  have hS : ∀ t, t0 ≤ t → t ≤ tmax →
      ShiftData (twoTermPoleData T hNp.le hsq hnorm hnorm0)
        (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0 t := by
    intro t h1 h2
    obtain ⟨Δ, rfl⟩ : ∃ Δ, t = t0 + Δ := ⟨t - t0, by omega⟩
    exact alt_shiftData T hNp.le hsq hnorm hnorm0 _ hC t0 Δ hrt (by omega)
      (div_eq_of_between h1 h2 hdiv) (fun k hk1 hk2 => hw k hk1 (by omega))
  exact
  { N := N
    D := twoTermPoleData T hNp.le hsq hnorm hnorm0
    hN := hNp
    hc := alt_hc' c hc hrN
    hx := alt_hx' c hc hr hrN
    hy := alt_hy' c hc hr hrN
    hdist := alt_hdist c hc hr hp
    J := s7_twoTerm T hNp.le hsq hnorm hnorm0 hNp hp2 ho hq _ _ _ (alt_hc' c hc hrN)
      (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) (alt_hdist c hc hr hp) t0 hB0
      (winRows c hc t0 tmax) (winCols c hc t0 tmax)
      (fun z hz => by
        simp only [winRows, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        exact hS _ hz.1 hz.2)
      (fun y hy => by
        simp only [winCols, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hS _ hy.1 hy.2) }

end CatalanCore.Uniform.Content.UFMoments
