import CatalanCore.Uniform.Content.RankProducer.Closed
import CatalanCore.Uniform.Bank.ThirdsContent.TwoTerm
import CatalanCore.Uniform.Bank.Thirds.Geom
set_option Elab.async false

/-! # The closed rank layer of the thirds bank (lane C2L; the only bank-specific step)

`thirdsAc` has `TwoTermData thirdsAc 3 2` (`thirdsAc_twoTerm`), so the generic
`RankProducer.rankClosedLayer` applies with `q = 3`, `o = 2`, the pole residue `rho3 p`
(`p ∣ 3 ρ - 2`, `1 ≤ ρ < p`) and the digit bound `K = 4`.

`thirdsRankHyp`: the thirds band (`r` even, `0 < r`, `2m < p`, `3 (r + 2m) < p²`, `N3 < p`)
discharges the whole validity region `RankHyp` of Theorem R.  `thirdsRankLayer` is the rank layer
of the thirds content route: base `rankPrice`, debit `0`.
-/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.RankProducer
  CatalanCore.Uniform.Bank.Thirds CatalanFrames.Thirds

/-- The thirds pole residue: `p ∣ 3 ρ - 2`. -/
def rho3 (p : ℕ) : ℕ := if p % 3 = 1 then (p + 2) / 3 else (2 * p + 2) / 3

theorem rho3_spec {p : ℕ} (hp : 3 < p) (h3 : p % 3 ≠ 0) :
    p ∣ 3 * rho3 p - 2 ∧ 1 ≤ rho3 p ∧ rho3 p < p := by
  unfold rho3
  split_ifs with h
  · exact ⟨⟨1, by omega⟩, by omega, by omega⟩
  · exact ⟨⟨2, by omega⟩, by omega, by omega⟩

/-- The bound `N_Fr` of the thirds frame. -/
noncomputable abbrev N3 : ℕ := NFr (1 / thirdsAc.norm) (-1 / thirdsAc.norm) 3 4

/-- The thirds validity predicate of the rank layer. -/
def thirdsRankValid (r p : ℕ) : Prop :=
  r % 2 = 0 ∧ 0 < r ∧ 2 * (altGeom (3 / 10) c310_pos).borderSize r < p ∧
    3 * (r + 2 * (altGeom (3 / 10) c310_pos).borderSize r) < p ^ 2 ∧ N3 < p

/-- At an even scale, `3 r ≤ 20 m + 10` for the border size `m` of `altGeom (3/10)`. -/
theorem border_lower {r : ℕ} (hr : r % 2 = 0) :
    3 * r ≤ 20 * (altGeom (3 / 10) c310_pos).borderSize r + 10 := by
  have hm : ((3 / 10 : ℚ) * r - 1) / 2 ≤ ((altGeom (3 / 10) c310_pos).borderSize r : ℚ) := by
    rw [altGeom_borderSize _ _ hr, Nat.cast_min]
    refine le_min (le_trans ?_ (Nat.le_ceil _)) (Nat.le_ceil _)
    linarith
  have : (3 : ℚ) * r ≤ 20 * ((altGeom (3 / 10) c310_pos).borderSize r : ℚ) + 10 := by linarith
  exact_mod_cast this

/-- **The thirds band discharges the validity region of Theorem R.** -/
theorem thirdsRankHyp (r p : ℕ) [hp : Fact p.Prime] (h : thirdsRankValid r p) :
    RankHyp (3 / 10) c310_pos 3 2 N3 4 r p (rho3 p) := by
  obtain ⟨hr2, hr0, hpm, hB, hN⟩ := h
  have hN3 : 3 < p := by
    have : 3 ≤ N3 := by unfold N3 NFr; omega
    omega
  have h3 : p % 3 ≠ 0 := by
    intro h0
    rcases (Nat.dvd_prime hp.out).1 (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega
  obtain ⟨hρ, hρ1, hρp⟩ := rho3_spec hN3 h3
  have hl := border_lower hr2
  have hK : (r + 2 * (altGeom (3 / 10) c310_pos).borderSize r) / p ≤ 4 := by
    have h5 : r + 2 * (altGeom (3 / 10) c310_pos).borderSize r < 5 * p := by omega
    exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hp.out.pos).2 (by omega))
  exact ⟨hr2, hr0, hpm, hB, hN, hK, hρ, hρ1, hρp⟩

/-- **The closed rank layer of the thirds content route** (frame `thirdsAc`, geometry `G310`). -/
noncomputable def thirdsRankLayer (depth : ℕ) : DebitLayer G310 thirdsAc depth :=
  rankClosedLayer (c := 3 / 10) (hc := c310_pos) thirdsAc_twoTerm 4 thirdsRankValid rho3
    (fun r p _ h => thirdsRankHyp r p h)

theorem thirdsRankLayer_base (depth : ℕ) : (thirdsRankLayer depth).base =
    fun r p => rankPrice ((altGeom (3 / 10) c310_pos).borderSize r) r p (rho3 p) := rfl

theorem thirdsRankLayer_debit (depth : ℕ) : (thirdsRankLayer depth).debit = 0 := rfl

theorem thirdsRankLayer_valid (depth : ℕ) : (thirdsRankLayer depth).valid = thirdsRankValid := rfl

#print axioms thirdsRankHyp
#print axioms thirdsRankLayer
#print axioms thirdsRankLayer_base
end CatalanCore.Uniform.Bank.ThirdsContent
