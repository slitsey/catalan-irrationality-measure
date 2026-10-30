import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.LP
import CatalanCore.Uniform.Content.UFSimple.Audit
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # UF piece covers for the fifths family (lane B, B5c)

The UF layer is `UFSimple.ufClosedLayer` (base `closedPrice`, debit 1).  On a profile piece the
best of the four closed candidates `(κ, ζ)` is a fixed one with a fixed quotient `q = r / p`, so a
piece cover is one candidate: `pieceOK_S`. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Uniform.Content.BankShared
open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.UFSimple CatalanCore.Uniform.Bank.Fifths CatalanFrames.Fifths
  CatalanFrames.HybGen

theorem div_mod_of (r p q : ℕ) (h1 : q * p ≤ r) (h2 : r < (q + 1) * p) :
    r / p = q ∧ r % p = r - q * p := by
  have hd : r / p = q := Nat.div_eq_of_lt_le h1 h2
  refine ⟨hd, ?_⟩
  have := Nat.mod_add_div r p
  rw [hd, Nat.mul_comm p q] at this
  omega

theorem closedPrice_le_cand (m r p ρ : ℕ) (κ ζ : Bool) :
    closedPrice m r p ρ ≤ candPrice m r p ρ κ ζ := by
  unfold closedPrice
  cases κ <;> cases ζ <;> simp [min_le_iff]

/-- The closed UF hypotheses at the fifths data. -/
theorem closedHyp5 {Fr : Frame} {o : ℕ} (T : TwoTermData Fr 5 o) (hnorm : Fr.norm = 25)
    (r p K j : ℕ) [Fact p.Prime] (hr : r % 2 = 0) (hr0 : 0 < r)
    (hm1 : 1 ≤ F5.borderSize r) (hsq5 : 5 * (r + p) ≤ p * p) (hpm : 2 * F5.borderSize r ≤ p)
    (hp7 : 7 ≤ p) (hK : 5 * K = j * p + o) (hj0 : 0 < j) (hj5 : j < 5) :
    ClosedHyp (2 / 9) two_ninths_pos Fr 5 o r p K where
  hr2 := hr
  hr0 := hr0
  hm1 := hm1
  hNp := by omega
  hpm := hpm
  hp2 := by omega
  hq0 := by norm_num
  hqp := by omega
  hsq := by
    intro t ht1 htN
    have ho := T.o_pos
    have ho' := T.o_lt
    intro hd
    have hx : 0 < 5 * t - o := by omega
    have := Nat.le_of_dvd hx hd
    rw [pow_two] at this
    omega
  hnorm := by rw [hnorm]; exact (norm25_mem p hp7).1
  hnorm0 := by rw [hnorm]; exact (norm25_mem p hp7).2
  hρ := ⟨j, by rw [Nat.mul_comm p j]; omega⟩
  hρ1 := by
    have := T.o_pos
    have hjp : 0 < j * p := Nat.mul_pos hj0 (by omega)
    omega
  hρp := by
    have := T.o_lt
    have hjp : j * p ≤ 4 * p := Nat.mul_le_mul_right p (by omega)
    omega

section Pieces
variable {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ)

/-- A UF piece cover by the closed candidate `(κ, ζ)`. -/
theorem pieceOK_S (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) (κ ζ : Bool) (j sn sd tn td : ℕ)
    (A B E D : ℤ) (hD : 0 < D) (hE : D * 2600000000 ≤ E) (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (hint : ∀ r p m k : ℕ, R0 ≤ r → 2 * r ≤ 18 * m + 9 → 18 * m ≤ 2 * r + 8 → 1 ≤ u → u < 5 →
      5 * k = j * p + u → sn * r / sd < p → p ≤ tn * r / td →
      (2 * m ≤ p ∧ 0 < j ∧ j < 5) ∧
      D * ((candPrice m r p k κ ζ + 1000 : ℕ) : ℤ) ≤ A * (r : ℤ) + B * (p : ℤ) + E) :
    PieceOK T depth j sn sd tn td A B E D := by
  refine pieceOK_of T depth hcF j sn sd tn td A B E D hD hE hnn ?_
  intro i hi hR p h1 h2 hp hk hpf
  obtain ⟨hr, hb1, hb2⟩ := member_dom depth hi
  have hu0 := T.hu0
  have hu1 := T.hu1
  obtain ⟨⟨c2, c4, c5⟩, hineq⟩ :=
    hint i.1 p (F5.borderSize i.1) _ hR hb1 hb2 hu0 hu1 hk h1 h2
  have hr0 : 0 < i.1 := by unfold R0 at hR; omega
  have hlow : i.1 < 900 * p := low_of hsd h900 h1
  have hp7 : 7 ≤ p := by unfold R0 at hR; omega
  have hp11 : 11112 ≤ p := by unfold R0 at hR; omega
  have hpp : 11112 * p ≤ p * p := Nat.mul_le_mul_right p hp11
  have c1 : 5 * (i.1 + p) ≤ p * p := by omega
  have c3 : 1 ≤ F5.borderSize i.1 := by unfold R0 at hR; omega
  have hH := closedHyp5 (shift_twoTerm T) (shift_norm T) i.1 p ((fifthsInst T).cd.kq p) j hr hr0
    c3 c1 c2 hp7 (by omega) c4 c5
  have hv : ∀ r' p' : ℕ, ∀ [Fact p'.Prime], (r' = i.1 ∧ p' = p) →
      ClosedHyp (2 / 9) two_ninths_pos Fr 5 u r' p' ((fun _ => (fifthsInst T).cd.kq p) p') := by
    intro r' p' _ h
    obtain ⟨rfl, rfl⟩ := h
    exact hH
  have hg := (ufClosedLayer (c := 2 / 9) (hc := two_ninths_pos) (depth := depth) (shift_twoTerm T)
    (fun r' p' => r' = i.1 ∧ p' = p) (fun _ => (fifthsInst T).cd.kq p) hv).gle i hi.1 p ⟨rfl, rfl⟩
  refine ⟨_, hg, ?_⟩
  have hdel := delCount_le F5 Fr depth i hi.1
  have hle : (closedPrice (F5.borderSize i.1) i.1 p ((fifthsInst T).cd.kq p) + 1 * delCount F5 i : ℕ) ≤
      candPrice (F5.borderSize i.1) i.1 p ((fifthsInst T).cd.kq p) κ ζ + 1000 := by
    have := closedPrice_le_cand (F5.borderSize i.1) i.1 p ((fifthsInst T).cd.kq p) κ ζ
    simp only [one_mul]
    omega
  have hle' : ((closedPrice (F5.borderSize i.1) i.1 p ((fifthsInst T).cd.kq p) + 1 * delCount F5 i : ℕ) : ℤ) ≤
      ((candPrice (F5.borderSize i.1) i.1 p ((fifthsInst T).cd.kq p) κ ζ + 1000 : ℕ) : ℤ) := by
    exact_mod_cast hle
  calc D * ((closedPrice (F5.borderSize i.1) i.1 p ((fifthsInst T).cd.kq p) + 1 * delCount F5 i : ℕ) : ℤ)
      ≤ D * ((candPrice (F5.borderSize i.1) i.1 p ((fifthsInst T).cd.kq p) κ ζ + 1000 : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hle' hD.le
    _ ≤ _ := hineq

end Pieces

#print axioms closedHyp5
#print axioms pieceOK_S
end CatalanCore.Uniform.Bank.FifthsContent
