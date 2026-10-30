import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Bank.FifthsContent.LPSums
import CatalanFrames.HybGen.TropGood
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # LP1 / LP2 piece covers for the fifths family (lane B, B5c)

`lp1_valid5`, `lp2_valid5`: the LP windows of the two-term frames of norm 25 on the geometry `F5`.
`pieceOK_lp1`, `pieceOK_lp2`: the LP pieces of the profile (debit `1`, absorbed in the constant
since `depth ≤ 1000`). -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Uniform.Content.BankShared
open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Bank.Fifths CatalanFrames.Fifths CatalanFrames.HybGen

theorem norm25_mem (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    ((25 : ℚ) ∈ CatalanCore.S p) ∧ red p (25 : ℚ) ≠ 0 := by
  refine ⟨by simpa using (Good.ofNat (ℓ := p) 25).mem, ?_⟩
  have h25 : (25 : ZMod p) ≠ 0 := by
    have : ((25 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
      have h55 : p ∣ 5 * 5 := by simpa using hd
      rcases (Fact.out : p.Prime).dvd_mul.mp h55 with h | h <;>
        exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    simpa using this
  simpa [red] using h25

theorem not_sq_dvd5 {p x : ℕ} (hp : 10 ≤ p) (hx0 : 0 < x) (hx : x < 10 * p) : ¬ p ^ 2 ∣ x := by
  intro hd
  have := Nat.le_of_dvd hx0 hd
  nlinarith

theorem lp1_valid5 {Fr : Frame} {o : ℕ} (T : TwoTermData Fr 5 o) (hnorm : Fr.norm = 25)
    (r p k j : ℕ) (hr : r % 2 = 0) [Fact p.Prime] (hp10 : 10 ≤ p)
    (hk : 5 * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hN2 : r + 2 * F5.borderSize r ≤ 2 * p) (hrp : p ≤ r) (hUk : r < p + k) :
    lp1Valid F5 Fr 5 o (fun _ _ => k) (fun _ _ => j) r p := by
  have hgk : (F5.geometry r).k = F5.borderSize r :=
    CatalanCore.Uniform.Content.BankShared.geometry_k_eq_borderSize F5 r
  refine ⟨F5_hyb hr, fun [hpf : Fact p.Prime] => ?_⟩
  have hn := norm25_mem p (by omega)
  rw [hgk]
  refine ⟨⟨T, ⟨by omega, hk, hk0, hkp, hj0, hN2⟩, ?_, by rw [hnorm]; exact hn.1,
    by rw [hnorm]; exact hn.2⟩, hrp, hUk, by omega⟩
  intro t ht1 htN
  have ho := T.o_pos
  refine not_sq_dvd5 hp10 (by have := T.o_lt; omega) (by omega)

theorem lp2_valid5 {Fr : Frame} {o : ℕ} (T : TwoTermData Fr 5 o) (hnorm : Fr.norm = 25)
    (r p k j : ℕ) (hr : r % 2 = 0) [Fact p.Prime] (hp10 : 10 ≤ p)
    (hk : 5 * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hNk : r + 2 * F5.borderSize r ≤ p + k) (hrp : r < p) (hkr : k ≤ r)
    (hpm : p < r + F5.borderSize r) :
    lp2Valid F5 Fr 5 o (fun _ _ => k) (fun _ _ => j) r p := by
  have hgk : (F5.geometry r).k = F5.borderSize r :=
    CatalanCore.Uniform.Content.BankShared.geometry_k_eq_borderSize F5 r
  refine ⟨F5_hyb hr, fun [hpf : Fact p.Prime] => ?_⟩
  have hn := norm25_mem p (by omega)
  rw [hgk]
  refine ⟨⟨⟨T, ⟨by omega, hk, hk0, hkp, hj0, hNk⟩, ?_, by rw [hnorm]; exact hn.1,
    by rw [hnorm]; exact hn.2⟩, hrp, hkr, by omega⟩, hpm⟩
  intro t ht1 htN
  have ho := T.o_pos
  refine not_sq_dvd5 hp10 (by have := T.o_lt; omega) (by omega)

section Pieces
variable {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ)

theorem pieceOK_lp1 (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) (j sn sd tn td : ℕ)
    (A B E D : ℤ) (hD : 0 < D) (hE : D * 2600000000 ≤ E) (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (hint : ∀ r p m k : ℕ, R0 ≤ r → 2 * r ≤ 18 * m + 9 → 18 * m ≤ 2 * r + 8 → 1 ≤ u → u < 5 →
      5 * k = j * p + u → sn * r / sd < p → p ≤ tn * r / td →
      (p ≤ r ∧ r < p + k ∧ r + 2 * m ≤ 2 * p ∧ k ≤ r ∧ 0 < k ∧ k < p ∧ 0 < j ∧ 10 ≤ p) ∧
      D * ((2 * (r - (k - (r - p))) + 2 * m + min m ((p + k - r + 1) / 2) +
        min m ((p + k - r) / 2) - (min (p + k - r) (2 * m) - m) + 1000 : ℕ) : ℤ) ≤
        A * (r : ℤ) + B * (p : ℤ) + E) :
    PieceOK T depth j sn sd tn td A B E D := by
  refine pieceOK_of T depth hcF j sn sd tn td A B E D hD hE hnn ?_
  intro i hi hR p h1 h2 hp hk hpf
  obtain ⟨hr, hb1, hb2⟩ := member_dom depth hi
  have hu0 := T.hu0
  have hu1 := T.hu1
  obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8⟩, hineq⟩ :=
    hint i.1 p (F5.borderSize i.1) _ hR hb1 hb2 hu0 hu1 hk h1 h2
  have hv := lp1_valid5 (shift_twoTerm T) (shift_norm T) i.1 p ((fifthsInst T).cd.kq p) j hr c8
    (by omega) c5 c6 c7 c3 c1 c2
  have hg := (lp1Layer F5 Fr depth 5 u (fun _ _ => (fifthsInst T).cd.kq p) (fun _ _ => j)).gle i
    hi.1 p hv
  refine ⟨_, hg, ?_⟩
  have hbase := lp1Base_closed F5 (fun _ _ => (fifthsInst T).cd.kq p) i.1 p c4
  have hdel := delCount_le F5 Fr depth i hi.1
  have hgk : (F5.geometry i.1).k = F5.borderSize i.1 :=
    CatalanCore.Uniform.Content.BankShared.geometry_k_eq_borderSize F5 i.1
  rw [hgk] at hbase
  have hle : (lp1Base F5 (fun _ _ => (fifthsInst T).cd.kq p) i.1 p + 1 * delCount F5 i : ℕ) ≤
      2 * (i.1 - ((fifthsInst T).cd.kq p - (i.1 - p))) + 2 * F5.borderSize i.1 +
        min (F5.borderSize i.1) ((p + (fifthsInst T).cd.kq p - i.1 + 1) / 2) +
        min (F5.borderSize i.1) ((p + (fifthsInst T).cd.kq p - i.1) / 2) -
        (min (p + (fifthsInst T).cd.kq p - i.1) (2 * F5.borderSize i.1) - F5.borderSize i.1) + 1000 := by
    simp only [one_mul]
    omega
  have hle' : ((lp1Base F5 (fun _ _ => (fifthsInst T).cd.kq p) i.1 p + 1 * delCount F5 i : ℕ) : ℤ) ≤
      ((2 * (i.1 - ((fifthsInst T).cd.kq p - (i.1 - p))) + 2 * F5.borderSize i.1 +
        min (F5.borderSize i.1) ((p + (fifthsInst T).cd.kq p - i.1 + 1) / 2) +
        min (F5.borderSize i.1) ((p + (fifthsInst T).cd.kq p - i.1) / 2) -
        (min (p + (fifthsInst T).cd.kq p - i.1) (2 * F5.borderSize i.1) - F5.borderSize i.1) + 1000 : ℕ) : ℤ) := by
    exact_mod_cast hle
  calc D * ((lp1Base F5 (fun _ _ => (fifthsInst T).cd.kq p) i.1 p + 1 * delCount F5 i : ℕ) : ℤ)
      ≤ D * ((2 * (i.1 - ((fifthsInst T).cd.kq p - (i.1 - p))) + 2 * F5.borderSize i.1 +
        min (F5.borderSize i.1) ((p + (fifthsInst T).cd.kq p - i.1 + 1) / 2) +
        min (F5.borderSize i.1) ((p + (fifthsInst T).cd.kq p - i.1) / 2) -
        (min (p + (fifthsInst T).cd.kq p - i.1) (2 * F5.borderSize i.1) - F5.borderSize i.1) + 1000 : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hle' hD.le
    _ ≤ _ := hineq

theorem pieceOK_lp2 (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) (j sn sd tn td : ℕ)
    (A B E D : ℤ) (hD : 0 < D) (hE : D * 2600000000 ≤ E) (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (hint : ∀ r p m k : ℕ, R0 ≤ r → 2 * r ≤ 18 * m + 9 → 18 * m ≤ 2 * r + 8 → 1 ≤ u → u < 5 →
      5 * k = j * p + u → sn * r / sd < p → p ≤ tn * r / td →
      (p < r + m →
        (r < p ∧ r + 2 * m ≤ p + k ∧ k ≤ r ∧ 0 < k ∧ k < p ∧ 0 < j ∧ 10 ≤ p) ∧
        D * ((2 * (r - k) + 2 * m + (m - min m ((p - r + 1) / 2)) +
          (m - min m ((p - r) / 2)) - (m - (p - r)) + 1000 : ℕ) : ℤ) ≤
          A * (r : ℤ) + B * (p : ℤ) + E) ∧
      (r + m ≤ p →
        (r < p ∧ 2 * m ≤ r) ∧
        D * ((2 * (r - k) + 2 * m + (2 * m - (p - r)) : ℕ) : ℤ) ≤
          A * (r : ℤ) + B * (p : ℤ) + E)) :
    PieceOK T depth j sn sd tn td A B E D := by
  refine pieceOK_of T depth hcF j sn sd tn td A B E D hD hE hnn ?_
  intro i hi hR p h1 h2 hp hk hpf
  obtain ⟨hr, hb1, hb2⟩ := member_dom depth hi
  have hu0 := T.hu0
  have hu1 := T.hu1
  obtain ⟨hA, hB⟩ := hint i.1 p (F5.borderSize i.1) _ hR hb1 hb2 hu0 hu1 hk h1 h2
  by_cases hpm : p < i.1 + F5.borderSize i.1
  · obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8⟩, hineq⟩ := hA hpm
    have hv := lp2_valid5 (shift_twoTerm T) (shift_norm T) i.1 p ((fifthsInst T).cd.kq p) j hr c8
      (by omega) c5 c6 c7 c2 c1 c4 hpm
    have hg := (lp2Layer F5 Fr depth 5 u (fun _ _ => (fifthsInst T).cd.kq p) (fun _ _ => j)).gle i
      hi.1 p hv
    refine ⟨_, hg, ?_⟩
    have hbase := lp2Base_closed F5 (fun _ _ => (fifthsInst T).cd.kq p) i.1 p c4
    have hdel := delCount_le F5 Fr depth i hi.1
    have hgk : (F5.geometry i.1).k = F5.borderSize i.1 :=
      CatalanCore.Uniform.Content.BankShared.geometry_k_eq_borderSize F5 i.1
    rw [hgk] at hbase
    have hle : (lp2Base F5 (fun _ _ => (fifthsInst T).cd.kq p) i.1 p + 1 * delCount F5 i : ℕ) ≤
        2 * (i.1 - (fifthsInst T).cd.kq p) + 2 * F5.borderSize i.1 +
          (F5.borderSize i.1 - min (F5.borderSize i.1) ((p - i.1 + 1) / 2)) +
          (F5.borderSize i.1 - min (F5.borderSize i.1) ((p - i.1) / 2)) -
          (F5.borderSize i.1 - (p - i.1)) + 1000 := by
      simp only [one_mul]
      omega
    have hle' : ((lp2Base F5 (fun _ _ => (fifthsInst T).cd.kq p) i.1 p + 1 * delCount F5 i : ℕ) : ℤ) ≤
        ((2 * (i.1 - (fifthsInst T).cd.kq p) + 2 * F5.borderSize i.1 +
          (F5.borderSize i.1 - min (F5.borderSize i.1) ((p - i.1 + 1) / 2)) +
          (F5.borderSize i.1 - min (F5.borderSize i.1) ((p - i.1) / 2)) -
          (F5.borderSize i.1 - (p - i.1)) + 1000 : ℕ) : ℤ) := by
      exact_mod_cast hle
    calc D * ((lp2Base F5 (fun _ _ => (fifthsInst T).cd.kq p) i.1 p + 1 * delCount F5 i : ℕ) : ℤ)
        ≤ D * ((2 * (i.1 - (fifthsInst T).cd.kq p) + 2 * F5.borderSize i.1 +
          (F5.borderSize i.1 - min (F5.borderSize i.1) ((p - i.1 + 1) / 2)) +
          (F5.borderSize i.1 - min (F5.borderSize i.1) ((p - i.1) / 2)) -
          (F5.borderSize i.1 - (p - i.1)) + 1000 : ℕ) : ℤ) :=
          mul_le_mul_of_nonneg_left hle' hD.le
      _ ≤ _ := hineq
  · push Not at hpm
    obtain ⟨⟨c1, c2⟩, hineq⟩ := hB hpm
    have hlow : i.1 < 900 * p := low_of hsd h900 h1
    have hp7 : 7 ≤ p := by unfold R0 at hR; omega
    have hsq := hsq_of5 hR hb2 hlow
    have hr1 : 1 ≤ i.1 := by unfold R0 at hR; omega
    have hg := fifths_T_gle T depth i hr hr1 p hp7 hsq
    have hD45 := XGm_D45_good (fifths_levels T) i.1 (F5.borderSize i.1) p hp hp7 c1 c2
    refine ⟨_, hg, ?_⟩
    have hle' : ((XGm (fifthsInst T) i.1 (F5.borderSize i.1) p : ℕ) : ℤ) ≤
        ((2 * (i.1 - (fifthsInst T).cd.kq p) + 2 * F5.borderSize i.1 +
          (2 * F5.borderSize i.1 - (p - i.1)) : ℕ) : ℤ) := by
      exact_mod_cast hD45
    calc D * ((XGm (fifthsInst T) i.1 (F5.borderSize i.1) p : ℕ) : ℤ)
        ≤ D * ((2 * (i.1 - (fifthsInst T).cd.kq p) + 2 * F5.borderSize i.1 +
          (2 * F5.borderSize i.1 - (p - i.1)) : ℕ) : ℤ) :=
          mul_le_mul_of_nonneg_left hle' hD.le
      _ ≤ _ := hineq

end Pieces

#print axioms lp1_valid5
#print axioms lp2_valid5
#print axioms pieceOK_lp1
#print axioms pieceOK_lp2
end CatalanCore.Uniform.Bank.FifthsContent
