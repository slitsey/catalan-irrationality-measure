module

public import CatalanCore.Uniform.Content.BankShared.TwoTerm.LP
public import CatalanCore.Uniform.Content.Smith.TwoTerm2

@[expose] public section
set_option Elab.async false

/-! # LP2 without the hypothesis `N ≤ p + k` (paper `lp2-strip-2026-10-29`)

For a two-term frame `ψ(z+1) - ψ(z+a/q)` (`TwoTermData Fr q o`), Theorem LP2 holds with the
hypothesis `N = r + 2m ≤ p + k` replaced by `N ≤ 2p`, with the same D4 potentials `uPot`, the same
saving `r + m - p` and (for members) the same debit 1.

* `rank_diag_mul_diag_le` (masking lemma): `rank (diag d₁ · A · diag d₂) ≤ rank A`.
* `LP2HypW`: the hypotheses (`TTCfg2` at `N = r + 2m`, so `N ≤ 2p`; `r < p`, `k ≤ r`, `5 ≤ p`).
* `LP2HypW.hred`: the scaled entries of `Full(X)` reduce to the LP2 table `BTg` of `LP2Matrix`;
  nodes `≥ p + k` (a third, simple pole at `t = p + k`) give zero rows and columns.
* `LP2HypW.gleAt`, `LP2HypW.gle`: the rank witness and the valuation bound.
* `lp2wValid`, `lp2wLayer`, `lp2wHyp_tt`, `lp2wValid_tt`, `lp2w_gle_tt`: the widened LP2 layer and
  branch statement on the alternating geometry (`lp2Base` unchanged). -/

open Polynomial Finset Matrix CatalanCore CatalanCore.Basic CatalanCore.Linalg CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared

namespace CatalanCore.Uniform.Content.BankShared.TwoTerm

/-! ### The masking lemma -/

/-- **Masking lemma.**  Multiplying by diagonal matrices on both sides (e.g. `0/1` masks that delete
rows and columns) does not raise the rank. -/
theorem rank_diag_mul_diag_le {ι κ K : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] [Field K] (A : Matrix ι κ K) (d₁ : ι → K) (d₂ : κ → K) :
    (diagonal d₁ * A * diagonal d₂).rank ≤ A.rank :=
  (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-! ### Hypotheses and the pole table below `p + k` -/

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o N r m k j : ℕ}

/-- Hypotheses of the widened Theorem LP2: `TTCfg2` at `N = r + 2m` (so `N ≤ 2p`, `p² ∤ q t - o`
for `1 ≤ t < N`), `r < p`, `k ≤ r`, `5 ≤ p`. -/
structure LP2HypW (Fr : Frame) (p q o r m k j : ℕ) [Fact p.Prime] : Prop where
  cfg : TTCfg2 Fr p q o (r + 2 * m) k j
  hrp : r < p
  hkr : k ≤ r
  p5 : 5 ≤ p

/-- Below `p + k` a `TTCfg2` configuration is a `TTCfg` configuration. -/
theorem cfgOfCfg2 (C : TTCfg2 Fr p q o N k j) : TTCfg Fr p q o (min N (p + k)) k j :=
  ⟨C.tt, C.sg.toSing, fun t h1 h2 => C.hsq t h1 (lt_of_lt_of_le h2 (min_le_left _ _)), C.hnm,
    C.hnm0⟩

/-- `LP2Hyp.good_Tg` for any `N` (`N ≤ p + k` from `TTCfg`). -/
theorem good_Tg_N (C : TTCfg Fr p q o N k j) (hrp : r < p) (hkr : k ≤ r) {A B : ℕ} (hAB : A < B)
    (hBN : B < N) :
    Good p ((p : ℚ) ^ (uPot p r k A + uPot p r k B) * Fr.Mn A B)
      (Tg p k (red p Fr.norm) (vk p q j) A B) := by
  have hkp := C.sg.hkp
  have hNk := C.sg.hNk
  have hAN : A < N := by omega
  by_cases hBk : B < k
  · have hA0 : uPot p r k A = 0 := by
      unfold uPot; rw [if_pos (by omega), if_neg (by omega)]
    have hB0 : uPot p r k B = 0 := by
      unfold uPot; rw [if_pos (by omega), if_neg (by omega)]
    rw [hA0, hB0, add_zero, pow_zero, one_mul]
    unfold Tg; rw [if_pos hBk]
    exact C.good_Mn_reg hAB hBN hBk
  · by_cases hAk : A < k
    · have hA0 : uPot p r k A = 0 := by
        unfold uPot; rw [if_pos (by omega), if_neg (by omega)]
      by_cases hBp : B < p
      · have hB1 : uPot p r k B = 1 := by
          unfold uPot; split_ifs <;> omega
        rw [hA0, hB1, zero_add, pow_one]
        have hd : ((B : ZMod p) - A) ≠ 0 := zmod_sub_ne_zero_of_lt hAB (by omega)
        have g := C.D.good_cross_ordered hAB hBN hd
        refine g.congr ?_
        rw [C.V_val hBN, C.V_val hAN]
        unfold Tg
        rw [if_neg hBk, if_pos hAk, if_pos hBp, if_pos (by omega : k ≤ B),
          if_neg (by omega : ¬ k ≤ A), if_neg (by omega : ¬ p ≤ B), if_neg (by omega : ¬ p ≤ A)]
        rw [mul_inv]; ring
      · have hB2 : uPot p r k B = 2 := by
          unfold uPot; rw [if_neg (by omega)]; rw [if_pos (by omega)]
        rw [hA0, hB2, zero_add]
        by_cases hBA : B - A = p
        · have g := C.D.good_square C.hN' hAB hBN
          refine g.congr ?_
          rw [hBA, TTSing.invRes_self (Fact.out : p.Prime), C.V_val hBN, C.V_val hAN]
          unfold Tg
          rw [if_neg hBk, if_pos hAk, if_neg hBp, if_pos hBA, if_pos (by omega : k ≤ B),
            if_neg (by omega : ¬ k ≤ A), if_pos (by omega : p ≤ B), if_neg (by omega : ¬ p ≤ A)]
          ring
        · have hd : ((B : ZMod p) - A) ≠ 0 := sub_ne_zero_of_ne hAB (by omega) hBA
          have g := C.D.good_cross hAN hBN hd
          have g2 := g.ell_mul
          refine (g2.congr' (by ring)).congr ?_
          unfold Tg
          rw [if_neg hBk, if_pos hAk, if_neg hBp, if_neg hBA]
    · have h1 := uPot_ge_one (p := p) (r := r) (k := k) (A := A) (by omega)
      have h2 := uPot_ge_one (p := p) (r := r) (k := k) (A := B) (by omega)
      have hd : ((B : ZMod p) - A) ≠ 0 := zmod_sub_ne_zero_of_lt hAB (by omega)
      have g := C.D.good_cross hAN hBN hd
      have := good_zero_of_cross g.1 (e := uPot p r k A + uPot p r k B) (by omega)
      refine this.congr ?_
      unfold Tg
      rw [if_neg hBk, if_neg hAk]

/-- `LP2Hyp.good_Td` for any `N`. -/
theorem good_Td_N (C : TTCfg Fr p q o N k j) (hrp : r < p) {A : ℕ} (hAr : A < r) (hAN : A < N) :
    Good p ((p : ℚ) ^ (uPot p r k A + uPot p r k A) * Fr.Mn A A)
      (Td p k (red p Fr.norm) (vk p q j) A) := by
  have hkp := C.sg.hkp
  by_cases hAk : A < k
  · have hA0 : uPot p r k A = 0 := by
      unfold uPot; rw [if_pos hAr, if_neg (by omega)]
    rw [hA0, add_zero, pow_zero, one_mul]
    unfold Td; rw [if_pos hAk]
    exact C.good_Mn_diag_reg hAN hAk
  · have hA1 : uPot p r k A = 1 := by
      unfold uPot; rw [if_pos hAr, if_pos (by omega)]
    rw [hA1]
    have g := C.D.good_diagonal hAN
    refine (g.congr' (by norm_num)).congr ?_
    rw [C.W_val hAN]
    unfold Td
    rw [if_neg hAk, if_pos (by omega : k ≤ A), if_neg (by omega : ¬ p ≤ A)]
    ring

/-! ### Nodes at or beyond `p + k`: zero rows and columns -/

theorem good_zero_of_sq {x : ℚ} (hx : (p : ℚ) ^ 2 * x ∈ S p) {e : ℕ} (he : 3 ≤ e) :
    Good p ((p : ℚ) ^ e * x) 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 3 := ⟨e - 3, by omega⟩
  have hpm : (p : ℚ) ∈ S p := (Good.natCast (ℓ := p) p).1
  have hm : (p : ℚ) ^ d * ((p : ℚ) ^ 2 * x) ∈ S p := (S p).mul_mem ((S p).pow_mem hpm d) hx
  have := (good_red hm).ell_mul
  refine this.congr' ?_
  ring

/-- The table vanishes at nodes `B ≥ p + k`. -/
theorem Tg_high {nr v : ZMod p} {A B : ℕ} (hAB : A < B) (hB : p + k ≤ B) :
    Tg p k nr v A B = 0 := by
  unfold Tg
  rw [if_neg (show ¬ B < k by omega)]
  by_cases hA : A < k
  · rw [if_pos hA, if_neg (show ¬ B < p by omega), if_neg (show ¬ B - A = p by omega)]
  · rw [if_neg hA]

/-- **Step 2.**  An entry with the larger node `B ≥ p + k` (`B < N ≤ 2p`) reduces to `0`. -/
theorem good_high (C : TTCfg2 Fr p q o N k j) (hp5 : 5 ≤ p) (hrp : r < p) (hkr : k ≤ r) {A B : ℕ} (hAB : A < B)
    (hBN : B < N) (hB : p + k ≤ B) :
    Good p ((p : ℚ) ^ (uPot p r k A + uPot p r k B) * Fr.Mn A B) 0 := by
  have hN2 := C.sg.hN2
  have hkp := C.sg.hkp
  have hB2 : uPot p r k B = 2 := by
    unfold uPot; rw [if_neg (show ¬ B < r by omega), if_pos (show p ≤ B by omega)]
  by_cases hAk : A < k
  · have hA0 : uPot p r k A = 0 := by
      unfold uPot; split_ifs <;> omega
    rw [hA0, hB2]
    have hd : ((B : ZMod p) - A) ≠ 0 := sub_ne_zero_of_ne hAB (by omega) (by omega)
    have g := C.D.good_cross (by omega) hBN hd
    exact good_zero_of_cross g.1 (by omega)
  · have h1 := uPot_ge_one (p := p) (r := r) (k := k) (A := A) (by omega)
    have hsq := C.D.square_mem (C.hN' hN2 (by omega)) (a := A) (b := B) (by omega) hBN
    exact good_zero_of_sq hsq (by omega)

/-- The widened entry table: every off-diagonal pair below `N` reduces to `Tg`. -/
theorem LP2HypW.good_Tg (H : LP2HypW Fr p q o r m k j) {A B : ℕ} (hAB : A < B)
    (hBN : B < r + 2 * m) :
    Good p ((p : ℚ) ^ (uPot p r k A + uPot p r k B) * Fr.Mn A B)
      (Tg p k (red p Fr.norm) (vk p q j) A B) := by
  by_cases hB : B < p + k
  · exact good_Tg_N (cfgOfCfg2 H.cfg) H.hrp H.hkr hAB (lt_min hBN hB)
  · rw [Tg_high hAB (by omega)]
    exact good_high H.cfg H.p5 H.hrp H.hkr hAB hBN (by omega)

theorem LP2HypW.good_Td (H : LP2HypW Fr p q o r m k j) {A : ℕ} (hAr : A < r) :
    Good p ((p : ℚ) ^ (uPot p r k A + uPot p r k A) * Fr.Mn A A)
      (Td p k (red p Fr.norm) (vk p q j) A) := by
  have hrp := H.hrp
  have hkp := H.cfg.sg.hkp
  exact good_Td_N (cfgOfCfg2 H.cfg) H.hrp hAr (lt_min (by omega) (by omega))

/-! ### The lifts (as `LP2Hyp.hred`) -/

theorem LP2HypW.lift_offdiag (H : LP2HypW Fr p q o r m k j) {A B : ℕ} (hAB : A ≠ B)
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (uPot p r k A + uPot p r k B)) * C (Fr.Mn A B) ∧
      phiP p g = rfC p (Tsym p k (red p Fr.norm) (vk p q j) A B) := by
  rcases lt_or_gt_of_ne hAB with h | h
  · have := H.good_Tg h hB
    have e : Tsym p k (red p Fr.norm) (vk p q j) A B = Tg p k (red p Fr.norm) (vk p q j) A B := by
      unfold Tsym; rw [if_pos h]
    rw [e]; exact lift_good p this
  · have := H.good_Tg h hA
    have e : Tsym p k (red p Fr.norm) (vk p q j) A B = Tg p k (red p Fr.norm) (vk p q j) B A := by
      unfold Tsym; rw [if_neg (by omega), if_pos h]
    rw [e, add_comm (uPot p r k A), Mn_symm]; exact lift_good p this

/-- **The entries of `Full(X)` reduce to the LP2 table `BTg`** (also for `p + k < N ≤ 2p`). -/
theorem LP2HypW.hred (H : LP2HypW Fr p q o r m k j) (a b : Fin r ⊕ Fin m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (uPot p r k (Frame.hybRow r m a) + uPot p r k (Frame.hybCol r m b))) *
        fullEntry Fr r m a b ∧
      phiP p g = BTg p r m k (red p Fr.norm) (vk p q j) a b := by
  have hA := hybRow_lt (r := r) (m := m) a
  have hB := hybCol_lt (r := r) (m := m) b
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hcc : c = c'
    · subst hcc
      have hcr := c.2
      have hgood := H.good_Td (A := (c : ℕ)) hcr
      obtain ⟨g, h1, h2⟩ := exists_lift_diag p (uPot p r k c + uPot p r k c) (Fr.Mn c c) hgood.1
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
      · rw [h2]
        have e1 : redQ p ⟨_, hgood.1⟩ = Td p k (red p Fr.norm) (vk p q j) c := hgood.2
        rw [e1]
        have e2 : Tsym p k (red p Fr.norm) (vk p q j) c c = Td p k (red p Fr.norm) (vk p q j) c := by
          unfold Tsym; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
        have e3 : uPot p r k (c : ℕ) = 0 ↔ (c : ℕ) < k := by
          by_cases hck : (c : ℕ) < k
          · have h' : ¬ k ≤ (c : ℕ) := by omega
            simp [uPot, hcr, h', hck]
          · have h' : k ≤ (c : ℕ) := by omega
            simp [uPot, hcr, h', hck]
        rw [add_comm]
        simp [BTg, Frame.hybRow, Frame.hybCol, e2, e3]
    · have hne : (c : ℕ) ≠ c' := fun h => hcc (Fin.ext h)
      obtain ⟨g, h1, h2⟩ := H.lift_offdiag hne (by have := c.2; have := H.hrp; omega)
        (by have := c'.2; omega)
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, hcc, Frame.hybRow, Frame.hybCol]
      · rw [h2]; simp [BTg, hcc, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := H.lift_offdiag (A := c) (B := r + 2 * (i' : ℕ) + 1)
      (by have := c.2; omega) (by have := c.2; omega) hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTg, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := H.lift_offdiag (A := r + 2 * (i : ℕ)) (B := c')
      (by have := c'.2; omega) hA (by have := c'.2; omega)
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTg, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := H.lift_offdiag (A := r + 2 * (i : ℕ)) (B := r + 2 * (i' : ℕ) + 1)
      (by omega) hA hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTg, Frame.hybRow, Frame.hybCol]

/-! ### The rank bound -/

/-- Border rows/columns at nodes `z ≥ p + k` of `GxG`, `GyG` vanish. -/
theorem Tsym_border_high {nr v : ZMod p} (hrp : r < p) (hkr : k ≤ r) {z : ℕ} (hz : p + k ≤ z) (w : Blk0 r k) :
    rfC p (Tsym p k nr v z w.1.val) = 0 := by
  have hwk : w.1.val < k := w.2
  rw [Tsym_zone (z := z) (by omega) hkr hwk, if_neg (show ¬ z < p by omega),
    if_neg (show ¬ z - w.1.val = p by omega), rfC_zero]

/-- The fictitious high datum: `z - p` below `p + k`, else an index of `B0` of the parity of `z - p`. -/
def cXw (p r k : ℕ) (hk2 : 2 ≤ k) (hkr : k ≤ r) (z : ℕ) : Blk0 r k :=
  if h : z - p < k then ⟨⟨z - p, by omega⟩, h⟩ else ⟨⟨(z - p) % 2, by omega⟩, show (z - p) % 2 < k by omega⟩

theorem cXw_val_lt {hk2 : 2 ≤ k} {hkr : k ≤ r} {z : ℕ} (h : z - p < k) :
    (cXw p r k hk2 hkr z).1.val = z - p := by
  unfold cXw; rw [dif_pos h]

theorem cXw_mod {hk2 : 2 ≤ k} {hkr : k ≤ r} (z : ℕ) :
    (cXw p r k hk2 hkr z).1.val % 2 = (z - p) % 2 := by
  unfold cXw
  split_ifs with h
  · rfl
  · exact Nat.mod_mod _ _

/-- **Theorem LP2 without `N ≤ p + k`, rank witness.**  Under `N ≤ 2p` the reduction `B̄ = BTg` of
`Full(X)` under the D4 potentials has `rank B̄ ≤ p`: it is the mask of an LP2 block matrix whose
rows/columns at nodes `≥ p + k` carry fictitious high data. -/
theorem LP2HypW.gleAt (H : LP2HypW Fr p q o r m k j) (hpm : p < r + m) :
    HasRankWit Fr p r m (fun a => uPot p r k (Frame.hybRow r m a))
      (fun b => uPot p r k (Frame.hybCol r m b)) (m - (p - r)) := by
  have C := H.cfg
  have hrp := H.hrp
  have hp5 := H.p5
  have hk0 := C.sg.hk0
  have hkr := H.hkr
  have hkp := C.sg.hkp
  have hN2 := C.sg.hN2
  have hnr : red p Fr.norm ≠ 0 := C.hnm0
  have hv : vk p q j ≠ 0 := C.sg.vk_ne C.tt
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k = 1 := by omega
    have h := C.sg.hk
    rw [hk1, mul_one] at h
    have := Nat.le_mul_of_pos_left p C.sg.hj0
    have := C.sg.hqp; have := C.tt.o_pos
    omega
  obtain ⟨d, hd⟩ : ∃ d, d = p - r := ⟨_, rfl⟩
  have hrd : r + d = p := by omega
  have hd0 : 0 < d := by omega
  have hdm : d ≤ m := by omega
  set nr := red p Fr.norm with hnrdef
  set v := vk p q j with hvdef
  have hpi : piG p nr v ≠ 0 := by
    unfold piG; rw [rfC_eq]
    exact (map_ne_zero (rfCH p)).2 (mul_ne_zero (inv_ne_zero hnr) (pow_ne_zero 2 hv))
  have hs0 : s0g k nr ≠ 0 := by
    unfold s0g rfX rfC
    rw [← map_add]
    exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))).2
      (Polynomial.X_add_C_ne_zero _)
  set σ := rfC p (nr⁻¹ * (v + 1)) with hσ
  let cX : ℕ → Blk0 r k := cXw p r k hk2 hkr
  -- the masked border blocks
  let Gx : Matrix (Fin m) (Blk0 r k) (RatFunc (ZMod p)) := Matrix.of fun x w =>
    if r + 2 * (x : ℕ) < p + k then GxG p r m k nr v x w else (if w = cX (r + 2 * (x : ℕ)) then σ else 0)
  let Gy : Matrix (Blk0 r k) (Fin m) (RatFunc (ZMod p)) := Matrix.of fun w y =>
    if r + 2 * (y : ℕ) + 1 < p + k then GyG p r m k nr v w y
    else (if w = cX (r + 2 * (y : ℕ) + 1) then σ else 0)
  have hGx : ∀ (x : Fin m) (w : Blk0 r k), Gx x w =
      if r + 2 * (x : ℕ) < p then -(rfC p (nr⁻¹ * v)) *
        EL p r k d w ⟨(p - (r + 2 * (x : ℕ)) - 1) % d, Nat.mod_lt _ hd0⟩
      else if w = cX (r + 2 * (x : ℕ)) then σ else 0 := by
    intro x w
    simp only [Gx, Matrix.of_apply]
    by_cases hlo : r + 2 * (x : ℕ) < p + k
    · rw [if_pos hlo]
      simp only [GxG, Matrix.of_apply]
      refine zone_shape_g (nr := nr) (v := v) hkr hd hd0 (z := r + 2 * (x : ℕ)) (by omega) w
        (cX (r + 2 * (x : ℕ))) ?_
      by_cases h : r + 2 * (x : ℕ) < p
      · exact Or.inl h
      · exact Or.inr (cXw_val_lt (by omega))
    · rw [if_neg hlo, if_neg (show ¬ r + 2 * (x : ℕ) < p by omega)]
  have hGy : ∀ (w : Blk0 r k) (y : Fin m), Gy w y =
      if r + 2 * (y : ℕ) + 1 < p then -(rfC p (nr⁻¹ * v)) *
        EL p r k d w ⟨(p - (r + 2 * (y : ℕ) + 1) - 1) % d, Nat.mod_lt _ hd0⟩
      else if w = cX (r + 2 * (y : ℕ) + 1) then σ else 0 := by
    intro w y
    simp only [Gy, Matrix.of_apply]
    by_cases hlo : r + 2 * (y : ℕ) + 1 < p + k
    · rw [if_pos hlo]
      simp only [GyG, Matrix.of_apply]
      rw [Tsym_symm]
      refine zone_shape_g (nr := nr) (v := v) hkr hd hd0 (z := r + 2 * (y : ℕ) + 1) (by omega) w
        (cX (r + 2 * (y : ℕ) + 1)) ?_
      by_cases h : r + 2 * (y : ℕ) + 1 < p
      · exact Or.inl h
      · exact Or.inr (cXw_val_lt (by omega))
    · rw [if_neg hlo, if_neg (show ¬ r + 2 * (y : ℕ) + 1 < p by omega)]
  have hrank := rank_BbarB_le (A0g p r k nr v) (Vg p r k nr v) (piG p nr v) (s0g k nr) (κg nr)
    (rfC p (nr⁻¹ * v)) σ hpi hs0 (EL p r k d) (hS_g r k nr v hp5 hrd hkr hnr hv) Gx Gy
    (fun x : Fin m => r + 2 * (x : ℕ) < p) (fun y : Fin m => r + 2 * (y : ℕ) + 1 < p)
    (fun x : Fin m => ⟨(p - (r + 2 * (x : ℕ)) - 1) % d, Nat.mod_lt _ hd0⟩)
    (fun y : Fin m => ⟨(p - (r + 2 * (y : ℕ) + 1) - 1) % d, Nat.mod_lt _ hd0⟩)
    (fun x : Fin m => cX (r + 2 * (x : ℕ))) (fun y : Fin m => cX (r + 2 * (y : ℕ) + 1))
    hGx hGy ?_ ?_
  rotate_left
  · intro x y hx hy
    have hx' := x.2
    have hy' := y.2
    intro h
    have h2 := congrArg Fin.val h
    simp only at h2
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
    omega
  · intro x y hx hy h
    have hx' : ¬ r + 2 * (x : ℕ) < p := hx
    have hy' : ¬ r + 2 * (y : ℕ) + 1 < p := hy
    have h1 := cXw_mod (p := p) (hk2 := hk2) (hkr := hkr) (r + 2 * (x : ℕ))
    have h2 := cXw_mod (p := p) (hk2 := hk2) (hkr := hkr) (r + 2 * (y : ℕ) + 1)
    have h3 : (cXw p r k hk2 hkr (r + 2 * (x : ℕ))).1.val =
        (cXw p r k hk2 hkr (r + 2 * (y : ℕ) + 1)).1.val := congrArg (fun t : Blk0 r k => t.1.val) h
    omega
  -- `BbarB` with the true border blocks is a mask of the one with fictitious data
  let dR : (Blk0 r k ⊕ Fin m) ⊕ Blk1 r k → RatFunc (ZMod p) :=
    Sum.elim (Sum.elim (fun _ => 1) (fun x => if r + 2 * (x : ℕ) < p + k then 1 else 0)) (fun _ => 1)
  let dC : (Blk0 r k ⊕ Fin m) ⊕ Blk1 r k → RatFunc (ZMod p) :=
    Sum.elim (Sum.elim (fun _ => 1) (fun y => if r + 2 * (y : ℕ) + 1 < p + k then 1 else 0))
      (fun _ => 1)
  have hGx0 : ∀ (x : Fin m) (w : Blk0 r k), ¬ r + 2 * (x : ℕ) < p + k →
      GxG p r m k nr v x w = 0 := by
    intro x w h
    simp only [GxG, Matrix.of_apply]
    exact Tsym_border_high hrp hkr (by omega) w
  have hGy0 : ∀ (w : Blk0 r k) (y : Fin m), ¬ r + 2 * (y : ℕ) + 1 < p + k →
      GyG p r m k nr v w y = 0 := by
    intro w y h
    simp only [GyG, Matrix.of_apply]
    rw [Tsym_symm]
    exact Tsym_border_high hrp hkr (by omega) w
  have hmask : BbarB (A0g p r k nr v) (Vg p r k nr v) (piG p nr v) (GxG p r m k nr v)
      (GyG p r m k nr v) =
      diagonal dR * BbarB (A0g p r k nr v) (Vg p r k nr v) (piG p nr v) Gx Gy * diagonal dC := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases i with (u | x) | c <;> rcases j with (w | y) | c'
    · simp [BbarB, dR, dC]
    · by_cases h : r + 2 * (y : ℕ) + 1 < p + k
      · simp [BbarB, dR, dC, Gy, h]
      · simp [BbarB, dR, dC, h, hGy0 u y h]
    · simp [BbarB, dR, dC]
    · by_cases h : r + 2 * (x : ℕ) < p + k
      · simp [BbarB, dR, dC, Gx, h]
      · simp [BbarB, dR, dC, h, hGx0 x w h]
    · simp [BbarB, dR, dC]
    · simp [BbarB, dR, dC]
    · simp [BbarB, dR, dC]
    · simp [BbarB, dR, dC]
    · simp [BbarB, dR, dC]
  have hBT : BTg p r m k nr v =
      (BbarB (A0g p r k nr v) (Vg p r k nr v) (piG p nr v) (GxG p r m k nr v)
        (GyG p r m k nr v)).submatrix (eB r m k) (eB r m k) := by
    ext a b
    exact (BTg_eq p r m k nr v hkr a b).symm
  refine ⟨BTg p r m k nr v, H.hred, ?_⟩
  rw [hBT, Matrix.rank_submatrix _ (eB r m k) (eB r m k), hmask]
  have h1 := rank_diag_mul_diag_le
    (BbarB (A0g p r k nr v) (Vg p r k nr v) (piG p nr v) Gx Gy) dR dC
  have hcb := card_blk r k
  simp only [Fintype.card_fin] at hrank
  omega

/-- **Theorem LP2 without `N ≤ p + k`.**  For `r < p < r + m`, `k ≤ r`, `r + 2m ≤ 2p` and the
corrected PoleData condition, `p^{τ' - (r + m - p)} · det Full(X)` is `ℤ_(p)`-integral. -/
theorem LP2HypW.gle (H : LP2HypW Fr p q o r m k j) (hpm : p < r + m) :
    GLE p (∑ a, uPot p r k (Frame.hybRow r m a) + ∑ b, uPot p r k (Frame.hybCol r m b) -
      (m - (p - r))) (Fr.fullPoly r m) :=
  (H.gleAt hpm).gle

/-! ### The widened LP2 layer -/

/-- Window of the widened LP2: hybrid shape, `LP2HypW` and `p < r + m`. -/
def lp2wValid (G : BlockGeom) (Fr : Frame) (q o : ℕ) (kf jf : ℕ → ℕ → ℕ) (r p : ℕ) : Prop :=
  HybShape G r ∧ ∀ [Fact p.Prime],
    LP2HypW Fr p q o r (G.geometry r).k (kf r p) (jf r p) ∧ p < r + (G.geometry r).k

/-- **Widened LP2 layer (debit 1)**; same price `lp2Base` as `lp2Layer`. -/
noncomputable def lp2wLayer (G : BlockGeom) (Fr : Frame) (depth : ℕ) (q o : ℕ)
    (kf jf : ℕ → ℕ → ℕ) : DebitLayer G Fr depth :=
  DebitLayer.lpd (lp2wValid G Fr q o kf jf) (lp2Base G kf)
    (fun r p _ h => lpDatumOfWit h.1 ((h.2.1).gleAt h.2.2))
    (fun r p _ h => by
      rw [lpDatumOfWit_u, lpDatumOfWit_v]
      rfl)

theorem lp2wHyp_tt (T : TwoTermData Fr q o) {nm : ℕ} (hnorm : Fr.norm = (nm : ℚ))
    {p r m k j : ℕ} [Fact p.Prime] (hpn : ¬ p ∣ nm) (hp5 : 5 ≤ p) (hpq : 2 * q ≤ p)
    (hk : q * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hN2 : r + 2 * m ≤ 2 * p) (hrp : r < p) (hkr : k ≤ r) : LP2HypW Fr p q o r m k j := by
  have hn := norm_good hnorm hpn
  have ho := T.o_pos
  have hoq := T.o_lt
  exact ⟨⟨T, ⟨by omega, hk, hk0, hkp, hj0, hN2⟩,
    not_sq_dvd_of_qN T (qN_le_of_two hN2 hpq), hn.1, hn.2⟩, hrp, hkr, hp5⟩

theorem lp2wValid_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (r p k j : ℕ) (hr : r % 2 = 0) [Fact p.Prime] (hpn : ¬ p ∣ nm)
    (hp5 : 5 ≤ p) (hpq : 2 * q ≤ p)
    (hk : q * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hN2 : r + 2 * (altGeom c hc).borderSize r ≤ 2 * p) (hrp : r < p) (hkr : k ≤ r)
    (hpm : p < r + (altGeom c hc).borderSize r) :
    lp2wValid (altGeom c hc) Fr q o (fun _ _ => k) (fun _ _ => j) r p := by
  have hgk : ((altGeom c hc).geometry r).k = (altGeom c hc).borderSize r :=
    geometry_k_eq_borderSize _ r
  refine ⟨altGeom_hybShape c hc hr, fun [Fact p.Prime] => ?_⟩
  rw [hgk]
  exact ⟨lp2wHyp_tt T hnorm hpn hp5 hpq hk hk0 hkp hj0 hN2 hrp hkr, hpm⟩

/-- **Widened LP2 branch** of the root class `j`: `lp2_gle_tt` with `N ≤ p + k` replaced by
`N ≤ 2p`; same price `2(r - k) + 2m + (2m - (p-r)) - (m - (p-r))` plus the deletion count. -/
theorem lp2w_gle_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hi : ((altGeom c hc).family Fr depth).Adm i) (hr : i.1 % 2 = 0)
    (p k j : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ nm) (hp5 : 5 ≤ p) (hpq : 2 * q ≤ p)
    (hk : q * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hN2 : i.1 + 2 * (altGeom c hc).borderSize i.1 ≤ 2 * p) (hrp : i.1 < p) (hkr : k ≤ i.1)
    (hpm : p < i.1 + (altGeom c hc).borderSize i.1) :
    GLE p (2 * (i.1 - k) + 2 * (altGeom c hc).borderSize i.1 +
        (2 * (altGeom c hc).borderSize i.1 - (p - i.1)) -
        ((altGeom c hc).borderSize i.1 - (p - i.1)) +
        delCount (altGeom c hc) i) (((altGeom c hc).family Fr depth).Q i) := by
  have hv := lp2wValid_tt c hc T hnorm i.1 p k j hr hpn hp5 hpq hk hk0 hkp hj0 hN2 hrp hkr hpm
  have hg := (lp2wLayer (altGeom c hc) Fr depth q o (fun _ _ => k) (fun _ _ => j)).gle i hi p hv
  refine hg.mono (le_of_eq ?_)
  show lp2Base (altGeom c hc) (fun _ _ => k) i.1 p + 1 * delCount (altGeom c hc) i = _
  rw [lp2Base_closed (altGeom c hc) (fun _ _ => k) i.1 p hkr, geometry_k_eq_borderSize, one_mul]

end CatalanCore.Uniform.Content.BankShared.TwoTerm

#print axioms CatalanCore.Uniform.Content.BankShared.TwoTerm.rank_diag_mul_diag_le
#print axioms CatalanCore.Uniform.Content.BankShared.TwoTerm.LP2HypW.gle
#print axioms CatalanCore.Uniform.Content.BankShared.TwoTerm.lp2w_gle_tt
