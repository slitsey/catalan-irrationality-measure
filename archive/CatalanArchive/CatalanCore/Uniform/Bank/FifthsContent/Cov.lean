import CatalanCore.Uniform.Bank.FifthsContent.Tbridge
import CatalanCore.Uniform.Bank.FifthsContent.M3Gen
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Piece covers for the fifths family (lane B, B5c)

`PieceOK T depth j sn sd tn td A B E D`: for every even-scale member `i` and prime `p` with
`sn r / sd < p ≤ tn r / td` and first pole index `kq p` satisfying `5 kq = j p + u`, some `n` clears
the member at `p` and `D n ≤ A r + B p + E`.  This is the integer form of the cover of the template
piece `mkPiece sn sd tn td A B E D` (`covAt_mk`).  Pieces are proved from five closed-form kinds:
`M3D` (any gap indices, `m3_general`), the sawtooth (`XGm_D1x`), `D3`, `D45` and `D6` of table T.
Below `R0 = 10^7` the crude exponent is the witness. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanFrames.Fifths CatalanCore.Rect

/-- The scale threshold below which the crude exponent is the witness. -/
def R0 : ℕ := 10 ^ 7

theorem border_bounds5 {r : ℕ} (hr : r % 2 = 0) :
    2 * r ≤ 18 * F5.borderSize r + 9 ∧ 18 * F5.borderSize r ≤ 2 * r + 8 := by
  have hb : F5.borderSize r = min ⌈((2 / 9 : ℚ) * r) / 2⌉₊ ⌈((2 / 9 : ℚ) * r - 1) / 2⌉₊ :=
    altGeom_borderSize (2 / 9) two_ninths_pos hr
  have hc : ⌈((2 / 9 : ℚ) * r - 1) / 2⌉₊ ≤ ⌈((2 / 9 : ℚ) * r) / 2⌉₊ :=
    Nat.ceil_le_ceil (by linarith)
  rw [min_eq_right hc] at hb
  rw [hb]
  set x : ℚ := ((2 / 9 : ℚ) * r - 1) / 2 with hx
  by_cases h0 : 0 ≤ x
  · have h1 := Nat.le_ceil x
    have h2 := Nat.ceil_lt_add_one h0
    have e : (18 : ℚ) * x = 2 * r - 9 := by rw [hx]; ring
    constructor
    · have : (2 : ℚ) * r ≤ 18 * (⌈x⌉₊ : ℚ) + 9 := by nlinarith
      exact_mod_cast this
    · have : (18 : ℚ) * (⌈x⌉₊ : ℚ) < 2 * r + 9 := by nlinarith
      have : 18 * ⌈x⌉₊ < 2 * r + 9 := by exact_mod_cast this
      omega
  · have hneg : x < 0 := lt_of_not_ge h0
    have hz : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.2 hneg.le
    rw [hz]
    have e : (18 : ℚ) * x = 2 * r - 9 := by rw [hx]; ring
    have : (2 : ℚ) * r < 9 := by nlinarith
    have : 2 * r < 9 := by exact_mod_cast this
    omega

theorem hsq_of5 {r p m : ℕ} (hr : R0 ≤ r) (hm : 18 * m ≤ 2 * r + 8) (hp : r < 900 * p) :
    5 * (r + 2 * m) < p * p := by
  unfold R0 at hr
  have h1 : 900 * p ≥ r + 1 := hp
  have h2 : (900 * p) * (900 * p) ≥ (r + 1) * (r + 1) := Nat.mul_le_mul h1 h1
  nlinarith

theorem Ecrude_small5 (cE : ℕ) (hcE : cE ≤ 49) (r p : ℕ) (hr : r < R0) (hp : 2 ≤ p) :
    Ecrude cE r p ≤ 2600000000 := by
  unfold Ecrude
  unfold R0 at hr
  have h1 : Nat.log p (14 * r) ≤ 27 := by
    refine (Nat.log_anti_left (by omega) hp).trans ?_
    have : Nat.log 2 (14 * r) < 28 := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp
      · exact Nat.log_lt_of_lt_pow (by omega) (by
          have : 14 * r < 14 * 10 ^ 7 := by omega
          have h28 : (14 * 10 ^ 7 : ℕ) < 2 ^ 28 := by norm_num
          omega)
    omega
  have h2 : 3 * Nat.log p (14 * r) + cE ≤ 130 := by omega
  calc 2 * r * (3 * Nat.log p (14 * r) + cE) ≤ 2 * (10 ^ 7) * 130 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr.le) h2
    _ = 2600000000 := by norm_num

/-- The integer form of the cover of one template piece (see the module docstring). -/
def PieceOK {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (j sn sd tn td : ℕ)
    (A B E D : ℤ) : Prop :=
  ∀ i : (AltE (2 / 9) two_ninths_pos Fr depth).ι, (AltE (2 / 9) two_ninths_pos Fr depth).Adm i →
    ∀ p : ℕ, sn * i.1 / sd < p → p ≤ tn * i.1 / td → p.Prime →
      (R0 ≤ i.1 → 5 * (fifthsInst T).cd.kq p = j * p + u) → ∀ [Fact p.Prime],
        ∃ n : ℕ, GLE p n ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) ∧
          D * (n : ℤ) ≤ A * (i.1 : ℤ) + B * (p : ℤ) + E

theorem pieceOK_of {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49)
    (j sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D) (hE : D * 2600000000 ≤ E)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (hbig : ∀ i : (AltE (2 / 9) two_ninths_pos Fr depth).ι,
      (AltE (2 / 9) two_ninths_pos Fr depth).Adm i → R0 ≤ i.1 →
      ∀ p : ℕ, sn * i.1 / sd < p → p ≤ tn * i.1 / td → p.Prime →
      5 * (fifthsInst T).cd.kq p = j * p + u → ∀ [Fact p.Prime],
        ∃ n : ℕ, GLE p n ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) ∧
          D * (n : ℤ) ≤ A * (i.1 : ℤ) + B * (p : ℤ) + E) :
    PieceOK T depth j sn sd tn td A B E D := by
  intro i hi p h1 h2 hp hk hpf
  by_cases hr : R0 ≤ i.1
  · exact hbig i hi hr p h1 h2 hp (hk hr)
  · push Not at hr
    refine ⟨Ecrude (cFr Fr) i.1 p, altGeom_gle_Ecrude (2 / 9) two_ninths_pos (by norm_num) Fr depth i hi.2 p, ?_⟩
    have h := Ecrude_small5 (cFr Fr) hcF i.1 p hr hp.two_le
    have h' : ((Ecrude (cFr Fr) i.1 p : ℕ) : ℤ) ≤ 2600000000 := by exact_mod_cast h
    have := hnn i.1 p h1 h2
    nlinarith

/-- A piece `mkPiece sn sd tn td A B E D` is covered if `PieceOK` holds. -/
theorem covAt_mk {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (j sn sd tn td : ℕ)
    (A B E D : ℤ) (hD : 0 < D) (h : PieceOK T depth j sn sd tn td A B E D)
    (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι)
    (hi : (AltE (2 / 9) two_ninths_pos Fr depth).Adm i) (p : ℕ)
    (hs : ⌊(mkPiece sn sd tn td A B E D).s * (F5.scale i : ℝ)⌋₊ < p)
    (ht : p ≤ ⌊(mkPiece sn sd tn td A B E D).t * (F5.scale i : ℝ)⌋₊) (hp : p.Prime)
    (hk : R0 ≤ i.1 → 5 * (fifthsInst T).cd.kq p = j * p + u) [Fact p.Prime] :
    ∃ n : ℕ, GLE p n ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) ∧
      (n : ℝ) ≤ (mkPiece sn sd tn td A B E D).α * (F5.scale i : ℝ) +
        (mkPiece sn sd tn td A B E D).β * p + (mkPiece sn sd tn td A B E D).C := by
  have hsc : F5.scale i = i.1 := rfl
  rw [hsc, floor_mk_s] at hs
  rw [hsc, floor_mk_t] at ht
  obtain ⟨n, hn, hb⟩ := h i hi p hs ht hp hk
  refine ⟨n, hn, ?_⟩
  rw [hsc]
  exact real_of_int_bound (x := n) (r := i.1) (p := p) D A B E hD hb

/-- The cover of a (real) template piece `P` by member prices at the primes with pole index `j`. -/
def CovP {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth j : ℕ) (P : Piece) : Prop :=
  ∀ i : (AltE (2 / 9) two_ninths_pos Fr depth).ι, (AltE (2 / 9) two_ninths_pos Fr depth).Adm i →
    ∀ p : ℕ, ⌊P.s * (F5.scale i : ℝ)⌋₊ < p → p ≤ ⌊P.t * (F5.scale i : ℝ)⌋₊ → p.Prime →
      (R0 ≤ i.1 → 5 * (fifthsInst T).cd.kq p = j * p + u) → ∀ [Fact p.Prime],
        ∃ n : ℕ, GLE p n ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) ∧
          (n : ℝ) ≤ P.α * (F5.scale i : ℝ) + P.β * p + P.C

theorem covP_mk {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth j sn sd tn td : ℕ)
    (A B E D : ℤ) (hD : 0 < D) (h : PieceOK T depth j sn sd tn td A B E D) :
    CovP T depth j (mkPiece sn sd tn td A B E D) :=
  fun i hi p hs ht hp hk _ => covAt_mk T depth j sn sd tn td A B E D hD h i hi p hs ht hp hk

/-! ### Closed-form kinds -/

section Kinds
variable {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ)

theorem shift_twoTerm {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) : TwoTermData Fr 5 u where
  o_pos := T.hu0
  o_lt := T.hu1
  delta_eq t ht := by
    rw [T.delta t (by omega), cast_linear T.hu1 (by omega)]
    norm_num
  dsq_eq t ht := by
    rw [T.dsq t (by omega), cast_linear T.hu1 (by omega)]
    norm_num

theorem shift_norm {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) : Fr.norm = 25 := by
  rw [T.norm_eq]; norm_num

theorem XGm_D3_fifths (r m p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (hm : 2 * m < p) (hu : p ≤ r) :
    XGm (fifthsInst T) r m p ≤ 2 * r + m :=
  val_D3 p r m (lev := (fifthsInst T).lev) hp.one_lt.le
    (fun c hc => (fifths_levels T).high p c hp.one_lt.le hc) hm hu

/-- The member constraints used by the integer statements. -/
theorem member_dom {i : (AltE (2 / 9) two_ninths_pos Fr depth).ι}
    (hi : (AltE (2 / 9) two_ninths_pos Fr depth).Adm i) :
    i.1 % 2 = 0 ∧ 2 * i.1 ≤ 18 * F5.borderSize i.1 + 9 ∧ 18 * F5.borderSize i.1 ≤ 2 * i.1 + 8 :=
  ⟨hi.2, (border_bounds5 hi.2).1, (border_bounds5 hi.2).2⟩

theorem low_of {sn sd r p : ℕ} (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (h1 : sn * r / sd < p) : r < 900 * p := by
  have h3 : sn * r < p * sd := (Nat.div_lt_iff_lt_mul hsd).1 h1
  have h4 : sn * r < sn * (900 * p) :=
    lt_of_lt_of_le h3 (by nlinarith)
  exact Nat.lt_of_mul_lt_mul_left h4

/-- M3D: `m3_general` for gap indices `n0, n1, n3`. -/
theorem pieceOK_m3 (hcF : cFr Fr ≤ 49) (n0 n1 n3 j sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (hE : D * 2600000000 ≤ E) (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (hint : ∀ r p m k : ℕ, R0 ≤ r → 2 * r ≤ 18 * m + 9 → 18 * m ≤ 2 * r + 8 → 1 ≤ u → u < 5 →
      5 * k = j * p + u → sn * r / sd < p → p ≤ tn * r / td → m ≤ p ∧
      D * (((2 * r + 2 * m : ℕ) : ℤ) - ((min (min ((n0 + 1) * p) ((n1 + 1) * p + k))
              (min (r + (n3 + 1) * p) (min (r + 2 * m) (r + p))) -
        max (max (n0 * p) (n1 * p + k)) (max (r + n3 * p) (max r (r + 2 * m - p))) : ℕ) : ℤ)) ≤
        A * (r : ℤ) + B * (p : ℤ) + E) :
    PieceOK T depth j sn sd tn td A B E D := by
  refine pieceOK_of T depth hcF j sn sd tn td A B E D hD hE hnn ?_
  intro i hi hR p h1 h2 hp hk hpf
  obtain ⟨hr, hb1, hb2⟩ := member_dom depth hi
  have hu0 : 1 ≤ u := T.hu0
  have hu1 : u < 5 := T.hu1
  have hlow : i.1 < 900 * p := low_of hsd h900 h1
  have hp7 : 7 ≤ p := by unfold R0 at hR; omega
  have hsq := hsq_of5 hR hb2 hlow
  obtain ⟨hmp, hineq⟩ := hint i.1 p (F5.borderSize i.1) _ hR hb1 hb2 hu0 hu1 hk h1 h2
  obtain ⟨n, hn, hle⟩ := m3_general (shift_twoTerm T) (shift_norm T) depth i hi p hp7 hsq hmp
    ((fifthsInst T).cd.kq p) j (by omega) n0 n1 n3
  refine ⟨n, hn, ?_⟩
  exact le_trans (mul_le_mul_of_nonneg_left hle hD.le) hineq

/-- Generic reduction for the table-T kinds: some `b ≥ XGm` is below the line. -/
theorem pieceOK_T (hcF : cFr Fr ≤ 49) (j sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (hE : D * 2600000000 ≤ E) (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (bound : ∀ (r m p : ℕ), p.Prime → R0 ≤ r → 7 ≤ p → 2 * r ≤ 18 * m + 9 → 18 * m ≤ 2 * r + 8 →
      5 * (fifthsInst T).cd.kq p = j * p + u → sn * r / sd < p → p ≤ tn * r / td →
      ∃ b : ℤ, (XGm (fifthsInst T) r m p : ℤ) ≤ b ∧ D * b ≤ A * (r : ℤ) + B * (p : ℤ) + E) :
    PieceOK T depth j sn sd tn td A B E D := by
  refine pieceOK_of T depth hcF j sn sd tn td A B E D hD hE hnn ?_
  intro i hi hR p h1 h2 hp hk hpf
  obtain ⟨hr, hb1, hb2⟩ := member_dom depth hi
  have hlow : i.1 < 900 * p := low_of hsd h900 h1
  have hp7 : 7 ≤ p := by unfold R0 at hR; omega
  have hsq := hsq_of5 hR hb2 hlow
  have hr1 : 1 ≤ i.1 := by unfold R0 at hR; omega
  have hg := fifths_T_gle T depth i hr hr1 p hp7 hsq
  obtain ⟨b, hb, hDb⟩ := bound i.1 (F5.borderSize i.1) p hp hR hp7 hb1 hb2 hk h1 h2
  refine ⟨_, hg, ?_⟩
  calc D * (XGm (fifthsInst T) i.1 (F5.borderSize i.1) p : ℤ) ≤ D * b :=
        mul_le_mul_of_nonneg_left hb hD.le
    _ ≤ _ := hDb

/-- Sawtooth kind (`XGm_D1x`), with `m = q p + s0` and `q ∈ {q0, q0+1, q0+2}`. -/
theorem pieceOK_saw (hcF : cFr Fr ≤ 49) (q0 j sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (hE : D * 2600000000 ≤ E) (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (hint : ∀ r p m : ℕ, R0 ≤ r → 2 * r ≤ 18 * m + 9 → 18 * m ≤ 2 * r + 8 →
      sn * r / sd < p → p ≤ tn * r / td → (q0 * p ≤ m ∧ m < (q0 + 3) * p) ∧
      ∀ s0 : ℕ, s0 < p → (m = q0 * p + s0 ∨ m = (q0 + 1) * p + s0 ∨ m = (q0 + 2) * p + s0) →
        D * (((2 * r + 2 * m - min s0 (p - s0) : ℕ)) : ℤ) ≤ A * (r : ℤ) + B * (p : ℤ) + E) :
    PieceOK T depth j sn sd tn td A B E D := by
  refine pieceOK_T T depth hcF j sn sd tn td A B E D hD hE hsd h900 hnn ?_
  intro r m p hp hR hp7 hb1 hb2 hk h1 h2
  have h := XGm_D1x (fifthsInst T) r m p hp (by omega)
  obtain ⟨⟨hq1, hq2⟩, hmain⟩ := hint r p m hR hb1 hb2 h1 h2
  have hp0 : 0 < p := hp.pos
  have hdm := Nat.div_add_mod m p
  have hlt : m % p < p := Nat.mod_lt _ hp0
  have hq3 : q0 ≤ m / p := (Nat.le_div_iff_mul_le hp0).2 hq1
  have hq4 : m / p < q0 + 3 := (Nat.div_lt_iff_lt_mul hp0).2 hq2
  refine ⟨((2 * r + 2 * m - min (m % p) (p - m % p) : ℕ) : ℤ), by exact_mod_cast h, ?_⟩
  apply hmain _ hlt
  have : m / p = q0 ∨ m / p = q0 + 1 ∨ m / p = q0 + 2 := by omega
  rcases this with h0 | h0 | h0
  · left; rw [h0] at hdm; rw [← hdm]; ring
  · right; left; rw [h0] at hdm; rw [← hdm]; ring
  · right; right; rw [h0] at hdm; rw [← hdm]; ring

/-- Kind `D3` (`2 m < p ≤ r`): `XGm ≤ 2 r + m`. -/
theorem pieceOK_D3 (hcF : cFr Fr ≤ 49) (j sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (hE : D * 2600000000 ≤ E) (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (hint : ∀ r p m k : ℕ, R0 ≤ r → 2 * r ≤ 18 * m + 9 → 18 * m ≤ 2 * r + 8 → 1 ≤ u → u < 5 →
      5 * k = j * p + u → sn * r / sd < p → p ≤ tn * r / td → (2 * m < p ∧ p ≤ r) ∧
      D * ((2 * r + m : ℕ) : ℤ) ≤ A * (r : ℤ) + B * (p : ℤ) + E) :
    PieceOK T depth j sn sd tn td A B E D := by
  refine pieceOK_T T depth hcF j sn sd tn td A B E D hD hE hsd h900 hnn ?_
  intro r m p hp hR hp7 hb1 hb2 hk h1 h2
  obtain ⟨⟨hm, hpr⟩, hmain⟩ := hint r p m _ hR hb1 hb2 T.hu0 T.hu1 hk h1 h2
  have h := XGm_D3_fifths T r m p hp hp7 hm hpr
  exact ⟨((2 * r + m : ℕ) : ℤ), by exact_mod_cast h, hmain⟩

/-- Kind `D45` (`r < p`, `2 m ≤ r`). -/
theorem pieceOK_D45 (hcF : cFr Fr ≤ 49) (j sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (hE : D * 2600000000 ≤ E) (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (hint : ∀ r p m k : ℕ, R0 ≤ r → 2 * r ≤ 18 * m + 9 → 18 * m ≤ 2 * r + 8 → 1 ≤ u → u < 5 →
      5 * k = j * p + u → sn * r / sd < p → p ≤ tn * r / td → (r < p ∧ 2 * m ≤ r) ∧
      D * ((2 * (r - k) + 2 * m + (2 * m - (p - r)) : ℕ) : ℤ) ≤ A * (r : ℤ) + B * (p : ℤ) + E) :
    PieceOK T depth j sn sd tn td A B E D := by
  refine pieceOK_T T depth hcF j sn sd tn td A B E D hD hE hsd h900 hnn ?_
  intro r m p hp hR hp7 hb1 hb2 hk h1 h2
  obtain ⟨⟨hrp, hmr⟩, hmain⟩ := hint r p m _ hR hb1 hb2 T.hu0 T.hu1 hk h1 h2
  have h := XGm_D45_good (fifths_levels T) r m p hp hp7 hrp hmr
  exact ⟨((2 * (r - (fifthsInst T).cd.kq p) + 2 * m + (2 * m - (p - r)) : ℕ) : ℤ),
    by exact_mod_cast h, hmain⟩

/-- Kind `D6` (`r + 2 m ≤ p`, `r ≤ k`). -/
theorem pieceOK_D6 (hcF : cFr Fr ≤ 49) (j sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (hE : D * 2600000000 ≤ E) (hsd : 0 < sd) (h900 : sd ≤ 900 * sn)
    (hnn : ∀ r p : ℕ, sn * r / sd < p → p ≤ tn * r / td → 0 ≤ A * (r : ℤ) + B * (p : ℤ))
    (hint : ∀ r p m k : ℕ, R0 ≤ r → 2 * r ≤ 18 * m + 9 → 18 * m ≤ 2 * r + 8 → 1 ≤ u → u < 5 →
      5 * k = j * p + u → sn * r / sd < p → p ≤ tn * r / td → (r + 2 * m ≤ p ∧ r ≤ k) ∧
      D * ((2 * m - (k - r) : ℕ) : ℤ) ≤ A * (r : ℤ) + B * (p : ℤ) + E) :
    PieceOK T depth j sn sd tn td A B E D := by
  refine pieceOK_T T depth hcF j sn sd tn td A B E D hD hE hsd h900 hnn ?_
  intro r m p hp hR hp7 hb1 hb2 hk h1 h2
  obtain ⟨⟨hN, hkr⟩, hmain⟩ := hint r p m _ hR hb1 hb2 T.hu0 T.hu1 hk h1 h2
  have h := XGm_D6_good (fifths_levels T) r m p hp hp7 hN hkr
  exact ⟨((2 * m - ((fifthsInst T).cd.kq p - r) : ℕ) : ℤ), by exact_mod_cast h, hmain⟩

end Kinds

#print axioms pieceOK_m3
#print axioms pieceOK_saw
#print axioms pieceOK_D6
end CatalanCore.Uniform.Bank.FifthsContent
