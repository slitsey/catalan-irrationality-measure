import CatalanCore.Uniform.Content.BankShared.TwoTerm.LP
import CatalanCore.Uniform.Content.BankShared.TwoTerm.M3D
import CatalanCore.Uniform.Content.BankShared.TwoTerm.UF
import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
import CatalanCore.Uniform.Bank.ThirdsContent.M3
import CatalanCore.Uniform.Bank.ThirdsContent.Edge
import CatalanCore.Uniform.Bank.FifthsContent.M3Gen
import CatalanFrames.Fifths.ContentHyb
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Audit of the generic two-term layer lemmas (lane C4)

Each `example` restates a bank-specialised statement of `Bank/ThirdsContent` or
`Bank/FifthsContent` (verbatim, at `q = 3`, norm `9`, slope `3/10`, or `q = 5`, norm `25`, slope
`2/9`) and proves it from the generic lemma of `BankShared.TwoTerm`.  The fifths statements whose
modules are currently out of date (`lp1_valid5`, `lp2_valid5`, `closedHyp5`, `fifths_T_gle`,
`tail5`, `pre5`) are restated without importing them.  The last two examples are the class map
(gap C3) on the actual thirds and fifths instances: the first root `kq p` is the pole index of the
root class `j = a p⁻¹ mod q`. -/

namespace CatalanCore.Uniform.Content.BankShared.TwoTerm.Audit
open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Uniform CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFSimple
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanFrames.HybCommon CatalanFrames.HybGen

/-! ### Thirds (`q = 3`, `o = e`, norm `9`, `G310 = altGeom (3/10)`) -/

section Thirds
open CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Bank.ThirdsContent CatalanFrames.Thirds

/-- `nocut_window3`. -/
example (p r a b o : ℕ) (hp : 0 < p) (n0 n1 K1 n3 : ℕ)
    (h0 : n0 * p ≤ a ∧ b ≤ (n0 + 1) * p)
    (h1 : n1 * p + o ≤ 3 * a ∧ 3 * b ≤ (n1 + K1 + 1) * p + o)
    (m1 : ∀ i : ℕ, 1 ≤ i → i ≤ K1 → ((n1 + i) * p + o) % 3 ≠ 0)
    (h3 : r + n3 * p ≤ a ∧ b ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r (ttSing p 3 o)) (min (x : ℤ) y) (max (x : ℤ) y) :=
  nocut_window p r a b 3 o hp (by norm_num) n0 n1 K1 n3 h0 h1 m1 h3

/-- `m3dValid_thirds`. -/
example {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (a b : ℕ → ℕ → ℕ) (r p : ℕ)
    (hr : r % 2 = 0) (hp5 : 5 ≤ p) (hN : 3 * (r + 2 * G310.borderSize r) < p * p)
    (hra : r ≤ a r p) (hab : a r p ≤ b r p) (hb1 : b r p ≤ r + 2 * G310.borderSize r)
    (hb2 : b r p ≤ r + p)
    (hj : max (a r p) (r + 2 * G310.borderSize r - p) ≤ b r p)
    (hcut : ∀ x y : ℕ, a r p ≤ x → x < b r p → a r p ≤ y → y < b r p →
      NoCut (Cut p r (ttSing p 3 e)) (min (x : ℤ) y) (max (x : ℤ) y)) :
    m3dValid G310 Fr a b r p :=
  m3dValid_tt (3 / 10) c310_pos (ThirdsData.twoTerm T) (nm := 3 * 3)
    (by rw [T.norm_eq]; norm_num) a b r p hr
    (fun hp => not_dvd_sq_of_lt hp (by norm_num) (by omega)) hN hra hab hb1 hb2 hj hcut

/-- `m3_gle`. -/
example {Fr : Frame} {depth : ℕ} (a b : ℕ → ℕ → ℕ) (i : (FamE Fr depth).ι)
    (hi : (FamE Fr depth).Adm i) (p : ℕ) [Fact p.Prime] (hv : m3dValid G310 Fr a b i.1 p) :
    GLE p (2 * i.1 + (2 * G310.borderSize i.1 -
      (b i.1 p - max (a i.1 p) (i.1 + 2 * G310.borderSize i.1 - p)))) ((FamE Fr depth).Q i) :=
  m3_gle_tt (Fr := Fr) (depth := depth) G310 a b i hi.1 p hv

/-- `thirds_trop_gle`. -/
example {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ)
    (i : (FamE Fr depth).ι) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime] :
    GLE p (tropExp (thirdsInst T) i.1 (G310.borderSize i.1) p) ((FamE Fr depth).Q i) :=
  trop_gle (thirdsInst T) (3 / 10) c310_pos depth i hr p

/-- `thirds_T_gle`. -/
example {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ)
    (i : (FamE Fr depth).ι) (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hsq : 3 * (i.1 + 2 * G310.borderSize i.1) < p * p) :
    GLE p (XGm (thirdsInst T) i.1 (G310.borderSize i.1) p) ((FamE Fr depth).Q i) :=
  T_gle (thirdsInst T) (arith_of_bad (thirds_badInfo T)).L_eq (3 / 10) c310_pos depth i hr hr1 p
    (not_bad_of_levels (thirds_levels T) Fact.out hp5) hsq

/-- `thirds_tail_gle`. -/
example {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ)
    (i : (FamE Fr depth).ι) (hi : (FamE Fr depth).Adm i) (p : ℕ) [hp : Fact p.Prime]
    (h : 4 * i.1 < p) : GLE p 0 ((FamE Fr depth).Q i) := by
  have hr2 : i.1 % 2 = 0 := hi.2
  have hb := altGeom_border_nat (3 / 10) c310_pos 3 10 (by norm_num) (by norm_num) hr2
  have he := T.he
  have key : ∀ j, 1 ≤ j → (1 ≤ i.1 → 3 * (thirdsInst T).cd.kq p = j * p + e) →
      GLE p 0 ((FamE Fr depth).Q i) := fun j hj hk =>
    tail_gle (thirdsInst T) (arith_of_bad (thirds_badInfo T)).L_eq (thirds_levels T) (3 / 10) c310_pos
      (by norm_num) depth i hr2 (q := 3) (o := e) (by norm_num) (by omega) p
      (fun h1 => ⟨by show 5 ≤ p; omega, by omega, by omega, hk h1⟩) hj (by omega)
  rcases Nat.eq_zero_or_pos i.1 with h0 | h0
  · exact key 1 le_rfl (fun h1 => by omega)
  · have h3 : p % 3 ≠ 0 := by
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp (Nat.dvd_of_mod_eq_zero h3)
      omega
    rcases thirds_kq_formula T (p := p) (by omega) h3 with ⟨-, hk⟩ | ⟨-, hk⟩
    · exact key 1 le_rfl (fun _ => by omega)
    · exact key 2 (by norm_num) (fun _ => by omega)

/-- `thirds_pre_gle`. -/
example {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ)
    (i : (FamE Fr depth).ι) (hi : (FamE Fr depth).Adm i) (p : ℕ) [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hpr : p ≤ 3 * i.1 / 1000) :
    ∃ n : ℕ, GLE p n ((FamE Fr depth).Q i) ∧
      (n : ℝ) ≤ 23 / 10 * (i.1 : ℝ) + thirdsBudget.X i.1 p := by
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hk1, hk2⟩ := altGeom_border_nat (3 / 10) c310_pos 3 10 (by norm_num) (by norm_num) hr2
  have hR : (10 : ℝ) * (2 * ((altGeom (3 / 10) c310_pos).borderSize i.1 : ℝ)) < 3 * i.1 + 10 := by
    exact_mod_cast hk2
  exact pre_gle (thirdsInst T) (arith_of_bad (thirds_badInfo T)).L_eq (3 / 10) c310_pos depth i hr2
    (by omega) p (not_bad_of_levels (thirds_levels T) hp.out hp5) 5 5 2 (23 / 10)
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)

/-- **Class map on the thirds instance** (C3): `kq p` is the pole index of the root class. -/
example {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (thirdsInst T).cd.kq p = poleIndex 3 (3 - e) p ∧
      3 * (thirdsInst T).cd.kq p = rootClass 3 (3 - e) p * p + e := by
  have he := T.he
  have hb := (thirds_good T hp hp5).2
  exact kq_eq_poleIndex (thirdsCD T) (fun _ => rfl) (by omega) (by omega) hp (by omega) hb
    (thirds_kq_att T p hp.isPrimePow hb)

end Thirds

/-! ### Fifths (`q = 5`, `o = u`, norm `25`, `F5 = altGeom (2/9)`) -/

section Fifths
open CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Bank.FifthsContent CatalanFrames.Fifths

/-- `nocut_window5`. -/
example (p r a b o : ℕ) (hp : 0 < p) (n0 n1 K1 n3 : ℕ)
    (h0 : n0 * p ≤ a ∧ b ≤ (n0 + 1) * p)
    (h1 : n1 * p + o ≤ 5 * a ∧ 5 * b ≤ (n1 + K1 + 1) * p + o)
    (m1 : ∀ i : ℕ, 1 ≤ i → i ≤ K1 → ((n1 + i) * p + o) % 5 ≠ 0)
    (h3 : r + n3 * p ≤ a ∧ b ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r (ttSing p 5 o)) (min (x : ℤ) y) (max (x : ℤ) y) :=
  nocut_window p r a b 5 o hp (by norm_num) n0 n1 K1 n3 h0 h1 m1 h3

/-- `nocut_window5k`. -/
example (p r a b o k : ℕ) (hp : 0 < p) (hk : (p : ℤ) ∣ 5 * (k : ℤ) - o)
    (hcop : IsCoprime (p : ℤ) 5) (n0 n1 n3 : ℕ)
    (h0 : n0 * p ≤ a ∧ b ≤ (n0 + 1) * p)
    (h1 : n1 * p + k ≤ a ∧ b ≤ (n1 + 1) * p + k)
    (h3 : r + n3 * p ≤ a ∧ b ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r (ttSing p 5 o)) (min (x : ℤ) y) (max (x : ℤ) y) :=
  nocut_window_k p r a b 5 o k hp (by exact_mod_cast hk) (by exact_mod_cast hcop) n0 n1 n3 h0 h1 h3

/-- `m3dValid_fifths`. -/
example {Fr : Frame} {o : ℕ} (T : TwoTermData Fr 5 o) (hnorm : Fr.norm = 25)
    (a b : ℕ → ℕ → ℕ) (r p : ℕ)
    (hr : r % 2 = 0) (hp7 : 7 ≤ p) (hN : 5 * (r + 2 * F5.borderSize r) < p * p)
    (hra : r ≤ a r p) (hab : a r p ≤ b r p) (hb1 : b r p ≤ r + 2 * F5.borderSize r)
    (hb2 : b r p ≤ r + p)
    (hj : max (a r p) (r + 2 * F5.borderSize r - p) ≤ b r p)
    (hcut : ∀ x y : ℕ, a r p ≤ x → x < b r p → a r p ≤ y → y < b r p →
      NoCut (Cut p r (ttSing p 5 o)) (min (x : ℤ) y) (max (x : ℤ) y)) :
    m3dValid F5 Fr a b r p :=
  m3dValid_tt (2 / 9) two_ninths_pos T (nm := 5 * 5) (by rw [hnorm]; norm_num) a b r p hr
    (fun hp => not_dvd_sq_of_lt hp (by norm_num) (by omega)) hN hra hab hb1 hb2 hj hcut

/-- `m3_gle5`. -/
example {Fr : Frame} {depth : ℕ} (a b : ℕ → ℕ → ℕ)
    (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι)
    (hi : (AltE (2 / 9) two_ninths_pos Fr depth).Adm i) (p : ℕ) [Fact p.Prime]
    (hv : m3dValid F5 Fr a b i.1 p) :
    GLE p (2 * i.1 + (2 * F5.borderSize i.1 -
      (b i.1 p - max (a i.1 p) (i.1 + 2 * F5.borderSize i.1 - p))))
      ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) :=
  m3_gle_tt (Fr := Fr) (depth := depth) F5 a b i hi.1 p hv

/-- `m3_general`. -/
example {Fr : Frame} {o : ℕ} (T : TwoTermData Fr 5 o) (hnorm : Fr.norm = 25)
    (depth : ℕ) (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι)
    (hi : (AltE (2 / 9) two_ninths_pos Fr depth).Adm i) (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hsq : 5 * (i.1 + 2 * F5.borderSize i.1) < p * p) (hmp : F5.borderSize i.1 ≤ p)
    (k j : ℕ) (hk : 5 * k = o + j * p) (n0 n1 n3 : ℕ) :
    ∃ n : ℕ, GLE p n ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) ∧
      (n : ℤ) ≤ ((2 * i.1 + 2 * F5.borderSize i.1 : ℕ) : ℤ) -
        ((min (min ((n0 + 1) * p) ((n1 + 1) * p + k))
              (min (i.1 + (n3 + 1) * p) (min (i.1 + 2 * F5.borderSize i.1) (i.1 + p))) -
          max (max (n0 * p) (n1 * p + k))
            (max (i.1 + n3 * p) (max i.1 (i.1 + 2 * F5.borderSize i.1 - p))) : ℕ) : ℤ) :=
  m3_general_tt (2 / 9) two_ninths_pos T (nm := 5 * 5) (by rw [hnorm]; norm_num) depth i hi.1
    hi.2 p (not_dvd_sq_of_lt Fact.out (by norm_num) (by omega)) (by omega) hsq hmp k j hk n0 n1 n3

/-- `lp1_valid5`. -/
example {Fr : Frame} {o : ℕ} (T : TwoTermData Fr 5 o) (hnorm : Fr.norm = 25)
    (r p k j : ℕ) (hr : r % 2 = 0) [Fact p.Prime] (hp10 : 10 ≤ p)
    (hk : 5 * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hN2 : r + 2 * F5.borderSize r ≤ 2 * p) (hrp : p ≤ r) (hUk : r < p + k) :
    lp1Valid F5 Fr 5 o (fun _ _ => k) (fun _ _ => j) r p :=
  lp1Valid_tt (2 / 9) two_ninths_pos T (nm := 5 * 5) (by rw [hnorm]; norm_num) r p k j hr
    (not_dvd_sq_of_lt Fact.out (by norm_num) (by omega)) (by omega) (by omega) hk hk0 hkp hj0
    hN2 hrp hUk

/-- `lp2_valid5`. -/
example {Fr : Frame} {o : ℕ} (T : TwoTermData Fr 5 o) (hnorm : Fr.norm = 25)
    (r p k j : ℕ) (hr : r % 2 = 0) [Fact p.Prime] (hp10 : 10 ≤ p)
    (hk : 5 * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hNk : r + 2 * F5.borderSize r ≤ p + k) (hrp : r < p) (hkr : k ≤ r)
    (hpm : p < r + F5.borderSize r) :
    lp2Valid F5 Fr 5 o (fun _ _ => k) (fun _ _ => j) r p :=
  lp2Valid_tt (2 / 9) two_ninths_pos T (nm := 5 * 5) (by rw [hnorm]; norm_num) r p k j hr
    (not_dvd_sq_of_lt Fact.out (by norm_num) (by omega)) (by omega) (by omega) hk hk0 hkp hj0
    hNk hrp hkr hpm

/-- `closedHyp5`. -/
example {Fr : Frame} {o : ℕ} (T : TwoTermData Fr 5 o) (hnorm : Fr.norm = 25)
    (r p K j : ℕ) [Fact p.Prime] (hr : r % 2 = 0) (hr0 : 0 < r)
    (hm1 : 1 ≤ F5.borderSize r) (hsq5 : 5 * (r + p) ≤ p * p) (hpm : 2 * F5.borderSize r ≤ p)
    (hp7 : 7 ≤ p) (hK : 5 * K = j * p + o) (hj0 : 0 < j) (hj5 : j < 5) :
    ClosedHyp (2 / 9) two_ninths_pos Fr 5 o r p K :=
  closedHyp_tt (2 / 9) two_ninths_pos T (nm := 5 * 5) (by rw [hnorm]; norm_num) r p K j hr hr0
    hm1 hsq5 hpm (not_dvd_sq_of_lt Fact.out (by norm_num) (by omega)) (by omega) (by omega) hK
    hj0 hj5

/-- `fifths_T_gle`. -/
example {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ)
    (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι) (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1)
    (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) (hsq : 5 * (i.1 + 2 * F5.borderSize i.1) < p * p) :
    GLE p (XGm (fifthsInst T) i.1 (F5.borderSize i.1) p)
      ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) :=
  T_gle (fifthsInst T) (fifths_arithmetic T).L_eq (2 / 9) two_ninths_pos depth i hr hr1 p
    (not_bad_of_levels (fifths_levels T) Fact.out hp7) hsq

/-- `tail5`. -/
example {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth j : ℕ) (hj : 1 ≤ j)
    (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι)
    (hi : (AltE (2 / 9) two_ninths_pos Fr depth).Adm i) (p : ℕ) (hp : p.Prime)
    (hk : 1 ≤ i.1 → 5 * (fifthsInst T).cd.kq p = j * p + u) (h : 63 * i.1 / 10 < p)
    [Fact p.Prime] :
    GLE p 0 ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) := by
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (2 / 9) two_ninths_pos 2 9 (by norm_num) (by norm_num) hr2
  have hu := T.hu1
  exact tail_gle (fifthsInst T) (fifths_arithmetic T).L_eq (fifths_levels T) (2 / 9) two_ninths_pos
    (by norm_num) depth i hr2 (q := 5) (o := u) (by norm_num) hu p
    (fun h1 => ⟨by show 7 ≤ p; omega, by omega, by omega, hk h1⟩) hj (by omega)

/-- `pre5` (budget `B5 = sqrtLog 7 122 + (unit + early R0 2600000000)`, `R0 = 10^7`). -/
example {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ)
    (hcF : CatalanCore.Uniform.Content.BankShared.cFr Fr ≤ 49)
    (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι)
    (hi : (AltE (2 / 9) two_ninths_pos Fr depth).Adm i) (p : ℕ) (hp : p.Prime)
    (h : p ≤ ⌊(1 / 900 : ℝ) * (F5.scale i : ℝ)⌋₊) [Fact p.Prime] :
    ∃ n : ℕ, GLE p n ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) ∧
      (n : ℝ) ≤ (20 / 9 : ℝ) * (F5.scale i : ℝ) +
        (SmallBudget.add (SmallBudget.sqrtLog 7 122)
          (SmallBudget.add SmallBudget.unit (SmallBudget.early (10 ^ 7) 2600000000))).X (F5.scale i) p := by
  have hsc : F5.scale i = i.1 := rfl
  rw [hsc]
  have h900 : 900 * p ≤ i.1 := by
    have h' := (Nat.le_floor_iff (by positivity)).1 h
    rw [hsc] at h'
    have : (900 * p : ℝ) ≤ i.1 := by linarith
    exact_mod_cast this
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (2 / 9) two_ninths_pos 2 9 (by norm_num) (by norm_num) hr2
  have hR : (9 : ℝ) * (2 * ((altGeom (2 / 9) two_ninths_pos).borderSize i.1 : ℝ)) < 2 * i.1 + 9 := by
    exact_mod_cast hb2
  have hbad : p ∈ (fifthsInst T).cd.bad → p * p ≤ 7 * i.1 := by
    intro hpb
    have hp5 : p ≤ 5 := by
      simp [fifthsInst, HybInst.ofSing, fifthsCD, badPrimes] at hpb
      omega
    have : p * p ≤ 5 * 5 := Nat.mul_le_mul hp5 hp5
    omega
  obtain ⟨n, hn, hle⟩ := pre_gle_any (fifthsInst T) (fifths_arithmetic T).L_eq (2 / 9) two_ninths_pos
    (by norm_num) depth i hr2 (by omega) p 7 122 3 49 (20 / 9) (by norm_num) hcF (by norm_num) hbad
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e1 : (SmallBudget.add (SmallBudget.sqrtLog 7 122) SmallBudget.unit).X i.1 p =
      (SmallBudget.sqrtLog 7 122).X i.1 p + SmallBudget.unit.X i.1 p := rfl
  have e2 : (SmallBudget.add (SmallBudget.sqrtLog 7 122)
      (SmallBudget.add SmallBudget.unit (SmallBudget.early (10 ^ 7) 2600000000))).X i.1 p =
      (SmallBudget.sqrtLog 7 122).X i.1 p +
        (SmallBudget.unit.X i.1 p + (SmallBudget.early (10 ^ 7) 2600000000).X i.1 p) := rfl
  have h0 := (SmallBudget.early (10 ^ 7) 2600000000).nonneg i.1 p
  rw [e1] at hle
  rw [e2]
  linarith

/-- **Class map on the fifths instance** (C3): `kq p` is the pole index of the root class. -/
example {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (fifthsInst T).cd.kq p = poleIndex 5 (5 - u) p ∧
      5 * (fifthsInst T).cd.kq p = rootClass 5 (5 - u) p * p + u := by
  have hu0 := T.hu0
  have hu1 := T.hu1
  have hb := (fifths_good T hp hp7).2
  exact kq_eq_poleIndex (fifthsCD T) (fun _ => rfl) (by omega) (by omega) hp (by omega) hb
    (fifths_kq_att T p hp.isPrimePow hb)

end Fifths

end CatalanCore.Uniform.Content.BankShared.TwoTerm.Audit

open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms rootClass_spec
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms rootClass_unique
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms rootClass_of_class
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms poleIndex_offset
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms kq_eq_poleIndex
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms lp1Hyp_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms lp2Hyp_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms lp1Valid_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms lp2Valid_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms lp1_gle_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms lp2_gle_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms nocut_window
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms nocut_window_k
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms nocut_of_gap
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms m3dValid_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms m3_gle_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms m3_gap_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms m3_general_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms closedHyp_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms uf_gle_tt
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms trop_gle
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms T_gle
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms T_gle_D1
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms T_gle_D1x
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms T_gle_D2
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms T_gle_D3
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms T_gle_D45
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms T_gle_D6
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms tail_gle
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms pre_gle
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms pre_crude
open CatalanCore.Uniform.Content.BankShared.TwoTerm in
#print axioms pre_gle_any
