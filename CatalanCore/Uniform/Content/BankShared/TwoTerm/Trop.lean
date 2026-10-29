import CatalanCore.Uniform.Content.BankShared.TwoTerm.Class
import CatalanCore.Uniform.Content.BankShared.Reindex
import CatalanCore.Uniform.Content.BankShared.AltCrude
import CatalanCore.Uniform.Content.BankShared.BudgetAdd
import CatalanCore.Rect.MinorContent
import CatalanFrames.HybGen.TropGood
import CatalanFrames.HybGen.TableSum
import CatalanFrames.HybGen.NumerologyAny
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Table T, tail and prefix for every two-term bank (lane C4, gap C4)

The tropical layer is stated over an arbitrary hybrid instance `I : HybInst Fr` of the frame (the
instance carries `q`, the norm and the bad primes) with the arithmetic data `ArithmeticInfo I Lc cm`
and, where the pole index enters, the level facts `LevelFacts I Gd (c < kq)`.  The geometry is
`altGeom c` at even scales.

* `kq_eq_poleIndex` (**class map for the instance**, C3): if `Φ(k) = k (q k - o)`, the first root
  `kq p` is the pole index of the root class: `q · kq p = j p + o` with `j = rootClass`.
* `trop_gle`: every member is `p ^ tropExp`-integral (any prime).
* `T_gle`: one level only (`Lc N < p²`, `p` not bad): `p ^ XGm`-integral.
* `T_gle_D1`, `T_gle_D1x`, `T_gle_D2`, `T_gle_D3`, `T_gle_D45`, `T_gle_D6`: the six branches of
  table T as clearing exponents (`D2` at its optimal `u₀ = k + p - r`).
* `tail_gle`: `q N < p + o + q` gives exponent `0` (branch D6).
* `pre_gle`: below `t1 r`, the exponent is at most `α₀ r + X r p`, `X` the data-free budget
  `sqrtLog A C + unit`, for every good prime; `pre_crude` and `pre_gle_any` add the bad primes
  through the crude exponent. -/

namespace CatalanCore.Uniform.Content.BankShared.TwoTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanCore.Rect

variable {Fr : Frame}

/-! ### Instance facts -/

/-- `BadInfo` (the old numerology) gives the arithmetic data. -/
theorem arith_of_bad {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) : ArithmeticInfo I Lc cm :=
  ⟨B.L_eq, B.Ebd_le, B.cOf_le⟩

/-- A good prime is not bad. -/
theorem not_bad_of_levels {I : HybInst Fr} {Gd : ℕ → Prop} {Z : ℕ → ℕ → Prop}
    (Lv : LevelFacts I Gd Z) {p : ℕ} (hp : p.Prime) (hG : Gd p) : p ∉ I.cd.bad :=
  fun h => (Lv.good p hp hG).2 p h dvd_rfl

/-- **Class map for the instance.**  If `Φ(k) = k (q k - o)` and `kq p` is attained (`0 < kq p`,
`p ∣ Φ(kq p)`), then `kq p` is the pole index of the root class `j = (q - o) p⁻¹ mod q`. -/
theorem kq_eq_poleIndex (cd : ContentData Fr) {q o : ℕ} (hPhi : ∀ k, cd.Phi k = k * (q * k - o))
    (ho0 : 0 < o) (hoq : o < q) {p : ℕ} (hp : p.Prime) (hqp : q < p) (hb : ∀ b ∈ cd.bad, ¬ b ∣ p)
    (hatt : 0 < cd.kq p ∧ p ∣ cd.Phi (cd.kq p)) :
    cd.kq p = poleIndex q (q - o) p ∧ q * cd.kq p = rootClass q (q - o) p * p + o := by
  obtain ⟨hs, hj0, hjq, hk0, hkp⟩ := rootClass_spec hp (a := q - o) (by omega) (by omega) hqp
  rw [show q - (q - o) = o by omega] at hs
  -- `kq p ≤ k < p` for the pole index `k`
  have hdk : p ∣ cd.Phi (poleIndex q (q - o) p) := by
    rw [hPhi]
    exact Dvd.dvd.mul_left ⟨rootClass q (q - o) p, by rw [Nat.mul_comm p]; omega⟩ _
  have hle := (cd.kq_le p _ hp.isPrimePow hb hk0 hdk).1
  -- `p ∣ q kq - o`
  have hd : p ∣ q * cd.kq p - o := by
    have h := hatt.2
    rw [hPhi] at h
    rcases hp.dvd_mul.1 h with h1 | h1
    · exact absurd (Nat.le_of_dvd hatt.1 h1) (by omega)
    · exact h1
  obtain ⟨j', hj'⟩ := hd
  have hqk : o ≤ q * cd.kq p := le_trans hoq.le (Nat.le_mul_of_pos_right q hatt.1)
  have hk' : q * cd.kq p = j' * p + o := by rw [Nat.mul_comm j' p]; omega
  have hj'q : j' < q := by
    by_contra hge
    push Not at hge
    have h1 : q * p ≤ j' * p := Nat.mul_le_mul_right p hge
    have h2 : q * cd.kq p < q * p := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  have hu := rootClass_unique hp (a := q - o) (by omega) (by omega) hqp hj'q
    (by rw [show q - (q - o) = o by omega]; exact hk')
  exact ⟨hu.2, by rw [hk', hu.1]⟩

/-! ### The tropical bridge -/

/-- Every member is `p ^ tropExp`-integral (any prime `p`, even `r`). -/
theorem trop_gle (I : HybInst Fr) [∀ r m, I.DiagOK r m] (c : ℚ) (hc : 0 < c) (depth : ℕ)
    (i : ((altGeom c hc).family Fr depth).ι) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime] :
    GLE p (tropExp I i.1 ((altGeom c hc).borderSize i.1) p)
      (((altGeom c hc).family Fr depth).Q i) := by
  obtain ⟨r, S⟩ := i
  have hQ := altGeom_member_commonMinor c hc Fr depth hr S
  have hG := commonMinorPoly_gle I p r ((altGeom c hc).borderSize r)
    (retainedFin (altGeom_hybShape c hc hr) S)
  exact hQ ▸ hG

/-- **Table T bridge.**  One level only (`Lc N < p²`) and `p` not bad: every member is
`p ^ XGm`-integral, `XGm = tropVal (HW lev p r m)`. -/
theorem T_gle (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc cm : ℕ} (B : ArithmeticInfo I Lc cm)
    (c : ℚ) (hc : 0 < c) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [Fact p.Prime] (hnb : p ∉ I.cd.bad)
    (hsq : Lc * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p) :
    GLE p (XGm I i.1 ((altGeom c hc).borderSize i.1) p) (((altGeom c hc).family Fr depth).Q i) := by
  have hG := trop_gle I c hc depth i hr p
  have hpp : p.Prime := Fact.out
  have hcnt : cntG I i.1 ((altGeom c hc).borderSize i.1) p = 0 := by
    apply cntG_zero _ _ _ _ hpp
    rw [B.L_eq, pow_two]
    exact hsq
  have hle := tropExp_le_arithmetic B i.1 ((altGeom c hc).borderSize i.1) p hr1 hpp
  rw [if_neg hnb, hcnt] at hle
  simp only [if_neg hnb, Nat.cast_zero, mul_zero, add_zero, zero_add] at hle
  have hle' : tropExp I i.1 ((altGeom c hc).borderSize i.1) p ≤
      XGm I i.1 ((altGeom c hc).borderSize i.1) p := by
    unfold XGm
    exact_mod_cast hle
  exact hG.mono hle'

/-! ### The six branches of table T -/

section Branches

variable (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc cm : ℕ} (B : ArithmeticInfo I Lc cm)
  (c : ℚ) (hc : 0 < c) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
  (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [Fact p.Prime] (hnb : p ∉ I.cd.bad)
  (hsq : Lc * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p)
include B hr hr1 hnb hsq

/-- Branch D1: `2 (r + m)`. -/
theorem T_gle_D1 :
    GLE p (2 * (i.1 + (altGeom c hc).borderSize i.1)) (((altGeom c hc).family Fr depth).Q i) :=
  (T_gle I B c hc depth i hr hr1 p hnb hsq).mono (XGm_D1 I _ _ _)

/-- Branch D1x (the sawtooth): `2 r + 2 m - δ_p(m)`, `p` odd. -/
theorem T_gle_D1x (h2 : p ≠ 2) :
    GLE p (2 * i.1 + 2 * (altGeom c hc).borderSize i.1 -
      min ((altGeom c hc).borderSize i.1 % p) (p - (altGeom c hc).borderSize i.1 % p))
      (((altGeom c hc).family Fr depth).Q i) :=
  (T_gle I B c hc depth i hr hr1 p hnb hsq).mono (XGm_D1x I _ _ _ Fact.out h2)

/-- Branch D3: `2 r + m` on `2 m < p ≤ r`. -/
theorem T_gle_D3 {Gd : ℕ → Prop} (Lv : LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (hm : 2 * (altGeom c hc).borderSize i.1 < p) (hpr : p ≤ i.1) :
    GLE p (2 * i.1 + (altGeom c hc).borderSize i.1) (((altGeom c hc).family Fr depth).Q i) :=
  (T_gle I B c hc depth i hr hr1 p hnb hsq).mono
    (val_D3 p i.1 _ (lev := I.lev) (Fact.out : p.Prime).one_lt.le
      (fun c' hc' => Lv.high p c' (Fact.out : p.Prime).one_lt.le hc') hm hpr)

/-- Branch D2 at its optimal `u₀ = k + p - r`: `2 (r - u₀) + 2 m + min(u₀, 2 m)` on
`2 m < p ≤ r`, `k ≤ r` (`k = kq p`). -/
theorem T_gle_D2 {Gd : ℕ → Prop} (Lv : LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (hG : Gd p) (hm : 2 * (altGeom c hc).borderSize i.1 < p) (hpr : p ≤ i.1)
    (hk : I.cd.kq p ≤ i.1) :
    GLE p (2 * (i.1 - (I.cd.kq p + p - i.1)) + 2 * (altGeom c hc).borderSize i.1 +
      min (I.cd.kq p + p - i.1) (2 * (altGeom c hc).borderSize i.1))
      (((altGeom c hc).family Fr depth).Q i) := by
  obtain ⟨u, L, h1, h2, h3, h4, h5⟩ := XGm_D2_good Lv i.1 ((altGeom c hc).borderSize i.1) p
    Fact.out hG hm hpr hk
  refine (T_gle I B c hc depth i hr hr1 p hnb hsq).mono (h5.trans ?_)
  omega

/-- Branch D45: `2 (r - k) + 2 m + (2 m - (p - r))` on `r < p`, `2 m ≤ r`. -/
theorem T_gle_D45 {Gd : ℕ → Prop} (Lv : LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (hG : Gd p) (hrp : i.1 < p) (hmr : 2 * (altGeom c hc).borderSize i.1 ≤ i.1) :
    GLE p (2 * (i.1 - I.cd.kq p) + 2 * (altGeom c hc).borderSize i.1 +
      (2 * (altGeom c hc).borderSize i.1 - (p - i.1))) (((altGeom c hc).family Fr depth).Q i) :=
  (T_gle I B c hc depth i hr hr1 p hnb hsq).mono
    (XGm_D45_good Lv i.1 _ p Fact.out hG hrp hmr)

/-- Branch D6: `2 m - (k - r)` on `r + 2 m ≤ p`, `r ≤ k`. -/
theorem T_gle_D6 {Gd : ℕ → Prop} (Lv : LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (hG : Gd p) (hN : i.1 + 2 * (altGeom c hc).borderSize i.1 ≤ p) (hk : i.1 ≤ I.cd.kq p) :
    GLE p (2 * (altGeom c hc).borderSize i.1 - (I.cd.kq p - i.1))
      (((altGeom c hc).family Fr depth).Q i) :=
  (T_gle I B c hc depth i hr hr1 p hnb hsq).mono
    (XGm_D6_good Lv i.1 _ p Fact.out hG hN hk)

end Branches

/-! ### Tail -/

/-- **Tail.**  With the pole index `q · kq p = j p + o` (`j ≥ 1`, `o < q`, `Lc ≤ q ≤ p`, `p ≥ 3`,
`p` good; needed only at scales `r ≥ 1`) and `q N < p + o + q` (`N = r + 2 m`), every member is
`p`-integral (exponent `0`): branch D6. -/
theorem tail_gle (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc cm : ℕ} (B : ArithmeticInfo I Lc cm)
    {Gd : ℕ → Prop} (Lv : LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hr : i.1 % 2 = 0) {q o j : ℕ} (hLq : Lc ≤ q) (hoq : o < q) (p : ℕ) [hp : Fact p.Prime]
    (hbig : 1 ≤ i.1 → Gd p ∧ q ≤ p ∧ 3 ≤ p ∧ q * I.cd.kq p = j * p + o) (hj : 1 ≤ j)
    (h : q * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p + o + q) :
    GLE p 0 (((altGeom c hc).family Fr depth).Q i) := by
  rcases Nat.eq_zero_or_pos i.1 with h0 | hr1
  · have := altGeom_gle_Ecrude c hc hc1 Fr depth i hr p
    have h00 : Ecrude (cFr Fr) i.1 p = 0 := by simp [Ecrude, h0]
    rw [h00] at this
    exact this
  obtain ⟨hG, hqp, hp3, hk⟩ := hbig hr1
  have hjp : p ≤ j * p := Nat.le_mul_of_pos_left p hj
  -- `N ≤ k`
  have hNk : i.1 + 2 * (altGeom c hc).borderSize i.1 ≤ I.cd.kq p := by
    have h1 : q * (i.1 + 2 * (altGeom c hc).borderSize i.1) < q * (I.cd.kq p + 1) := by
      rw [mul_add_one]; omega
    have := Nat.lt_of_mul_lt_mul_left h1
    omega
  -- `N ≤ p`
  have hNp : i.1 + 2 * (altGeom c hc).borderSize i.1 ≤ p := by
    by_contra hc'
    push Not at hc'
    have h1 : q * (p + 1) ≤ q * (i.1 + 2 * (altGeom c hc).borderSize i.1) :=
      Nat.mul_le_mul_left q hc'
    rw [mul_add_one] at h1
    have h2 : (o + 1) * p ≤ q * p := Nat.mul_le_mul_right p hoq
    rw [add_one_mul] at h2
    have h3 : o ≤ o * p := Nat.le_mul_of_pos_right o hp.out.pos
    omega
  -- one level only
  have hsq : Lc * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p := by
    have h1 : Lc * (i.1 + 2 * (altGeom c hc).borderSize i.1) ≤
        q * (i.1 + 2 * (altGeom c hc).borderSize i.1) := Nat.mul_le_mul_right _ hLq
    have h2 : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp3
    omega
  have hgl := T_gle_D6 I B c hc depth i hr hr1 p (not_bad_of_levels Lv hp.out hG) hsq Lv hG hNp
    (by omega)
  exact hgl.mono (by omega)

/-! ### Prefix -/

theorem log2_mul_pow (r e : ℕ) (hr : r ≠ 0) : Nat.log 2 (r * 2 ^ e) = Nat.log 2 r + e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, ← mul_assoc,
      Nat.log_mul_base (by norm_num) (Nat.mul_ne_zero hr (pow_ne_zero _ (by norm_num))), ih]
    ring

/-- **Prefix, good primes** (`p ∉ bad`, `p ≤ r`).  With the bank inequalities `Lc N ≤ A r`,
`Lc N ≤ 2^e r`, `2 (r + m) e ≤ C r`, `2 (r + m) ≤ C r` and `2 (r + m) ≤ α₀ r + 1`, some clearing
exponent is at most `α₀ r + X r p`, `X` the budget `sqrtLog A C + unit`. -/
theorem pre_gle (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc cm : ℕ} (B : ArithmeticInfo I Lc cm)
    (c : ℚ) (hc : 0 < c) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [hp : Fact p.Prime] (hnb : p ∉ I.cd.bad)
    (A C e : ℕ) (α0 : ℝ)
    (hA : Lc * (i.1 + 2 * (altGeom c hc).borderSize i.1) ≤ A * i.1)
    (he : Lc * (i.1 + 2 * (altGeom c hc).borderSize i.1) ≤ i.1 * 2 ^ e)
    (hC1 : 2 * (i.1 + (altGeom c hc).borderSize i.1) * e ≤ C * i.1)
    (hC2 : 2 * (i.1 + (altGeom c hc).borderSize i.1) ≤ C * i.1)
    (h0 : 2 * ((i.1 : ℝ) + (altGeom c hc).borderSize i.1) ≤ α0 * i.1 + 1) (hpr : p ≤ i.1) :
    ∃ n : ℕ, GLE p n (((altGeom c hc).family Fr depth).Q i) ∧
      (n : ℝ) ≤ α0 * i.1 + (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit).X i.1 p := by
  have hG := trop_gle I c hc depth i hr p
  refine ⟨_, hG, ?_⟩
  set r := i.1 with hrdef
  set m := (altGeom c hc).borderSize r with hmdef
  have hX : (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit).X r p =
      (SmallBudget.sqrtLog A C).X r p + 1 := by
    show (SmallBudget.sqrtLog A C).X r p + SmallBudget.unit.X r p = _
    congr 1
    simp [SmallBudget.unit, SmallBudget.ofCutoff, hpr]
  have hX0 := (SmallBudget.sqrtLog A C).nonneg r p
  have hle := tropExp_le_arithmetic B r m p hr1 hp.out
  rw [if_neg hnb] at hle
  simp only [if_neg hnb, zero_add] at hle
  have hD1 : XGm I r m p ≤ 2 * (r + m) := XGm_D1 _ _ _ _
  have hXG : (tropVal (HW I.lev p r m) : ℝ) ≤ 2 * ((r : ℝ) + m) := by
    have : tropVal (HW I.lev p r m) ≤ 2 * (r + m) := hD1
    exact_mod_cast this
  rw [hX]
  by_cases hsq : p * p ≤ A * r
  · rw [SmallBudget.sqrtLog_X_of A C r p hsq]
    have hcnt := cntG_le I r m p hp.out
    rw [B.L_eq] at hcnt
    have hlog : Nat.log 2 (Lc * (r + 2 * m)) ≤ Nat.log 2 r + e := by
      rw [← log2_mul_pow r e (by omega)]
      exact Nat.log_mono_right he
    have hcn : 2 * (r + m) * cntG I r m p ≤ C * r * (Nat.log 2 r + 1) := by
      have h1 : 2 * (r + m) * cntG I r m p ≤ 2 * (r + m) * (Nat.log 2 r + e) :=
        Nat.mul_le_mul_left _ (hcnt.trans hlog)
      have h2 : 2 * (r + m) * Nat.log 2 r ≤ C * r * Nat.log 2 r := Nat.mul_le_mul_right _ hC2
      calc 2 * (r + m) * cntG I r m p ≤ 2 * (r + m) * (Nat.log 2 r + e) := h1
        _ = 2 * (r + m) * Nat.log 2 r + 2 * (r + m) * e := by ring
        _ ≤ C * r * Nat.log 2 r + C * r := Nat.add_le_add h2 hC1
        _ = C * r * (Nat.log 2 r + 1) := by ring
    have hcn' : ((2 * (r + m) * cntG I r m p : ℕ) : ℝ) ≤ (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
      have h := (Nat.cast_le (α := ℝ)).2 hcn
      have e : ((C * r * (Nat.log 2 r + 1) : ℕ) : ℝ) = (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
        push_cast; ring
      rw [e] at h
      exact h
    linarith
  · push Not at hsq
    have hz : cntG I r m p = 0 := by
      apply cntG_zero _ _ _ _ hp.out
      rw [B.L_eq, pow_two]
      omega
    rw [hz] at hle
    simp only [mul_zero, Nat.cast_zero, zero_add] at hle
    linarith

/-- `Ecrude cE r p ≤ 2 (cE + 12) r (log₂ r + 1)` for every `p ≥ 2`. -/
theorem Ecrude_log (cE r p : ℕ) (hp : 2 ≤ p) :
    Ecrude cE r p ≤ 2 * (cE + 12) * r * (Nat.log 2 r + 1) := by
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0; simp [Ecrude]
  unfold Ecrude
  have h1 : Nat.log p (14 * r) ≤ Nat.log 2 r + 4 := by
    refine (Nat.log_anti_left (by omega) hp).trans ?_
    have hL : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by omega) r
    have : Nat.log 2 (14 * r) < Nat.log 2 r + 5 := by
      refine Nat.log_lt_of_lt_pow (by omega) ?_
      have h16 : 14 * r < 2 ^ (Nat.log 2 r + 5) := by
        have : 2 ^ (Nat.log 2 r + 5) = 16 * 2 ^ (Nat.log 2 r + 1) := by ring
        rw [this]; omega
      exact h16
    omega
  have h3 : 3 * Nat.log 2 r ≤ (cE + 12) * Nat.log 2 r := Nat.mul_le_mul_right _ (by omega)
  have h2 : 3 * Nat.log p (14 * r) + cE ≤ (cE + 12) * (Nat.log 2 r + 1) := by
    have : (cE + 12) * (Nat.log 2 r + 1) = (cE + 12) * Nat.log 2 r + (cE + 12) := by ring
    omega
  calc 2 * r * (3 * Nat.log p (14 * r) + cE) ≤ 2 * r * ((cE + 12) * (Nat.log 2 r + 1)) :=
        Nat.mul_le_mul_left _ h2
    _ = 2 * (cE + 12) * r * (Nat.log 2 r + 1) := by ring

/-- **Prefix, any prime with `p² ≤ A r`**, by the crude exponent (`cFr Fr ≤ cE`,
`2 (cE + 12) ≤ C`, `c ≤ 1`). -/
theorem pre_crude (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (depth : ℕ)
    (i : ((altGeom c hc).family Fr depth).ι) (hr : i.1 % 2 = 0) (p : ℕ) [hp : Fact p.Prime]
    (A C cE : ℕ) (α0 : ℝ) (hα0 : 0 ≤ α0) (hcE : cFr Fr ≤ cE) (hC : 2 * (cE + 12) ≤ C)
    (hsq : p * p ≤ A * i.1) (hpr : p ≤ i.1) :
    ∃ n : ℕ, GLE p n (((altGeom c hc).family Fr depth).Q i) ∧
      (n : ℝ) ≤ α0 * i.1 + (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit).X i.1 p := by
  refine ⟨_, altGeom_gle_Ecrude c hc hc1 Fr depth i hr p, ?_⟩
  have hX : (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit).X i.1 p =
      (C : ℝ) * i.1 * ((Nat.log 2 i.1 : ℝ) + 1) + 1 := by
    show (SmallBudget.sqrtLog A C).X i.1 p + SmallBudget.unit.X i.1 p = _
    rw [SmallBudget.sqrtLog_X_of A C i.1 p hsq]
    congr 1
    simp [SmallBudget.unit, SmallBudget.ofCutoff, hpr]
  have hE := Ecrude_log (cFr Fr) i.1 p hp.out.two_le
  have hE2 : 2 * (cFr Fr + 12) * i.1 * (Nat.log 2 i.1 + 1) ≤ C * i.1 * (Nat.log 2 i.1 + 1) := by
    have : 2 * (cFr Fr + 12) ≤ C := le_trans (by omega) hC
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
  have hE' : ((Ecrude (cFr Fr) i.1 p : ℕ) : ℝ) ≤ (C : ℝ) * i.1 * ((Nat.log 2 i.1 : ℝ) + 1) := by
    have : Ecrude (cFr Fr) i.1 p ≤ C * i.1 * (Nat.log 2 i.1 + 1) := hE.trans hE2
    exact_mod_cast this
  rw [hX]
  have : (0 : ℝ) ≤ α0 * i.1 := mul_nonneg hα0 (Nat.cast_nonneg _)
  linarith

/-- **Prefix, every prime `p ≤ r`**: good primes by `pre_gle`, bad primes (`p² ≤ A r`) by the
crude exponent. -/
theorem pre_gle_any (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc cm : ℕ}
    (B : ArithmeticInfo I Lc cm) (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (depth : ℕ)
    (i : ((altGeom c hc).family Fr depth).ι) (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ)
    [hp : Fact p.Prime] (A C e cE : ℕ) (α0 : ℝ) (hα0 : 0 ≤ α0) (hcE : cFr Fr ≤ cE)
    (hC : 2 * (cE + 12) ≤ C) (hbad : p ∈ I.cd.bad → p * p ≤ A * i.1)
    (hA : Lc * (i.1 + 2 * (altGeom c hc).borderSize i.1) ≤ A * i.1)
    (he : Lc * (i.1 + 2 * (altGeom c hc).borderSize i.1) ≤ i.1 * 2 ^ e)
    (hC1 : 2 * (i.1 + (altGeom c hc).borderSize i.1) * e ≤ C * i.1)
    (hC2 : 2 * (i.1 + (altGeom c hc).borderSize i.1) ≤ C * i.1)
    (h0 : 2 * ((i.1 : ℝ) + (altGeom c hc).borderSize i.1) ≤ α0 * i.1 + 1) (hpr : p ≤ i.1) :
    ∃ n : ℕ, GLE p n (((altGeom c hc).family Fr depth).Q i) ∧
      (n : ℝ) ≤ α0 * i.1 + (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit).X i.1 p := by
  by_cases hb : p ∈ I.cd.bad
  · exact pre_crude c hc hc1 depth i hr p A C cE α0 hα0 hcE hC (hbad hb) hpr
  · exact pre_gle I B c hc depth i hr hr1 p hb A C e α0 hA he hC1 hC2 h0 hpr

end CatalanCore.Uniform.Content.BankShared.TwoTerm
