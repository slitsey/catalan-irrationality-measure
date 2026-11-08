module

public import CatalanCore.Uniform.Bank.Plane2.Const
public import CatalanCore.Uniform.Bank.Halves.Geom
public import CatalanCore.Uniform.Content.Sweep.RowP1
public import CatalanCore.Uniform.Content.Sweep.CellsB
public import CatalanCore.Uniform.Content.Shape.Alt
public import CatalanCore.Uniform.Content.BankShared.Reindex

@[expose] public section
set_option Elab.async false

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

/-!
# ζ(3) content side, rows applied to the family (lane H, wave Z2; ledger Z03, Z04)

The member `(r, S)` of the Löwner family of the one-term datum on the halves geometry is the determinant of
`seqFullN (fS 1 0) (eS 1 0)` with window rows `r + 2 i` and columns `r + 2 i + 1`.  This module applies the
sweep rows `B1`, `B2`, `B4`, `E1`, `P1` (generic in `u`, here `u = 0`) to it and states them as explicit natural
number exponents, with the integer parts (`⌊r/p⌋`, `⌊2m/p⌋`) as numerals so that the pieces of the content
cover are linear implications closed by `omega` (`Zeta3Data.*`).
-/

namespace CatalanCore.Uniform.Bank.Plane2

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Bank.Halves
  CatalanCore.Uniform.Content.BankShared

/-- The member polynomial of `(r, S)`. -/
noncomputable abbrev zQ (r : ℕ) (S : Finset (FH.geometry r).C) : ℚ[X] :=
  SeqFamily.poly zeta3Datum.f zeta3Datum.e FH.geometry ⟨r, S⟩

/-- The member is the determinant of `seqFullN (fS 1 0) (eS 1 0)` on the window nodes. -/
theorem zQ_eq (r : ℕ) (hr : r % 2 = 0) (S : Finset (FH.geometry r).C) :
    zQ r S = (seqFullN (fS 1 0) (eS 1 0) (fun a : S => ((a.1 : (FH.geometry r).C) : ℕ))
      (fun i : Fin (FH.geometry r).k => r + 2 * (i : ℕ))
      (fun i : Fin (FH.geometry r).k => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  have hs : HybShape FH r := FH_hyb hr
  have hx : (FH.geometry r).xs = fun i : Fin (FH.geometry r).k => r + 2 * (i : ℕ) := funext hs.xs_eq
  have hy : (FH.geometry r).ys = fun i : Fin (FH.geometry r).k => r + 2 * (i : ℕ) + 1 := funext hs.ys_eq
  unfold zQ SeqFamily.poly
  rw [zeta3Datum_f, zeta3Datum_e, hx, hy]

theorem zQ_inj (r : ℕ) (hr : r % 2 = 0) (S : Finset (FH.geometry r).C) :
    Function.Injective (fun a : S => ((a.1 : (FH.geometry r).C) : ℕ)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem zQ_lt (r : ℕ) (hr : r % 2 = 0) (S : Finset (FH.geometry r).C) (a : S) :
    ((a.1 : (FH.geometry r).C) : ℕ) < r := hybShape_lt_scale (FH_hyb hr) a.1

/-- Row `B1` on the family: `3 (r + m) - ‖m‖_p`. -/
theorem zrow_B1 {r p m : ℕ} [Fact p.Prime] (hr : r % 2 = 0) (S : Finset (FH.geometry r).C)
    (hm : (FH.geometry r).k = m) (hp5 : 5 ≤ p) (hN : 2 * (r + 2 * m) < p * p) :
    GLE p (3 * (r + m) - min (m % p) (p - m % p)) (zQ r S) := by
  subst hm
  rw [zQ_eq r hr S]
  exact row_B1 (v := 1) _ (zQ_inj r hr S) (zQ_lt r hr S) hN hp5

/-- Row `B2` on the family (`p ≤ r`): `6 (r + m - p)`. -/
theorem zrow_B2 {r p m : ℕ} [Fact p.Prime] (hr : r % 2 = 0) (S : Finset (FH.geometry r).C)
    (hm : (FH.geometry r).k = m) (hp5 : 5 ≤ p) (hN : 2 * (r + 2 * m) < p * p) (hpr : p ≤ r) :
    GLE p (6 * (r + m - p)) (zQ r S) := by
  subst hm
  rw [zQ_eq r hr S]
  exact row_B2 (v := 1) hp5 _ (zQ_inj r hr S) (zQ_lt r hr S) hN hpr

/-- Row `B4` on the family (`r ≤ p`): `3 (r + 2 m - p)`. -/
theorem zrow_B4 {r p m : ℕ} [Fact p.Prime] (hr : r % 2 = 0) (S : Finset (FH.geometry r).C)
    (hm : (FH.geometry r).k = m) (hp5 : 5 ≤ p) (hN : 2 * (r + 2 * m) < p * p) (hpr : r ≤ p) :
    GLE p (3 * (r + 2 * m - p)) (zQ r S) := by
  subst hm
  rw [zQ_eq r hr S]
  exact row_B4 (v := 1) hp5 _ (zQ_inj r hr S) (zQ_lt r hr S) hN hpr

/-! ### Two periods: the weight table and its duals -/

/-- A node of `[b p, b p + 2 p)` lies in period `b` below `(b+1) p` and in period `b + 1` above. -/
theorem per_div {p b s : ℕ} (hb1 : b * p ≤ s) (hb2 : s < b * p + 2 * p) :
    s / p = if s < b * p + p then b else b + 1 := by
  have e1 : (b + 1) * p = b * p + p := by ring
  have e2 : (b + 1 + 1) * p = b * p + 2 * p := by ring
  split_ifs with h
  · exact Nat.div_eq_of_lt_le hb1 (by rw [Nat.add_mul, Nat.one_mul]; exact h)
  · exact Nat.div_eq_of_lt_le (by rw [e1]; omega) (by rw [e2]; exact hb2)

/-- The dual inequality on the two periods meeting a window of length at most `p` starting at `r`. -/
theorem w3B_two {p b r t t' a1 a2 c1 c2 : ℕ} (hb1 : b * p ≤ r) (hb2 : r < b * p + p)
    (ht : r ≤ t) (ht2 : t < r + p) (ht' : r ≤ t') (ht'2 : t' < r + p)
    (h1 : 2 ≤ a1 + c2) (h2 : 2 ≤ a2 + c1) :
    w3B p t t' ≤ (if t < b * p + p then a1 else a2) + (if t' < b * p + p then c1 else c2) := by
  have d1 := per_div (p := p) (b := b) (s := t) (by omega) (by omega)
  have d2 := per_div (p := p) (b := b) (s := t') (by omega) (by omega)
  unfold w3B
  rw [d1, d2]
  split_ifs <;> omega

/-- Sum of a two-valued function over `range m`, rows `r + 2 i < T`. -/
theorem sum_range_lt (a c m K : ℕ) :
    ∑ i ∈ Finset.range m, (if 2 * i < K then a else c) =
      a * min m ((K + 1) / 2) + c * (m - min m ((K + 1) / 2)) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : 2 * n < K
    · have h1 : min (n + 1) ((K + 1) / 2) = n + 1 := by omega
      have h2 : min n ((K + 1) / 2) = n := by omega
      rw [if_pos h, h1, h2]; simp [Nat.sub_self]; ring
    · have h1 : min (n + 1) ((K + 1) / 2) = (K + 1) / 2 := by omega
      have h2 : min n ((K + 1) / 2) = (K + 1) / 2 := by omega
      rw [if_neg h, h1, h2]
      have : n + 1 - (K + 1) / 2 = n - (K + 1) / 2 + 1 := by omega
      rw [this]; ring

/-- The same for the columns `r + 2 j + 1 < T`. -/
theorem sum_range_lt' (a c m K : ℕ) :
    ∑ i ∈ Finset.range m, (if 2 * i + 1 < K then a else c) =
      a * min m (K / 2) + c * (m - min m (K / 2)) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : 2 * n + 1 < K
    · have h1 : min (n + 1) (K / 2) = n + 1 := by omega
      have h2 : min n (K / 2) = n := by omega
      rw [if_pos h, h1, h2]; simp [Nat.sub_self]; ring
    · have h1 : min (n + 1) (K / 2) = K / 2 := by omega
      have h2 : min n (K / 2) = K / 2 := by omega
      rw [if_neg h, h1, h2]
      have : n + 1 - K / 2 = n - K / 2 + 1 := by omega
      rw [this]; ring

/-- Sum of a two-valued function over `Ico lo hi`. -/
theorem sum_Ico_two (a c T lo hi : ℕ) :
    ∑ t ∈ Finset.Ico lo hi, (if t < T then a else c) =
      a * (min hi T - lo) + c * (hi - max lo T) := by
  by_cases hlh : lo ≤ hi
  · induction hi, hlh using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, ih]
      by_cases h : n < T
      · have h1 : min (n + 1) T - lo = (min n T - lo) + 1 := by omega
        have h2 : n + 1 - max lo T = n - max lo T := by omega
        rw [if_pos h, h1, h2]; ring
      · have h1 : min (n + 1) T - lo = min n T - lo := by omega
        have h2 : n + 1 - max lo T = (n - max lo T) + 1 := by omega
        rw [if_neg h, h1, h2]; ring
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    have h1 : min hi T - lo = 0 := by omega
    have h2 : hi - max lo T = 0 := by omega
    rw [h1, h2]; simp

/-- Row `E1` on the family, with the two-period dual `(U1, V1 | U2, V2)`. -/
theorem zrow_E1 {r p m : ℕ} [Fact p.Prime] (hr : r % 2 = 0) (S : Finset (FH.geometry r).C)
    (hm : (FH.geometry r).k = m) (hp5 : 5 ≤ p) (hm2 : 2 * m < p)
    (hN : 2 * (r + 2 * m) + 2 * p < p * p) {b : ℕ} (hb1 : b * p ≤ r) (hb2 : r < b * p + p)
    (U1 V1 U2 V2 : ℕ) (h1 : 2 ≤ U1 + V2) (h2 : 2 ≤ U2 + V1) :
    GLE p (3 * r + (U1 * min m ((b * p + p - r + 1) / 2) + U2 * (m - min m ((b * p + p - r + 1) / 2))) +
      (V1 * min m ((b * p + p - r) / 2) + V2 * (m - min m ((b * p + p - r) / 2)))) (zQ r S) := by
  subst hm
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  rw [zQ_eq r hr S]
  have key := row_E1 (p := p) 1 0 (by
      intro h
      have : (p : ℤ) ∣ 1 := h
      have := Int.eq_one_of_dvd_one (by positivity) this
      have := (Fact.out : p.Prime).one_lt
      omega) hodd hp5 hm2 hN _ (zQ_inj r hr S) (zQ_lt r hr S)
    (fun i => if 2 * i < b * p + p - r then U1 else U2)
    (fun j => if 2 * j + 1 < b * p + p - r then V1 else V2) (by
      intro i j hi hj
      rw [w3_zero]
      have := w3B_two (p := p) (b := b) (r := r) (t := r + 2 * i) (t' := r + 2 * j + 1)
        (a1 := U1) (a2 := U2) (c1 := V1) (c2 := V2) hb1 hb2 (by omega) (by omega) (by omega)
        (by omega) h1 h2
      have e1 : (r + 2 * i < b * p + p) ↔ (2 * i < b * p + p - r) := by omega
      have e2 : (r + 2 * j + 1 < b * p + p) ↔ (2 * j + 1 < b * p + p - r) := by omega
      simp only [e1, e2] at this
      exact this)
  rw [sum_range_lt, sum_range_lt'] at key
  exact key

theorem p_odd_of_prime {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) : p % 2 = 1 := by
  rcases hp.out.eq_two_or_odd with h | h
  · omega
  · exact h

theorem not_dvd_one (p : ℕ) [hp : Fact p.Prime] : ¬ (p : ℤ) ∣ 1 := by
  intro h
  have := Int.eq_one_of_dvd_one (by positivity) h
  have := hp.out.one_lt
  omega

/-- Row `P1` on the family, band `k = 2 k2` (`E = [r, r + s)`), dual `(W1 | W2)` on the two periods. -/
theorem zrow_P1e0 {r p m : ℕ} [Fact p.Prime] (hr : r % 2 = 0) (S : Finset (FH.geometry r).C)
    (hm : (FH.geometry r).k = m) (hp5 : 5 ≤ p) (hN : 2 * (r + 2 * m) + 2 * p < p * p)
    {b k2 : ℕ} (hb1 : b * p ≤ r) (hb2 : r < b * p + p) (hk0 : 1 ≤ k2)
    (hk1 : 2 * (k2 * p) ≤ 2 * m) (hk2 : 2 * m < 2 * (k2 * p) + p) (W1 W2 : ℕ) (hW : 2 ≤ W1 + W2) :
    GLE p (3 * (r + m) - 3 * (m - k2 * p) +
      (W1 * (min (r + (2 * m - 2 * (k2 * p))) (b * p + p) - r) +
        W2 * (r + (2 * m - 2 * (k2 * p)) - max r (b * p + p)))) (zQ r S) := by
  subst hm
  have hodd := p_odd_of_prime (p := p) hp5
  rw [zQ_eq r hr S]
  set m := (FH.geometry r).k with hmdef
  have hkp : p ≤ k2 * p := Nat.le_mul_of_pos_left p hk0
  have hq : 2 * m / p = 2 * k2 := by
    apply Nat.div_eq_of_lt_le
    · have : 2 * k2 * p = 2 * (k2 * p) := by ring
      omega
    · have : (2 * k2 + 1) * p = 2 * (k2 * p) + p := by ring
      omega
  have hs : 2 * m % p = 2 * m - 2 * (k2 * p) := by
    have := Nat.div_add_mod (2 * m) p
    rw [hq] at this
    have e : p * (2 * k2) = 2 * (k2 * p) := by ring
    omega
  have hP1E : P1E p r m = Finset.Ico r (r + (2 * m - 2 * (k2 * p))) := by
    unfold P1E
    rw [hq, hs]
    have : (2 * k2) % 2 = 0 := by omega
    simp [this]
  have hm1 : m / p = k2 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have : (k2 + 1) * p = k2 * p + p := by ring
      omega
  have hmod : m % p = m - k2 * p := by
    have := Nat.div_add_mod m p
    rw [hm1] at this
    have e : p * k2 = k2 * p := by ring
    omega
  have hmin : min (m % p) (p - m % p) = m - k2 * p := by omega
  have key := row_P1 (p := p) 1 0 (not_dvd_one p) hodd hp5 (by omega) hN _ (zQ_inj r hr S) (zQ_lt r hr S)
    (fun t => if t < b * p + p then W1 else W2) (by
      intro t ht t' ht'
      rw [hP1E, Finset.mem_Ico] at ht ht'
      rw [w3_zero]
      exact w3B_two (p := p) (b := b) (r := r) (t := t) (t' := t') (a1 := W1) (a2 := W2) (c1 := W1) (c2 := W2)
        hb1 hb2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  rw [hP1E, sum_Ico_two, hmin] at key
  exact key

/-- Row `P1` on the family, band `k = 2 k2 + 1` (`E = [r + s, r + p)`). -/
theorem zrow_P1e1 {r p m : ℕ} [Fact p.Prime] (hr : r % 2 = 0) (S : Finset (FH.geometry r).C)
    (hm : (FH.geometry r).k = m) (hp5 : 5 ≤ p) (hN : 2 * (r + 2 * m) + 2 * p < p * p)
    {b k2 : ℕ} (hb1 : b * p ≤ r) (hb2 : r < b * p + p)
    (hk1 : 2 * (k2 * p) + p ≤ 2 * m) (hk2 : 2 * m < 2 * (k2 * p) + 2 * p) (W1 W2 : ℕ) (hW : 2 ≤ W1 + W2) :
    GLE p (3 * (r + m) - 3 * (k2 * p + p - m) +
      (W1 * (min (r + p) (b * p + p) - (r + (2 * m - (2 * (k2 * p) + p)))) +
        W2 * (r + p - max (r + (2 * m - (2 * (k2 * p) + p))) (b * p + p)))) (zQ r S) := by
  subst hm
  have hodd := p_odd_of_prime (p := p) hp5
  rw [zQ_eq r hr S]
  set m := (FH.geometry r).k with hmdef
  have hq : 2 * m / p = 2 * k2 + 1 := by
    apply Nat.div_eq_of_lt_le
    · have : (2 * k2 + 1) * p = 2 * (k2 * p) + p := by ring
      omega
    · have : (2 * k2 + 1 + 1) * p = 2 * (k2 * p) + 2 * p := by ring
      omega
  have hs : 2 * m % p = 2 * m - (2 * (k2 * p) + p) := by
    have := Nat.div_add_mod (2 * m) p
    rw [hq] at this
    have e : p * (2 * k2 + 1) = 2 * (k2 * p) + p := by ring
    omega
  have hP1E : P1E p r m = Finset.Ico (r + (2 * m - (2 * (k2 * p) + p))) (r + p) := by
    unfold P1E
    rw [hq, hs]
    have : ¬ (2 * k2 + 1) % 2 = 0 := by omega
    simp [this]
  have hm1 : m / p = k2 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have : (k2 + 1) * p = k2 * p + p := by ring
      omega
  have hmod : m % p = m - k2 * p := by
    have := Nat.div_add_mod m p
    rw [hm1] at this
    have e : p * k2 = k2 * p := by ring
    omega
  have hmin : min (m % p) (p - m % p) = k2 * p + p - m := by omega
  have key := row_P1 (p := p) 1 0 (not_dvd_one p) hodd hp5 (by omega) hN _ (zQ_inj r hr S) (zQ_lt r hr S)
    (fun t => if t < b * p + p then W1 else W2) (by
      intro t ht t' ht'
      rw [hP1E, Finset.mem_Ico] at ht ht'
      rw [w3_zero]
      exact w3B_two (p := p) (b := b) (r := r) (t := t) (t' := t') (a1 := W1) (a2 := W2) (c1 := W1) (c2 := W2)
        hb1 hb2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  rw [hP1E, sum_Ico_two, hmin] at key
  exact key

end CatalanCore.Uniform.Bank.Plane2
