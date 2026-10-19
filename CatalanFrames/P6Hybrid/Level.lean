module

public import CatalanCore.Arith.Hybrid.ExactLev
public import CatalanFrames.P6.Content
public import CatalanFrames.HybCommon.Numer

@[expose] public section

/-!
# The P6 hybrid level instance (`HybInst.ofExact`)

`p6Inst r m := HybInst.ofExact p6CD (p6dok r m) …`: the exact-class level of the generic constructor
`ExactLev.lean`, with the diagonal used only at the positions `c < r` and the border `r + 2 m`.  P6
supplies only

* the two p-adic bounds `p6_hD`, `p6_hD2` (denominators `k (3k-2) (2k-1)`, `L = 3`);
* the numerology `p6_badInfo r m : BadInfo (p6Inst r m) 3 2` (the cubic `Ebd` bound fails for `Ebd N = Φ`,
  but `Ebd N = 3 N` is enough);
* the two level facts used by the Z-regime count: `p6_lev_zero_low` (`A < kq6 p`) and
  `p6_lev_zero_win` (class `1`, window `[(p+1)/2, p)`, off the diagonal set).
-/

open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

/-- The positions whose diagonal entry is used by `Full r m`, and the border corner. -/
def p6dok (r m c : ℕ) : Prop := c < r ∨ c = r + 2 * m

lemma fact_le_of_lt {p E n : ℕ} (hp : p.Prime) (hn : 0 < n) (h : n < p ^ (E + 1)) :
    n.factorization p ≤ E := by
  have h1 : p ^ (n.factorization p) ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
  have h2 : p ^ (n.factorization p) < p ^ (E + 1) := lt_of_le_of_lt h1 h
  have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h2
  omega

lemma pw_mem_lt (p : ℕ) [hp : Fact p.Prime] {E n : ℕ} (hn : 0 < n) (h : n < p ^ (E + 1)) :
    ((p : ℚ) ^ E / (n : ℚ)) ∈ LocRing p :=
  pw_mem p hn (fact_le_of_lt hp.out hn h)

/-- `p^E Δ_k ∈ ℤ_(p)` for `3 N < p^{E+1}`, `1 ≤ k ≤ N`. -/
lemma p6_hD (p : ℕ) [Fact p.Prime] (E N k : ℕ) (hE : 3 * N < p ^ (E + 1)) (hk : 1 ≤ k)
    (hkN : k ≤ N) : (p : ℚ) ^ E * p6Frame.Delta k ∈ LocRing p := by
  have e : (p : ℚ) ^ E * p6Frame.Delta k = (p : ℚ) ^ E / (k : ℚ) +
      6 * ((p : ℚ) ^ E / ((3 * k - 2 : ℕ) : ℚ)) - 6 * ((p : ℚ) ^ E / ((2 * k - 1 : ℕ) : ℚ)) := by
    rw [Delta_eq k hk, c3 (by omega), c2 (by omega)]; ring
  rw [e]
  have h6 := six_mem p
  refine (LocRing p).sub_mem ((LocRing p).add_mem (pw_mem_lt p (by omega) (by omega))
    ((LocRing p).mul_mem h6 (pw_mem_lt p (by omega) (by omega))))
    ((LocRing p).mul_mem h6 (pw_mem_lt p (by omega) (by omega)))

/-- `p^{2E} D_k ∈ ℤ_(p)` for `3 N < p^{E+1}`, `1 ≤ k ≤ N`. -/
lemma p6_hD2 (p : ℕ) [Fact p.Prime] (E N k : ℕ) (hE : 3 * N < p ^ (E + 1)) (hk : 1 ≤ k)
    (hkN : k ≤ N) : (p : ℚ) ^ (2 * E) * p6Frame.Dsq k ∈ LocRing p := by
  have e : (p : ℚ) ^ (2 * E) * p6Frame.Dsq k = ((p : ℚ) ^ E / (k : ℚ)) ^ 2 +
      18 * ((p : ℚ) ^ E / ((3 * k - 2 : ℕ) : ℚ)) ^ 2 -
        12 * ((p : ℚ) ^ E / ((2 * k - 1 : ℕ) : ℚ)) ^ 2 := by
    rw [Dsq_eq k hk, ← c3 (by omega : 0 < k), ← c2 (by omega : 0 < k), ← sq_pow_eq]
    generalize ((3 * k - 2 : ℕ) : ℚ) = x
    generalize ((2 * k - 1 : ℕ) : ℚ) = y
    ring
  rw [e]
  have h18 : (18 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (18 : ℤ)
  have h12 : (12 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (12 : ℤ)
  refine (LocRing p).sub_mem ((LocRing p).add_mem
    ((LocRing p).pow_mem (pw_mem_lt p (by omega) (by omega)) 2)
    ((LocRing p).mul_mem h18 ((LocRing p).pow_mem (pw_mem_lt p (by omega) (by omega)) 2)))
    ((LocRing p).mul_mem h12 ((LocRing p).pow_mem (pw_mem_lt p (by omega) (by omega)) 2))

/-- **The P6 hybrid instance** (exact-class levels; diagonal used on `p6dok r m`). -/
noncomputable def p6Inst (r m : ℕ) : HybInst p6Frame :=
  HybInst.ofExact p6CD (p6dok r m) p6_hD p6_hD2

instance p6Inst_diagOK (r m : ℕ) : (p6Inst r m).DiagOK r m := ⟨fun _ h => h⟩

lemma p6Inst_lev (r m q A : ℕ) : (p6Inst r m).lev q A = xlev p6Frame (p6dok r m) q A := rfl

/-- **The numerology** of the P6 instance: `L = 3`, `cOf ≤ 2`, `Ebd N + N = 4 N ≤ 5 N³`. -/
theorem p6_badInfo (r m : ℕ) : BadInfo (p6Inst r m) 3 2 where
  L_eq := rfl
  Lc_le := by norm_num
  cm_le := by norm_num
  Ebd_le := fun N => by
    show 3 * N + N ≤ 5 * N ^ 3
    rcases N with _ | N
    · simp
    · nlinarith [Nat.zero_le N, Nat.zero_le (N * N), Nat.zero_le (N * N * N)]
  two_mem := by show 2 ∈ ({2, 3} : Finset ℕ); simp
  bad_le := fun b hb => by
    have : b ∈ ({2, 3} : Finset ℕ) := hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  cOf_le := fun p => by
    show (36 : ℕ).factorization p ≤ 2
    have h36 : (36 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 2 := by
      have : (36 : ℕ) = 2 ^ 2 * 3 ^ 2 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three]
    rw [h36, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> omega

/-- **(Z0)** below the first singular index the level is `0`. -/
theorem p6_lev_zero_low {r m p A : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hA : A < kq6 p) :
    (p6Inst r m).lev p A = 0 :=
  ofExact_lev_zero_low p6CD (p6dok r m) p6_hD p6_hD2 hp
    (by show p ∉ ({2, 3} : Finset ℕ); simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
    hA

/-! ### (Z1): class-1 cancellation on the window `[(p+1)/2, p)` -/

section Window

variable {p : ℕ} [hpf : Fact p.Prime]

lemma unit_mem {n : ℕ} (hn : 0 < n) (hnd : ¬ p ∣ n) : (1 : ℚ) / (n : ℚ) ∈ LocRing p := by
  have := pow_div_mem (p := p) (n := n) (j := 0) hn
    (by rw [Nat.factorization_eq_zero_of_not_dvd hnd])
  simpa using this

lemma six_div_mem {n : ℕ} (hn : 0 < n) (hnd : ¬ p ∣ n) : 6 / (n : ℚ) ∈ LocRing p := by
  rw [div_eq_mul_one_div]
  exact (LocRing p).mul_mem (six_mem p) (unit_mem hn hnd)

/-- the `3k-2` term, with the `1/p` pole at `k = (p+2)/3` removed -/
lemma t3_mem (h1 : p % 6 = 1) {k : ℕ} (hk : 1 ≤ k) (hkp : k < p) :
    6 / ((3 * k - 2 : ℕ) : ℚ) - (if k = (p + 2) / 3 then 6 / (p : ℚ) else 0) ∈ LocRing p := by
  by_cases hk1 : k = (p + 2) / 3
  · have : 3 * k - 2 = p := by omega
    rw [if_pos hk1, this, sub_self]
    exact (LocRing p).zero_mem
  · rw [if_neg hk1, sub_zero]
    refine six_div_mem (by omega) ?_
    rintro ⟨j, hj⟩
    have hj3 : j < 3 := by
      by_contra h
      have := Nat.mul_le_mul_left p (not_lt.mp h)
      omega
    interval_cases j <;> omega

/-- the `2k-1` term, with the `1/p` pole at `k = (p+1)/2` removed -/
lemma t2_mem (h1 : p % 6 = 1) {k : ℕ} (hk : 1 ≤ k) (hkp : k < p) :
    6 / ((2 * k - 1 : ℕ) : ℚ) - (if k = (p + 1) / 2 then 6 / (p : ℚ) else 0) ∈ LocRing p := by
  by_cases hk1 : k = (p + 1) / 2
  · have : 2 * k - 1 = p := by omega
    rw [if_pos hk1, this, sub_self]
    exact (LocRing p).zero_mem
  · rw [if_neg hk1, sub_zero]
    refine six_div_mem (by omega) ?_
    rintro ⟨j, hj⟩
    have hj3 : j < 2 := by
      by_contra h
      have := Nat.mul_le_mul_left p (not_lt.mp h)
      omega
    interval_cases j <;> omega

/-- **(Z1)** `S(A) = ∑_{k ≤ A} Δ_k` is `p`-integral on the window `(p+1)/2 ≤ A < p`, `p ≡ 1 (6)`: the
two poles `6/p` (from `3k-2 = p` and `2k-1 = p`) cancel. -/
theorem p6_Sp_window (h1 : p % 6 = 1) {A : ℕ} (hA1 : (p + 1) / 2 ≤ A) (hA2 : A < p) :
    Sp p6Frame A ∈ LocRing p := by
  have hk1 : (p + 2) / 3 ∈ Icc 1 A := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hk2 : (p + 1) / 2 ∈ Icc 1 A := Finset.mem_Icc.mpr ⟨by omega, hA1⟩
  have hI1 : ∑ k ∈ Icc 1 A, (if k = (p + 2) / 3 then 6 / (p : ℚ) else 0) = 6 / (p : ℚ) := by
    rw [Finset.sum_ite_eq', if_pos hk1]
  have hI2 : ∑ k ∈ Icc 1 A, (if k = (p + 1) / 2 then 6 / (p : ℚ) else 0) = 6 / (p : ℚ) := by
    rw [Finset.sum_ite_eq', if_pos hk2]
  have e : Sp p6Frame A = ∑ k ∈ Icc 1 A, ((1 / (k : ℚ) +
      (6 / ((3 * k - 2 : ℕ) : ℚ) - (if k = (p + 2) / 3 then 6 / (p : ℚ) else 0))) -
      (6 / ((2 * k - 1 : ℕ) : ℚ) - (if k = (p + 1) / 2 then 6 / (p : ℚ) else 0))) +
      ((∑ k ∈ Icc 1 A, (if k = (p + 2) / 3 then 6 / (p : ℚ) else 0)) -
        ∑ k ∈ Icc 1 A, (if k = (p + 1) / 2 then 6 / (p : ℚ) else 0)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    unfold Sp
    refine Finset.sum_congr rfl fun k hk => ?_
    have := (Finset.mem_Icc.mp hk).1
    rw [Delta_eq k this, c3 (by omega), c2 (by omega)]; ring
  rw [e, hI1, hI2, sub_self, add_zero]
  refine (LocRing p).sum_mem fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  refine (LocRing p).sub_mem ((LocRing p).add_mem ?_ (t3_mem h1 hk'.1 (by omega)))
    (t2_mem h1 hk'.1 (by omega))
  exact unit_mem (by omega) (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)

end Window

/-- **(Z1)** class-1 cancellation: on the window `[(p+1)/2, p)` the level is `0` at the positions off
the diagonal set `p6dok r m` (the `D`-condition is vacuous there). -/
theorem p6_lev_zero_win {r m p A : ℕ} (hp : p.Prime) (h1 : p % 6 = 1) (hA1 : (p + 1) / 2 ≤ A)
    (hA2 : A < p) (hd : ¬ p6dok r m A) : (p6Inst r m).lev p A = 0 := by
  haveI := Fact.mk hp
  rw [p6Inst_lev]
  have e1 : p = p ^ 1 := (pow_one p).symm
  rw [e1, xlev_pow_zero_iff _ hp le_rfl]
  simp only [Nat.sub_self, pow_zero, one_pow, one_mul]
  exact ⟨(pint_iff p _).2 (p6_Sp_window h1 hA1 hA2), fun h => absurd h hd⟩

end CatalanFrames.P6Hybrid
