module

public import CatalanCore.Uniform.Content.BankShared.Inst.Roots
public import CatalanFrames.Fifths.ContentLocal
public import CatalanFrames.HybGen.NumerologyAny

@[expose] public section
set_option Elab.async false

/-! # The generic frame instance of a two-term bank (lane C6L, gap C6)

For any frame `Fr` with `ShiftData Fr q u` (`q ≥ 2`, `1 ≤ u < q`: `Δ_k = 1/k - q/(q k - u)`, norm `q²`),
one content table and one hybrid instance, generalising `CatalanFrames.Fifths.Instance` (`q = 5`) and
`CatalanFrames.Thirds.Instance` (`q = 3`):

* `shift_toTwoTerm`, `shift_ofTwoTerm`: `ShiftData Fr q u` ↔ `TwoTermData Fr q u` with norm `q²`;
* `smallQ_ok`: the small-prime clearing at every bad prime (`small5_ok` at `q = 5`);
* `twoTermCD T : ContentData Fr`: `Φ(k) = k (q k - u)`, `L = q`, `normN = q²`, bad primes `badQ q`,
  `kq = poleIndex q (q - u)` (the class-map pole index), `small = smallQ q`;
* `twoTermInst T : HybInst Fr` (block valued, `Ebd N = N (q N - u)`), instance `DiagOK`;
* `twoTerm_levels`: `LevelFacts` with good primes `p > q` and zero set `c < kq`;
* `twoTerm_arithmetic`, `twoTerm_arithmetic_prime`, `twoTerm_arithmetic_small`: `ArithmeticInfo` with
  `Lc = q` (needs `Ebd N + N ≤ 5 N³`; true for `q ≤ u + 4`, `q ≤ 10`), `twoTerm_not_arithmetic`: false
  for `u + 4 < q` (at `N = 1`);
* the remaining hypotheses of `catValid_bank`: `twoTerm_norm`, `twoTerm_hP`, `twoTerm_hkq`;
  of `pre_gle_any`: `twoTerm_bad_le`. -/

namespace CatalanCore.Uniform.Content.BankShared.Inst
open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Basic
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanFrames.HybCommon CatalanFrames.HybGen
open CatalanFrames.Fifths (ShiftData cast_linear fifthsPower_mem fifthsMn_symm)

/-! ### `ShiftData` and `TwoTermData` -/

section Shift
variable {Fr : Frame} {q u : ℕ}

/-- `ShiftData` gives the two-term data (`o = u`). -/
theorem shift_toTwoTerm (T : ShiftData Fr q u) : TwoTermData Fr q u where
  o_pos := T.hu0
  o_lt := T.hu1
  delta_eq t ht := by
    rw [T.delta t (by omega), cast_linear (k := t) T.hu1 (by omega)]
  dsq_eq t ht := by
    rw [T.dsq t (by omega), cast_linear (k := t) T.hu1 (by omega)]

/-- Two-term data with norm `q²` give `ShiftData`. -/
theorem shift_ofTwoTerm (hq : 2 ≤ q) (T : TwoTermData Fr q u) (hn : Fr.norm = (q : ℚ) ^ 2) :
    ShiftData Fr q u where
  hM := hq
  hu0 := T.o_pos
  hu1 := T.o_lt
  norm_eq := hn
  delta k hk := by rw [T.delta_eq k hk, cast_linear T.o_lt hk]
  dsq k hk := by rw [T.dsq_eq k hk, cast_linear T.o_lt hk]

end Shift

/-! ### Local integrality at the bad primes -/

/-- `p^⌊log_p (q h)⌋ / n` is `p`-integral for `0 < n ≤ q h`. -/
theorem power_mem_q (p : ℕ) [Fact p.Prime] {q n h : ℕ} (hn : 0 < n) (hnh : n ≤ q * h) :
    ((p : ℚ) ^ Nat.log p (q * h) / (n : ℚ)) ∈ LocRing p :=
  fifthsPower_mem p hn (Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
    (le_trans (Nat.ordProj_le p hn.ne') hnh))

theorem natq_mem (p : ℕ) [Fact p.Prime] (n : ℕ) : (n : ℚ) ∈ LocRing p := by
  exact_mod_cast int_mem_locRing (ℓ := p) (n : ℤ)

section Local
variable {Fr : Frame} {q u : ℕ} (T : ShiftData Fr q u)

include T in
/-- Off-diagonal: `q² M(a, b) = (1/(b - a)) ∑_{a < k ≤ b} Δ_k`. -/
theorem qMn_lt {a b : ℕ} (hab : a < b) :
    (q : ℚ) ^ 2 * Fr.Mn a b = (1 / ((b : ℚ) - a)) * ∑ k ∈ Ioc a b, Fr.Delta k := by
  have hq : (q : ℚ) ^ 2 ≠ 0 := by
    have : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by have := T.hM; omega)
    exact pow_ne_zero 2 this.ne'
  unfold Frame.Mn
  rw [ite_eq_right hab.ne, max_eq_right hab.le, min_eq_left hab.le, T.norm_eq, ← mul_assoc, ← mul_assoc,
    mul_one_div_cancel hq, one_mul]

include T in
/-- Diagonal: `q² M(a, a) = -∑_{k ≤ a} D_k`. -/
theorem qMn_diag (a : ℕ) : (q : ℚ) ^ 2 * Fr.Mn a a = -∑ k ∈ Icc 1 a, Fr.Dsq k := by
  have hq : (q : ℚ) ^ 2 ≠ 0 := by
    have : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by have := T.hM; omega)
    exact pow_ne_zero 2 this.ne'
  unfold Frame.Mn
  rw [ite_eq_left rfl, T.norm_eq, ← mul_assoc, mul_neg, mul_one_div_cancel hq, neg_one_mul]

include T in
theorem qOff_mem (p : ℕ) [Fact p.Prime] {h a b : ℕ} (hab : a < b) (hbh : b < h) :
    ((p : ℚ) ^ Nat.log p (q * h)) ^ 2 * ((q : ℚ) ^ 2 * Fr.Mn a b) ∈ LocRing p := by
  set v : ℚ := (p : ℚ) ^ Nat.log p (q * h) with hv
  have hu := T.hu1
  have hq1 : 1 ≤ q := by have := T.hM; omega
  have hqh : h ≤ q * h := Nat.le_mul_of_pos_left h (by omega)
  have hs : ∑ k ∈ Ioc a b, Fr.Delta k =
      ∑ k ∈ Ioc a b, (1 / (k : ℚ) - (q : ℚ) / ((q * k - u : ℕ) : ℚ)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Ioc.mp hk).1; omega
    exact T.delta k hk0
  have e1 : ∑ k ∈ Ioc a b, (v / (k : ℚ) - (q : ℚ) * (v / ((q * k - u : ℕ) : ℚ))) =
      v * ∑ k ∈ Ioc a b, (1 / (k : ℚ) - (q : ℚ) / ((q * k - u : ℕ) : ℚ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key : v ^ 2 * ((q : ℚ) ^ 2 * Fr.Mn a b) =
      (v / ((b - a : ℕ) : ℚ)) *
        ∑ k ∈ Ioc a b, (v / (k : ℚ) - (q : ℚ) * (v / ((q * k - u : ℕ) : ℚ))) := by
    rw [e1, qMn_lt T hab, hs, Nat.cast_sub hab.le]
    ring
  rw [key]
  apply (LocRing p).mul_mem
  · exact power_mem_q p (by omega) (by omega)
  · refine Subring.sum_mem _ fun k hk => ?_
    have hk' := Finset.mem_Ioc.mp hk
    have hkq : q ≤ q * k := Nat.le_mul_of_pos_right q (by omega)
    have hkh : q * k ≤ q * h := Nat.mul_le_mul_left q (by omega)
    apply (LocRing p).sub_mem (power_mem_q p (by omega) (by omega))
    exact (LocRing p).mul_mem (natq_mem p q) (power_mem_q p (by omega) (by omega))

include T in
theorem qDiag_mem (p : ℕ) [Fact p.Prime] {h a : ℕ} (ha : a < h) :
    ((p : ℚ) ^ Nat.log p (q * h)) ^ 2 * ((q : ℚ) ^ 2 * Fr.Mn a a) ∈ LocRing p := by
  set v : ℚ := (p : ℚ) ^ Nat.log p (q * h) with hv
  have hu := T.hu1
  have hq1 : 1 ≤ q := by have := T.hM; omega
  have hqh : h ≤ q * h := Nat.le_mul_of_pos_left h (by omega)
  have hs : ∑ k ∈ Icc 1 a, Fr.Dsq k =
      ∑ k ∈ Icc 1 a, (1 / (k : ℚ) ^ 2 - (q : ℚ) ^ 2 / ((q * k - u : ℕ) : ℚ) ^ 2) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
    exact T.dsq k hk0
  have e1 : ∑ k ∈ Icc 1 a, ((v / (k : ℚ)) ^ 2 - (q : ℚ) ^ 2 * (v / ((q * k - u : ℕ) : ℚ)) ^ 2) =
      v ^ 2 * ∑ k ∈ Icc 1 a, (1 / (k : ℚ) ^ 2 - (q : ℚ) ^ 2 / ((q * k - u : ℕ) : ℚ) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key : v ^ 2 * ((q : ℚ) ^ 2 * Fr.Mn a a) =
      -∑ k ∈ Icc 1 a, ((v / (k : ℚ)) ^ 2 - (q : ℚ) ^ 2 * (v / ((q * k - u : ℕ) : ℚ)) ^ 2) := by
    rw [e1, qMn_diag T, hs]
    ring
  rw [key]
  apply (LocRing p).neg_mem
  refine Subring.sum_mem _ fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  have hkq : q ≤ q * k := Nat.le_mul_of_pos_right q (by omega)
  have hkh : q * k ≤ q * h := Nat.mul_le_mul_left q (by omega)
  apply (LocRing p).sub_mem ((LocRing p).pow_mem (power_mem_q p (by omega) (by omega)) 2)
  exact (LocRing p).mul_mem ((LocRing p).pow_mem (natq_mem p q) 2)
    ((LocRing p).pow_mem (power_mem_q p (by omega) (by omega)) 2)

include T in
/-- `(p^⌊log_p (q h)⌋)² q² M(a, b)` is `p`-integral for `a, b < h`. -/
theorem qNorm_mem (p : ℕ) [Fact p.Prime] {h a b : ℕ} (ha : a < h) (hb : b < h) :
    ((p : ℚ) ^ Nat.log p (q * h)) ^ 2 * ((q : ℚ) ^ 2 * Fr.Mn a b) ∈ LocRing p := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact qOff_mem T p hab hb
  · exact qDiag_mem T p ha
  · rw [fifthsMn_symm]
    exact qOff_mem T p hba ha

include T in
/-- **Small primes** (`small5_ok` at `q = 5`): `smallQ q h ² M(a, b)` is `p`-integral at every bad `p`. -/
theorem smallQ_ok (p : ℕ) [Fact p.Prime] (hp : p ∈ badQ q) (h a b : ℕ) (ha : a < h) (hb : b < h) :
    ((smallQ q h : ℕ) : ℚ) ^ 2 * Fr.Mn a b ∈ LocRing p := by
  have hdiv : q * p ^ Nat.log p (q * h) ∣ smallQ q h := by
    unfold smallQ
    exact Nat.mul_dvd_mul_left q (Finset.dvd_prod_of_mem (fun b => b ^ Nat.log b (q * h)) hp)
  obtain ⟨d, hd⟩ := hdiv
  have he : ((smallQ q h : ℕ) : ℚ) ^ 2 * Fr.Mn a b =
      (d : ℚ) ^ 2 * (((p : ℚ) ^ Nat.log p (q * h)) ^ 2 * ((q : ℚ) ^ 2 * Fr.Mn a b)) := by
    rw [hd]
    push_cast
    ring
  rw [he]
  exact (LocRing p).mul_mem ((LocRing p).pow_mem (natq_mem p d) 2) (qNorm_mem T p ha hb)

end Local

/-! ### The content table and the hybrid instance -/

section Inst
variable {Fr : Frame} {q u : ℕ} (T : ShiftData Fr q u)

include T in
/-- **The content table of a two-term bank**: `Φ(k) = k (q k - u)`, `L = q`, norm `q²`, bad primes the
primes `≤ q`, first root `kq = poleIndex q (q - u)`, small-prime clearer `smallQ q`. -/
noncomputable def twoTermCD : ContentData Fr where
  L := q
  hL := by have := T.hM; omega
  Phi := fun k => k * (q * k - u)
  Phi_pos := fun k hk => Nat.mul_pos hk (by
    have := T.hu1
    have := Nat.le_mul_of_pos_right q hk
    omega)
  bad := badQ q
  bad_prime := fun _ hp => badQ_prime hp
  normN := q ^ 2
  norm_eq := by rw [T.norm_eq, Nat.cast_pow]
  norm_dvd := by
    intro p hp hd
    have hq := T.hM
    exact mem_badQ.2 ⟨Nat.le_of_dvd (by omega) (hp.dvd_of_dvd_pow hd), hp⟩
  delta_int := by
    intro k hk
    refine ⟨-(u : ℤ), ?_⟩
    have hu := T.hu1
    have hqk : q ≤ q * k := Nat.le_mul_of_pos_right q hk
    have hlt : (u : ℚ) < (q : ℚ) * k := by exact_mod_cast (show u < q * k by omega)
    have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have hk0 : (k : ℚ) ≠ 0 := by linarith
    have hlin : (q : ℚ) * k - u ≠ 0 := by linarith
    have hlin' : (k : ℚ) * q - u ≠ 0 := by rw [mul_comm]; exact hlin
    rw [T.delta k hk, Nat.cast_mul, cast_linear T.hu1 hk]
    push_cast
    field_simp [hk0, hlin, hlin']
    ring
  dsq_int := by
    intro k hk
    refine ⟨((q : ℤ) * k - u) ^ 2 - (q : ℤ) ^ 2 * (k : ℤ) ^ 2, ?_⟩
    have hu := T.hu1
    have hqk : q ≤ q * k := Nat.le_mul_of_pos_right q hk
    have hlt : (u : ℚ) < (q : ℚ) * k := by exact_mod_cast (show u < q * k by omega)
    have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have hk0 : (k : ℚ) ≠ 0 := by linarith
    have hlin : (q : ℚ) * k - u ≠ 0 := by linarith
    have hlin' : (k : ℚ) * q - u ≠ 0 := by rw [mul_comm]; exact hlin
    rw [T.dsq k hk, Nat.cast_mul, cast_linear T.hu1 hk]
    push_cast
    field_simp [hk0, hlin, hlin']
  kq := poleIndex q (q - u)
  kq_le := fun _ _ hQ hb hk hd => ttRoot_le T.hu0 T.hu1 hQ hb hk hd
  small := smallQ q
  small_pos := smallQ_pos (by have := T.hM; omega)
  small_ok := by
    intro p _ hp h a b ha hb
    exact smallQ_ok T p hp h a b ha hb
  small_poly := smallQ_poly (by have := T.hM; omega)

include T in
/-- **The hybrid instance of a two-term bank** (block valued, `Ebd N = N (q N - u)`). -/
noncomputable def twoTermInst : HybInst Fr :=
  HybInst.ofSing (twoTermCD T) (fun N => N * (q * N - u)) (fun _ _ h => tt_phi_le h)

include T in
instance twoTermInst_diagOK (r m : ℕ) : (twoTermInst T).DiagOK r m :=
  HybInst.DiagOK.of_all (fun _ => trivial) r m

theorem twoTermInst_cd : (twoTermInst T).cd = twoTermCD T := rfl
theorem twoTermInst_lev (Q c : ℕ) : (twoTermInst T).lev Q c = blk (twoTermCD T).Phi Q c := rfl
theorem twoTermInst_bad : (twoTermInst T).cd.bad = badQ q := rfl
theorem twoTermInst_kq (Q : ℕ) : (twoTermInst T).cd.kq Q = poleIndex q (q - u) Q := rfl
theorem twoTermInst_L : (twoTermInst T).cd.L = q := rfl
theorem twoTermInst_normN : (twoTermInst T).cd.normN = q ^ 2 := rfl
theorem twoTermInst_Ebd (N : ℕ) : (twoTermInst T).Ebd N = N * (q * N - u) := rfl

/-- The first root is attained at every good prime power. -/
theorem twoTerm_kq_att (Q : ℕ) (hQ : IsPrimePow Q) (hb : ∀ p ∈ (twoTermCD T).bad, ¬ p ∣ Q) :
    0 < (twoTermCD T).kq Q ∧ Q ∣ (twoTermCD T).Phi ((twoTermCD T).kq Q) :=
  ttRoot_att T.hu0 T.hu1 hQ hb

/-- The first root at a prime `p > q`: `q · kq p = j p + u`, `j = rootClass q (q - u) p`. -/
theorem twoTerm_kq_eq {p : ℕ} (hp : p.Prime) (hqp : q < p) :
    q * (twoTermInst T).cd.kq p = rootClass q (q - u) p * p + u :=
  (ttRoot_spec T.hu0 T.hu1 hp.isPrimePow fun b hb hd => by
    have h1 := mem_badQ.1 hb
    have := (Nat.prime_dvd_prime_iff_eq h1.2 hp).mp hd
    omega).1

theorem twoTerm_lev_zero_iff {Q c : ℕ} (hQ : IsPrimePow Q) (hb : ∀ p ∈ (twoTermCD T).bad, ¬ p ∣ Q) :
    (twoTermInst T).lev Q c = 0 ↔ c < (twoTermCD T).kq Q := by
  rw [twoTermInst_lev]
  have h := blk_pos_iff (twoTermCD T) (twoTerm_kq_att T) (c := c) hQ hb
  omega

theorem twoTerm_lev_high (Q c : ℕ) (hQ : 1 ≤ Q) (h : Q ≤ c) : 0 < (twoTermInst T).lev Q c := by
  rw [twoTermInst_lev]
  exact blk_pos_of (k := Q) (Finset.mem_Icc.mpr ⟨hQ, h⟩)
    (show Q ∣ Q * (q * Q - u) from dvd_mul_right _ _)

/-- A prime `p > q` is a good prime power. -/
theorem twoTerm_good {p : ℕ} (hp : p.Prime) (hqp : q < p) :
    IsPrimePow p ∧ ∀ b ∈ (twoTermCD T).bad, ¬ b ∣ p := by
  refine ⟨hp.isPrimePow, fun b hb hd => ?_⟩
  have hb' := mem_badQ.1 (show b ∈ badQ q from hb)
  have := (Nat.prime_dvd_prime_iff_eq hb'.2 hp).mp hd
  omega

/-- **Level facts of the two-term instance**: good primes `p > q`, zero set `c < kq`. -/
theorem twoTerm_levels :
    LevelFacts (twoTermInst T) (fun p => q < p) (fun Q c => c < (twoTermInst T).cd.kq Q) where
  good := fun _ hp h => twoTerm_good T hp h
  zero_iff := fun _ _ hQ hb => twoTerm_lev_zero_iff T hQ hb
  high := fun Q c hQ hQc => twoTerm_lev_high T Q c hQ hQc

/-- The normalisation exponents: `cOf p = v_p(q²)`. -/
theorem twoTerm_cOf (p : ℕ) : cOf (twoTermInst T) p = (q ^ 2).factorization p := rfl

theorem twoTerm_cOf_le_prime (hq : q.Prime) (p : ℕ) : cOf (twoTermInst T) p ≤ 2 := by
  rw [twoTerm_cOf, Nat.Prime.factorization_pow hq]
  by_cases h : p = q
  · subst h; simp
  · simp [Ne.symm h]

/-- The bad-prime logarithm: `∑_{b ≤ q prime} log b`. -/
theorem twoTerm_badLog : badLog (twoTermInst T) = ∑ b ∈ badQ q, Real.log b := rfl

/-- **Arithmetic data of the two-term instance** (`Lc = q`), given the cubic growth bound and a bound on
`v_p(q²)`. -/
theorem twoTerm_arithmetic {cm : ℕ} (hE : ∀ N, N * (q * N - u) + N ≤ 5 * N ^ 3)
    (hcm : ∀ p, (q ^ 2).factorization p ≤ cm) : ArithmeticInfo (twoTermInst T) q cm where
  L_eq := rfl
  Ebd_le := hE
  cOf_le := hcm

theorem twoTerm_arithmetic_prime (hq : q.Prime) (hE : ∀ N, N * (q * N - u) + N ≤ 5 * N ^ 3) :
    ArithmeticInfo (twoTermInst T) q 2 :=
  twoTerm_arithmetic T hE (fun p => twoTerm_cOf_le_prime T hq p)

/-- `ArithmeticInfo (twoTermInst T) q 2` for a prime `q ≤ min (u + 4) 10`. -/
theorem twoTerm_arithmetic_small (hq : q.Prime) (h4 : q ≤ u + 4) (h10 : q ≤ 10) :
    ArithmeticInfo (twoTermInst T) q 2 :=
  twoTerm_arithmetic_prime T hq (tt_ebd_cubic T.hu0 T.hu1 h4 h10)

/-- **No-go for the cubic interface bound**: if `u + 4 < q` then `Ebd 1 + 1 = q - u + 1 > 5 = Ecub 1`, so
the two-term instance has no `ArithmeticInfo` (for any `Lc`, `cm`). -/
theorem twoTerm_not_arithmetic (h : u + 4 < q) (Lc cm : ℕ) : ¬ ArithmeticInfo (twoTermInst T) Lc cm := by
  intro B
  have hb : 1 * (q * 1 - u) + 1 ≤ 5 * 1 ^ 3 := B.Ebd_le 1
  simp only [Nat.one_mul, Nat.mul_one, one_pow] at hb
  omega

include T in
/-- The norm as a natural number `q q` (the `hnorm` of `catValid_bank`). -/
theorem twoTerm_norm : Fr.norm = ((q * q : ℕ) : ℚ) := by
  rw [T.norm_eq, Nat.cast_mul, sq]

/-- The bad primes are `≤ q` (the `hbad` of `pre_gle_any`: `p * p ≤ q * q`). -/
theorem twoTerm_bad_le {p : ℕ} (hp : p ∈ (twoTermInst T).cd.bad) : p ≤ q := badQ_le hp

/-- **The prime hypothesis `hP` of `catValid_bank`** for any `Pbad` with `2 q ≤ Pbad + 1`, `4 ≤ Pbad`
(good predicate `q < p`, norm `q q`). -/
theorem twoTerm_hP {Pbad : ℕ} (h2q : 2 * q ≤ Pbad + 1) (h4 : 4 ≤ Pbad) :
    ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ q * q ∧ 5 ≤ p ∧ 2 * q ≤ p ∧ p ∉ (twoTermInst T).cd.bad ∧ q < p ∧ p ≠ 2 := by
  intro p hp hP
  have hq := T.hM
  exact ⟨not_dvd_sq_of_lt hp (by omega) (by omega), by omega, by omega, not_mem_badQ (by omega),
    by omega, by omega⟩

/-- **The class-map hypothesis `hkq` of `catValid_bank`**: above `Pbad ≥ q`, the first root is the pole
index `k` of the root class (`q k = j p + u`, `0 < j < q`). -/
theorem twoTerm_hkq {Pbad : ℕ} (hq : q ≤ Pbad) :
    ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + u → 0 < j → j < q → 0 < k → k < p →
      (twoTermInst T).cd.kq p = k := by
  intro p hp hP j k hk _ hjq _ _
  have hu0 := T.hu0
  have hu1 := T.hu1
  have hk' : q * k = j * p + (q - (q - u)) := by
    rw [show q - (q - u) = u by omega]
    exact hk
  exact (rootClass_unique hp (a := q - u) (by omega) (by omega) (by omega) hjq hk').2.symm

end Inst

/-! ### Comparison tools -/

/-- Shrinking the good predicate keeps the level facts. -/
theorem levelFacts_mono {Fr : Frame} {I : HybInst Fr} {Gd Gd' : ℕ → Prop} {Z : ℕ → ℕ → Prop}
    (Lv : LevelFacts I Gd Z) (h : ∀ p, p.Prime → Gd' p → Gd p) : LevelFacts I Gd' Z :=
  ⟨fun p hp hG => Lv.good p hp (h p hp hG), Lv.zero_iff, Lv.high⟩

/-- Two content tables with the same `Φ` and bad primes, both attaining their first roots, have the same
first root at every good prime power. -/
theorem kq_eq_of_att {Fr : Frame} (c1 c2 : ContentData Fr) (hPhi : ∀ k, c1.Phi k = c2.Phi k)
    (hbad : c1.bad = c2.bad)
    (h1 : ∀ Q, IsPrimePow Q → (∀ p ∈ c1.bad, ¬ p ∣ Q) → 0 < c1.kq Q ∧ Q ∣ c1.Phi (c1.kq Q))
    (h2 : ∀ Q, IsPrimePow Q → (∀ p ∈ c2.bad, ¬ p ∣ Q) → 0 < c2.kq Q ∧ Q ∣ c2.Phi (c2.kq Q))
    {Q : ℕ} (hQ : IsPrimePow Q) (hb : ∀ p ∈ c1.bad, ¬ p ∣ Q) : c1.kq Q = c2.kq Q := by
  have hb2 : ∀ p ∈ c2.bad, ¬ p ∣ Q := by rw [← hbad]; exact hb
  obtain ⟨a1, d1⟩ := h1 Q hQ hb
  obtain ⟨a2, d2⟩ := h2 Q hQ hb2
  exact le_antisymm (c1.kq_le Q _ hQ hb a2 (by rw [hPhi]; exact d2)).1
    (c2.kq_le Q _ hQ hb2 a1 (by rw [← hPhi]; exact d1)).1

end CatalanCore.Uniform.Content.BankShared.Inst
