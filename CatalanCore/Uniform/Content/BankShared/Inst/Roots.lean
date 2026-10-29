import CatalanCore.Uniform.Content.BankShared.TwoTerm.Class
import CatalanFrames.HybGen.NatRoots
set_option Elab.async false

/-! # Two-term banks of any modulus: bad primes, first roots, small primes (lane C6L, gap C6)

A two-term bank of modulus `q` (`q ≥ 2`, offset `1 ≤ u < q`, member `a = q - u`) has
`Φ(k) = k (q k - u)`, `L = q`, norm `q²` and bad primes `badQ q` = the primes `≤ q`
(they contain the primes of the norm).  This module is the arithmetic, frame-free part of the generic
instance (`Inst.TwoTerm`); it generalises `CatalanFrames.Fifths.{Roots, RootArithmetic, RationalData}`
(`q = 5`) and `CatalanFrames.Thirds.Instance` (`q = 3`).

* `badQ`, `mem_badQ`, `good_pow_base`, `good_pow_cop`: a prime power avoiding the bad primes is a power of a
  prime `p > q`, hence coprime to `q` and `> q`;
* `rootClass_spec_cop`, `rootClass_unique_cop`: the class map of `TwoTerm.Class` for any modulus `P` coprime
  to `q` (not only primes);
* `ttRoot_spec`, `ttRoot_att`, `ttRoot_le` (**first root**): `kq Q = poleIndex q (q - u) Q` is attained and
  minimal for every good prime power `Q`, with `Q ≤ q k`;
* `smallQ` (`= q ∏_{b ≤ q prime} b ^ ⌊log_b (q h)⌋`, generalising `small5`), `smallQ_pos`, `smallQ_poly`;
* `tt_phi_le`, `tt_ebd_cubic`: `Ebd N = N (q N - u)` bounds `Φ` below `N`, and `Ebd N + N ≤ 5 N³` when
  `q ≤ u + 4`, `q ≤ 10`. -/

namespace CatalanCore.Uniform.Content.BankShared.Inst
open CatalanCore CatalanCore.Uniform.Content.BankShared.TwoTerm

/-! ### Bad primes -/

/-- The bad primes of a two-term bank of modulus `q`: the primes `≤ q`. -/
def badQ (q : ℕ) : Finset ℕ := (Finset.range (q + 1)).filter Nat.Prime

theorem mem_badQ {q b : ℕ} : b ∈ badQ q ↔ b ≤ q ∧ b.Prime := by
  unfold badQ
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem badQ_prime {q b : ℕ} (hb : b ∈ badQ q) : b.Prime := (mem_badQ.1 hb).2

theorem badQ_le {q b : ℕ} (hb : b ∈ badQ q) : b ≤ q := (mem_badQ.1 hb).1

/-- A number above `q` is not bad. -/
theorem not_mem_badQ {q p : ℕ} (h : q < p) : p ∉ badQ q := fun hb => by
  have := badQ_le hb
  omega

/-- A prime power avoiding the bad primes is a power of a prime `p > q`. -/
theorem good_pow_base {q Q : ℕ} (hQ : IsPrimePow Q) (hb : ∀ b ∈ badQ q, ¬ b ∣ Q) :
    ∃ p n : ℕ, p.Prime ∧ 0 < n ∧ p ^ n = Q ∧ q < p := by
  obtain ⟨p, n, hp, hn, rfl⟩ := hQ
  refine ⟨p, n, hp.nat_prime, hn, rfl, ?_⟩
  by_contra hle
  exact hb p (mem_badQ.2 ⟨by omega, hp.nat_prime⟩) (dvd_pow_self p hn.ne')

/-- A good prime power is coprime to `q` and exceeds `q`. -/
theorem good_pow_cop {q Q : ℕ} (hq : 0 < q) (hQ : IsPrimePow Q) (hb : ∀ b ∈ badQ q, ¬ b ∣ Q) :
    Nat.Coprime Q q ∧ q < Q := by
  obtain ⟨p, n, hp, hn, rfl, hqp⟩ := good_pow_base hQ hb
  exact ⟨(coprime_of_lt hp hq hqp).pow_left n, lt_of_lt_of_le hqp (Nat.le_self_pow hn.ne' p)⟩

/-! ### The class map for a coprime modulus -/

/-- `j P ≡ a (mod q)` in `ZMod q`, for `P` coprime to `q`. -/
theorem rootClass_mul_cop {q a P : ℕ} (hq : 0 < q) (hcop : Nat.Coprime P q) :
    ((rootClass q a P : ℕ) : ZMod q) * (P : ZMod q) = (a : ZMod q) := by
  have : NeZero q := ⟨by omega⟩
  unfold rootClass
  rw [ZMod.natCast_zmod_val, mul_assoc, mul_comm ((P : ZMod q))⁻¹ (P : ZMod q),
    ZMod.coe_mul_inv_eq_one P hcop, mul_one]

/-- **The class map, coprime modulus.**  For `0 < a < q < P`, `P` coprime to `q`:
`q k = j P + (q - a)` with `0 < j < q`, `0 < k < P`, `j = rootClass q a P`, `k = poleIndex q a P`. -/
theorem rootClass_spec_cop {q a P : ℕ} (hcop : Nat.Coprime P q) (ha0 : 0 < a) (haq : a < q)
    (hqP : q < P) :
    q * poleIndex q a P = rootClass q a P * P + (q - a) ∧ 0 < rootClass q a P ∧
      rootClass q a P < q ∧ 0 < poleIndex q a P ∧ poleIndex q a P < P := by
  have hq : 0 < q := by omega
  have : NeZero q := ⟨by omega⟩
  have hjq : rootClass q a P < q := ZMod.val_lt _
  have hdvd : q ∣ rootClass q a P * P + (q - a) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_sub haq.le,
      ZMod.natCast_self, rootClass_mul_cop hq hcop]
    ring
  have hk : q * poleIndex q a P = rootClass q a P * P + (q - a) := Nat.mul_div_cancel' hdvd
  have hj0 : 0 < rootClass q a P := by
    rcases Nat.eq_zero_or_pos (rootClass q a P) with h0 | h0
    · exfalso
      rw [h0, zero_mul, zero_add] at hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · exact h0
  refine ⟨hk, hj0, hjq, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (poleIndex q a P) with h0 | h0
    · rw [h0, mul_zero] at hk; omega
    · exact h0
  · by_contra hge
    have hge' : P ≤ poleIndex q a P := by omega
    have h1 : q * P ≤ q * poleIndex q a P := Nat.mul_le_mul_left q hge'
    have h2 : (rootClass q a P + 1) * P ≤ q * P := Nat.mul_le_mul_right P hjq
    rw [add_one_mul] at h2
    omega

/-- **Uniqueness, coprime modulus**: `(rootClass, poleIndex)` is the only pair `(j, k)` with `j < q` and
`q k = j P + (q - a)`. -/
theorem rootClass_unique_cop {q a P j k : ℕ} (hcop : Nat.Coprime P q) (haq : a < q)
    (hjq : j < q) (hk : q * k = j * P + (q - a)) : j = rootClass q a P ∧ k = poleIndex q a P := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le a) haq
  have : NeZero q := ⟨by omega⟩
  have hz : ((j : ℕ) : ZMod q) * (P : ZMod q) = (a : ZMod q) := by
    have h1 : ((q * k : ℕ) : ZMod q) = ((j * P + (q - a) : ℕ) : ZMod q) := by rw [hk]
    rw [Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub haq.le, ZMod.natCast_self] at h1
    linear_combination -h1
  have hjz : ((j : ℕ) : ZMod q) = (a : ZMod q) * ((P : ZMod q))⁻¹ := by
    rw [← hz, mul_assoc, ZMod.coe_mul_inv_eq_one P hcop, mul_one]
  have hjr : j = rootClass q a P := by
    unfold rootClass
    rw [← hjz, ZMod.val_natCast_of_lt hjq]
  refine ⟨hjr, ?_⟩
  unfold poleIndex
  rw [← hjr, ← hk, Nat.mul_div_cancel_left k hq]

/-! ### The first root of `Φ(k) = k (q k - u)` at a good prime power -/

/-- The first root `poleIndex q (q - u) Q`: `q k = j Q + u`, `0 < j < q`, `0 < k < Q`. -/
theorem ttRoot_spec {q u Q : ℕ} (hu0 : 1 ≤ u) (hu1 : u < q) (hQ : IsPrimePow Q)
    (hb : ∀ b ∈ badQ q, ¬ b ∣ Q) :
    q * poleIndex q (q - u) Q = rootClass q (q - u) Q * Q + u ∧ 0 < rootClass q (q - u) Q ∧
      rootClass q (q - u) Q < q ∧ 0 < poleIndex q (q - u) Q ∧ poleIndex q (q - u) Q < Q := by
  obtain ⟨hcop, hqQ⟩ := good_pow_cop (by omega) hQ hb
  have h := rootClass_spec_cop hcop (a := q - u) (by omega) (by omega) hqQ
  rwa [show q - (q - u) = u by omega] at h

/-- The first root is a root: `Q ∣ Φ(kq Q)`. -/
theorem ttRoot_att {q u Q : ℕ} (hu0 : 1 ≤ u) (hu1 : u < q) (hQ : IsPrimePow Q)
    (hb : ∀ b ∈ badQ q, ¬ b ∣ Q) :
    0 < poleIndex q (q - u) Q ∧ Q ∣ poleIndex q (q - u) Q * (q * poleIndex q (q - u) Q - u) := by
  obtain ⟨h1, -, -, h4, -⟩ := ttRoot_spec hu0 hu1 hQ hb
  refine ⟨h4, Dvd.dvd.mul_left ⟨rootClass q (q - u) Q, ?_⟩ _⟩
  rw [Nat.mul_comm Q]
  omega

/-- **Minimality of the first root**: `Q ∣ Φ(k)`, `k > 0` give `kq Q ≤ k` and `Q ≤ q k`. -/
theorem ttRoot_le {q u Q k : ℕ} (hu0 : 1 ≤ u) (hu1 : u < q) (hQ : IsPrimePow Q)
    (hb : ∀ b ∈ badQ q, ¬ b ∣ Q) (hk : 0 < k) (hd : Q ∣ k * (q * k - u)) :
    poleIndex q (q - u) Q ≤ k ∧ Q ≤ q * k := by
  obtain ⟨-, -, -, -, hs5⟩ := ttRoot_spec hu0 hu1 hQ hb
  obtain ⟨hcop, -⟩ := good_pow_cop (by omega) hQ hb
  obtain ⟨p, n, hp, hn, rfl, hqp⟩ := good_pow_base hQ hb
  have hpu : ¬ p ∣ u := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hqk : q ≤ q * k := Nat.le_mul_of_pos_right q hk
  have hkq : k ≤ q * k := Nat.le_mul_of_pos_left k (by omega)
  rcases CatalanFrames.HybGen.primePower_split hp hpu (by omega : u ≤ q * k) hd with hc | hc
  · have := Nat.le_of_dvd hk hc
    constructor <;> omega
  · obtain ⟨t, ht⟩ := hc
    have hpos : 0 < q * k - u := by omega
    have ht0 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, Nat.mul_zero] at ht
        omega
      · exact h0
    have hle : p ^ n ≤ q * k - u := by
      rw [ht]
      exact Nat.le_mul_of_pos_right _ ht0
    rcases Nat.lt_or_ge t q with htq | htq
    · have hk' : q * k = t * p ^ n + (q - (q - u)) := by
        rw [show q - (q - u) = u by omega, Nat.mul_comm t]
        omega
      have he := (rootClass_unique_cop hcop (a := q - u) (by omega) htq hk').2
      constructor <;> omega
    · have hmul : p ^ n * q ≤ p ^ n * t := Nat.mul_le_mul_left _ htq
      have h1 : q * p ^ n < q * k := by
        rw [Nat.mul_comm q (p ^ n)]
        omega
      have h2 := Nat.lt_of_mul_lt_mul_left h1
      constructor <;> omega

/-! ### Small primes -/

/-- The small-prime clearer of a two-term bank of modulus `q` (`small5` at `q = 5`). -/
def smallQ (q h : ℕ) : ℕ := q * ∏ b ∈ badQ q, b ^ Nat.log b (q * h)

theorem smallQ_pos {q : ℕ} (hq : 1 ≤ q) (h : ℕ) : 0 < smallQ q h := by
  unfold smallQ
  exact Nat.mul_pos (by omega) (Finset.prod_pos fun b hb => pow_pos (badQ_prime hb).pos _)

/-- `smallQ q h ≤ q^(c+1) (h + 1)^c`, `c = #badQ q`. -/
theorem smallQ_poly {q : ℕ} (hq : 1 ≤ q) : ∃ A C : ℕ, ∀ h, smallQ q h ≤ A * (h + 1) ^ C := by
  refine ⟨q * q ^ (badQ q).card, (badQ q).card, fun h => ?_⟩
  have hfac : ∀ b ∈ badQ q, b ^ Nat.log b (q * h) ≤ q * (h + 1) := by
    intro b _
    rcases Nat.eq_zero_or_pos (q * h) with h0 | h0
    · rw [h0, Nat.log_zero_right, pow_zero]
      exact Nat.mul_pos (by omega) (by omega)
    · exact (Nat.pow_log_le_self b h0.ne').trans (Nat.mul_le_mul_left q (by omega))
  have hprod := Finset.prod_le_pow_card (badQ q) (fun b => b ^ Nat.log b (q * h)) (q * (h + 1)) hfac
  unfold smallQ
  calc q * ∏ b ∈ badQ q, b ^ Nat.log b (q * h) ≤ q * (q * (h + 1)) ^ (badQ q).card :=
        Nat.mul_le_mul_left q hprod
    _ = q * q ^ (badQ q).card * (h + 1) ^ (badQ q).card := by rw [mul_pow, ← mul_assoc]

/-! ### The growth bound `Ebd N = N (q N - u)` -/

/-- `Φ(k) ≤ Ebd N` for `k ≤ N`, `Ebd N = N (q N - u)` (the least admissible bound: `Φ` is monotone). -/
theorem tt_phi_le {q u k N : ℕ} (h : k ≤ N) : k * (q * k - u) ≤ N * (q * N - u) :=
  Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.mul_le_mul_left q h) u)

/-- `Ebd N + N ≤ 5 N³` when `q ≤ u + 4` (the case `N = 1`) and `q ≤ 10` (the cases `N ≥ 2`). -/
theorem tt_ebd_cubic {q u : ℕ} (hu0 : 1 ≤ u) (hu1 : u < q) (h4 : q ≤ u + 4) (h10 : q ≤ 10) (N : ℕ) :
    N * (q * N - u) + N ≤ 5 * N ^ 3 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N
    · simp
    · simp only [Nat.one_mul, Nat.mul_one, one_pow]
      omega
  · have hqN : q ≤ q * N := Nat.le_mul_of_pos_right q (by omega)
    have e1 : N * (q * N - u) + N ≤ N * (q * N) := by
      have h1 : q * N - u + 1 ≤ q * N := by omega
      calc N * (q * N - u) + N = N * (q * N - u + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ N * (q * N) := Nat.mul_le_mul_left N h1
    have e2 : q * N ≤ 5 * N * N := Nat.mul_le_mul_right N (by omega : q ≤ 5 * N)
    calc N * (q * N - u) + N ≤ N * (q * N) := e1
      _ ≤ N * (5 * N * N) := Nat.mul_le_mul_left N e2
      _ = 5 * N ^ 3 := by ring

end CatalanCore.Uniform.Content.BankShared.Inst
