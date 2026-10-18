module

public import CatalanFrames.P6.Frame
public import CatalanCore.Arith.Growth

@[expose] public section

/-!
# P6 content: `HasContent (ofFrame p6Frame) (67/24)` (WP10)

Instance of the generic content engine (`CatalanCore.Arith`) for `L(2,χ₋₃)/4`:
`Φ(k) = k(3k-2)(2k-1)`, bad primes `{2,3}`, `kq` = FJ-P6 Lemma 3.1, classes `1,5 (mod 6)` with
`c = 3, 2`, and the weight `small h = 6 · 2^{⌊log₂ 3h⌋} · 3^{⌊log₃ 3h⌋}` (FJ-P6 Lemma 4.1).
-/

open Finset Classical

namespace CatalanFrames.P6

open CatalanCore CatalanCore.Arith CatalanCore.Basic

lemma Mn_lt {a b : ℕ} (hab : a < b) :
    p6Frame.Mn a b = (1 / 36 : ℚ) * (1 / ((b : ℚ) - a)) * ∑ k ∈ Ioc a b, p6Frame.Delta k := by
  unfold Frame.Mn
  rw [if_neg hab.ne, max_eq_right hab.le, min_eq_left hab.le]
  simp [p6Frame]

lemma Mn_diag (a : ℕ) :
    p6Frame.Mn a a = -((1 / 36 : ℚ) * ∑ k ∈ Icc 1 a, p6Frame.Dsq k) := by
  unfold Frame.Mn
  rw [if_pos rfl]
  simp [p6Frame]

lemma Mn_symm (a b : ℕ) : p6Frame.Mn a b = p6Frame.Mn b a := by
  unfold Frame.Mn
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

lemma c3 {k : ℕ} (hk : 0 < k) : ((3 * k - 2 : ℕ) : ℚ) = 3 * (k : ℚ) - 2 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma c2 {k : ℕ} (hk : 0 < k) : ((2 * k - 1 : ℕ) : ℚ) = 2 * (k : ℚ) - 1 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-! ### The weight at the bad primes -/

section small

variable (p : ℕ) [Fact p.Prime]

lemma pw_mem {N n : ℕ} (hn : 0 < n) (hv : n.factorization p ≤ N) :
    ((p : ℚ) ^ N / (n : ℚ)) ∈ LocRing p := by
  have := div_mem_locRing (p := p) (n := n) (W := p ^ N) hn (Nat.pow_dvd_pow p hv)
  simpa using this

lemma pw_mem' {n h : ℕ} (hn : 0 < n) (hnh : n ≤ 3 * h) :
    ((p : ℚ) ^ Nat.log p (3 * h) / (n : ℚ)) ∈ LocRing p :=
  pw_mem p hn (Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
    (le_trans (Nat.ordProj_le p hn.ne') hnh))

lemma six_mem : (6 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (6 : ℤ)

lemma off_mem {h a b : ℕ} (hab : a < b) (hbh : b < h) :
    ((p : ℚ) ^ Nat.log p (3 * h)) ^ 2 * (36 * p6Frame.Mn a b) ∈ LocRing p := by
  set u : ℚ := (p : ℚ) ^ Nat.log p (3 * h) with hu
  have hs : ∑ k ∈ Ioc a b, p6Frame.Delta k =
      ∑ k ∈ Ioc a b, (1 / (k : ℚ) + 6 / ((3 * k - 2 : ℕ) : ℚ) - 6 / ((2 * k - 1 : ℕ) : ℚ)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Ioc.mp hk).1; omega
    rw [Delta_eq k hk0, c3 hk0, c2 hk0]
  have e : ∑ k ∈ Ioc a b, (u / (k : ℚ) + 6 * (u / ((3 * k - 2 : ℕ) : ℚ)) -
        6 * (u / ((2 * k - 1 : ℕ) : ℚ))) =
      u * ∑ k ∈ Ioc a b, (1 / (k : ℚ) + 6 / ((3 * k - 2 : ℕ) : ℚ) - 6 / ((2 * k - 1 : ℕ) : ℚ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key : u ^ 2 * (36 * p6Frame.Mn a b) =
      (u / ((b - a : ℕ) : ℚ)) * ∑ k ∈ Ioc a b, (u / (k : ℚ) + 6 * (u / ((3 * k - 2 : ℕ) : ℚ)) -
        6 * (u / ((2 * k - 1 : ℕ) : ℚ))) := by
    rw [e, Mn_lt hab, hs, Nat.cast_sub hab.le]
    ring
  rw [key]
  apply (LocRing p).mul_mem
  · exact pw_mem' p (by omega) (by omega)
  · refine Subring.sum_mem _ fun k hk => ?_
    have hk' := Finset.mem_Ioc.mp hk
    apply (LocRing p).sub_mem
    · apply (LocRing p).add_mem (pw_mem' p (by omega) (by omega))
      exact (LocRing p).mul_mem (six_mem p) (pw_mem' p (by omega) (by omega))
    · exact (LocRing p).mul_mem (six_mem p) (pw_mem' p (by omega) (by omega))

lemma diag_mem {h a : ℕ} (ha : a < h) :
    ((p : ℚ) ^ Nat.log p (3 * h)) ^ 2 * (36 * p6Frame.Mn a a) ∈ LocRing p := by
  set u : ℚ := (p : ℚ) ^ Nat.log p (3 * h) with hu
  have hs : ∑ k ∈ Icc 1 a, p6Frame.Dsq k =
      ∑ k ∈ Icc 1 a, (1 / (k : ℚ) ^ 2 + 18 / ((3 * k - 2 : ℕ) : ℚ) ^ 2 -
        12 / ((2 * k - 1 : ℕ) : ℚ) ^ 2) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
    rw [Dsq_eq k hk0, c3 hk0, c2 hk0]
  have e : ∑ k ∈ Icc 1 a, ((u / (k : ℚ)) ^ 2 + 18 * (u / ((3 * k - 2 : ℕ) : ℚ)) ^ 2 -
        12 * (u / ((2 * k - 1 : ℕ) : ℚ)) ^ 2) =
      u ^ 2 * ∑ k ∈ Icc 1 a, (1 / (k : ℚ) ^ 2 + 18 / ((3 * k - 2 : ℕ) : ℚ) ^ 2 -
        12 / ((2 * k - 1 : ℕ) : ℚ) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key : u ^ 2 * (36 * p6Frame.Mn a a) =
      -∑ k ∈ Icc 1 a, ((u / (k : ℚ)) ^ 2 + 18 * (u / ((3 * k - 2 : ℕ) : ℚ)) ^ 2 -
        12 * (u / ((2 * k - 1 : ℕ) : ℚ)) ^ 2) := by
    rw [e, Mn_diag, hs]
    ring
  rw [key]
  apply (LocRing p).neg_mem
  refine Subring.sum_mem _ fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  have h18 : (18 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (18 : ℤ)
  have h12 : (12 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (12 : ℤ)
  apply (LocRing p).sub_mem
  · apply (LocRing p).add_mem ((LocRing p).pow_mem (pw_mem' p (by omega) (by omega)) 2)
    exact (LocRing p).mul_mem h18 ((LocRing p).pow_mem (pw_mem' p (by omega) (by omega)) 2)
  · exact (LocRing p).mul_mem h12 ((LocRing p).pow_mem (pw_mem' p (by omega) (by omega)) 2)

lemma norm_mem {h a b : ℕ} (ha : a < h) (hb : b < h) :
    ((p : ℚ) ^ Nat.log p (3 * h)) ^ 2 * (36 * p6Frame.Mn a b) ∈ LocRing p := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact off_mem p hab hb
  · exact diag_mem p ha
  · rw [Mn_symm]; exact off_mem p hba ha

end small

/-- The weight for the bad primes `2, 3`. -/
def small6 (h : ℕ) : ℕ := 6 * 2 ^ Nat.log 2 (3 * h) * 3 ^ Nat.log 3 (3 * h)

lemma small6_ok (p : ℕ) [Fact p.Prime] (hp : p ∈ ({2, 3} : Finset ℕ)) (h a b : ℕ) (ha : a < h)
    (hb : b < h) : ((small6 h : ℕ) : ℚ) ^ 2 * p6Frame.Mn a b ∈ LocRing p := by
  have hp' : p = 2 ∨ p = 3 := by simpa using hp
  rcases hp' with rfl | rfl
  · have e : ((small6 h : ℕ) : ℚ) ^ 2 * p6Frame.Mn a b =
        ((3 : ℚ) ^ Nat.log 3 (3 * h)) ^ 2 *
          ((((2 : ℕ) : ℚ) ^ Nat.log 2 (3 * h)) ^ 2 * (36 * p6Frame.Mn a b)) := by
      unfold small6; push_cast; ring
    rw [e]
    exact (LocRing 2).mul_mem ((LocRing 2).pow_mem ((LocRing 2).pow_mem
      (by exact_mod_cast int_mem_locRing (ℓ := 2) (3 : ℤ)) _) 2) (norm_mem 2 ha hb)
  · have e : ((small6 h : ℕ) : ℚ) ^ 2 * p6Frame.Mn a b =
        ((2 : ℚ) ^ Nat.log 2 (3 * h)) ^ 2 *
          ((((3 : ℕ) : ℚ) ^ Nat.log 3 (3 * h)) ^ 2 * (36 * p6Frame.Mn a b)) := by
      unfold small6; push_cast; ring
    rw [e]
    exact (LocRing 3).mul_mem ((LocRing 3).pow_mem ((LocRing 3).pow_mem
      (by exact_mod_cast int_mem_locRing (ℓ := 3) (2 : ℤ)) _) 2) (norm_mem 3 ha hb)

lemma small6_poly (h : ℕ) : small6 h ≤ 54 * (h + 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp [small6]
  · have h2 := Nat.pow_log_le_self 2 (by omega : 3 * h ≠ 0)
    have h3 := Nat.pow_log_le_self 3 (by omega : 3 * h ≠ 0)
    unfold small6
    calc 6 * 2 ^ Nat.log 2 (3 * h) * 3 ^ Nat.log 3 (3 * h) ≤ 6 * (3 * h) * (3 * h) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 6 h2) h3
      _ ≤ 54 * (h + 1) ^ 2 := by nlinarith

/-! ### `kq` (FJ-P6 Lemma 3.1) -/

/-- First `k ≥ 1` with `q ∣ k(3k-2)(2k-1)` for prime powers `q` prime to 6. -/
def kq6 (q : ℕ) : ℕ := if q % 6 = 1 then (q + 2) / 3 else (q + 1) / 2

lemma no_two_dvd {p k : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hk : 0 < k) :
    ¬ (p ∣ k ∧ p ∣ 3 * k - 2) ∧ ¬ (p ∣ 3 * k - 2 ∧ p ∣ 2 * k - 1) ∧
      ¬ (p ∣ k ∧ p ∣ 2 * k - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hA, hB⟩
    have := Nat.dvd_sub (Dvd.dvd.mul_left hA 3) hB
    have e : 3 * k - (3 * k - 2) = 2 := by omega
    rw [e] at this
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  · rintro ⟨hB, hC⟩
    have := Nat.dvd_sub (Dvd.dvd.mul_left hC 3) (Dvd.dvd.mul_left hB 2)
    have e : 3 * (2 * k - 1) - 2 * (3 * k - 2) = 1 := by omega
    rw [e] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · rintro ⟨hA, hC⟩
    have := Nat.dvd_sub (Dvd.dvd.mul_left hA 2) hC
    have e : 2 * k - (2 * k - 1) = 1 := by omega
    rw [e] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

lemma kq6_le {q k : ℕ} (hq : IsPrimePow q) (h2 : ¬ 2 ∣ q) (h3 : ¬ 3 ∣ q) (hk : 0 < k)
    (hd : q ∣ k * (3 * k - 2) * (2 * k - 1)) : kq6 q ≤ k ∧ q ≤ 3 * k := by
  obtain ⟨p, e, hp0, he, hqe⟩ := hq
  have hp := hp0.nat_prime
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 (hqe ▸ dvd_pow_self 2 he.ne')
  obtain ⟨n1, n2, n3⟩ := no_two_dvd hp hp2 hk
  have hq6 : q % 6 = 1 ∨ q % 6 = 5 := by omega
  have hpd : p ∣ k * (3 * k - 2) * (2 * k - 1) :=
    dvd_trans (hqe ▸ dvd_pow_self p he.ne') hd
  have cop : ∀ m : ℕ, ¬ p ∣ m → Nat.Coprime q m := fun m hm =>
    hqe ▸ Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have hcases : q ∣ k ∨ q ∣ 3 * k - 2 ∨ q ∣ 2 * k - 1 := by
    rcases (hp.dvd_mul.mp hpd) with hpd1 | hC
    · rcases hp.dvd_mul.mp hpd1 with hA | hB
      · left
        have : ¬ p ∣ (3 * k - 2) * (2 * k - 1) := by
          intro h'
          rcases hp.dvd_mul.mp h' with h'' | h''
          · exact n1 ⟨hA, h''⟩
          · exact n3 ⟨hA, h''⟩
        rw [mul_assoc] at hd
        exact (cop _ this).dvd_of_dvd_mul_right hd
      · right; left
        have : ¬ p ∣ k * (2 * k - 1) := by
          intro h'
          rcases hp.dvd_mul.mp h' with h'' | h''
          · exact n1 ⟨h'', hB⟩
          · exact n2 ⟨hB, h''⟩
        have hd' : q ∣ (k * (2 * k - 1)) * (3 * k - 2) := by
          have : k * (3 * k - 2) * (2 * k - 1) = (k * (2 * k - 1)) * (3 * k - 2) := by ring
          rwa [this] at hd
        exact (cop _ this).dvd_of_dvd_mul_left hd'
    · right; right
      have : ¬ p ∣ k * (3 * k - 2) := by
        intro h'
        rcases hp.dvd_mul.mp h' with h'' | h''
        · exact n3 ⟨h'', hC⟩
        · exact n2 ⟨h'', hC⟩
      exact (cop _ this).dvd_of_dvd_mul_left hd
  unfold kq6
  rcases hcases with hc | hc | hc
  · have := Nat.le_of_dvd hk hc
    split_ifs <;> omega
  · obtain ⟨t, ht⟩ := hc
    rcases Nat.lt_or_ge t 2 with ht2 | ht2
    · interval_cases t
      · omega
      · split_ifs <;> omega
    · have := Nat.mul_le_mul_left q ht2
      split_ifs <;> omega
  · have := Nat.le_of_dvd (by omega) hc
    split_ifs <;> omega

/-! ### The content table -/

/-- The content table of P6. -/
noncomputable def p6CD : ContentData p6Frame where
  L := 3
  hL := by norm_num
  Phi := fun k => k * (3 * k - 2) * (2 * k - 1)
  Phi_pos := fun k hk => Nat.mul_pos (Nat.mul_pos hk (by omega)) (by omega)
  bad := {2, 3}
  bad_prime := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  normN := 36
  norm_eq := by simp [p6Frame]
  norm_dvd := by
    intro p hp hd
    have h36 : p ∣ 2 ^ 2 * 3 ^ 2 := by norm_num; exact hd
    rcases hp.dvd_mul.mp h36 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      simp [this]
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
      simp [this]
  delta_int := by
    intro k hk
    refine ⟨2 - k, ?_⟩
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have n1 : 3 * (k : ℚ) - 2 ≠ 0 := by intro h; linarith
    have n2 : 2 * (k : ℚ) - 1 ≠ 0 := by intro h; linarith
    have n0 : (k : ℚ) ≠ 0 := by intro h; linarith
    rw [Delta_eq k hk, Nat.cast_mul, Nat.cast_mul, c3 hk, c2 hk]
    push_cast
    generalize hx : 3 * (k : ℚ) - 2 = x at *
    generalize hy : 2 * (k : ℚ) - 1 = y at *
    field_simp
    subst hx hy
    ring
  dsq_int := by
    intro k hk
    refine ⟨(3 * (k : ℤ) - 2) ^ 2 * (2 * (k : ℤ) - 1) ^ 2 +
      18 * (k : ℤ) ^ 2 * (2 * (k : ℤ) - 1) ^ 2 - 12 * (k : ℤ) ^ 2 * (3 * (k : ℤ) - 2) ^ 2, ?_⟩
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have n1 : 3 * (k : ℚ) - 2 ≠ 0 := by intro h; linarith
    have n2 : 2 * (k : ℚ) - 1 ≠ 0 := by intro h; linarith
    have n0 : (k : ℚ) ≠ 0 := by intro h; linarith
    rw [Dsq_eq k hk, Nat.cast_mul, Nat.cast_mul, c3 hk, c2 hk]
    push_cast
    generalize hx : 3 * (k : ℚ) - 2 = x at *
    generalize hy : 2 * (k : ℚ) - 1 = y at *
    field_simp
  kq := kq6
  kq_le := by
    intro q k hq hbad hk hd
    exact kq6_le hq (hbad 2 (by simp)) (hbad 3 (by simp)) hk hd
  small := small6
  small_pos := fun h => by unfold small6; positivity
  small_ok := by
    intro p _ hp h a b ha hb
    exact small6_ok p hp h a b ha hb
  small_poly := ⟨54, 2, fun h => small6_poly h⟩

/-- Residue classes `1, 5 (mod 6)` with `c = 3, 2`. -/
noncomputable def p6GD : GrowthData p6CD where
  M := 6
  n := 2
  res := ![1, 5]
  c := ![3, 2]
  d := ![0, 0]
  hc := by intro i; fin_cases i <;> norm_num
  hd := by intro i; fin_cases i <;> norm_num
  cover := by
    intro q _ hbad
    have h2 : ¬ 2 ∣ q := hbad 2 (by simp [p6CD])
    have h3 : ¬ 3 ∣ q := hbad 3 (by simp [p6CD])
    have hq : q % 6 = 1 ∨ q % 6 = 5 := by omega
    rcases hq with h | h
    · exact ⟨0, by rw [← ZMod.natCast_mod q 6, h]; rfl⟩
    · exact ⟨1, by rw [← ZMod.natCast_mod q 6, h]; rfl⟩
  thr := by
    intro i q a hqp hbad hi hu
    have hu' : kq6 q ≤ a := hu
    unfold kq6 at hu'
    fin_cases i
    · have hi' : (q : ZMod 6) = ((1 : ℕ) : ZMod 6) := by simpa using hi
      have h1 : q % 6 = 1 := by
        have := (ZMod.natCast_eq_natCast_iff' q 1 6).mp hi'
        simpa using this
      simp only [h1, ite_true] at hu'
      have : q ≤ 3 * a := by omega
      show (q : ℝ) ≤ (3 : ℝ) * a + 0
      have h4 : (q : ℝ) ≤ 3 * a := by exact_mod_cast this
      linarith
    · have hi' : (q : ZMod 6) = ((5 : ℕ) : ZMod 6) := by simpa using hi
      have h5 : q % 6 = 5 := by
        have := (ZMod.natCast_eq_natCast_iff' q 5 6).mp hi'
        simpa using this
      have h1 : ¬ q % 6 = 1 := by omega
      simp only [h1, ite_false] at hu'
      have : q ≤ 2 * a := by omega
      show (q : ℝ) ≤ (2 : ℝ) * a + 0
      have h4 : (q : ℝ) ≤ 2 * a := by exact_mod_cast this
      linarith

/-- **P6 content**: `HasContent (ofFrame p6Frame) (67/24)` from the generic engine. -/
theorem hasContent : HasContent (PolyFamily.ofFrame p6Frame) (67 / 24) := by
  have : NeZero p6GD.M := inferInstanceAs (NeZero 6)
  have hunit : ∀ i, IsUnit (p6GD.res i) := by
    intro i; fin_cases i
    · exact isUnit_one
    · exact (by decide : IsUnit (5 : ZMod 6))
  have e : p6GD.Lam = 67 / 24 := by
    have : p6GD.Lam = 2 * ((Nat.totient 6 : ℕ) : ℝ)⁻¹ * ∑ i : Fin 2, Icont (![3, 2] i) := rfl
    rw [this, Fin.sum_univ_two]
    have : Nat.totient 6 = 2 := by decide
    norm_num [Icont, this]
  have := hasContent_of_classes p6GD hunit
  rwa [e] at this

end CatalanFrames.P6
