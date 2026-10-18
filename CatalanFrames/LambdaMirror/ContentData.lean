module

public import CatalanFrames.LambdaMirror.Frame
public import CatalanCore.Arith.Growth

@[expose] public section

/-!
# Mirror content data (`ContentData`/`GrowthData` for `mirFrame`)

`F = ψ(z+1/4) - ψ(z+1)` (`λ' = G/2 + 5π²/96`): `Φ(k) = k(4k-3)`, bad primes `{2, 3}` with weight
`4·2^{⌊log₂ h⌋}·3^{⌊log₃ 12h⌋}`, classes `1 (mod 4)` (`c = 4`) and `3 (mod 4)` (`c = 4/3`).
Fed to the shared engine `CatalanCore.Arith.hasContent_of_classes` in `LambdaMirror/Content.lean`.
-/

open Finset Classical Filter

namespace CatalanFrames.LambdaMirror

open CatalanCore CatalanCore.Arith CatalanCore.Basic

lemma mir_Delta {k : ℕ} (hk : 0 < k) :
    mirFrame.Delta k = 3 / ((k : ℚ) * (4 * k - 3)) := Delta_eq k hk

lemma mir_Dsq {k : ℕ} (hk : 0 < k) :
    mirFrame.Dsq k = 16 / (4 * (k : ℚ) - 3) ^ 2 - 1 / (k : ℚ) ^ 2 := Dsq_eq k hk

lemma mir_Mn_lt {a b : ℕ} (hab : a < b) :
    mirFrame.Mn a b = (1 / 16 : ℚ) * (1 / ((b : ℚ) - a)) * ∑ k ∈ Ioc a b, mirFrame.Delta k := by
  unfold Frame.Mn
  rw [if_neg hab.ne, max_eq_right hab.le, min_eq_left hab.le]
  simp [mirFrame]

lemma mir_Mn_diag (a : ℕ) :
    mirFrame.Mn a a = -((1 / 16 : ℚ) * ∑ k ∈ Icc 1 a, mirFrame.Dsq k) := by
  unfold Frame.Mn
  rw [if_pos rfl]
  simp [mirFrame]

lemma mir_Mn_symm (a b : ℕ) : mirFrame.Mn a b = mirFrame.Mn b a := by
  unfold Frame.Mn
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

lemma cast43 {k : ℕ} (hk : 0 < k) : ((4 * k - 3 : ℕ) : ℚ) = 4 * (k : ℚ) - 3 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-! ### `kq` for the mirror -/

/-- `j_q = 1` if `q ≡ 1 (mod 4)`, `3` otherwise. -/
def jq (q : ℕ) : ℕ := if q % 4 = 1 then 1 else 3

/-- First `k ≥ 1` with `q ∣ k (4k-3)` (for prime powers `q` coprime to `6`). -/
def kq (q : ℕ) : ℕ := (jq q * q + 3) / 4

lemma jq_cases (q : ℕ) : jq q = 1 ∨ jq q = 3 := by unfold jq; split_ifs <;> simp

lemma kq_le_of_dvd {q k : ℕ} (hq : IsPrimePow q) (hqo : Odd q) (hq3 : ¬ 3 ∣ q) (hk : 0 < k)
    (hd : q ∣ k * (4 * k - 3)) : kq q ≤ k ∧ q ≤ 4 * k - 3 := by
  obtain ⟨p, e, hp0, he, rfl⟩ := hq
  have hp := hp0.nat_prime
  have hq2 : (p ^ e) % 2 = 1 := Nat.odd_iff.mp hqo
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hq3 (dvd_pow_self 3 (by omega))
  have hcases : p ^ e ∣ k ∨ p ^ e ∣ 4 * k - 3 := by
    by_cases hpk : p ∣ k
    · left
      have : Nat.Coprime p (4 * k - 3) := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro h4
        have h5 : p ∣ 4 * k := Dvd.dvd.mul_left hpk 4
        have h6 : p ∣ 3 := by
          have := Nat.dvd_sub h5 h4
          have e1 : 4 * k - (4 * k - 3) = 3 := by omega
          rwa [e1] at this
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h6)
      exact (Nat.Coprime.pow_left e this).dvd_of_dvd_mul_right hd
    · right
      have : Nat.Coprime (p ^ e) k :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
      exact this.dvd_of_dvd_mul_left hd
  have hjq := jq_cases (p ^ e)
  rcases hcases with hc | hc
  · have := Nat.le_of_dvd hk hc
    unfold kq
    rcases hjq with hj | hj <;> rw [hj] <;> omega
  · obtain ⟨t, ht⟩ := hc
    have h4k : 4 * k - 3 = (p ^ e) * t := ht
    have hq3' : (p ^ e) % 4 = 1 ∨ (p ^ e) % 4 = 3 := by omega
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0] at h4k; omega
      · exact h0
    refine ⟨?_, ?_⟩
    · unfold kq
      have hmod : ((p ^ e) * t) % 4 = 1 := by omega
      rcases hq3' with h1 | h3
      · have hj : jq (p ^ e) = 1 := by unfold jq; simp [h1]
        rw [hj]
        have : (p ^ e) ≤ (p ^ e) * t := Nat.le_mul_of_pos_right _ htpos
        omega
      · have hj : jq (p ^ e) = 3 := by unfold jq; simp [h3]
        rw [hj]
        have := Nat.mul_mod (p ^ e) t 4
        rw [h3] at this
        have ht3 : t % 4 = 3 := by omega
        have : 3 ≤ t := by omega
        have : 3 * (p ^ e) ≤ (p ^ e) * t := by nlinarith
        omega
    · rw [h4k]; exact Nat.le_mul_of_pos_right _ htpos

/-! ### The weight at the bad primes `2, 3` -/

/-- `2^{⌊log₂ h⌋} · 3^{⌊log₃ 12h⌋}`. -/
def sc (h : ℕ) : ℕ := 2 ^ Nat.log 2 h * 3 ^ Nat.log 3 (12 * h)

/-- `3^e ∣ k (4k-3)` forces `3^e ≤ 12 k`. -/
lemma three_pow_le {e k : ℕ} (hk : 0 < k) (hd : 3 ^ e ∣ k * (4 * k - 3)) : 3 ^ e ≤ 12 * k := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp; omega
  have h3 : 3 ∣ k * (4 * k - 3) := (dvd_pow_self 3 he.ne').trans hd
  have h3k : 3 ∣ k := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · exact h
    · omega
  obtain ⟨k', rfl⟩ := h3k
  have hk' : 0 < k' := by omega
  by_cases he2 : e ≤ 2
  · have : 3 ^ e ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) he2
    omega
  · push Not at he2
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 3 := ⟨e - 3, by omega⟩
    have e1 : 3 * k' * (4 * (3 * k') - 3) = 9 * (k' * (4 * k' - 1)) := by
      have : 4 * (3 * k') - 3 = 3 * (4 * k' - 1) := by omega
      rw [this]; ring
    rw [e1] at hd
    have hd' : 3 ^ (f + 1) ∣ k' * (4 * k' - 1) := by
      have : 3 ^ (f + 3) = 9 * 3 ^ (f + 1) := by ring
      rw [this] at hd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
    have hcop : Nat.Coprime k' (4 * k' - 1) := by
      have h1 : Nat.gcd k' (4 * k' - 1) ∣ 4 * k' - 1 := Nat.gcd_dvd_right _ _
      have h2 : Nat.gcd k' (4 * k' - 1) ∣ 4 * k' := Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 4
      have h3 := Nat.dvd_sub h2 h1
      have : 4 * k' - (4 * k' - 1) = 1 := by omega
      rw [this] at h3
      exact Nat.dvd_one.mp h3
    have hpp : IsPrimePow (3 ^ (f + 1)) := (Nat.prime_three.isPrimePow).pow (by omega)
    have hle : 3 ^ (f + 1) ≤ 4 * k' - 1 := by
      rcases (Nat.Coprime.isPrimePow_dvd_mul hcop hpp).1 hd' with h | h
      · have := Nat.le_of_dvd hk' h; omega
      · exact Nat.le_of_dvd (by omega) h
    have : 3 ^ (f + 3) = 9 * 3 ^ (f + 1) := by ring
    omega

/-- `n` has 2-adic valuation `≤ ⌊log₂ h⌋` and 3-adic valuation `≤ ⌊log₃ 12h⌋`. -/
def Good (h n : ℕ) : Prop :=
  0 < n ∧ 2 ^ (n.factorization 2) ≤ h ∧ 3 ^ (n.factorization 3) ≤ 12 * h

lemma sc_div_mem {p h n : ℕ} [Fact p.Prime] (hp : p = 2 ∨ p = 3) (hg : Good h n) :
    ((sc h : ℕ) : ℚ) / (n : ℚ) ∈ LocRing p := by
  obtain ⟨hn, h2, h3⟩ := hg
  apply div_mem_locRing hn
  unfold sc
  rcases hp with rfl | rfl
  · exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (Nat.le_log_of_pow_le (by norm_num) h2)) _
  · exact Dvd.dvd.mul_left (Nat.pow_dvd_pow 3 (Nat.le_log_of_pow_le (by norm_num) h3)) _

lemma good_of_lt {h n : ℕ} (hn : 0 < n) (hnh : n < h) : Good h n :=
  ⟨hn, le_trans (Nat.ordProj_le 2 hn.ne') hnh.le,
    le_trans (Nat.ordProj_le 3 hn.ne') (by omega)⟩

lemma good_lin {h k : ℕ} (hk : 0 < k) (hkh : k < h) : Good h (4 * k - 3) := by
  refine ⟨by omega, ?_, le_trans (Nat.ordProj_le 3 (by omega)) (by omega)⟩
  rw [Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 4 * k - 3)]
  simp; omega

lemma good_phi {h k : ℕ} (hk : 0 < k) (hkh : k < h) : Good h (k * (4 * k - 3)) := by
  refine ⟨Nat.mul_pos hk (by omega), ?_, ?_⟩
  · rw [Nat.factorization_mul hk.ne' (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 4 * k - 3), add_zero]
    exact le_trans (Nat.ordProj_le 2 hk.ne') hkh.le
  · have := three_pow_le hk ((Nat.ordProj_dvd _ 3))
    omega

lemma mir_small_off {h a b : ℕ} (hab : a < b) (hbh : b < h) {p : ℕ} [Fact p.Prime]
    (hp : p = 2 ∨ p = 3) :
    (((4 * sc h : ℕ) : ℚ)) ^ 2 * mirFrame.Mn a b ∈ LocRing p := by
  have hs : ∑ k ∈ Ioc a b, mirFrame.Delta k =
      3 * ∑ k ∈ Ioc a b, (1 / ((k * (4 * k - 3) : ℕ) : ℚ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Ioc.mp hk).1; omega
    rw [mir_Delta hk0, Nat.cast_mul, cast43 hk0]
    ring
  have hba : ((b : ℚ) - a) ≠ 0 := by
    have : (a : ℚ) < b := by exact_mod_cast hab
    linarith
  have key : (((4 * sc h : ℕ) : ℚ)) ^ 2 * mirFrame.Mn a b =
      3 * (((sc h : ℚ) / ((b - a : ℕ) : ℚ)) *
        ∑ k ∈ Ioc a b, ((sc h : ℚ) / ((k * (4 * k - 3) : ℕ) : ℚ))) := by
    rw [mir_Mn_lt hab, hs, Nat.cast_sub hab.le]
    simp only [div_eq_mul_one_div (sc h : ℚ), ← Finset.mul_sum]
    push_cast
    field_simp
    ring
  rw [key]
  refine (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (3 : ℤ))
    ((LocRing p).mul_mem (sc_div_mem hp (good_of_lt (by omega) (by omega))) ?_)
  refine Subring.sum_mem _ fun k hk => ?_
  have hk' := Finset.mem_Ioc.mp hk
  exact sc_div_mem hp (good_phi (by omega) (by omega))

lemma mir_small_diag {h a : ℕ} (ha : a < h) {p : ℕ} [Fact p.Prime] (hp : p = 2 ∨ p = 3) :
    (((4 * sc h : ℕ) : ℚ)) ^ 2 * mirFrame.Mn a a ∈ LocRing p := by
  have key : (((4 * sc h : ℕ) : ℚ)) ^ 2 * mirFrame.Mn a a =
      -∑ k ∈ Icc 1 a, (16 * ((sc h : ℚ) / ((4 * k - 3 : ℕ) : ℚ)) ^ 2 -
        ((sc h : ℚ) / (k : ℚ)) ^ 2) := by
    rw [mir_Mn_diag, mul_neg, Finset.mul_sum, Finset.mul_sum, neg_inj]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk0
    have h4 : 4 * (k : ℚ) - 3 ≠ 0 := by linarith
    have h5 : (k : ℚ) ≠ 0 := by linarith
    rw [mir_Dsq hk0, cast43 hk0]
    push_cast
    field_simp
    ring
  rw [key]
  apply (LocRing p).neg_mem
  refine Subring.sum_mem _ fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  have hk0 : 0 < k := by omega
  refine (LocRing p).sub_mem ((LocRing p).mul_mem
    (by exact_mod_cast int_mem_locRing (ℓ := p) (16 : ℤ))
    ((LocRing p).pow_mem (sc_div_mem hp (good_lin hk0 (by omega))) 2))
    ((LocRing p).pow_mem (sc_div_mem hp (good_of_lt hk0 (by omega))) 2)

lemma mir_small_ok {p : ℕ} [Fact p.Prime] (hp : p = 2 ∨ p = 3) (h a b : ℕ) (ha : a < h)
    (hb : b < h) : (((4 * sc h : ℕ) : ℚ)) ^ 2 * mirFrame.Mn a b ∈ LocRing p := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact mir_small_off hab hb hp
  · exact mir_small_diag ha hp
  · rw [mir_Mn_symm]; exact mir_small_off hba ha hp

/-- The content table of the mirror. -/
noncomputable def mirCD : ContentData mirFrame where
  L := 4
  hL := by norm_num
  Phi := fun k => k * (4 * k - 3)
  Phi_pos := fun k hk => Nat.mul_pos hk (by omega)
  bad := {2, 3}
  bad_prime := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    exacts [Nat.prime_two, Nat.prime_three]
  normN := 16
  norm_eq := by simp [mirFrame]
  norm_dvd := by
    intro p hp hd
    have : p ∣ 2 ^ 4 := by norm_num; exact hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    simp [this]
  delta_int := by
    intro k hk
    refine ⟨3, ?_⟩
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have h4 : 4 * (k : ℚ) - 3 ≠ 0 := by linarith
    have h4' : (k : ℚ) * 4 - 3 ≠ 0 := by linarith
    have h5 : (k : ℚ) ≠ 0 := by linarith
    rw [mir_Delta hk, Nat.cast_mul, cast43 hk]
    push_cast
    field_simp
  dsq_int := by
    intro k hk
    refine ⟨16 * (k : ℤ) ^ 2 - (4 * (k : ℤ) - 3) ^ 2, ?_⟩
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have h4 : 4 * (k : ℚ) - 3 ≠ 0 := by linarith
    have h5 : (k : ℚ) ≠ 0 := by linarith
    rw [mir_Dsq hk, Nat.cast_mul, cast43 hk]
    push_cast
    field_simp
  kq := kq
  kq_le := by
    intro q k hq hbad hk hd
    have h2 : ¬ 2 ∣ q := hbad 2 (by simp)
    have h3 : ¬ 3 ∣ q := hbad 3 (by simp)
    have hodd : Odd q := Nat.odd_iff.mpr (by omega)
    have := kq_le_of_dvd hq hodd h3 hk hd
    exact ⟨this.1, by show q ≤ 4 * k; have := this.2; omega⟩
  small := fun h => 4 * sc h
  small_pos := fun h => by unfold sc; positivity
  small_ok := by
    intro p _ hp h a b ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    exact mir_small_ok hp h a b ha hb
  small_poly := by
    refine ⟨48, 2, fun h => ?_⟩
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp [sc]
    · have h2 := Nat.pow_log_le_self 2 hh.ne'
      have h3 := Nat.pow_log_le_self 3 (show 12 * h ≠ 0 by omega)
      have : sc h ≤ h * (12 * h) := Nat.mul_le_mul h2 h3
      nlinarith

/-- The residue classes of the mirror: `1 (mod 4)` with `c = 4`, `3 (mod 4)` with `c = 4/3`. -/
noncomputable def mirGD : GrowthData mirCD where
  M := 4
  n := 2
  res := ![1, 3]
  c := ![4, 4 / 3]
  d := ![0, 0]
  hc := by intro i; fin_cases i <;> norm_num
  hd := by intro i; fin_cases i <;> norm_num
  cover := by
    intro q _ hbad
    have h2 : ¬ 2 ∣ q := hbad 2 (by simp [mirCD])
    have hq : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases hq with h | h
    · exact ⟨0, by rw [← ZMod.natCast_mod q 4, h]; rfl⟩
    · exact ⟨1, by rw [← ZMod.natCast_mod q 4, h]; rfl⟩
  thr := by
    intro i q a hqp hbad hi hu
    have h2 : ¬ 2 ∣ q := hbad 2 (by simp [mirCD])
    have hu' : kq q ≤ a := hu
    unfold kq jq at hu'
    fin_cases i
    · have hi' : (q : ZMod 4) = ((1 : ℕ) : ZMod 4) := by simpa using hi
      have h1 : q % 4 = 1 := by
        have := (ZMod.natCast_eq_natCast_iff' q 1 4).mp hi'
        simpa using this
      simp only [h1, if_true] at hu'
      have : q ≤ 4 * a := by omega
      show (q : ℝ) ≤ (4 : ℝ) * a + 0
      have h4 : (q : ℝ) ≤ 4 * a := by exact_mod_cast this
      linarith
    · have hi' : (q : ZMod 4) = ((3 : ℕ) : ZMod 4) := by simpa using hi
      have h3 : q % 4 = 3 := by
        have := (ZMod.natCast_eq_natCast_iff' q 3 4).mp hi'
        simpa using this
      have h1 : ¬ q % 4 = 1 := by omega
      simp only [h1, if_false] at hu'
      have : 3 * q ≤ 4 * a := by omega
      have h4 : (3 * q : ℝ) ≤ 4 * a := by exact_mod_cast this
      show (q : ℝ) ≤ (4 / 3 : ℝ) * a + 0
      linarith

end CatalanFrames.LambdaMirror
