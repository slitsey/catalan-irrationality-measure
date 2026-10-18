module

public import CatalanCore.Arith.Growth

@[expose] public section

/-!
# Negative control: the λ frame through the generic content engine

Instantiates `ContentData`/`GrowthData` for the frame `F = ψ(z+1) - ψ(z+3/4)` (`w = ![-1,1]`,
`μ = ![3/4,1]`, `norm = 16`) and recovers `HasContent (ofFrame lamFrame) (313/105)`, the statement
that the legacy `CatalanLambda/{Integrality,Growth,GrowthFinal}` (about 780 lines) prove.
This is a test of the engine, not the production λ instance (that is `CatalanFrames/Lambda`, WP9).
-/

open Finset Classical Filter

namespace CatalanCore.Arith.Example

open Basic

/-- The λ frame. -/
def lamFrame : Frame where
  d := 2
  μ := ![3 / 4, 1]
  w := ![-1, 1]
  norm := 16
  xs := 5 / 8
  δ0 := 3 / 8
  n0off := 0
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
  hw := by simp [Fin.sum_univ_two]
  hnorm := by norm_num

lemma lam_Delta {k : ℕ} (hk : 0 < k) :
    lamFrame.Delta k = -(1 / ((k : ℚ) * (4 * k - 1))) := by
  have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have h4 : 4 * (k : ℚ) - 1 ≠ 0 := by linarith
  have h5 : (k : ℚ) ≠ 0 := by linarith
  have h6 : (k : ℚ) - 1 + 3 / 4 ≠ 0 := by linarith
  have h7 : (k : ℚ) - 1 + 1 ≠ 0 := by linarith
  have e : lamFrame.Delta k = ∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![(3 / 4 : ℚ), 1] i) := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  rw [show (k : ℚ) - 1 + 3 / 4 = (4 * k - 1) / 4 by ring, show (k : ℚ) - 1 + 1 = k by ring]
  field_simp
  ring

lemma lam_Dsq {k : ℕ} (hk : 0 < k) :
    lamFrame.Dsq k = 1 / (k : ℚ) ^ 2 - 16 / (4 * (k : ℚ) - 1) ^ 2 := by
  have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have h4 : 4 * (k : ℚ) - 1 ≠ 0 := by linarith
  have h5 : (k : ℚ) ≠ 0 := by linarith
  have h6 : (k : ℚ) - 1 + 3 / 4 ≠ 0 := by linarith
  have h7 : (k : ℚ) - 1 + 1 ≠ 0 := by linarith
  have e : lamFrame.Dsq k = ∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![(3 / 4 : ℚ), 1] i) ^ 2 := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  rw [show (k : ℚ) - 1 + 3 / 4 = (4 * k - 1) / 4 by ring, show (k : ℚ) - 1 + 1 = k by ring]
  field_simp
  ring

lemma lam_Mn_lt {a b : ℕ} (hab : a < b) :
    lamFrame.Mn a b = (1 / 16 : ℚ) * (1 / ((b : ℚ) - a)) * ∑ k ∈ Ioc a b, lamFrame.Delta k := by
  unfold Frame.Mn
  rw [if_neg hab.ne, max_eq_right hab.le, min_eq_left hab.le]
  simp [lamFrame]

lemma lam_Mn_diag (a : ℕ) :
    lamFrame.Mn a a = -((1 / 16 : ℚ) * ∑ k ∈ Icc 1 a, lamFrame.Dsq k) := by
  unfold Frame.Mn
  rw [if_pos rfl]
  simp [lamFrame]

lemma lam_Mn_symm (a b : ℕ) : lamFrame.Mn a b = lamFrame.Mn b a := by
  unfold Frame.Mn
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

/-! ### The 2-adic weight `small h = 4 · 2^{⌊log₂ h⌋}` -/

lemma two_div_mem {n h : ℕ} (hn : 0 < n) (hv : 2 ^ (n.factorization 2) ≤ h) :
    ((2 : ℚ) ^ Nat.log 2 h / (n : ℚ)) ∈ LocRing 2 := by
  have : ((2 ^ Nat.log 2 h : ℕ) : ℚ) / (n : ℚ) ∈ LocRing 2 := by
    apply div_mem_locRing hn
    apply Nat.pow_dvd_pow
    exact Nat.le_log_of_pow_le (by norm_num) hv
  simpa using this

lemma two_div_k {k h : ℕ} (hk : 0 < k) (hkh : k < h) : ((2 : ℚ) ^ Nat.log 2 h / (k : ℚ)) ∈ LocRing 2 :=
  two_div_mem hk (le_trans (Nat.ordProj_le 2 hk.ne') hkh.le)

lemma two_div_odd {n h : ℕ} (hn : 0 < n) (ho : ¬ 2 ∣ n) (hh : 0 < h) :
    ((2 : ℚ) ^ Nat.log 2 h / (n : ℚ)) ∈ LocRing 2 := by
  apply two_div_mem hn
  rw [Nat.factorization_eq_zero_of_not_dvd ho]
  simp; omega


/-! ### `kq` for λ (legacy `jq`, `kq`, `kq_le_of_dvd`) -/

/-- `j_q = 1` if `q ≡ 3 (mod 4)`, `3` otherwise. -/
def jq (q : ℕ) : ℕ := if q % 4 = 3 then 1 else 3

/-- First `k ≥ 1` with `q ∣ k (4k-1)` (for odd prime powers `q`). -/
def kq (q : ℕ) : ℕ := (jq q * q + 1) / 4

lemma jq_cases (q : ℕ) : jq q = 1 ∨ jq q = 3 := by unfold jq; split_ifs <;> simp

lemma kq_le_of_dvd {q k : ℕ} (hq : IsPrimePow q) (hqo : Odd q) (hk : 0 < k)
    (hd : q ∣ k * (4 * k - 1)) : kq q ≤ k ∧ q ≤ 4 * k - 1 := by
  obtain ⟨p, e, hp0, he, rfl⟩ := hq
  have hp := hp0.nat_prime
  have hq2 : (p ^ e) % 2 = 1 := Nat.odd_iff.mp hqo
  have hcop : Nat.Coprime k (4 * k - 1) := by
    have h1 : Nat.gcd k (4 * k - 1) ∣ 4 * k - 1 := Nat.gcd_dvd_right _ _
    have h2 : Nat.gcd k (4 * k - 1) ∣ 4 * k := Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 4
    have h3 := Nat.dvd_sub h2 h1
    have : 4 * k - (4 * k - 1) = 1 := by omega
    rw [this] at h3
    exact Nat.dvd_one.mp h3
  have hcases : p ^ e ∣ k ∨ p ^ e ∣ 4 * k - 1 := by
    by_cases hpk : p ∣ k
    · left
      have : Nat.Coprime p (4 * k - 1) := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro h4
        have := Nat.dvd_sub (Dvd.dvd.mul_left hpk 4) h4
        have e1 : 4 * k - (4 * k - 1) = 1 := by omega
        rw [e1] at this
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      exact (Nat.Coprime.pow_left e this).dvd_of_dvd_mul_right hd
    · right
      have : Nat.Coprime (p ^ e) k := Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
      exact this.dvd_of_dvd_mul_left hd
  have hjq := jq_cases (p ^ e)
  rcases hcases with hc | hc
  · have := Nat.le_of_dvd hk hc
    unfold kq
    rcases hjq with hj | hj <;> rw [hj] <;> omega
  · obtain ⟨t, ht⟩ := hc
    have h4k : 4 * k - 1 = (p ^ e) * t := ht
    have hq3 : (p ^ e) % 4 = 1 ∨ (p ^ e) % 4 = 3 := by omega
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0] at h4k; omega
      · exact h0
    refine ⟨?_, ?_⟩
    · unfold kq
      have hmod : ((p ^ e) * t) % 4 = 3 := by omega
      rcases hq3 with h1 | h3
      · have hj : jq (p ^ e) = 3 := by unfold jq; simp [h1]
        rw [hj]
        have := Nat.mul_mod (p ^ e) t 4
        rw [h1] at this
        have ht3 : t % 4 = 3 := by omega
        have : 3 ≤ t := by omega
        have : 3 * (p ^ e) ≤ (p ^ e) * t := by nlinarith
        omega
      · have hj : jq (p ^ e) = 1 := by unfold jq; simp [h3]
        rw [hj]
        have : (p ^ e) ≤ (p ^ e) * t := Nat.le_mul_of_pos_right _ htpos
        omega
    · rw [h4k]; exact Nat.le_mul_of_pos_right _ htpos

lemma cast4 {k : ℕ} (hk : 0 < k) : ((4 * k - 1 : ℕ) : ℚ) = 4 * (k : ℚ) - 1 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma two_div_phi {k h : ℕ} (hk : 0 < k) (hkh : k < h) :
    ((2 : ℚ) ^ Nat.log 2 h / ((k * (4 * k - 1) : ℕ) : ℚ)) ∈ LocRing 2 := by
  apply two_div_mem (Nat.mul_pos hk (by omega))
  rw [Nat.factorization_mul hk.ne' (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 4 * k - 1), add_zero]
  exact le_trans (Nat.ordProj_le 2 hk.ne') hkh.le

lemma lam_small_off {h a b : ℕ} (hab : a < b) (hbh : b < h) :
    (((4 * 2 ^ Nat.log 2 h : ℕ) : ℚ)) ^ 2 * lamFrame.Mn a b ∈ LocRing 2 := by
  have hs : ∑ k ∈ Ioc a b, lamFrame.Delta k =
      -∑ k ∈ Ioc a b, (1 / ((k * (4 * k - 1) : ℕ) : ℚ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Ioc.mp hk).1; omega
    rw [lam_Delta hk0, Nat.cast_mul, cast4 hk0]
  have hba : ((b : ℚ) - a) ≠ 0 := by
    have : (a : ℚ) < b := by exact_mod_cast hab
    linarith
  have h2 : (2 : ℚ) ^ Nat.log 2 h ≠ 0 := by positivity
  have key : (((4 * 2 ^ Nat.log 2 h : ℕ) : ℚ)) ^ 2 * lamFrame.Mn a b =
      -(((2 : ℚ) ^ Nat.log 2 h / ((b - a : ℕ) : ℚ)) *
        ∑ k ∈ Ioc a b, ((2 : ℚ) ^ Nat.log 2 h / ((k * (4 * k - 1) : ℕ) : ℚ))) := by
    rw [lam_Mn_lt hab, hs, Nat.cast_sub hab.le]
    simp only [div_eq_mul_one_div ((2 : ℚ) ^ Nat.log 2 h), ← Finset.mul_sum]
    push_cast
    field_simp
    ring
  rw [key]
  apply (LocRing 2).neg_mem
  apply (LocRing 2).mul_mem
  · apply two_div_mem (by omega)
    exact le_trans (Nat.ordProj_le 2 (by omega)) (by omega)
  · refine Subring.sum_mem _ fun k hk => ?_
    have hk' := Finset.mem_Ioc.mp hk
    exact two_div_phi (by omega) (by omega)

lemma lam_small_diag {h a : ℕ} (ha : a < h) :
    (((4 * 2 ^ Nat.log 2 h : ℕ) : ℚ)) ^ 2 * lamFrame.Mn a a ∈ LocRing 2 := by
  have hsum : ∑ k ∈ Icc 1 a, (((2 : ℚ) ^ Nat.log 2 h / (k : ℚ)) ^ 2 -
        16 * ((2 : ℚ) ^ Nat.log 2 h / ((4 * k - 1 : ℕ) : ℚ)) ^ 2) =
      (((4 * 2 ^ Nat.log 2 h : ℕ) : ℚ)) ^ 2 * ((1 / 16 : ℚ) * ∑ k ∈ Icc 1 a, lamFrame.Dsq k) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk0
    have h4 : 4 * (k : ℚ) - 1 ≠ 0 := by linarith
    have h5 : (k : ℚ) ≠ 0 := by linarith
    rw [lam_Dsq hk0, cast4 hk0]
    push_cast
    field_simp
    ring
  have key : (((4 * 2 ^ Nat.log 2 h : ℕ) : ℚ)) ^ 2 * lamFrame.Mn a a =
      -∑ k ∈ Icc 1 a, (((2 : ℚ) ^ Nat.log 2 h / (k : ℚ)) ^ 2 -
        16 * ((2 : ℚ) ^ Nat.log 2 h / ((4 * k - 1 : ℕ) : ℚ)) ^ 2) := by
    rw [hsum, lam_Mn_diag]; ring
  rw [key]
  apply (LocRing 2).neg_mem
  refine Subring.sum_mem _ fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  have hk0 : 0 < k := by omega
  apply (LocRing 2).sub_mem ((LocRing 2).pow_mem (two_div_k hk0 (by omega)) 2)
  apply (LocRing 2).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := 2) (16 : ℤ))
  exact (LocRing 2).pow_mem (two_div_odd (by omega) (by omega) (by omega)) 2

lemma lam_small_ok (h a b : ℕ) (ha : a < h) (hb : b < h) :
    (((4 * 2 ^ Nat.log 2 h : ℕ) : ℚ)) ^ 2 * lamFrame.Mn a b ∈ LocRing 2 := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact lam_small_off hab hb
  · exact lam_small_diag ha
  · rw [lam_Mn_symm]; exact lam_small_off hba ha

/-- The content table of λ. -/
noncomputable def lamCD : ContentData lamFrame where
  L := 4
  hL := by norm_num
  Phi := fun k => k * (4 * k - 1)
  Phi_pos := fun k hk => Nat.mul_pos hk (by omega)
  bad := {2}
  bad_prime := by intro p hp; simp at hp; subst hp; exact Nat.prime_two
  normN := 16
  norm_eq := by simp [lamFrame]
  norm_dvd := by
    intro p hp hd
    have : p ∣ 2 ^ 4 := by norm_num; exact hd
    simpa using (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
  delta_int := by
    intro k hk
    refine ⟨-1, ?_⟩
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have h4 : 4 * (k : ℚ) - 1 ≠ 0 := by linarith
    have h4' : (k : ℚ) * 4 - 1 ≠ 0 := by linarith
    have h5 : (k : ℚ) ≠ 0 := by linarith
    rw [lam_Delta hk, Nat.cast_mul, cast4 hk]
    push_cast
    field_simp
  dsq_int := by
    intro k hk
    refine ⟨(4 * (k : ℤ) - 1) ^ 2 - 16 * (k : ℤ) ^ 2, ?_⟩
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have h4 : 4 * (k : ℚ) - 1 ≠ 0 := by linarith
    have h4' : (k : ℚ) * 4 - 1 ≠ 0 := by linarith
    have h5 : (k : ℚ) ≠ 0 := by linarith
    rw [lam_Dsq hk, Nat.cast_mul, cast4 hk]
    push_cast
    field_simp
  kq := kq
  kq_le := by
    intro q k hq hbad hk hd
    have hodd : Odd q := Nat.odd_iff.mpr (by have := hbad 2 (by simp); omega)
    have := kq_le_of_dvd hq hodd hk hd
    exact ⟨this.1, by show q ≤ 4 * k; have := this.2; omega⟩
  small := fun h => 4 * 2 ^ Nat.log 2 h
  small_pos := fun h => by positivity
  small_ok := by
    intro p _ hp h a b ha hb
    have : p = 2 := by simpa using hp
    subst this
    exact lam_small_ok h a b ha hb
  small_poly := by
    refine ⟨4, 1, fun h => ?_⟩
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp
    · have := Nat.pow_log_le_self 2 hh.ne'
      simp only [pow_one]
      nlinarith

/-- The residue classes of λ: `3 (mod 4)` with `c = 4`, and `1 (mod 4)` with `c = 4/3`. -/
noncomputable def lamGD : GrowthData lamCD where
  M := 4
  n := 2
  res := ![3, 1]
  c := ![4, 4 / 3]
  d := ![2, 2 / 3]
  hc := by intro i; fin_cases i <;> norm_num
  hd := by intro i; fin_cases i <;> norm_num
  cover := by
    intro q _ hbad
    have h2 : ¬ 2 ∣ q := hbad 2 (by simp [lamCD])
    have hq : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases hq with h | h
    · exact ⟨1, by rw [← ZMod.natCast_mod q 4, h]; rfl⟩
    · exact ⟨0, by rw [← ZMod.natCast_mod q 4, h]; rfl⟩
  thr := by
    intro i q a hqp hbad hi hu
    have h2 : ¬ 2 ∣ q := hbad 2 (by simp [lamCD])
    have hu' : kq q ≤ a := hu
    unfold kq jq at hu'
    fin_cases i
    · have hi' : (q : ZMod 4) = ((3 : ℕ) : ZMod 4) := by simpa using hi
      have h3 : q % 4 = 3 := by
        have := (ZMod.natCast_eq_natCast_iff' q 3 4).mp hi'
        simpa using this
      simp only [h3, if_true] at hu'
      have : q ≤ 4 * a + 2 := by omega
      show (q : ℝ) ≤ (4 : ℝ) * a + 2
      exact_mod_cast this
    · have hi' : (q : ZMod 4) = ((1 : ℕ) : ZMod 4) := by simpa using hi
      have h1 : q % 4 = 1 := by
        have := (ZMod.natCast_eq_natCast_iff' q 1 4).mp hi'
        simpa using this
      have h3 : ¬ q % 4 = 3 := by omega
      simp only [h3, if_false] at hu'
      have : 3 * q ≤ 4 * a + 2 := by omega
      have h4 : (3 * q : ℝ) ≤ 4 * a + 2 := by exact_mod_cast this
      show (q : ℝ) ≤ (4 / 3 : ℝ) * a + 2 / 3
      linarith

/-- Negative control: the engine reproduces `313/105` for λ. -/
theorem lam_hasContent : HasContent (PolyFamily.ofFrame lamFrame) (313 / 105) := by
  have : NeZero lamGD.M := inferInstanceAs (NeZero 4)
  have hunit : ∀ i, IsUnit (lamGD.res i) := by
    intro i; fin_cases i
    · exact (by decide : IsUnit (3 : ZMod 4))
    · exact isUnit_one
  have e : lamGD.Lam = 313 / 105 := by
    have : lamGD.Lam = 2 * ((Nat.totient 4 : ℕ) : ℝ)⁻¹ * ∑ i : Fin 2, Icont (![4, 4 / 3] i) := rfl
    rw [this, Fin.sum_univ_two]
    have : Nat.totient 4 = 2 := by decide
    norm_num [Icont, this]
  have := hasContent_of_classes lamGD hunit
  rwa [e] at this

end CatalanCore.Arith.Example
