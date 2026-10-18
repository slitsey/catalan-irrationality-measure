module

public import CatalanLambda.Defs
public import CatalanLambda.Local
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Pow

@[expose] public section

/-!
# Integrality of `q^h · D_h · P_h(p/q)` (AQ steps 2-3, integer formulation)
-/

open Finset Matrix Classical

namespace CatalanLambda

/-- `j_q = 1` if `q ≡ 3 (mod 4)`, `3` otherwise. -/
def jq (q : ℕ) : ℕ := if q % 4 = 3 then 1 else 3

/-- First `k ≥ 1` with `q ∣ k (4k-1)` (for odd prime powers `q`). -/
def kq (q : ℕ) : ℕ := (jq q * q + 1) / 4

/-- The AQ potential: `u_q(a) = 1`. -/
def uq (h q a : ℕ) : Prop := kq q ≤ a ∨ a + 1 + q ≤ h

/-- Odd prime powers `≤ 4h`. -/
noncomputable def Qset (h : ℕ) : Finset ℕ :=
  (Finset.range (4 * h + 1)).filter (fun q => IsPrimePow q ∧ Odd q)

/-- Odd part of the scaling weight. -/
noncomputable def Wodd (h a : ℕ) : ℕ := ∏ q ∈ (Qset h).filter (fun q => uq h q a), q.minFac

/-- `2^{L} · Wodd`, `L = ⌊log₂ h⌋`. -/
noncomputable def Wm (h a : ℕ) : ℕ := 2 ^ Nat.log 2 h * Wodd h a

/-- The scaling weight `W(a)`. -/
noncomputable def W (h a : ℕ) : ℕ := 4 * Wm h a

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

lemma uq_of_dvd_diff {h q a b : ℕ} (hab : a < b) (hb : b < h) (hd : q ∣ b - a) : uq h q a := by
  right
  have := Nat.le_of_dvd (by omega) hd
  omega

lemma uq_of_dvd_supp {h q k b : ℕ} (hq : IsPrimePow q) (hqo : Odd q) (hk : 0 < k) (hkb : k ≤ b)
    (hd : q ∣ k * (4 * k - 1)) : uq h q b := by
  left
  have := (kq_le_of_dvd hq hqo hk hd).1
  omega

/-- `p^{v_p(n)}` divides the odd weight when every prime power `p^e ∣ n` is "active". -/
lemma pow_dvd_Wodd {h c n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : ∀ e, 0 < e → p ^ e ∣ n → p ^ e ≤ 4 * h ∧ uq h (p ^ e) c) :
    p ^ (n.factorization p) ∣ Wodd h c := by
  set v := n.factorization p with hv
  have hinj : Set.InjOn (fun e : ℕ => p ^ e) (Finset.Icc 1 v : Finset ℕ) := fun x _ y _ hxy =>
    Nat.pow_right_injective hp.two_le hxy
  have h1 : p ^ v = ∏ q ∈ (Finset.Icc 1 v).image (fun e : ℕ => p ^ e), q.minFac := by
    rw [Finset.prod_image hinj]
    rw [Finset.prod_congr rfl (g := fun _ => p)]
    · simp
    · intro e he
      have : e ≠ 0 := by have := (Finset.mem_Icc.mp he).1; omega
      exact hp.pow_minFac this
  rw [h1]
  unfold Wodd
  apply Finset.prod_dvd_prod_of_subset
  intro q hq
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
  have he1 := (Finset.mem_Icc.mp he).1
  have he2 := (Finset.mem_Icc.mp he).2
  have hdvd : p ^ e ∣ n := (Nat.pow_dvd_pow p he2).trans (Nat.ordProj_dvd n p)
  obtain ⟨hle, hu⟩ := H e he1 hdvd
  simp only [Finset.mem_filter, Qset, Finset.mem_range]
  refine ⟨⟨by omega, ?_, ?_⟩, hu⟩
  · exact (hp.isPrimePow).pow (by omega)
  · exact (hp.odd_of_ne_two hp2).pow

lemma div_mem_S {p : ℕ} [hp : Fact p.Prime] {n W : ℕ} (hn : 0 < n)
    (h : p ^ (n.factorization p) ∣ W) : ((W : ℚ) / n) ∈ S p := by
  obtain ⟨t, ht⟩ := h
  have hm : ¬ p ∣ n / p ^ (n.factorization p) := Nat.not_dvd_ordCompl hp.out hn.ne'
  have hn' : p ^ (n.factorization p) * (n / p ^ (n.factorization p)) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  set m := n / p ^ (n.factorization p) with hmdef
  have hpv : (p : ℚ) ^ (n.factorization p) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0] at hn'; omega
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have : ((W : ℚ) / n) = (t : ℚ) * ((m : ℚ))⁻¹ := by
    have hnq : (n : ℚ) = (p : ℚ) ^ (n.factorization p) * m := by exact_mod_cast hn'.symm
    rw [ht, hnq]; push_cast; field_simp
  rw [this]
  apply (S p).mul_mem
  · exact natCast_mem (S p) t
  · show ¬ p ∣ ((m : ℚ))⁻¹.den
    rw [Rat.inv_natCast_den]; simpa [hm0] using hm

lemma memS_A {h a b p : ℕ} [hpf : Fact p.Prime] (hab : a < b) (hb : b < h) :
    ((Wm h a : ℚ) / ((b - a : ℕ) : ℚ)) ∈ S p := by
  have hp : p.Prime := hpf.out
  apply div_mem_S (by omega)
  unfold Wm
  by_cases hp2 : p = 2
  · subst hp2
    refine (Dvd.dvd.mul_right ?_ _)
    apply Nat.pow_dvd_pow
    apply Nat.le_log_of_pow_le (by norm_num)
    have := Nat.ordProj_le 2 (show b - a ≠ 0 by omega)
    omega
  · refine Dvd.dvd.mul_left ?_ _
    apply pow_dvd_Wodd hp hp2
    intro e he hd
    exact ⟨by have := Nat.le_of_dvd (by omega) hd; omega, uq_of_dvd_diff hab hb hd⟩

lemma memS_B {h k n b p : ℕ} [hpf : Fact p.Prime] (hk : 0 < k) (hkb : k ≤ b) (hb : b < h)
    (hn : 0 < n) (hnd : n ∣ k * (4 * k - 1)) :
    ((Wm h b : ℚ) / (n : ℚ)) ∈ S p := by
  have hp : p.Prime := hpf.out
  apply div_mem_S hn
  unfold Wm
  by_cases hp2 : p = 2
  · subst hp2
    refine (Dvd.dvd.mul_right ?_ _)
    apply Nat.pow_dvd_pow
    apply Nat.le_log_of_pow_le (by norm_num)
    have hd1 : 2 ^ (n.factorization 2) ∣ k * (4 * k - 1) := (Nat.ordProj_dvd n 2).trans hnd
    have hcop : Nat.Coprime (2 ^ (n.factorization 2)) (4 * k - 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_two_left]
      exact ⟨2 * k - 1, by omega⟩
    have hd2 := hcop.dvd_of_dvd_mul_right hd1
    have := Nat.le_of_dvd hk hd2
    omega
  · refine Dvd.dvd.mul_left ?_ _
    apply pow_dvd_Wodd hp hp2
    intro e he hd
    have hd' : p ^ e ∣ k * (4 * k - 1) := hd.trans hnd
    have hpp : IsPrimePow (p ^ e) := hp.isPrimePow.pow (by omega)
    have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
    have := kq_le_of_dvd hpp hodd hk hd'
    exact ⟨by omega, uq_of_dvd_supp hpp hodd hk hkb hd'⟩

lemma cast_4k1 {k : ℕ} (hk : 0 < k) : ((4 * k - 1 : ℕ) : ℚ) = 4 * (k : ℚ) - 1 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma int_of_forall_S (x : ℚ) (H : ∀ (p : ℕ) [Fact p.Prime], x ∈ S p) : ∃ z : ℤ, x = z := by
  by_cases hd : x.den = 1
  · exact ⟨x.num, (Rat.coe_int_num_of_den_eq_one hd).symm⟩
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    haveI := Fact.mk hp
    exact absurd hpd (H p)

lemma Wm_pos (h a : ℕ) : 0 < Wm h a := by
  unfold Wm Wodd
  apply Nat.mul_pos (by positivity)
  apply Finset.prod_pos
  intro q _
  exact Nat.minFac_pos q

lemma W_pos (h a : ℕ) : 0 < W h a := by unfold W; have := Wm_pos h a; omega

lemma M0n_lt {a b : ℕ} (hab : a < b) :
    M0n a b = -(1 / (4 * ((b : ℚ) - a))) *
      ∑ k ∈ Ioc a b, 1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)) := by
  unfold M0n
  rw [if_neg hab.ne, max_eq_right hab.le, min_eq_left hab.le]

lemma M0n_symm (a b : ℕ) : M0n a b = M0n b a := by
  unfold M0n
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

lemma entry_lt (h : ℕ) {a b : ℕ} (hab : a < b) (hb : b < h) :
    ∃ z : ℤ, (W h a : ℚ) * W h b * M0n a b = z := by
  apply int_of_forall_S
  intro p hpf
  have hp : p.Prime := Fact.out
  have key : (W h a : ℚ) * W h b * M0n a b =
      -(((Wm h a : ℚ) / ((b - a : ℕ) : ℚ)) *
        ∑ k ∈ Ioc a b, ((Wm h b : ℚ) / ((k * (4 * k - 1) : ℕ) : ℚ))) := by
    rw [M0n_lt hab, Nat.cast_sub hab.le]
    have hba : ((b : ℚ) - a) ≠ 0 := by
      have : (a : ℚ) < b := by exact_mod_cast hab
      linarith
    have hs : ∀ k ∈ Ioc a b, (Wm h b : ℚ) / ((k * (4 * k - 1) : ℕ) : ℚ)
        = (Wm h b : ℚ) * (4 * (1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)))) := by
      intro k hk
      have hk0 : 0 < k := by have := (Finset.mem_Ioc.mp hk).1; omega
      rw [Nat.cast_mul, cast_4k1 hk0]
      have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk0
      have h4 : 4 * (k : ℚ) - 1 ≠ 0 := by linarith
      have h5 : (k : ℚ) ≠ 0 := by linarith
      field_simp
    rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold W
    push_cast
    field_simp
  rw [key]
  apply (S p).neg_mem
  apply (S p).mul_mem (memS_A hab hb)
  apply Subring.sum_mem
  intro k hk
  have hk' := Finset.mem_Ioc.mp hk
  have hk0 : 0 < k := by omega
  have h2 : 0 < 4 * k - 1 := by omega
  exact memS_B hk0 hk'.2 hb (Nat.mul_pos hk0 h2) dvd_rfl

lemma entry_diag (h : ℕ) {a : ℕ} (ha : a < h) :
    ∃ z : ℤ, (W h a : ℚ) * W h a * M0n a a = z := by
  apply int_of_forall_S
  intro p hpf
  have key : (W h a : ℚ) * W h a * M0n a a =
      -∑ k ∈ Icc 1 a, (((Wm h a : ℚ) / (k : ℚ)) ^ 2 -
        16 * ((Wm h a : ℚ) / ((4 * k - 1 : ℕ) : ℚ)) ^ 2) := by
    unfold M0n
    rw [if_pos rfl, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
    rw [cast_4k1 hk0]
    have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk0
    have h4 : 4 * (k : ℚ) - 1 ≠ 0 := by linarith
    have h5 : (k : ℚ) ≠ 0 := by linarith
    unfold W
    push_cast
    field_simp
    ring
  rw [key]
  apply (S p).neg_mem
  apply Subring.sum_mem
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  have hk0 : 0 < k := by omega
  have h2 : 0 < 4 * k - 1 := by omega
  have m1 : ((Wm h a : ℚ) / (k : ℚ)) ∈ S p :=
    memS_B hk0 hk'.2 ha hk0 (Dvd.intro _ rfl)
  have m2 : ((Wm h a : ℚ) / ((4 * k - 1 : ℕ) : ℚ)) ∈ S p :=
    memS_B hk0 hk'.2 ha h2 (Dvd.intro_left _ rfl)
  have s16 : (16 : ℚ) ∈ S p := by simpa using natCast_mem (S p) 16
  exact (S p).sub_mem ((S p).pow_mem m1 2) ((S p).mul_mem s16 ((S p).pow_mem m2 2))

theorem entry_int (h : ℕ) {a b : ℕ} (ha : a < h) (hb : b < h) :
    ∃ z : ℤ, (W h a : ℚ) * W h b * M0n a b = z := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact entry_lt h hab hb
  · exact entry_diag h ha
  · obtain ⟨z, hz⟩ := entry_lt h hba ha
    exact ⟨z, by rw [M0n_symm, mul_comm (W h a : ℚ)]; exact hz⟩

/-- The explicit denominator-clearing constant: `D_h = (∏_{a<h} W(a))²`. -/
noncomputable def Dden (h : ℕ) : ℕ := (∏ a : Fin h, W h a) ^ 2

lemma Dden_pos (h : ℕ) : 0 < Dden h := by
  unfold Dden
  apply pow_pos
  exact Finset.prod_pos fun a _ => W_pos h a

/-- **(2a-i)**  `q^h · D_h · P_h(p/q)` is an integer. -/
theorem integrality (h : ℕ) (p q : ℤ) (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ) ^ h * (Dden h : ℚ) * P h ((p : ℚ) / q) = z := by
  choose Z hZ using fun (a b : Fin h) => entry_int h a.2 b.2
  let Zm : Matrix (Fin h) (Fin h) ℤ :=
    Matrix.of fun a b => (if a = b then p * (W h a : ℤ) * (W h a : ℤ) else 0) + q * Z a b
  refine ⟨Zm.det, ?_⟩
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmat : Zm.map (Int.cast : ℤ → ℚ) =
      (q : ℚ) • (Matrix.diagonal (fun a : Fin h => (W h a : ℚ)) *
        (((p : ℚ) / q) • (1 : Matrix (Fin h) (Fin h) ℚ) + M0 h) *
        Matrix.diagonal (fun a : Fin h => (W h a : ℚ))) := by
    ext a b
    simp only [Matrix.map_apply, Zm, Matrix.of_apply, Matrix.smul_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply, M0, smul_eq_mul]
    have := hZ a b
    by_cases hab : a = b
    · subst hab
      simp only [if_true, Int.cast_add, Int.cast_mul, Int.cast_ite, Int.cast_zero, Int.cast_natCast]
      rw [← this]
      field_simp
    · simp only [hab, ite_false, Int.cast_add, Int.cast_mul, Int.cast_ite, Int.cast_zero, mul_zero, add_zero, Int.cast_natCast]
      rw [← this]
      ring
  have hdet := RingHom.map_det (Int.castRingHom ℚ) Zm
  have hmap : (Int.castRingHom ℚ).mapMatrix Zm = Zm.map (Int.cast : ℤ → ℚ) := rfl
  rw [hmap, hmat, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  simp only [eq_intCast, Fintype.card_fin] at hdet
  rw [hdet]
  unfold Dden P
  push_cast
  ring

/-- **(2a-i)** packaged form. -/
theorem exists_denominator_clearing (h : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∀ p q : ℤ, 0 < q → ∃ z : ℤ, (q : ℚ) ^ h * D * P h ((p : ℚ) / q) = z :=
  ⟨Dden h, Dden_pos h, fun p q hq => integrality h p q hq⟩

end CatalanLambda
