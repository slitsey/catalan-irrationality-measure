module

public import CatalanCore.Frame.Spec
public import CatalanCore.Basic.PrimePower
public import Mathlib.Data.Nat.Log
public import Mathlib.RingTheory.MatrixPolynomialAlgebra
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The content engine, part 1: integrality of `q^h · Dden(h) · P_h(p/q)`

Generalises `CatalanLambda/Integrality` (and its Mirror twin) to any `Frame`, driven by a small
table `ContentData`.  The row weight is `W(a) = small(h) · ∏_{q active at a} minFac q`, where
`q` runs over prime powers `≤ L h` prime to the finitely many "bad" primes (those dividing the
normalisation, plus whatever the instance wants to treat by hand), and `q` is *active* at `a`
iff `kq q ≤ a ∨ a + 1 + q ≤ h`.  This is the dual certificate of the tropical bound
(FJ-P6 Lemma 3.2): `u_a = 1[a high] + 1[a low, a ≤ h-1-q]`.

Instance obligations (see `ContentData`):
* numerator integrality `Δ_k Φ(k) ∈ ℤ`, `D_k Φ(k)² ∈ ℤ`;
* `kq`: a prime power `q` dividing `Φ(k)` has `kq q ≤ k` and `q ≤ L k` (λ: Lemma `kq_le_of_dvd`;
  P6: FJ Lemma 3.1);
* the bad primes (2 for λ, 2 and 3 for P6) are handled by a weight `small h`, with
  `small(h)² · M[a][b] ∈ ℤ_(p)` and `small(h)` polynomially bounded.
-/

open Finset Matrix Classical

namespace CatalanCore.Arith

open Basic

/-- What an instance supplies to the content engine. -/
structure ContentData (Fr : Frame) where
  /-- all linear forms of `Φ(k)` are `≤ L k` -/
  L : ℕ
  hL : 1 ≤ L
  /-- `Φ(k)`: product of the linear forms in the denominators of `Δ_k`
  (λ: `k(4k-1)`; mirror: `k(4k-3)`; P6: `k(3k-2)(2k-1)`) -/
  Phi : ℕ → ℕ
  Phi_pos : ∀ k, 0 < k → 0 < Phi k
  /-- primes treated by hand -/
  bad : Finset ℕ
  bad_prime : ∀ p ∈ bad, p.Prime
  /-- the normalisation is a natural number divisible only by bad primes -/
  normN : ℕ
  norm_eq : Fr.norm = normN
  norm_dvd : ∀ p, p.Prime → p ∣ normN → p ∈ bad
  delta_int : ∀ k, 0 < k → ∃ z : ℤ, Fr.Delta k * Phi k = z
  dsq_int : ∀ k, 0 < k → ∃ z : ℤ, Fr.Dsq k * (Phi k : ℚ) ^ 2 = z
  /-- first index at which a prime power `q` can divide `Φ` -/
  kq : ℕ → ℕ
  kq_le : ∀ q k, IsPrimePow q → (∀ p ∈ bad, ¬ p ∣ q) → 0 < k → q ∣ Phi k →
    kq q ≤ k ∧ q ≤ L * k
  /-- weight for the bad primes -/
  small : ℕ → ℕ
  small_pos : ∀ h, 0 < small h
  small_ok : ∀ (p : ℕ) [Fact p.Prime], p ∈ bad → ∀ h a b, a < h → b < h →
    ((small h : ℚ)) ^ 2 * Fr.Mn a b ∈ LocRing p
  small_poly : ∃ A C : ℕ, ∀ h, small h ≤ A * (h + 1) ^ C

namespace ContentData

variable {Fr : Frame} (cd : ContentData Fr)

/-- `q` is active at row `a` (for size `h`). -/
def uq (h q a : ℕ) : Prop := cd.kq q ≤ a ∨ a + 1 + q ≤ h

/-- Prime powers `≤ L h`, prime to the bad primes. -/
noncomputable def Qset (h : ℕ) : Finset ℕ :=
  (Finset.range (cd.L * h + 1)).filter (fun q => IsPrimePow q ∧ ∀ p ∈ cd.bad, ¬ p ∣ q)

/-- Active prime powers at row `a`. -/
noncomputable def Fa (h a : ℕ) : Finset ℕ := (cd.Qset h).filter (fun q => cd.uq h q a)

/-- The part of the weight made of active prime powers. -/
noncomputable def Wodd (h a : ℕ) : ℕ := ∏ q ∈ cd.Fa h a, q.minFac

/-- The row weight. -/
noncomputable def W (h a : ℕ) : ℕ := cd.small h * cd.Wodd h a

/-- The denominator-clearing constant `Dden = (∏_{a<h} W(a))²`. -/
noncomputable def Dden (h : ℕ) : ℕ := (∏ a : Fin h, cd.W h a) ^ 2

lemma Wodd_pos (h a : ℕ) : 0 < cd.Wodd h a :=
  Finset.prod_pos fun q _ => Nat.minFac_pos q

lemma W_pos (h a : ℕ) : 0 < cd.W h a := Nat.mul_pos (cd.small_pos h) (cd.Wodd_pos h a)

lemma Dden_pos (h : ℕ) : 0 < cd.Dden h := by
  unfold Dden
  exact pow_pos (Finset.prod_pos fun (a : Fin h) _ => cd.W_pos h (a : ℕ)) 2

lemma normN_pos : 0 < cd.normN := by
  have := Fr.hnorm
  rw [cd.norm_eq] at this
  exact_mod_cast this

/-- Primes not in `bad` do not divide `normN`. -/
lemma not_dvd_normN {p : ℕ} (hp : p.Prime) (hb : p ∉ cd.bad) : ¬ p ∣ cd.normN :=
  fun h => hb (cd.norm_dvd p hp h)

lemma coprime_bad_pow {p e : ℕ} (hp : p.Prime) (hb : p ∉ cd.bad) :
    ∀ p' ∈ cd.bad, ¬ p' ∣ p ^ e := by
  intro p' hp' hd
  have hp'p : p' ∣ p := (cd.bad_prime p' hp').dvd_of_dvd_pow hd
  have := (Nat.prime_dvd_prime_iff_eq (cd.bad_prime p' hp') hp).1 hp'p
  exact hb (this ▸ hp')

lemma pow_dvd_Wodd {h c n p : ℕ} (hp : p.Prime) (hb : p ∉ cd.bad)
    (H : ∀ e, 0 < e → p ^ e ∣ n → p ^ e ≤ cd.L * h ∧ cd.uq h (p ^ e) c) :
    p ^ (n.factorization p) ∣ cd.Wodd h c := by
  apply pow_dvd_prod_minFac hp
  intro e he hd
  obtain ⟨h1, h2⟩ := H e he hd
  simp only [Fa, Qset, Finset.mem_filter, Finset.mem_range]
  exact ⟨⟨by omega, hp.isPrimePow.pow (by omega), cd.coprime_bad_pow hp hb⟩, h2⟩

lemma memS_A {h a b p : ℕ} [hpf : Fact p.Prime] (hb : p ∉ cd.bad) (hab : a < b) (hbh : b < h) :
    ((cd.Wodd h a : ℚ) / ((b - a : ℕ) : ℚ)) ∈ LocRing p := by
  apply div_mem_locRing (by omega)
  apply cd.pow_dvd_Wodd hpf.out hb
  intro e _ hd
  have := Nat.le_of_dvd (by omega) hd
  have hL := cd.hL
  exact ⟨by have := Nat.le_mul_of_pos_left h (show 0 < cd.L by omega); omega, Or.inr (by omega)⟩

lemma memS_B {h k n b p : ℕ} [hpf : Fact p.Prime] (hb : p ∉ cd.bad) (hk : 0 < k) (hkb : k ≤ b)
    (hbh : b < h) (hn : 0 < n) (hnd : n ∣ cd.Phi k) :
    ((cd.Wodd h b : ℚ) / (n : ℚ)) ∈ LocRing p := by
  apply div_mem_locRing hn
  apply cd.pow_dvd_Wodd hpf.out hb
  intro e he hd
  have hpp : IsPrimePow (p ^ e) := hpf.out.isPrimePow.pow (by omega)
  obtain ⟨h1, h2⟩ := cd.kq_le (p ^ e) k hpp (cd.coprime_bad_pow hpf.out hb) hk (hd.trans hnd)
  have hL := cd.hL
  exact ⟨by nlinarith, Or.inl (by omega)⟩

lemma Mn_lt {a b : ℕ} (hab : a < b) :
    Fr.Mn a b = (cd.normN : ℚ)⁻¹ * (1 / ((b : ℚ) - a)) * ∑ k ∈ Ioc a b, Fr.Delta k := by
  unfold Frame.Mn
  rw [if_neg hab.ne, max_eq_right hab.le, min_eq_left hab.le, cd.norm_eq]
  simp

lemma Mn_diag (a : ℕ) :
    Fr.Mn a a = -((cd.normN : ℚ)⁻¹ * ∑ k ∈ Icc 1 a, Fr.Dsq k) := by
  unfold Frame.Mn
  rw [if_pos rfl, cd.norm_eq]
  simp

lemma Mn_symm (a b : ℕ) : Fr.Mn a b = Fr.Mn b a := by
  unfold Frame.Mn
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

/-- `Wodd_b · Δ_k` is `p`-integral. -/
lemma memS_delta {h k b p : ℕ} [hpf : Fact p.Prime] (hb : p ∉ cd.bad) (hk : 0 < k) (hkb : k ≤ b)
    (hbh : b < h) : ((cd.Wodd h b : ℚ) * Fr.Delta k) ∈ LocRing p := by
  obtain ⟨z, hz⟩ := cd.delta_int k hk
  have hP : (cd.Phi k : ℚ) ≠ 0 := by exact_mod_cast (cd.Phi_pos k hk).ne'
  have : (cd.Wodd h b : ℚ) * Fr.Delta k = (z : ℚ) * ((cd.Wodd h b : ℚ) / (cd.Phi k : ℚ)) := by
    rw [← hz]; field_simp
  rw [this]
  exact (LocRing p).mul_mem (int_mem_locRing z)
    (cd.memS_B hb hk hkb hbh (cd.Phi_pos k hk) dvd_rfl)

lemma memS_dsq {h k a p : ℕ} [hpf : Fact p.Prime] (hb : p ∉ cd.bad) (hk : 0 < k) (hka : k ≤ a)
    (hah : a < h) : (((cd.Wodd h a : ℚ)) ^ 2 * Fr.Dsq k) ∈ LocRing p := by
  obtain ⟨z, hz⟩ := cd.dsq_int k hk
  have hP : (cd.Phi k : ℚ) ≠ 0 := by exact_mod_cast (cd.Phi_pos k hk).ne'
  have : ((cd.Wodd h a : ℚ)) ^ 2 * Fr.Dsq k =
      (z : ℚ) * ((cd.Wodd h a : ℚ) / (cd.Phi k : ℚ)) ^ 2 := by
    rw [← hz]; field_simp
  rw [this]
  exact (LocRing p).mul_mem (int_mem_locRing z)
    ((LocRing p).pow_mem (cd.memS_B hb hk hka hah (cd.Phi_pos k hk) dvd_rfl) 2)

lemma entry_lt_good {h a b p : ℕ} [hpf : Fact p.Prime] (hb : p ∉ cd.bad) (hab : a < b)
    (hbh : b < h) :
    ((cd.Wodd h a : ℚ) * cd.Wodd h b * Fr.Mn a b) ∈ LocRing p := by
  have hba : ((b : ℚ) - a) ≠ 0 := by
    have : (a : ℚ) < b := by exact_mod_cast hab
    linarith
  have key : (cd.Wodd h a : ℚ) * cd.Wodd h b * Fr.Mn a b =
      (cd.normN : ℚ)⁻¹ * (((cd.Wodd h a : ℚ) / ((b - a : ℕ) : ℚ)) *
        ∑ k ∈ Ioc a b, ((cd.Wodd h b : ℚ) * Fr.Delta k)) := by
    rw [cd.Mn_lt hab, Nat.cast_sub hab.le, ← Finset.mul_sum]
    field_simp
  rw [key]
  refine (LocRing p).mul_mem (inv_natCast_mem_locRing (cd.not_dvd_normN hpf.out hb))
    ((LocRing p).mul_mem (cd.memS_A hb hab hbh) (Subring.sum_mem _ fun k hk => ?_))
  have hk' := Finset.mem_Ioc.mp hk
  exact cd.memS_delta hb (by omega) hk'.2 hbh

lemma entry_diag_good {h a p : ℕ} [hpf : Fact p.Prime] (hb : p ∉ cd.bad) (ha : a < h) :
    ((cd.Wodd h a : ℚ) * cd.Wodd h a * Fr.Mn a a) ∈ LocRing p := by
  have key : (cd.Wodd h a : ℚ) * cd.Wodd h a * Fr.Mn a a =
      -((cd.normN : ℚ)⁻¹ * ∑ k ∈ Icc 1 a, ((cd.Wodd h a : ℚ) ^ 2 * Fr.Dsq k)) := by
    rw [cd.Mn_diag, ← Finset.mul_sum]
    ring
  rw [key]
  refine (LocRing p).neg_mem ((LocRing p).mul_mem
    (inv_natCast_mem_locRing (cd.not_dvd_normN hpf.out hb)) (Subring.sum_mem _ fun k hk => ?_))
  have hk' := Finset.mem_Icc.mp hk
  exact cd.memS_dsq hb (by omega) hk'.2 ha

/-- Local integrality of every weighted entry. -/
lemma entry_good {h a b p : ℕ} [hpf : Fact p.Prime] (ha : a < h) (hb : b < h) :
    ((cd.W h a : ℚ) * cd.W h b * Fr.Mn a b) ∈ LocRing p := by
  by_cases hbad : p ∈ cd.bad
  · have e : (cd.W h a : ℚ) * cd.W h b * Fr.Mn a b =
        ((cd.Wodd h a * cd.Wodd h b : ℕ) : ℤ) * ((cd.small h : ℚ) ^ 2 * Fr.Mn a b) := by
      unfold W; push_cast; ring
    rw [e]
    exact (LocRing p).mul_mem (int_mem_locRing _) (cd.small_ok p hbad h a b ha hb)
  · have e : (cd.W h a : ℚ) * cd.W h b * Fr.Mn a b =
        (((cd.small h) ^ 2 : ℕ) : ℤ) * ((cd.Wodd h a : ℚ) * cd.Wodd h b * Fr.Mn a b) := by
      unfold W; push_cast; ring
    rw [e]
    refine (LocRing p).mul_mem (int_mem_locRing _) ?_
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact cd.entry_lt_good hbad hab hb
    · exact cd.entry_diag_good hbad ha
    · rw [Mn_symm, mul_comm (cd.Wodd h a : ℚ)]
      exact cd.entry_lt_good hbad hba ha

theorem entry_int (h : ℕ) {a b : ℕ} (ha : a < h) (hb : b < h) :
    ∃ z : ℤ, (cd.W h a : ℚ) * cd.W h b * Fr.Mn a b = z := by
  obtain ⟨z, hz⟩ := int_of_forall_locRing _ (fun p _ => cd.entry_good (p := p) ha hb)
  exact ⟨z, hz⟩

/-- **Integrality**: `q^h · Dden(h) · P_h(p/q)` is an integer. -/
theorem integrality (h : ℕ) (p q : ℤ) (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ) ^ h * (cd.Dden h : ℚ) * Fr.P h ((p : ℚ) / q) = z := by
  choose Z hZ using fun (a b : Fin h) => cd.entry_int h a.2 b.2
  let Zm : Matrix (Fin h) (Fin h) ℤ :=
    Matrix.of fun a b => (if a = b then p * (cd.W h a : ℤ) * (cd.W h a : ℤ) else 0) + q * Z a b
  refine ⟨Zm.det, ?_⟩
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmat : Zm.map (Int.cast : ℤ → ℚ) =
      (q : ℚ) • (Matrix.diagonal (fun a : Fin h => (cd.W h a : ℚ)) *
        (((p : ℚ) / q) • (1 : Matrix (Fin h) (Fin h) ℚ) + Fr.M h) *
        Matrix.diagonal (fun a : Fin h => (cd.W h a : ℚ))) := by
    ext a b
    simp only [Matrix.map_apply, Zm, Matrix.of_apply, Matrix.smul_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply, Frame.M, Frame.MRect, smul_eq_mul]
    have := hZ a b
    by_cases hab : a = b
    · subst hab
      simp only [if_true, Int.cast_add, Int.cast_mul, Int.cast_ite, Int.cast_zero, Int.cast_natCast]
      rw [← this]
      field_simp
    · simp only [hab, ite_false, Int.cast_add, Int.cast_mul, Int.cast_ite, Int.cast_zero, mul_zero,
        add_zero, Int.cast_natCast]
      rw [← this]
      ring
  have hdet := RingHom.map_det (Int.castRingHom ℚ) Zm
  have hmap : (Int.castRingHom ℚ).mapMatrix Zm = Zm.map (Int.cast : ℤ → ℚ) := rfl
  rw [hmap, hmat, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  simp only [eq_intCast, Fintype.card_fin] at hdet
  rw [hdet]
  unfold Dden Frame.P
  push_cast
  ring

end ContentData

/-- `P_h(r)` is the evaluation of the polynomial `Ppoly h`. -/
theorem eval_Ppoly (Fr : Frame) (h : ℕ) (r : ℚ) : (Fr.Ppoly h).eval r = Fr.P h r := by
  unfold Frame.Ppoly Frame.P
  rw [Polynomial.eval, ← Polynomial.coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [Frame.M, Frame.MRect, Matrix.one_apply]
  · simp [hab, Frame.M, Frame.MRect, Matrix.one_apply]

/-- **Integrality in the form of `HasContent`'s second clause.** -/
theorem integrality_of {Fr : Frame} (cd : ContentData Fr) (h : ℕ) (p q : ℤ) (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ) ^ (PolyFamily.ofFrame Fr).deg h * cd.Dden h *
      (PolyFamily.ofFrame Fr).evalQ h (p / q) = z := by
  obtain ⟨z, hz⟩ := cd.integrality h p q hq
  refine ⟨z, ?_⟩
  simp only [PolyFamily.ofFrame, PolyFamily.evalQ, id]
  rw [eval_Ppoly]
  exact hz

end CatalanCore.Arith
