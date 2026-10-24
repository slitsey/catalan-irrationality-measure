module

public import CatalanFrames.Thirds.Frame
public import CatalanCore.Arith.Growth
public import CatalanCore.Arith.Hybrid.SingLev

@[expose] public section

/-!
# Content data of the thirds frames (M3)

`Φ(k) = k(3k-e)`, `e = 2` (shift `1/3`) or `e = 1` (shift `2/3`), norm `9`, bad primes `{2,3}`.
Everything is stated for an arbitrary frame `Fr` satisfying `ThirdsData Fr e`; the contour data
`xs`, `δ0`, `n0off` of the frame are never used (they only enter the decay part).
-/

open Finset Classical

namespace CatalanFrames.Thirds

open CatalanCore CatalanCore.Arith CatalanCore.Basic

/-- The hypotheses on the frame used by the content layer. -/
structure ThirdsData (Fr : Frame) (e : ℕ) : Prop where
  he : e = 1 ∨ e = 2
  norm_eq : Fr.norm = 9
  delta : ∀ k : ℕ, 0 < k → Fr.Delta k = 1 / (k : ℚ) - 3 / ((3 * k - e : ℕ) : ℚ)
  dsq : ∀ k : ℕ, 0 < k → Fr.Dsq k = 1 / (k : ℚ) ^ 2 - 9 / ((3 * k - e : ℕ) : ℚ) ^ 2

lemma cast3 {e k : ℕ} (he : e = 1 ∨ e = 2) (hk : 0 < k) :
    ((3 * k - e : ℕ) : ℚ) = 3 * (k : ℚ) - e := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- `thirdsFrame` with shift `(3-e)/3` and norm `9` satisfies `ThirdsData`. -/
theorem ThirdsData.of_thirdsFrame {e : ℕ} (he : e = 1 ∨ e = 2) (s : ℚ)
    (hs : s = (3 - (e : ℚ)) / 3)
    (xs δ0 : ℚ) (n0 : ℕ) (h0 : 0 < s) (h1 : s < 1) (hN : (0 : ℚ) < 9) :
    ThirdsData (thirdsFrame s 9 xs δ0 n0 h0 h1 hN) e where
  he := he
  norm_eq := rfl
  delta := by
    intro k hk
    rw [Delta_eq, cast3 he hk]
    have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have h3 : 3 * (k : ℚ) - e ≠ 0 := by
      rcases he with rfl | rfl <;> norm_num <;> linarith
    have h4 : (k : ℚ) - 1 + s ≠ 0 := by
      rw [hs]
      rcases he with rfl | rfl <;> norm_num <;> linarith
    have hk0 : (k : ℚ) ≠ 0 := by linarith
    rw [hs] at h4 ⊢
    field_simp
    ring
  dsq := by
    intro k hk
    rw [Dsq_eq, cast3 he hk]
    have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have h3 : 3 * (k : ℚ) - e ≠ 0 := by
      rcases he with rfl | rfl <;> norm_num <;> linarith
    have h4 : (k : ℚ) - 1 + s ≠ 0 := by
      rw [hs]
      rcases he with rfl | rfl <;> norm_num <;> linarith
    have hk0 : (k : ℚ) ≠ 0 := by linarith
    rw [hs] at h4 ⊢
    field_simp
    ring

section Small

variable {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e)

include T in
lemma tMn_lt {a b : ℕ} (hab : a < b) :
    Fr.Mn a b = (1 / 9 : ℚ) * (1 / ((b : ℚ) - a)) * ∑ k ∈ Ioc a b, Fr.Delta k := by
  unfold Frame.Mn
  rw [if_neg hab.ne, max_eq_right hab.le, min_eq_left hab.le, T.norm_eq]

include T in
lemma tMn_diag (a : ℕ) : Fr.Mn a a = -((1 / 9 : ℚ) * ∑ k ∈ Icc 1 a, Fr.Dsq k) := by
  unfold Frame.Mn
  rw [if_pos rfl, T.norm_eq]
  ring

lemma tMn_symm (a b : ℕ) : Fr.Mn a b = Fr.Mn b a := by
  unfold Frame.Mn
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

variable (p : ℕ) [Fact p.Prime]

lemma tpw_mem {N n : ℕ} (hn : 0 < n) (hv : n.factorization p ≤ N) :
    ((p : ℚ) ^ N / (n : ℚ)) ∈ LocRing p := by
  have := div_mem_locRing (p := p) (n := n) (W := p ^ N) hn (Nat.pow_dvd_pow p hv)
  simpa using this

lemma tpw_mem' {n h : ℕ} (hn : 0 < n) (hnh : n ≤ 3 * h) :
    ((p : ℚ) ^ Nat.log p (3 * h) / (n : ℚ)) ∈ LocRing p :=
  tpw_mem p hn (Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
    (le_trans (Nat.ordProj_le p hn.ne') hnh))

lemma three_mem : (3 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (3 : ℤ)

include T in
lemma toff_mem {h a b : ℕ} (hab : a < b) (hbh : b < h) :
    ((p : ℚ) ^ Nat.log p (3 * h)) ^ 2 * (9 * Fr.Mn a b) ∈ LocRing p := by
  set u : ℚ := (p : ℚ) ^ Nat.log p (3 * h) with hu
  have hs : ∑ k ∈ Ioc a b, Fr.Delta k =
      ∑ k ∈ Ioc a b, (1 / (k : ℚ) - 3 / ((3 * k - e : ℕ) : ℚ)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Ioc.mp hk).1; omega
    exact T.delta k hk0
  have e1 : ∑ k ∈ Ioc a b, (u / (k : ℚ) - 3 * (u / ((3 * k - e : ℕ) : ℚ))) =
      u * ∑ k ∈ Ioc a b, (1 / (k : ℚ) - 3 / ((3 * k - e : ℕ) : ℚ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key : u ^ 2 * (9 * Fr.Mn a b) =
      (u / ((b - a : ℕ) : ℚ)) * ∑ k ∈ Ioc a b, (u / (k : ℚ) - 3 * (u / ((3 * k - e : ℕ) : ℚ))) := by
    rw [e1, tMn_lt T hab, hs, Nat.cast_sub hab.le]
    ring
  rw [key]
  apply (LocRing p).mul_mem
  · exact tpw_mem' p (by omega) (by omega)
  · refine Subring.sum_mem _ fun k hk => ?_
    have hk' := Finset.mem_Ioc.mp hk
    have hE := T.he
    apply (LocRing p).sub_mem (tpw_mem' p (by omega) (by omega))
    exact (LocRing p).mul_mem (three_mem p) (tpw_mem' p (by omega) (by omega))

include T in
lemma tdiag_mem {h a : ℕ} (ha : a < h) :
    ((p : ℚ) ^ Nat.log p (3 * h)) ^ 2 * (9 * Fr.Mn a a) ∈ LocRing p := by
  set u : ℚ := (p : ℚ) ^ Nat.log p (3 * h) with hu
  have hs : ∑ k ∈ Icc 1 a, Fr.Dsq k =
      ∑ k ∈ Icc 1 a, (1 / (k : ℚ) ^ 2 - 9 / ((3 * k - e : ℕ) : ℚ) ^ 2) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
    exact T.dsq k hk0
  have e1 : ∑ k ∈ Icc 1 a, ((u / (k : ℚ)) ^ 2 - 9 * (u / ((3 * k - e : ℕ) : ℚ)) ^ 2) =
      u ^ 2 * ∑ k ∈ Icc 1 a, (1 / (k : ℚ) ^ 2 - 9 / ((3 * k - e : ℕ) : ℚ) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key : u ^ 2 * (9 * Fr.Mn a a) =
      -∑ k ∈ Icc 1 a, ((u / (k : ℚ)) ^ 2 - 9 * (u / ((3 * k - e : ℕ) : ℚ)) ^ 2) := by
    rw [e1, tMn_diag T, hs]
    ring
  rw [key]
  apply (LocRing p).neg_mem
  refine Subring.sum_mem _ fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  have hE := T.he
  have h9 : (9 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (9 : ℤ)
  apply (LocRing p).sub_mem ((LocRing p).pow_mem (tpw_mem' p (by omega) (by omega)) 2)
  exact (LocRing p).mul_mem h9 ((LocRing p).pow_mem
    (tpw_mem' p (by omega) (by omega)) 2)

include T in
lemma tnorm_mem {h a b : ℕ} (ha : a < h) (hb : b < h) :
    ((p : ℚ) ^ Nat.log p (3 * h)) ^ 2 * (9 * Fr.Mn a b) ∈ LocRing p := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact toff_mem T p hab hb
  · exact tdiag_mem T p ha
  · rw [tMn_symm]; exact toff_mem T p hba ha

end Small

/-- The weight for the bad primes `2, 3`. -/
def tsmall (h : ℕ) : ℕ := 3 * 2 ^ Nat.log 2 (3 * h) * 3 ^ Nat.log 3 (3 * h)

lemma tsmall_ok {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({2, 3} : Finset ℕ)) (h a b : ℕ) (ha : a < h) (hb : b < h) :
    ((tsmall h : ℕ) : ℚ) ^ 2 * Fr.Mn a b ∈ LocRing p := by
  have hp' : p = 2 ∨ p = 3 := by simpa using hp
  rcases hp' with rfl | rfl
  · have e1 : ((tsmall h : ℕ) : ℚ) ^ 2 * Fr.Mn a b =
        ((3 : ℚ) ^ Nat.log 3 (3 * h)) ^ 2 *
          ((((2 : ℕ) : ℚ) ^ Nat.log 2 (3 * h)) ^ 2 * (9 * Fr.Mn a b)) := by
      unfold tsmall; push_cast; ring
    rw [e1]
    exact (LocRing 2).mul_mem ((LocRing 2).pow_mem ((LocRing 2).pow_mem
      (by exact_mod_cast int_mem_locRing (ℓ := 2) (3 : ℤ)) _) 2) (tnorm_mem T 2 ha hb)
  · have e1 : ((tsmall h : ℕ) : ℚ) ^ 2 * Fr.Mn a b =
        ((2 : ℚ) ^ Nat.log 2 (3 * h)) ^ 2 *
          ((((3 : ℕ) : ℚ) ^ Nat.log 3 (3 * h)) ^ 2 * (9 * Fr.Mn a b)) := by
      unfold tsmall; push_cast; ring
    rw [e1]
    exact (LocRing 3).mul_mem ((LocRing 3).pow_mem ((LocRing 3).pow_mem
      (by exact_mod_cast int_mem_locRing (ℓ := 3) (2 : ℤ)) _) 2) (tnorm_mem T 3 ha hb)

lemma tsmall_poly (h : ℕ) : tsmall h ≤ 27 * (h + 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp [tsmall]
  · have h2 := Nat.pow_log_le_self 2 (by omega : 3 * h ≠ 0)
    have h3 := Nat.pow_log_le_self 3 (by omega : 3 * h ≠ 0)
    unfold tsmall
    calc 3 * 2 ^ Nat.log 2 (3 * h) * 3 ^ Nat.log 3 (3 * h) ≤ 3 * (3 * h) * (3 * h) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 3 h2) h3
      _ ≤ 27 * (h + 1) ^ 2 := by nlinarith

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.tsmall_ok
#print axioms CatalanFrames.Thirds.ThirdsData.of_thirdsFrame
