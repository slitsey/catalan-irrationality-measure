module
public import CatalanFrames.Fifths.ContentLocal
public import CatalanFrames.HybCommon.Numer
@[expose] public section
open Finset Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Basic
  CatalanFrames.HybCommon
namespace CatalanFrames.Fifths
variable {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u)
include T in
/-- Full content data for Phi(k)=k(5k-u), norm25 and bad primes2,3,5. -/
noncomputable def fifthsCD : ContentData Fr where
  L := 5
  hL := by norm_num
  Phi := fun k => k*(5*k-u)
  Phi_pos := fun k hk => Nat.mul_pos hk (by have hu := T.hu1;omega)
  bad := badPrimes
  bad_prime := by
    intro p hp
    simp only [badPrimes,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl <;> decide
  normN := 25
  norm_eq := by rw [T.norm_eq];norm_num
  norm_dvd := by
    intro p hp hd
    have hh : p ∣ 5^2 := by norm_num;exact hd
    have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp (hp.dvd_of_dvd_pow hh)
    subst p
    simp [badPrimes]
  delta_int := by
    intro k hk
    refine ⟨-(u : ℤ),?_⟩
    have hu := T.hu1
    have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have hu' : (u : ℚ)<5 := by exact_mod_cast hu
    have hk0 : (k : ℚ) ≠ 0 := by linarith
    have hlin : 5*(k : ℚ)-u ≠ 0 := by linarith
    have hlin' : (k : ℚ)*5-u ≠ 0 := by nlinarith
    rw [T.delta k hk,Nat.cast_mul,cast_linear T.hu1 hk]
    push_cast
    field_simp [hk0,hlin,hlin']
    <;> ring
  dsq_int := by
    intro k hk
    refine ⟨(5*(k : ℤ)-u)^2-25*(k : ℤ)^2,?_⟩
    have hu := T.hu1
    have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have hu' : (u : ℚ)<5 := by exact_mod_cast hu
    have hk0 : (k : ℚ) ≠ 0 := by linarith
    have hlin : 5*(k : ℚ)-u ≠ 0 := by linarith
    have hlin' : (k : ℚ)*5-u ≠ 0 := by nlinarith
    rw [T.dsq k hk,Nat.cast_mul,cast_linear T.hu1 hk]
    push_cast
    field_simp [hk0,hlin,hlin']
    <;> ring
  kq := firstRoot u
  kq_le := fun q k hq hb hk hd => firstRoot_minimal_good T.hu0 T.hu1 hq hb hk hd
  small := small5
  small_pos := small5_pos
  small_ok := by
    intro p _ hp h a b ha hb
    exact small5_ok T p hp h a b ha hb
  small_poly := ⟨625,3,small5_poly⟩
include T in
noncomputable def fifthsInst : HybInst Fr :=
  HybInst.ofSing (fifthsCD T) (fun N => N*(5*N-1)) (fun k N h => phi_le_sharp T.hu0 h)
include T in
instance fifthsInst_diagOK (r m : ℕ) : (fifthsInst T).DiagOK r m :=
  HybInst.DiagOK.of_all (fun _ => trivial) r m
lemma fifthsInst_lev (q c : ℕ) : (fifthsInst T).lev q c = blk (fifthsCD T).Phi q c := rfl
lemma fifths_kq_att (q : ℕ) (hq : IsPrimePow q)
    (hb : ∀ p ∈ (fifthsCD T).bad,¬p∣q) :
    0<(fifthsCD T).kq q ∧ q∣(fifthsCD T).Phi ((fifthsCD T).kq q) := by
  exact firstRoot_att_good T.hu0 T.hu1 hq hb
lemma fifths_lev_zero_iff {q c : ℕ} (hq : IsPrimePow q)
    (hb : ∀ p ∈ (fifthsCD T).bad,¬p∣q) :
    (fifthsInst T).lev q c=0 ↔ c<(fifthsCD T).kq q := by
  rw [fifthsInst_lev]
  have h := blk_pos_iff (fifthsCD T) (fifths_kq_att T) (c := c) hq hb
  omega
lemma fifths_lev_high (q c : ℕ) (hq : 1≤q) (h : q≤c) : 0<(fifthsInst T).lev q c := by
  rw [fifthsInst_lev]
  exact blk_pos_of (k := q) (Finset.mem_Icc.mpr ⟨hq,h⟩)
    (show q∣q*(5*q-u) from dvd_mul_right _ _)
lemma fifths_good {p : ℕ} (hp : p.Prime) (h7 : 7≤p) :
    IsPrimePow p ∧ ∀ q ∈ (fifthsCD T).bad,¬q∣p := by
  refine ⟨hp.isPrimePow,?_⟩
  intro q hq hd
  have hq' : q=2 ∨ q=3 ∨ q=5 := by simpa [fifthsCD,badPrimes] using hq
  rcases hq' with rfl|rfl|rfl
  · have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd;omega
  · have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd;omega
  · have he := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hp).mp hd;omega
/-- Actual good predicate is p>=7, avoiding the forbidden prime5. -/
theorem fifths_levels :
    LevelFacts (fifthsInst T) (fun p => 7≤p) (fun q c => c<(fifthsInst T).cd.kq q) where
  good := fun p hp h7 => fifths_good T hp h7
  zero_iff := fun q c hq hb => fifths_lev_zero_iff T hq hb
  high := fun q c hq hqc => fifths_lev_high T q c hq hqc
lemma fifths_cOf_le (p : ℕ) : cOf (fifthsInst T) p ≤ 2 := by
  show (25 : ℕ).factorization p ≤ 2
  rw [show (25 : ℕ)=5^2 by norm_num,Nat.Prime.factorization_pow (by decide : Nat.Prime 5)]
  by_cases h : p=5
  · subst h;simp
  · simp [Finsupp.single_apply,Ne.symm h]
lemma fifths_Ebd_cubic (N : ℕ) : (fifthsInst T).Ebd N+N ≤ 5*N^3 := by
  change N*(5*N-1)+N ≤ 5*N^3
  exact sharp_Ebd_cubic (by norm_num) N
lemma fifths_badLog : badLog (fifthsInst T)=Real.log 30 := by
  unfold badLog
  change (∑ b ∈ badPrimes,Real.log (b : ℝ))=Real.log 30
  norm_num [badPrimes]
  rw [show (30 : ℝ)=2*3*5 by norm_num,Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  ring
end CatalanFrames.Fifths
set_option pp.fullNames true
#print axioms CatalanFrames.Fifths.fifthsCD
#print axioms CatalanFrames.Fifths.fifths_levels
#print axioms CatalanFrames.Fifths.fifths_cOf_le
#print axioms CatalanFrames.Fifths.fifths_Ebd_cubic
#print axioms CatalanFrames.Fifths.fifths_badLog
