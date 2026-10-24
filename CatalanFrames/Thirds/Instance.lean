module

public import CatalanFrames.Thirds.ContentData
public import CatalanFrames.HybGen.ClassBand

@[expose] public section

/-!
# The hybrid instance of the thirds frames (M3 / M4 instance)

`thirdsCD T : ContentData Fr` for `Φ(k) = k(3k-e)`, bad primes `{2,3}`, `L = 3`, norm `9`;
`thirdsInst T : HybInst Fr` (block valued, `HybInst.ofSing`); `BadInfo`, `LevelFacts`, and the
class dictionaries (`Band`) with `p + e ≡ 0 (mod 3)` giving `3 kq = p + e`, otherwise `3 kq = 2p + e`.
-/

open Finset Classical

namespace CatalanFrames.Thirds

open CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Basic CatalanFrames.HybCommon
  CatalanFrames.HybGen

/-- `t = 1` if `3 ∣ q + e`, else `t = 2` (then `3 ∣ 2q + e` for `q` prime to 3). -/
def tq (e q : ℕ) : ℕ := if (q + e) % 3 = 0 then 1 else 2

/-- First `k ≥ 1` with `q ∣ k (3k - e)`. -/
def kqT (e q : ℕ) : ℕ := (tq e q * q + e) / 3

lemma kqT_spec {e q : ℕ} (he : e = 1 ∨ e = 2) (hq : 2 ≤ q) (h3 : q % 3 ≠ 0) :
    3 * kqT e q = tq e q * q + e ∧ 0 < kqT e q ∧
      ((q + e) % 3 = 0 ∧ tq e q = 1 ∨ (q + e) % 3 ≠ 0 ∧ tq e q = 2) := by
  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases he with rfl | rfl <;> rcases hq3 with h | h <;> (unfold kqT tq; split_ifs <;> omega)

lemma pp_cases {p n k e : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e) (hk : 0 < k) (he : e ≤ 2)
    (hd : p ^ n ∣ k * (3 * k - e)) : p ^ n ∣ k ∨ p ^ n ∣ 3 * k - e := by
  by_cases hpk : p ∣ k
  · left
    have : Nat.Coprime p (3 * k - e) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h4
      have h5 : p ∣ 3 * k := Dvd.dvd.mul_left hpk 3
      have h6 : p ∣ e := by
        have := Nat.dvd_sub h5 h4
        have e1 : 3 * k - (3 * k - e) = e := by omega
        rwa [e1] at this
      exact hpe h6
    exact (Nat.Coprime.pow_left n this).dvd_of_dvd_mul_right hd
  · right
    have : Nat.Coprime (p ^ n) k :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
    exact this.dvd_of_dvd_mul_left hd

lemma kqT_le_of_dvd {e q k : ℕ} (he : e = 1 ∨ e = 2) (hq : IsPrimePow q) (hq2 : q % 2 = 1)
    (hq3 : q % 3 ≠ 0) (hk : 0 < k) (hd : q ∣ k * (3 * k - e)) :
    kqT e q ≤ k ∧ q ≤ 3 * k := by
  obtain ⟨p, n, hp0, hn, rfl⟩ := hq
  have hp := hp0.nat_prime
  have hpq : p ∣ p ^ n := dvd_pow_self p hn.ne'
  have hpe : ¬ p ∣ e := by
    intro h
    have h1 : p ≤ e := Nat.le_of_dvd (by omega) h
    have h2 := hp.two_le
    have : p = 2 := by omega
    subst this
    have : 2 ∣ 2 ^ n := hpq
    omega
  have hq1 : 2 ≤ p ^ n := by
    calc 2 ≤ p := hp.two_le
      _ ≤ p ^ n := Nat.le_self_pow hn.ne' p
  obtain ⟨h1, h2, h3⟩ := kqT_spec he hq1 hq3
  have hA : 3 * kqT e (p ^ n) ≤ 2 * p ^ n + e := by
    rcases h3 with ⟨_, ht⟩ | ⟨_, ht⟩ <;> rw [ht] at h1 <;> omega
  have hB : (p ^ n + e) % 3 = 0 → 3 * kqT e (p ^ n) = p ^ n + e := by
    intro hm
    rcases h3 with ⟨_, ht⟩ | ⟨hm', _⟩
    · rw [ht] at h1; omega
    · exact absurd hm hm'
  rcases pp_cases hp hpe hk (by omega) hd with hc | hc
  · have := Nat.le_of_dvd hk hc
    constructor <;> omega
  · obtain ⟨t, ht⟩ := hc
    have hpos : 0 < 3 * k - e := by omega
    rcases Nat.lt_or_ge t 3 with h | h
    · interval_cases t
      · omega
      · have := hB (by omega)
        constructor <;> omega
      · constructor <;> omega
    · have : p ^ n * 3 ≤ p ^ n * t := Nat.mul_le_mul_left _ h
      constructor <;> omega

lemma tPhi_le {e : ℕ} (he : e = 1 ∨ e = 2) (k N : ℕ) (h : k ≤ N) :
    k * (3 * k - e) ≤ 4 * N * N := by
  calc k * (3 * k - e) ≤ N * (3 * N) := Nat.mul_le_mul h (by omega)
    _ ≤ 4 * N * N := by nlinarith

section Inst

variable {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e)

include T in
/-- The content table. -/
noncomputable def thirdsCD : ContentData Fr where
  L := 3
  hL := by norm_num
  Phi := fun k => k * (3 * k - e)
  Phi_pos := fun k hk => Nat.mul_pos hk (by have := T.he; omega)
  bad := {2, 3}
  bad_prime := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  normN := 9
  norm_eq := by rw [T.norm_eq]; norm_num
  norm_dvd := by
    intro p hp hd
    have : p ∣ 3 ^ 2 := by norm_num; exact hd
    have h3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow this)
    simp [h3]
  delta_int := by
    intro k hk
    refine ⟨-(e : ℤ), ?_⟩
    have hE := T.he
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have h3 : 3 * (k : ℚ) - e ≠ 0 := by rcases hE with rfl | rfl <;> norm_num <;> linarith
    have h5 : (k : ℚ) ≠ 0 := by linarith
    have h3' : (k : ℚ) * 3 - e ≠ 0 := by rcases hE with rfl | rfl <;> norm_num <;> linarith
    rw [T.delta k hk, Nat.cast_mul, cast3 hE hk]
    push_cast
    field_simp
    ring
  dsq_int := by
    intro k hk
    refine ⟨(3 * (k : ℤ) - e) ^ 2 - 9 * (k : ℤ) ^ 2, ?_⟩
    have hE := T.he
    have h1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have h3 : 3 * (k : ℚ) - e ≠ 0 := by rcases hE with rfl | rfl <;> norm_num <;> linarith
    have h5 : (k : ℚ) ≠ 0 := by linarith
    have h3' : (k : ℚ) * 3 - e ≠ 0 := by rcases hE with rfl | rfl <;> norm_num <;> linarith
    rw [T.dsq k hk, Nat.cast_mul, cast3 hE hk]
    push_cast
    field_simp
    try ring
  kq := kqT e
  kq_le := by
    intro q k hq hbad hk hd
    have h2 : ¬ 2 ∣ q := hbad 2 (by simp)
    have h3 : ¬ 3 ∣ q := hbad 3 (by simp)
    have := kqT_le_of_dvd T.he hq (by omega) (by omega) hk hd
    exact ⟨this.1, this.2⟩
  small := tsmall
  small_pos := fun h => by unfold tsmall; positivity
  small_ok := by
    intro p _ hp h a b ha hb
    exact tsmall_ok T p hp h a b ha hb
  small_poly := ⟨27, 2, fun h => tsmall_poly h⟩

include T in
/-- The block-valued hybrid instance of the thirds frame. -/
noncomputable def thirdsInst : HybInst Fr :=
  HybInst.ofSing (thirdsCD T) (fun N => 4 * N * N) (fun k N h => tPhi_le T.he k N h)

include T in
instance thirdsInst_diagOK (r m : ℕ) : (thirdsInst T).DiagOK r m :=
  HybInst.DiagOK.of_all (fun _ => trivial) r m

lemma thirdsInst_lev (q c : ℕ) : (thirdsInst T).lev q c = blk (thirdsCD T).Phi q c := rfl

lemma thirds_kq_att (q : ℕ) (hq : IsPrimePow q) (hb : ∀ p ∈ (thirdsCD T).bad, ¬ p ∣ q) :
    0 < (thirdsCD T).kq q ∧ q ∣ (thirdsCD T).Phi ((thirdsCD T).kq q) := by
  have h2 : ¬ 2 ∣ q := hb 2 (by simp [thirdsCD])
  have h3 : ¬ 3 ∣ q := hb 3 (by simp [thirdsCD])
  have hq1 : 2 ≤ q := by
    obtain ⟨p, n, hp, hn, rfl⟩ := hq
    have := hp.nat_prime.two_le
    calc 2 ≤ p := this
      _ ≤ p ^ n := Nat.le_self_pow hn.ne' p
  obtain ⟨h1, h4, h5⟩ := kqT_spec T.he hq1 (by omega)
  refine ⟨h4, ?_⟩
  show q ∣ kqT e q * (3 * kqT e q - e)
  have : 3 * kqT e q - e = tq e q * q := by omega
  rw [this]
  exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _

lemma thirds_lev_zero_iff {q c : ℕ} (hq : IsPrimePow q) (hb : ∀ p ∈ (thirdsCD T).bad, ¬ p ∣ q) :
    (thirdsInst T).lev q c = 0 ↔ c < (thirdsCD T).kq q := by
  rw [thirdsInst_lev]
  have := blk_pos_iff (thirdsCD T) (thirds_kq_att T) (c := c) hq hb
  omega

lemma thirds_lev_high (q c : ℕ) (hq : 1 ≤ q) (h : q ≤ c) : 0 < (thirdsInst T).lev q c := by
  rw [thirdsInst_lev]
  exact blk_pos_of (k := q) (Finset.mem_Icc.mpr ⟨hq, h⟩)
    (show q ∣ q * (3 * q - e) from dvd_mul_right _ _)

lemma thirds_good {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    IsPrimePow p ∧ ∀ q ∈ (thirdsCD T).bad, ¬ q ∣ p := by
  refine ⟨hp.isPrimePow, ?_⟩
  intro q hq hd
  have hq' : q = 2 ∨ q = 3 := by simpa [thirdsCD] using hq
  rcases hq' with rfl | rfl
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd; omega
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd; omega

/-- **Level facts of the thirds instance.** -/
theorem thirds_levels :
    LevelFacts (thirdsInst T) (fun p => 5 ≤ p) (fun q c => c < (thirdsInst T).cd.kq q) where
  good := fun p hp h5 => thirds_good T hp h5
  zero_iff := fun q c hq hb => thirds_lev_zero_iff T hq hb
  high := fun q c hq1 hqc => thirds_lev_high T q c hq1 hqc

lemma thirds_cOf_le (p : ℕ) : cOf (thirdsInst T) p ≤ 2 := by
  show (9 : ℕ).factorization p ≤ 2
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
  by_cases h : p = 3
  · subst h; simp
  · simp [Finsupp.single_apply, Ne.symm h]

/-- **Bad-prime numerology**: `BadInfo (thirdsInst T) 3 2`. -/
theorem thirds_badInfo : BadInfo (thirdsInst T) 3 2 where
  L_eq := rfl
  Lc_le := by norm_num
  cm_le := by norm_num
  Ebd_le := fun N => cubic_Ebd N
  two_mem := by simp [thirdsInst, HybInst.ofSing, thirdsCD]
  bad_le := fun b hb => by
    simp [thirdsInst, HybInst.ofSing, thirdsCD] at hb; omega
  cOf_le := thirds_cOf_le T

/-! ### Class dictionaries -/

lemma cls6 {p r : ℕ} (h : (p : ZMod 6) = (r : ℕ)) (hr : r < 6) : p % 6 = r := by
  have := (ZMod.natCast_eq_natCast_iff' p r 6).mp h
  omega

lemma thirds_kq_formula {p : ℕ} (hp5 : 5 ≤ p) (h3 : p % 3 ≠ 0) :
    ((p + e) % 3 = 0 ∧ 3 * (thirdsInst T).cd.kq p = p + e) ∨
      ((p + e) % 3 ≠ 0 ∧ 3 * (thirdsInst T).cd.kq p = 2 * p + e) := by
  have hk : (thirdsInst T).cd.kq p = kqT e p := rfl
  rw [hk]
  obtain ⟨h1, h2, h3'⟩ := kqT_spec T.he (by omega : 2 ≤ p) h3
  rcases h3' with ⟨a, b⟩ | ⟨a, b⟩
  · rw [b] at h1; left; exact ⟨a, by omega⟩
  · rw [b] at h1; right; exact ⟨a, by omega⟩

end Inst

section Bands

variable {Fr : Frame}

/-- `e = 2`: class `1 (mod 6)` is low (`3 kq = p + 2`). -/
theorem thirds_band_2_1 (T : ThirdsData Fr 2) : Band (thirdsInst T) 6 (1 : ZMod 6) 3 1 1 2 := by
  intro p hp hpc
  have h6 := cls6 (r := 1) (by simpa using hpc) (by norm_num)
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  have h1 := thirds_kq_formula T h5 (by omega)
  unfold BandP
  omega

/-- `e = 2`: class `5 (mod 6)` is high (`3 kq = 2p + 2`). -/
theorem thirds_band_2_5 (T : ThirdsData Fr 2) : Band (thirdsInst T) 6 (5 : ZMod 6) 3 2 1 2 := by
  intro p hp hpc
  have h6 := cls6 (r := 5) (by simpa using hpc) (by norm_num)
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  have h1 := thirds_kq_formula T h5 (by omega)
  unfold BandP
  omega

/-- `e = 1`: class `5 (mod 6)` is low (`3 kq = p + 1`). -/
theorem thirds_band_1_5 (T : ThirdsData Fr 1) : Band (thirdsInst T) 6 (5 : ZMod 6) 3 1 1 2 := by
  intro p hp hpc
  have h6 := cls6 (r := 5) (by simpa using hpc) (by norm_num)
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  have h1 := thirds_kq_formula T h5 (by omega)
  unfold BandP
  omega

/-- `e = 1`: class `1 (mod 6)` is high (`3 kq = 2p + 1`). -/
theorem thirds_band_1_1 (T : ThirdsData Fr 1) : Band (thirdsInst T) 6 (1 : ZMod 6) 3 2 1 2 := by
  intro p hp hpc
  have h6 := cls6 (r := 1) (by simpa using hpc) (by norm_num)
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  have h1 := thirds_kq_formula T h5 (by omega)
  unfold BandP
  omega

end Bands

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.thirds_badInfo
#print axioms CatalanFrames.Thirds.thirds_levels
#print axioms CatalanFrames.Thirds.thirds_band_2_1
#print axioms CatalanFrames.Thirds.thirds_band_1_1
