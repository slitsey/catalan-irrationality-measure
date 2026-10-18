module

public import CatalanCore.Arith.Hybrid.Tropical
public import CatalanCore.Frame.Spec
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# The level majorant of the λ-hybrid and the bound `D_hyb · det Full(X) ∈ ℤ[X]`

WP-H5 step 1b (DW §1, paper eq. (major)).  For the λ frame (`LamLike`) the entry at labels
`(A, B)` has, for every prime `p`, the `p`-adic weight (`GLE`)

  `[p = 2]·4 + ∑_{e ≥ 1} wt (p^e) A B`,

where, for a prime power `q`,
* `blk q a` is the number of `q`-singular indices `k ∈ [1, a]` (`q ∣ k (4k-1)`);
* `wt q A B = 1[blk A ≠ blk B] + 1[q ∣ A - B]` for `A ≠ B`, and `2·1[blk A > 0]` for `A = B`.

`Lemma trop` (`Tropical.lean`) then gives `GLE p (tropVal W_p) (Fr.fullPoly r m)`; the exponent
`tropVal W_p` vanishes for `p > 4 (r + 2m)`, and `Dhyb r m = ∏_p p^{tropVal W_p}` clears all
denominators of `Fr.fullPoly r m`.  Nothing here depends on `α`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

/-- The λ frame, as far as the content argument is concerned. -/
structure LamLike (Fr : Frame) : Prop where
  norm_eq : Fr.norm = 16
  delta_eq : ∀ k : ℕ, 1 ≤ k → Fr.Delta k = -(4 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)))
  dsq_eq : ∀ k : ℕ, 1 ≤ k → Fr.Dsq k = 1 / (k : ℚ) ^ 2 - 16 / (4 * (k : ℚ) - 1) ^ 2

/-! ### Singular indices and the one-level weight -/

/-- `k` is `q`-singular: `q ∣ k (4k-1)`. -/
def Sing (q k : ℕ) : Prop := q ∣ k * (4 * k - 1)

instance (q k : ℕ) : Decidable (Sing q k) := by unfold Sing; infer_instance

/-- The block of `a`: the number of `q`-singular indices in `[1, a]`. -/
def blk (q a : ℕ) : ℕ := ((Icc 1 a).filter (Sing q)).card

/-- The one-level weight `w^{(q)}(A, B)` of DW §1. -/
def wt (q A B : ℕ) : ℕ :=
  if A = B then (if 0 < blk q A then 2 else 0)
  else (if blk q A ≠ blk q B then 1 else 0) + (if (q : ℤ) ∣ (A : ℤ) - B then 1 else 0)

lemma wt_le_two (q A B : ℕ) : wt q A B ≤ 2 := by
  unfold wt; split_ifs <;> omega

lemma wt_comm (q A B : ℕ) : wt q A B = wt q B A := by
  unfold wt
  by_cases h : A = B
  · subst h; rfl
  · have h' : ¬ B = A := fun e => h e.symm
    have : ((q : ℤ) ∣ (A : ℤ) - B) ↔ ((q : ℤ) ∣ (B : ℤ) - A) := by
      rw [← dvd_neg]; simp
    simp only [h, h', if_false]
    have e1 : (blk q A ≠ blk q B) ↔ (blk q B ≠ blk q A) := ne_comm
    simp only [e1, this]

lemma blk_lt {q lo hi k : ℕ} (hk : k ∈ Ioc lo hi) (hs : Sing q k) : blk q lo < blk q hi := by
  unfold blk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨k, ?_, ?_⟩
    · have := Finset.mem_Ioc.mp hk
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, this.2⟩, hs⟩
    · have := Finset.mem_Ioc.mp hk
      simp only [Finset.mem_filter, Finset.mem_Icc, not_and]
      intro h; omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    have := Finset.mem_Ioc.mp hk
    exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩

lemma blk_pos_of {q c k : ℕ} (hk : k ∈ Icc 1 c) (hs : Sing q k) : 0 < blk q c := by
  unfold blk
  exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hs⟩⟩

/-! ### Counting lemma -/

lemma fact_le_count {p : ℕ} (hp : p.Prime) {n E : ℕ} (hn : 0 < n) (hnE : n < p ^ (E + 1))
    (P : ℕ → Prop) [DecidablePred P] (hP : ∀ e ∈ Icc 1 E, p ^ e ∣ n → P e) :
    n.factorization p ≤ ((Icc 1 E).filter P).card := by
  have hf : n.factorization p ≤ E := by
    have h1 : p ^ (n.factorization p) ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
    have h2 : p ^ (n.factorization p) < p ^ (E + 1) := lt_of_le_of_lt h1 hnE
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h2
    omega
  calc n.factorization p = (Icc 1 (n.factorization p)).card := by simp
    _ ≤ _ := by
      apply Finset.card_le_card
      intro e he
      have he' := Finset.mem_Icc.mp he
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨he'.1, by omega⟩, hP e (Finset.mem_Icc.mpr ⟨he'.1, by omega⟩) ?_⟩
      exact (pow_dvd_pow p he'.2).trans (Nat.ordProj_dvd n p)

lemma pow_div_mem {p : ℕ} [Fact p.Prime] {n j : ℕ} (hn : 0 < n) (hj : n.factorization p ≤ j) :
    ((p : ℚ) ^ j) / (n : ℚ) ∈ LocRing p := by
  have := div_mem_locRing (p := p) hn (W := p ^ j) (pow_dvd_pow p hj)
  simpa using this

/-! ### Entry bounds -/

section Entries

variable {Fr : Frame} (hF : LamLike Fr) (p : ℕ) [hp : Fact p.Prime] (c : ℕ)

/-- Total weight of the entry at labels `(A, B)`. -/
def levels (E : ℕ) (A B : ℕ) : ℕ := ∑ e ∈ Icc 1 E, wt (p ^ e) A B

include hF in
lemma entry_off {E N lo hi : ℕ} (hc : (p : ℚ) ^ c * (1 / 16) ∈ LocRing p)
    (hE : 4 * N * N < p ^ (E + 1)) (hlo : lo < hi) (hhi : hi ≤ N) :
    (p : ℚ) ^ (c + levels p E lo hi) * Fr.Mn lo hi ∈ LocRing p := by
  have hp' := hp.out
  have hMn : Fr.Mn lo hi = (1 / 16) * (1 / ((hi : ℚ) - lo)) * ∑ k ∈ Ioc lo hi, Fr.Delta k := by
    unfold Frame.Mn
    rw [if_neg (by omega), hF.norm_eq, max_eq_right hlo.le, min_eq_left hlo.le]
  -- split the weight into the two counts
  set W1 := ((Icc 1 E).filter (fun e => blk (p ^ e) lo ≠ blk (p ^ e) hi)).card with hW1
  set W2 := ((Icc 1 E).filter (fun e => (p ^ e : ℕ) ∣ hi - lo)).card with hW2
  have hlev : levels p E lo hi = W1 + W2 := by
    unfold levels wt
    rw [Finset.sum_congr rfl (g := fun e => (if blk (p ^ e) lo ≠ blk (p ^ e) hi then 1 else 0) +
      (if (p ^ e : ℕ) ∣ hi - lo then 1 else 0))]
    · rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
      simp [hW1, hW2]
    · intro e _
      rw [if_neg (by omega)]
      have : (((p ^ e : ℕ) : ℤ) ∣ (lo : ℤ) - hi) ↔ (p ^ e : ℕ) ∣ hi - lo := by
        rw [← dvd_neg, neg_sub]
        have : ((hi : ℤ) - lo) = ((hi - lo : ℕ) : ℤ) := by omega
        rw [this]; exact Int.natCast_dvd_natCast
      simp only [this]
  have hdpos : 0 < hi - lo := by omega
  have hNpos : 1 ≤ N := by omega
  have hdN : hi - lo < p ^ (E + 1) := by
    have h1 : hi - lo ≤ N := by omega
    have h2 : N ≤ 4 * N * N := by nlinarith
    omega
  have hd : (p : ℚ) ^ W2 / ((hi - lo : ℕ) : ℚ) ∈ LocRing p :=
    pow_div_mem hdpos (fact_le_count hp.out hdpos hdN _ (fun e _ h => h))
  have hS : (p : ℚ) ^ W1 * ∑ k ∈ Ioc lo hi, Fr.Delta k ∈ LocRing p := by
    rw [Finset.mul_sum]
    apply (LocRing p).sum_mem
    intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    have hk1 : 1 ≤ k := by omega
    have hn : 0 < k * (4 * k - 1) := Nat.mul_pos (by omega) (by omega)
    have hnE : k * (4 * k - 1) < p ^ (E + 1) := by
      have : k * (4 * k - 1) ≤ 4 * N * N := by
        calc k * (4 * k - 1) ≤ N * (4 * N) := Nat.mul_le_mul (by omega) (by omega)
          _ = 4 * N * N := by ring
      have h2 : 4 * N * N < p ^ (E + 1) := hE
      have h3 : k * (4 * k - 1) ≤ 4 * N * N := this
      omega
    have hfl : (k * (4 * k - 1)).factorization p ≤ W1 :=
      fact_le_count hp.out hn hnE _ (fun e _ hdv => by
        exact ne_of_lt (blk_lt hk (show Sing (p ^ e) k from hdv)))
    have := pow_div_mem (p := p) hn hfl
    have hcast : ((k * (4 * k - 1) : ℕ) : ℚ) = (k : ℚ) * (4 * (k : ℚ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at this
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have h4 : (4 * (k : ℚ) - 1) ≠ 0 := by
      have : (1 : ℚ) ≤ k := by exact_mod_cast hk1
      intro h; linarith
    rw [hF.delta_eq k hk1]
    have e : (p : ℚ) ^ W1 * -(4 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)))
        = -((p : ℚ) ^ W1 / ((k : ℚ) * (4 * (k : ℚ) - 1))) := by
      field_simp
    rw [e]
    exact (LocRing p).neg_mem this
  rw [hMn, hlev]
  have e : (p : ℚ) ^ (c + (W1 + W2)) *
      (1 / 16 * (1 / ((hi : ℚ) - lo)) * ∑ k ∈ Ioc lo hi, Fr.Delta k)
      = ((p : ℚ) ^ c * (1 / 16)) * ((p : ℚ) ^ W2 / ((hi - lo : ℕ) : ℚ)) *
        ((p : ℚ) ^ W1 * ∑ k ∈ Ioc lo hi, Fr.Delta k) := by
    rw [Nat.cast_sub hlo.le]
    ring
  rw [e]
  exact (LocRing p).mul_mem ((LocRing p).mul_mem hc hd) hS

include hF in
lemma entry_diag {E N a : ℕ} (hc : (p : ℚ) ^ c * (1 / 16) ∈ LocRing p)
    (hE : 4 * N * N < p ^ (E + 1)) (ha : a ≤ N) :
    (p : ℚ) ^ (c + levels p E a a) * Fr.Mn a a ∈ LocRing p := by
  have hp' := hp.out
  have hMn : Fr.Mn a a = -(1 / 16) * ∑ k ∈ Icc 1 a, Fr.Dsq k := by
    unfold Frame.Mn
    rw [if_pos rfl, hF.norm_eq]
  set W' := ((Icc 1 E).filter (fun e => 0 < blk (p ^ e) a)).card with hW'
  have hlev : levels p E a a = 2 * W' := by
    unfold levels wt
    rw [Finset.sum_congr rfl (g := fun e => 2 * (if 0 < blk (p ^ e) a then 1 else 0))]
    · rw [← Finset.mul_sum, Finset.sum_boole]; simp [hW']
    · intro e _
      rw [if_pos rfl]; split_ifs <;> simp
  have hS : (p : ℚ) ^ (2 * W') * ∑ k ∈ Icc 1 a, Fr.Dsq k ∈ LocRing p := by
    rw [Finset.mul_sum]
    apply (LocRing p).sum_mem
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hk1 : 1 ≤ k := hk'.1
    have hn : 0 < k * (4 * k - 1) := Nat.mul_pos (by omega) (by omega)
    have hnE : k * (4 * k - 1) < p ^ (E + 1) := by
      have : k * (4 * k - 1) ≤ 4 * N * N := by
        calc k * (4 * k - 1) ≤ N * (4 * N) := Nat.mul_le_mul (by omega) (by omega)
          _ = 4 * N * N := by ring
      have h2 : 4 * N * N < p ^ (E + 1) := hE
      omega
    have hfl : (k * (4 * k - 1)).factorization p ≤ W' :=
      fact_le_count hp.out hn hnE _ (fun e _ hdv => by
        exact blk_pos_of hk (show Sing (p ^ e) k from hdv))
    have hn2 : 0 < (k * (4 * k - 1)) ^ 2 := by positivity
    have hf2 : ((k * (4 * k - 1)) ^ 2).factorization p ≤ 2 * W' := by
      rw [Nat.factorization_pow]
      simp only [Finsupp.smul_apply, smul_eq_mul]
      omega
    have := pow_div_mem (p := p) hn2 hf2
    have hcast : (((k * (4 * k - 1)) ^ 2 : ℕ) : ℚ) = ((k : ℚ) * (4 * (k : ℚ) - 1)) ^ 2 := by
      rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at this
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have h4 : (4 * (k : ℚ) - 1) ≠ 0 := by
      have : (1 : ℚ) ≤ k := by exact_mod_cast hk1
      intro h; linarith
    rw [hF.dsq_eq k hk1]
    have e : (p : ℚ) ^ (2 * W') * (1 / (k : ℚ) ^ 2 - 16 / (4 * (k : ℚ) - 1) ^ 2)
        = ((1 - 8 * (k : ℤ) : ℤ) : ℚ) *
          ((p : ℚ) ^ (2 * W') / (((k : ℚ) * (4 * (k : ℚ) - 1)) ^ 2)) := by
      have hz : ((1 - 8 * (k : ℤ) : ℤ) : ℚ) = 1 - 8 * (k : ℚ) := by push_cast; ring
      rw [hz]
      have key : ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → y = 4 * x - 1 →
          1 / x ^ 2 - 16 / y ^ 2 = (1 - 8 * x) / (x * y) ^ 2 := by
        intro x y hx hy hxy
        field_simp
        subst hxy
        ring
      rw [key _ _ hkq h4 rfl]
      ring
    rw [e]
    exact (LocRing p).mul_mem (int_mem_locRing _) this
  rw [hMn, hlev]
  have e : (p : ℚ) ^ (c + 2 * W') * (-(1 / 16) * ∑ k ∈ Icc 1 a, Fr.Dsq k)
      = -((p : ℚ) ^ c * (1 / 16)) * ((p : ℚ) ^ (2 * W') * ∑ k ∈ Icc 1 a, Fr.Dsq k) := by
    ring
  rw [e]
  exact (LocRing p).mul_mem ((LocRing p).neg_mem hc) hS

include hF in
/-- Entry bound for arbitrary labels `A, B ≤ N`. -/
lemma entry_gle {E N : ℕ} (hc : (p : ℚ) ^ c * (1 / 16) ∈ LocRing p)
    (hE : 4 * N * N < p ^ (E + 1)) {A B : ℕ} (hA : A ≤ N) (hB : B ≤ N) :
    (p : ℚ) ^ (c + levels p E A B) * Fr.Mn A B ∈ LocRing p := by
  rcases lt_trichotomy A B with h | h | h
  · exact entry_off hF p c hc hE h hB
  · subst h; exact entry_diag hF p c hc hE hA
  · have hm : Fr.Mn A B = Fr.Mn B A := by
      unfold Frame.Mn
      rw [if_neg (by omega), if_neg (by omega), max_comm, min_comm]
    have hl : levels p E A B = levels p E B A := by
      unfold levels; exact Finset.sum_congr rfl fun e _ => wt_comm _ _ _
    rw [hm, hl]
    exact entry_off hF p c hc hE h hA

end Entries

/-! ### The determinant of `Full(X)` -/

section Full

variable {Fr : Frame} (hF : LamLike Fr)

/-- The `2`-adic correction coming from the factor `1/16`. -/
def cOf (p : ℕ) : ℕ := if p = 2 then 4 else 0

lemma cOf_mem (p : ℕ) [hp : Fact p.Prime] : (p : ℚ) ^ cOf p * (1 / 16) ∈ LocRing p := by
  unfold cOf
  split_ifs with h
  · subst h; norm_num
  · have : ¬ p ∣ 16 := by
      intro hd
      have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
      rw [h16] at hd
      have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow hd)
      exact h this
    have h2 := inv_natCast_mem_locRing (ℓ := p) this
    simpa using h2

/-- The number of levels summed over. -/
def Elev (r m : ℕ) : ℕ := 4 * (r + 2 * m) * (r + 2 * m)

lemma Elev_lt (p : ℕ) (hp : 2 ≤ p) (r m : ℕ) : 4 * (r + 2 * m) * (r + 2 * m) < p ^ (Elev r m + 1) := by
  have h1 : Elev r m + 1 < 2 ^ (Elev r m + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (Elev r m + 1) ≤ p ^ (Elev r m + 1) := Nat.pow_le_pow_left hp _
  have e : 4 * (r + 2 * m) * (r + 2 * m) = Elev r m := rfl
  rw [e]
  exact lt_of_lt_of_le (Nat.lt_succ_self _ |>.trans h1) h2

/-- The weight table of `Full(X)` at the prime `p`. -/
def hybW (r m p : ℕ) (a b : Fin r ⊕ Fin m) : ℕ :=
  cOf p + levels p (Elev r m) (Frame.hybRow r m a) (Frame.hybCol r m b)

/-- The tropical exponent at `p`. -/
noncomputable def tropExp (r m p : ℕ) : ℕ := tropVal (hybW r m p)

lemma hybRow_le (r m : ℕ) (a : Fin r ⊕ Fin m) : Frame.hybRow r m a ≤ r + 2 * m := by
  rcases a with c | i
  · simp [Frame.hybRow]; have := c.2; omega
  · simp [Frame.hybRow]

lemma hybCol_le (r m : ℕ) (a : Fin r ⊕ Fin m) : Frame.hybCol r m a ≤ r + 2 * m := by
  rcases a with c | i
  · simp [Frame.hybCol]; have := c.2; omega
  · simp [Frame.hybCol]

include hF in
/-- **The hybrid tropical bound.**  Every coefficient of `det Full(X)` is `p^{tropExp}`-integral. -/
theorem fullPoly_gle (p : ℕ) [Fact p.Prime] (r m : ℕ) :
    GLE p (tropExp r m p) (Fr.fullPoly r m) := by
  unfold Frame.fullPoly tropExp
  apply det_gle
  intro a b
  have h1 : GLE p (hybW r m p a b) (C (Fr.Mn (Frame.hybRow r m a) (Frame.hybCol r m b))) := by
    rw [GLE.C_iff]
    exact entry_gle hF p _ (cOf_mem p) (Elev_lt p (Fact.out : p.Prime).two_le r m)
      (hybRow_le r m a) (hybCol_le r m b)
  have hX : GLE p (hybW r m p a b) (X : ℚ[X]) := GLE.X.mono (Nat.zero_le _)
  rcases a with c | i <;> rcases b with c' | j
  · by_cases h : c = c'
    · simpa [Matrix.of_apply, h] using hX.add h1
    · simpa [Matrix.of_apply, h] using h1
  all_goals simpa [Matrix.of_apply] using h1

lemma blk_eq_zero_of_large {p e N a : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hbig : 4 * N < p)
    (ha : a ≤ N) : blk (p ^ e) a = 0 := by
  unfold blk
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hs
  have hk' := Finset.mem_Icc.mp hk
  have h1 : p ∣ k * (4 * k - 1) := (dvd_pow_self p (by omega)).trans hs
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
  · have := Nat.le_of_dvd (by omega) h; omega
  · have := Nat.le_of_dvd (by omega) h; omega

lemma wt_eq_zero_of_large {p e N A B : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hbig : 4 * N < p)
    (hA : A ≤ N) (hB : B ≤ N) : wt (p ^ e) A B = 0 := by
  unfold wt
  rw [blk_eq_zero_of_large hp he hbig hA, blk_eq_zero_of_large hp he hbig hB]
  by_cases h : A = B
  · simp [h]
  · rw [if_neg h]
    have hnd : ¬ (((p ^ e : ℕ) : ℤ) ∣ (A : ℤ) - B) := by
      intro hd
      have h0 := Int.eq_zero_of_abs_lt_dvd hd (by
        have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
        have h2 : (p : ℤ) ≤ ((p ^ e : ℕ) : ℤ) := by exact_mod_cast this
        rw [abs_lt]; constructor <;> omega)
      omega
    push_cast at hnd
    simp [hnd]

lemma tropExp_eq_zero (r m p : ℕ) (hp : p.Prime) (hbig : 4 * (r + 2 * m) + 2 < p) :
    tropExp r m p = 0 := by
  unfold tropExp
  have hz : hybW r m p = fun _ _ => 0 := by
    funext a b
    unfold hybW cOf levels
    rw [if_neg (by omega)]
    rw [Finset.sum_eq_zero (fun e he => wt_eq_zero_of_large hp (Finset.mem_Icc.mp he).1
      (by omega) (hybRow_le r m a) (hybCol_le r m b))]
    rfl
  rw [hz]
  unfold tropVal
  simp

/-- The explicit common denominator: `∏_{p ≤ 4N+2} p^{tropExp}`. -/
noncomputable def Dhyb (r m : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime, p ^ tropExp r m p

lemma Dhyb_pos (r m : ℕ) : 0 < Dhyb r m := by
  unfold Dhyb
  exact Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _

include hF in
/-- **Integrality.**  `Dhyb · det Full(X)` has integer coefficients. -/
theorem Dhyb_integral (r m : ℕ) (i : ℕ) :
    ∃ z : ℤ, (Dhyb r m : ℚ) * (Fr.fullPoly r m).coeff i = z := by
  apply int_of_forall_locRing
  intro p hp
  have hgle := fullPoly_gle hF p r m i
  by_cases hb : p < 4 * (r + 2 * m) + 3
  · have hmem : p ∈ (Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hp.out⟩
    have hD : (Dhyb r m : ℚ) = (p : ℚ) ^ tropExp r m p *
        ((∏ q ∈ ((Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime).erase p,
          q ^ tropExp r m q : ℕ) : ℚ) := by
      unfold Dhyb
      rw [← Nat.cast_pow, ← Nat.cast_mul, Finset.mul_prod_erase _ (fun q => q ^ tropExp r m q) hmem]
    rw [hD]
    have hR := int_mem_locRing (ℓ := p)
      ((∏ q ∈ ((Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime).erase p,
          q ^ tropExp r m q : ℕ) : ℤ)
    have := (LocRing p).mul_mem hgle (by simpa using hR)
    convert this using 1; push_cast; ring
  · have h0 := tropExp_eq_zero r m p hp.out (by omega)
    rw [h0] at hgle
    simp only [pow_zero, one_mul] at hgle
    rw [mul_comm]
    exact (LocRing p).mul_mem hgle (by exact_mod_cast int_mem_locRing (ℓ := p) (Dhyb r m : ℤ))

lemma log_Dhyb (r m : ℕ) :
    Real.log (Dhyb r m) = ∑ p ∈ (Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime,
      (tropExp r m p : ℝ) * Real.log p := by
  unfold Dhyb
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity

end Full

end CatalanCore.Arith.Hybrid
