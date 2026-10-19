module

public import CatalanCore.Arith.Hybrid.Majorant

@[expose] public section

/-!
# Block-valued levels: the instance constructor for λ and the mirror

`lev q a = blk q a`, the number of `q`-singular indices `k ∈ [1, a]` (`q ∣ Φ k`).  Levels never
cancel, so this is the exact valuation bound of the paper's eq. (major).  `HybInst.ofSing` builds a
`HybInst` from `ContentData` plus a bound `Ebd` on `Φ k` for `k ≤ N`.

P6 must NOT use this constructor: its levels cancel (the block count overcounts by about
`0.14 r²`); it supplies its own level-valued `lev` and proofs of `off_val`, `diag_val`, `lev_large`,
`lev_Ebd`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

/-- `k` is `q`-singular: `q ∣ Φ k`. -/
def Sing (Φ : ℕ → ℕ) (q k : ℕ) : Prop := q ∣ Φ k

instance (Φ : ℕ → ℕ) (q k : ℕ) : Decidable (Sing Φ q k) := by unfold Sing; infer_instance

/-- The block of `a`: the number of `q`-singular indices in `[1, a]`. -/
def blk (Φ : ℕ → ℕ) (q a : ℕ) : ℕ := ((Icc 1 a).filter (Sing Φ q)).card

variable {Φ : ℕ → ℕ}

lemma blk_lt {q lo hi k : ℕ} (hk : k ∈ Ioc lo hi) (hs : Sing Φ q k) :
    blk Φ q lo < blk Φ q hi := by
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

lemma blk_pos_of {q c k : ℕ} (hk : k ∈ Icc 1 c) (hs : Sing Φ q k) : 0 < blk Φ q c := by
  unfold blk
  exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hs⟩⟩

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

section Constructor

variable {Fr : Frame} (cd : CatalanCore.Arith.ContentData Fr) (Ebd : ℕ → ℕ)
  (hle : ∀ k N, k ≤ N → cd.Phi k ≤ Ebd N)

include hle in
lemma sing_off_val (p : ℕ) [hp : Fact p.Prime] (E N lo hi : ℕ) (hE1 : Ebd N < p ^ (E + 1))
    (hE2 : N < p ^ (E + 1)) (hlo : lo < hi) (hhi : hi ≤ N) :
    (p : ℚ) ^ (levels (blk cd.Phi) p E lo hi) *
      ((1 / ((hi : ℚ) - lo)) * ∑ k ∈ Ioc lo hi, Fr.Delta k) ∈ LocRing p := by
  have hp' := hp.out
  set W1 := ((Icc 1 E).filter (fun e => blk cd.Phi (p ^ e) lo ≠ blk cd.Phi (p ^ e) hi)).card
    with hW1
  set W2 := ((Icc 1 E).filter (fun e => (p ^ e : ℕ) ∣ hi - lo)).card with hW2
  have hlev : levels (blk cd.Phi) p E lo hi = W1 + W2 := by
    unfold levels wt
    rw [Finset.sum_congr rfl (g := fun e =>
      (if blk cd.Phi (p ^ e) lo ≠ blk cd.Phi (p ^ e) hi then 1 else 0) +
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
  have hdN : hi - lo < p ^ (E + 1) := by omega
  have hd : (p : ℚ) ^ W2 / ((hi - lo : ℕ) : ℚ) ∈ LocRing p :=
    pow_div_mem hdpos (fact_le_count hp.out hdpos hdN _ (fun e _ h => h))
  have hS : (p : ℚ) ^ W1 * ∑ k ∈ Ioc lo hi, Fr.Delta k ∈ LocRing p := by
    rw [Finset.mul_sum]
    apply (LocRing p).sum_mem
    intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    have hk1 : 0 < k := by omega
    have hn : 0 < cd.Phi k := cd.Phi_pos k hk1
    have hnE : cd.Phi k < p ^ (E + 1) := lt_of_le_of_lt (hle k N (by omega)) hE1
    have hfl : (cd.Phi k).factorization p ≤ W1 :=
      fact_le_count hp.out hn hnE _ (fun e _ hdv => by
        exact ne_of_lt (blk_lt hk (show Sing cd.Phi (p ^ e) k from hdv)))
    have := pow_div_mem (p := p) hn hfl
    obtain ⟨z, hz⟩ := cd.delta_int k hk1
    have hPq : (cd.Phi k : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : (p : ℚ) ^ W1 * Fr.Delta k = (z : ℚ) * ((p : ℚ) ^ W1 / (cd.Phi k : ℚ)) := by
      rw [← hz]; field_simp
    rw [e]
    exact (LocRing p).mul_mem (int_mem_locRing _) this
  rw [hlev]
  have e : (p : ℚ) ^ (W1 + W2) * ((1 / ((hi : ℚ) - lo)) * ∑ k ∈ Ioc lo hi, Fr.Delta k)
      = ((p : ℚ) ^ W2 / ((hi - lo : ℕ) : ℚ)) * ((p : ℚ) ^ W1 * ∑ k ∈ Ioc lo hi, Fr.Delta k) := by
    rw [Nat.cast_sub hlo.le]
    ring
  rw [e]
  exact (LocRing p).mul_mem hd hS

include hle in
lemma sing_diag_val (p : ℕ) [hp : Fact p.Prime] (E N a : ℕ) (hE1 : Ebd N < p ^ (E + 1))
    (ha : a ≤ N) :
    (p : ℚ) ^ (levels (blk cd.Phi) p E a a) * ∑ k ∈ Icc 1 a, Fr.Dsq k ∈ LocRing p := by
  have hp' := hp.out
  set W' := ((Icc 1 E).filter (fun e => 0 < blk cd.Phi (p ^ e) a)).card with hW'
  have hlev : levels (blk cd.Phi) p E a a = 2 * W' := by
    unfold levels wt
    rw [Finset.sum_congr rfl (g := fun e => 2 * (if 0 < blk cd.Phi (p ^ e) a then 1 else 0))]
    · rw [← Finset.mul_sum, Finset.sum_boole]; simp [hW']
    · intro e _
      rw [if_pos rfl]; split_ifs <;> simp
  rw [hlev, Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  have hk1 : 0 < k := by omega
  have hn : 0 < cd.Phi k := cd.Phi_pos k hk1
  have hnE : cd.Phi k < p ^ (E + 1) := lt_of_le_of_lt (hle k N (by omega)) hE1
  have hfl : (cd.Phi k).factorization p ≤ W' :=
    fact_le_count hp.out hn hnE _ (fun e _ hdv => by
      exact blk_pos_of (k := k) hk (show Sing cd.Phi (p ^ e) k from hdv))
  have hn2 : 0 < (cd.Phi k) ^ 2 := by positivity
  have hf2 : ((cd.Phi k) ^ 2).factorization p ≤ 2 * W' := by
    rw [Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    omega
  have := pow_div_mem (p := p) hn2 hf2
  obtain ⟨z, hz⟩ := cd.dsq_int k hk1
  have hPq : (cd.Phi k : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have e : (p : ℚ) ^ (2 * W') * Fr.Dsq k =
      (z : ℚ) * ((p : ℚ) ^ (2 * W') / ((cd.Phi k ^ 2 : ℕ) : ℚ)) := by
    rw [← hz]; push_cast; field_simp
  rw [e]
  exact (LocRing p).mul_mem (int_mem_locRing _) this

lemma sing_lev_large (p e N a : ℕ) (hp : p.Prime) (hb : p ∉ cd.bad) (he : 1 ≤ e)
    (hbig : cd.L * N < p ^ e) (ha : a ≤ N) : blk cd.Phi (p ^ e) a = 0 := by
  unfold blk
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hs
  have hk' := Finset.mem_Icc.mp hk
  have := (cd.kq_le (p ^ e) k (hp.isPrimePow.pow (by omega)) (cd.coprime_bad_pow hp hb)
    (by omega) hs).2
  have h2 : cd.L * k ≤ cd.L * N := Nat.mul_le_mul_left _ (by omega)
  omega

include hle in
lemma sing_lev_Ebd (q N a : ℕ) (hbig : Ebd N + N < q) (ha : a ≤ N) : blk cd.Phi q a = 0 := by
  unfold blk
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hs
  have hk' := Finset.mem_Icc.mp hk
  have h1 : 0 < cd.Phi k := cd.Phi_pos k (by omega)
  have := Nat.le_of_dvd h1 hs
  have := hle k N (by omega)
  omega

/-- The block-valued instance (λ, mirror). -/
noncomputable def HybInst.ofSing : HybInst Fr where
  cd := cd
  Ebd := Ebd
  lev := blk cd.Phi
  off_val := fun p _ E N lo hi h1 h2 h3 h4 => sing_off_val cd Ebd hle p E N lo hi h1 h2 h3 h4
  diag_val := fun p _ E N a h1 h2 _ => sing_diag_val cd Ebd hle p E N a h1 h2
  lev_large := fun p e N a hp hb he hbig ha => sing_lev_large cd p e N a hp hb he hbig ha
  lev_Ebd := fun q N a hbig ha => sing_lev_Ebd cd Ebd hle q N a hbig ha

instance (r m : ℕ) : (HybInst.ofSing cd Ebd hle).DiagOK r m := ⟨fun _ _ => trivial⟩

/--  iff the first singular index has been reached. -/
theorem blk_pos_iff (hatt : ∀ q, IsPrimePow q → (∀ p ∈ cd.bad, ¬ p ∣ q) →
      0 < cd.kq q ∧ q ∣ cd.Phi (cd.kq q))
    {q c : ℕ} (hq : IsPrimePow q) (hb : ∀ p ∈ cd.bad, ¬ p ∣ q) :
    0 < blk cd.Phi q c ↔ cd.kq q ≤ c := by
  constructor
  · intro h
    unfold blk at h
    obtain ⟨k, hk⟩ := Finset.card_pos.mp h
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
    have := Finset.mem_Icc.mp hk1
    exact (cd.kq_le q k hq hb (by omega) hk2).1.trans this.2
  · intro h
    obtain ⟨h1, h2⟩ := hatt q hq hb
    exact blk_pos_of (k := cd.kq q) (Finset.mem_Icc.mpr ⟨h1, h⟩) h2

end Constructor

end CatalanCore.Arith.Hybrid
