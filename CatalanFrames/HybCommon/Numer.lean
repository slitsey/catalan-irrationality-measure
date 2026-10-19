module

public import CatalanCore.Arith.Hybrid.Extra
public import CatalanCore.Arith.Hybrid.PieceSum
public import CatalanCore.Arith.Hybrid.Pieces
public import CatalanCore.Arith.Hybrid.Majorant

@[expose] public section

/-!
# The numerology layer of the hybrid content bound, generic in the frame

Everything here is stated over a hybrid instance `I` and the numerology `BadInfo I Lc cm`:
* `Lc` is `I.cd.L` (λ, mirror: `4`; L(2, χ₋₃): `3`),
* `cm` bounds the normalisation exponents `cOf I p` (λ: `4`; L(2, χ₋₃): `2`),
* `Ebd N + N ≤ 5 N³` (λ: `4N² + N`),
* the bad primes are `≤ 3` and contain `2` (λ: `{2, 3}`; L(2, χ₋₃): `{2, 3}`).
The hybrid size `m` is arbitrary (λ: `r / 8`), the modulus `M` and the class set `Cs ⊆ ZMod M` of the good
primes are arbitrary (λ: `M = 4`, `Cs = {1, 3}`; L(2, χ₋₃): `M = 6`, `Cs = {1, 5}`), and the weight `w`
of the level-1 part is an arbitrary non-negative function.  No zero-set or residue-class assumption is
made on the levels here.

* `tropExp_leG`: per-prime bound for the tropical exponent (bad primes, higher levels, level 1);
* `sum_le_gen`: `∑_{p < L N + 6} T p log p ≤ extraG L E c β r m + ∑_{c ∈ Cs} clsSum M c w 0 (R c)`.
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- The numerology of a hybrid instance (see the module docstring). -/
structure BadInfo (I : HybInst Fr) (Lc cm : ℕ) : Prop where
  L_eq : I.cd.L = Lc
  Lc_le : Lc ≤ 4
  cm_le : cm ≤ 4
  Ebd_le : ∀ N, I.Ebd N + N ≤ 5 * N ^ 3
  two_mem : 2 ∈ I.cd.bad
  bad_le : ∀ b ∈ I.cd.bad, b ≤ 3
  cOf_le : ∀ p, cOf I p ≤ cm

/-- The cubic bound `E N = 5 N³` of the numerology. -/
abbrev Ecub (N : ℕ) : ℕ := 5 * N ^ 3

/-- **Generic facts about the levels of a hybrid instance.**  `Gd` selects the good primes (all other
primes are bad or small) and `Z q c` says that the level of `q` at `c` is zero.  The zero set need not be
an initial segment: this is the generic form used for any modulus; the initial-segment case
`Z q c := c < kq q` is `TropFacts` below. -/
structure LevelFacts (I : HybInst Fr) (Gd : ℕ → Prop) (Z : ℕ → ℕ → Prop) : Prop where
  good : ∀ p, p.Prime → Gd p → IsPrimePow p ∧ ∀ q ∈ I.cd.bad, ¬ q ∣ p
  zero_iff : ∀ q c, IsPrimePow q → (∀ p ∈ I.cd.bad, ¬ p ∣ q) → (I.lev q c = 0 ↔ Z q c)
  high : ∀ q c, 1 ≤ q → q ≤ c → 0 < I.lev q c

/-- `4 N² + N ≤ 5 N³`: the λ and mirror `Ebd N + N` is inside the cubic interface bound. -/
lemma cubic_Ebd (N : ℕ) : 4 * N * N + N ≤ 5 * N ^ 3 := by
  rcases N with _ | N
  · simp
  · nlinarith [Nat.zero_le N, Nat.zero_le (N * N), Nat.zero_le (N * N * N)]

/-- The sum of `log b` over the bad primes. -/
noncomputable def badLog (I : HybInst Fr) : ℝ := ∑ b ∈ I.cd.bad, Real.log b

lemma badLog_nonneg (I : HybInst Fr) : 0 ≤ badLog I :=
  Finset.sum_nonneg fun b hb => Real.log_nonneg (by exact_mod_cast (I.cd.bad_prime b hb).one_lt.le)

/-- Level-count for non-bad primes. -/
noncomputable def cntG (I : HybInst Fr) (r m p : ℕ) : ℕ :=
  ((Finset.Icc 2 (Elev I r m)).filter (fun e => p ^ e ≤ I.cd.L * (r + 2 * m))).card

lemma cntG_le (I : HybInst Fr) (r m p : ℕ) (hp : p.Prime) :
    cntG I r m p ≤ Nat.log 2 (I.cd.L * (r + 2 * m)) := by
  unfold cntG
  calc _ ≤ (Finset.Icc 2 (Nat.log 2 (I.cd.L * (r + 2 * m)))).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
        have h2 := Finset.mem_Icc.mp he1
        refine Finset.mem_Icc.mpr ⟨h2.1, ?_⟩
        apply Nat.le_log_of_pow_le (by norm_num)
        exact (Nat.pow_le_pow_left hp.two_le e).trans he2
    _ ≤ _ := by simp

lemma cntG_zero (I : HybInst Fr) (r m p : ℕ) (hp : p.Prime) (h : I.cd.L * (r + 2 * m) < p ^ 2) :
    cntG I r m p = 0 := by
  unfold cntG
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hle
  have h2 := (Finset.mem_Icc.mp he).1
  have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos h2
  omega

lemma cnt_bad_G (I : HybInst Fr) (b r m : ℕ) (hb : 2 ≤ b) :
    ((Finset.Icc 1 (Elev I r m)).filter
      (fun e => b ^ e ≤ I.Ebd (r + 2 * m) + (r + 2 * m))).card ≤
      Nat.log 2 (I.Ebd (r + 2 * m) + (r + 2 * m)) := by
  calc _ ≤ (Finset.Icc 1 (Nat.log 2 (I.Ebd (r + 2 * m) + (r + 2 * m)))).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
        have h2 := Finset.mem_Icc.mp he1
        refine Finset.mem_Icc.mpr ⟨h2.1, ?_⟩
        apply Nat.le_log_of_pow_le (by norm_num)
        exact (Nat.pow_le_pow_left hb e).trans he2
    _ ≤ _ := by simp

lemma Bnd_le_G {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) (r m : ℕ) :
    Bnd I r m ≤ Lc * (r + 2 * m) + 6 := by
  have : I.cd.bad.sup id ≤ 3 := Finset.sup_le fun b hb => B.bad_le b hb
  unfold Bnd
  rw [B.L_eq]
  omega

/-- The bad-prime weight of a prime in the bad set. -/
noncomputable def exBad (cm r m : ℕ) : ℝ :=
  (r + m : ℝ) * (cm + 2 * (Nat.log 2 (Ecub (r + 2 * m)) : ℝ))

/-- **Per-prime bound for the tropical exponent**: the bad primes carry `exBad`, the good primes
the level-1 part `tropVal (HW lev p r m)` plus the higher levels. -/
theorem tropExp_leG {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) (r m p : ℕ) (hr : 1 ≤ r)
    (hp : p.Prime) :
    (tropExp I r m p : ℝ) ≤ (if p ∈ I.cd.bad then exBad cm r m else 0) +
      ((2 * (r + m) * cntG I r m p : ℕ) : ℝ) +
      (if p ∈ I.cd.bad then 0 else (tropVal (HW I.lev p r m) : ℝ)) := by
  have hn2 : (0 : ℝ) ≤ ((2 * (r + m) * cntG I r m p : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases hX : p ∈ I.cd.bad
  · have hb := tropExp_le_bad I r m p
    have hcB := cnt_bad_G I p r m hp.two_le
    have hlg : Nat.log 2 (I.Ebd (r + 2 * m) + (r + 2 * m)) ≤ Nat.log 2 (Ecub (r + 2 * m)) :=
      Nat.log_mono_right (B.Ebd_le _)
    have hc : cOf I p ≤ cm := B.cOf_le p
    have h1 : tropExp I r m p ≤ cm * (r + m) + 2 * (r + m) * Nat.log 2 (Ecub (r + 2 * m)) := by
      refine hb.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hc) ?_)
      exact Nat.mul_le_mul_left _ (hcB.trans hlg)
    have h1' : (tropExp I r m p : ℝ) ≤
        (cm : ℝ) * (r + m : ℕ) + 2 * (r + m : ℕ) * (Nat.log 2 (Ecub (r + 2 * m)) : ℕ) := by
      exact_mod_cast h1
    rw [if_pos hX, if_pos hX]
    unfold exBad
    push_cast at h1' hn2 ⊢
    nlinarith
  · have hb := tropExp_le I r m p hr hp hX
    rw [cOf_eq_zero I hp hX, zero_mul, zero_add] at hb
    rw [if_neg hX, if_neg hX]
    have hb' : (tropExp I r m p : ℝ) ≤
        ((tropVal (HW I.lev p r m) + 2 * (r + m) * cntG I r m p : ℕ) : ℝ) := by
      exact_mod_cast hb
    push_cast at hb' ⊢
    linarith

/-- The classes of a family of good primes: summing over the class set `Cs` covers the good primes. -/
lemma good_sum_le_cls {M : ℕ} (Cs : Finset (ZMod M)) (bad : Finset ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (Bd : ℕ)
    (hcls : ∀ p, p.Prime → p ∉ bad → (p : ZMod M) ∈ Cs) :
    ∑ p ∈ (Finset.range (Bd + 1)).filter Nat.Prime, (if p ∈ bad then (0 : ℝ) else w p * Real.log p) ≤
      ∑ c ∈ Cs, clsSum M c w 0 Bd := by
  have hset : (Finset.range (Bd + 1)).filter Nat.Prime = (Finset.Ioc 0 Bd).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩
  simp only [clsSum_eq]
  rw [Finset.sum_comm, hset, Finset.sum_filter]
  refine Finset.sum_le_sum fun p hp => ?_
  have hlog : 0 ≤ w p * Real.log p := by
    by_cases hp1 : p.Prime
    · exact mul_nonneg (hw0 p) (Real.log_nonneg (by exact_mod_cast hp1.one_lt.le))
    · by_cases h0 : p = 0
      · subst h0; simp
      · have : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr h0
        exact mul_nonneg (hw0 p) (Real.log_nonneg (by exact_mod_cast this))
  by_cases hpp : p.Prime
  · rw [if_pos hpp]
    have e : ∑ c ∈ Cs, (if p.Prime ∧ (p : ZMod M) = c then w p * Real.log p else 0) =
        if (p : ZMod M) ∈ Cs then w p * Real.log p else 0 := by
      simp only [hpp, true_and]
      rw [Finset.sum_ite_eq]
    rw [e]
    by_cases hb : p ∈ bad
    · rw [if_pos hb]; split_ifs <;> [exact hlog; exact le_rfl]
    · rw [if_neg hb, if_pos (hcls p hpp hb)]
  · rw [if_neg hpp]
    refine le_of_eq ?_
    simp [hpp]

/-- **Level-1 plus negligible terms, generic.** -/
theorem sum_le_gen {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) {M : ℕ} [NeZero M]
    (Cs : Finset (ZMod M)) (R : ZMod M → ℕ) (r m : ℕ) (T : ℕ → ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (cnt : ℕ → ℕ)
    (hcnt_le : ∀ p, p.Prime → cnt p ≤ Nat.log 2 (Lc * (r + 2 * m)))
    (hcnt0 : ∀ p, p.Prime → Lc * (r + 2 * m) < p ^ 2 → cnt p = 0)
    (hT : ∀ p, p.Prime → (T p : ℝ) ≤ (if p ∈ I.cd.bad then exBad cm r m else 0) +
      ((2 * (r + m) * cnt p : ℕ) : ℝ) + (if p ∈ I.cd.bad then 0 else w p))
    (hcls : ∀ p, p.Prime → p ∉ I.cd.bad → (p : ZMod M) ∈ Cs)
    (hRb : ∀ c ∈ Cs, ∀ b ∈ I.cd.bad, (b : ZMod M) = c → b ≤ R c)
    (ht : ∀ c ∈ Cs, ∀ p, p.Prime → p ∉ I.cd.bad → (p : ZMod M) = c → R c < p → w p = 0) :
    ∑ p ∈ (Finset.range (Lc * (r + 2 * m) + 6)).filter Nat.Prime, (T p : ℝ) * Real.log p ≤
      extraG Lc Ecub cm (badLog I) r m + ∑ c ∈ Cs, clsSum M c w 0 (R c) := by
  set Q := Lc * (r + 2 * m) with hQ
  set P := (Finset.range (Q + 6)).filter Nat.Prime with hP
  set P5 := (Finset.range (Q + 5)).filter Nat.Prime with hP5
  have hpt : ∀ p ∈ P, (T p : ℝ) * Real.log p ≤
      (((2 * (r + m) * cnt p : ℕ) : ℝ) * Real.log p) +
        ((if p ∈ I.cd.bad then exBad cm r m * Real.log p else 0) +
          (if p ∈ I.cd.bad then 0 else w p * Real.log p)) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have := mul_le_mul_of_nonneg_right (hT p hpp) hlog
    by_cases hb : p ∈ I.cd.bad
    · simp only [hb, if_true] at this ⊢
      linarith
    · simp only [hb, if_false] at this ⊢
      linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the level counts
  have hex5 : ∑ p ∈ P5, ((2 * (r + m) * cnt p : ℕ) : ℝ) * Real.log p ≤
      ((Nat.sqrt Q : ℝ) + 1) *
        (2 * (r + m : ℝ) * (Nat.log 2 Q : ℕ) * Real.log ((Lc : ℝ) * (r + 2 * m) + 5)) :=
    ex_sum_bound r m (Q + 5) Lc le_rfl (fun p => 2 * (r + m) * cnt p) (Nat.log 2 Q)
      (fun p hp => Nat.mul_le_mul_left _ (hcnt_le p hp))
      (fun p hp h => by simp [hcnt0 p hp h])
  have hex : ∑ p ∈ P, ((2 * (r + m) * cnt p : ℕ) : ℝ) * Real.log p ≤
      ((Nat.sqrt Q : ℝ) + 1) *
        (2 * (r + m : ℝ) * (Nat.log 2 Q : ℕ) * Real.log ((Lc : ℝ) * (r + 2 * m) + 5)) := by
    by_cases hq : (Q + 5).Prime
    · have hnot : (Q + 5) ∉ P5 := by simp [hP5]
      have hPe : P = insert (Q + 5) P5 := by
        ext p
        simp only [hP, hP5, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h : p = Q + 5
          · exact Or.inl h
          · exact Or.inr ⟨by omega, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · subst h; exact ⟨by omega, hq⟩
          · exact ⟨by omega, h2⟩
      rw [hPe, Finset.sum_insert hnot]
      have hz : cnt (Q + 5) = 0 := hcnt0 _ hq (by nlinarith)
      simp only [hz, Nat.mul_zero, Nat.cast_zero, zero_mul, zero_add]
      exact hex5
    · have hPe : P = P5 := by
        ext p
        simp only [hP, hP5, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          have : p ≠ Q + 5 := fun h => hq (h ▸ h2)
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      rw [hPe]
      exact hex5
  -- the bad primes
  have hbad : ∑ p ∈ P, (if p ∈ I.cd.bad then exBad cm r m * Real.log p else 0) ≤
      exBad cm r m * badLog I := by
    have hexnn : 0 ≤ exBad cm r m := by unfold exBad; positivity
    rw [← Finset.sum_filter]
    unfold badLog
    rw [Finset.mul_sum]
    have hsub : P.filter (fun p => p ∈ I.cd.bad) ⊆ I.cd.bad := fun x hx => (Finset.mem_filter.mp hx).2
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ =>
      mul_nonneg hexnn (Real.log_nonneg (by exact_mod_cast (I.cd.bad_prime b hb).one_lt.le))
  -- the level-1 sums
  have hg : ∑ p ∈ P, (if p ∈ I.cd.bad then 0 else w p * Real.log p) ≤
      ∑ c ∈ Cs, clsSum M c w 0 (R c) := by
    have hPe : P = (Finset.range (Q + 5 + 1)).filter Nat.Prime := rfl
    rw [hPe]
    refine (good_sum_le_cls Cs I.cd.bad w hw0 (Q + 5) hcls).trans ?_
    refine Finset.sum_le_sum fun c hc => ?_
    refine clsSum_le_of_tail c w hw0 (B := Q + 5) (B' := R c) ?_
    intro p hp1 hpp hpc
    by_cases hb : p ∈ I.cd.bad
    · exact absurd (hRb c hc p hb hpc) (by omega)
    · exact ht c hc p hpp hb hpc hp1
  unfold extraG
  have e1 : (r + m : ℝ) * (cm + 2 * (Nat.log 2 (Ecub (r + 2 * m)) : ℝ)) * badLog I =
      exBad cm r m * badLog I := rfl
  rw [e1]
  have e2 : ((Nat.sqrt (Lc * (r + 2 * m)) : ℝ) + 1) *
      (2 * (r + m : ℝ) * (Nat.log 2 (Lc * (r + 2 * m)) : ℝ) *
        Real.log ((Lc : ℝ) * (r + 2 * m) + 5)) =
      ((Nat.sqrt Q : ℝ) + 1) *
        (2 * (r + m : ℝ) * (Nat.log 2 Q : ℕ) * Real.log ((Lc : ℝ) * (r + 2 * m) + 5)) := rfl
  rw [e2]
  linarith

/-- `sum_le_gen`, summed over the primes below `Bnd I r m` (the range of `log Dhyb`, `log DhybT`). -/
theorem sum_Bnd_le_gen {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) {M : ℕ} [NeZero M]
    (Cs : Finset (ZMod M)) (R : ZMod M → ℕ) (r m : ℕ) (T : ℕ → ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (cnt : ℕ → ℕ)
    (hcnt_le : ∀ p, p.Prime → cnt p ≤ Nat.log 2 (Lc * (r + 2 * m)))
    (hcnt0 : ∀ p, p.Prime → Lc * (r + 2 * m) < p ^ 2 → cnt p = 0)
    (hT : ∀ p, p.Prime → (T p : ℝ) ≤ (if p ∈ I.cd.bad then exBad cm r m else 0) +
      ((2 * (r + m) * cnt p : ℕ) : ℝ) + (if p ∈ I.cd.bad then 0 else w p))
    (hcls : ∀ p, p.Prime → p ∉ I.cd.bad → (p : ZMod M) ∈ Cs)
    (hRb : ∀ c ∈ Cs, ∀ b ∈ I.cd.bad, (b : ZMod M) = c → b ≤ R c)
    (ht : ∀ c ∈ Cs, ∀ p, p.Prime → p ∉ I.cd.bad → (p : ZMod M) = c → R c < p → w p = 0) :
    ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (T p : ℝ) * Real.log p ≤
      extraG Lc Ecub cm (badLog I) r m + ∑ c ∈ Cs, clsSum M c w 0 (R c) := by
  refine le_trans ?_ (sum_le_gen B Cs R r m T w hw0 cnt hcnt_le hcnt0 hT hcls hRb ht)
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.range_mono (Bnd_le_G B r m))) fun p hp _ =>
    mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))

/-- The bad primes are inside `{2, 3}`, so `badLog ≤ 3 log 2`. -/
theorem BadInfo.badLog_le {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) :
    badLog I ≤ 3 * Real.log 2 := by
  have hsub : I.cd.bad ⊆ {2, 3} := fun b hb => by
    have h1 := B.bad_le b hb
    have h2 := (I.cd.bad_prime b hb).two_le
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  unfold badLog
  calc ∑ b ∈ I.cd.bad, Real.log b ≤ ∑ b ∈ ({2, 3} : Finset ℕ), Real.log b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ => by
          have := Finset.mem_insert.mp hb
          rcases this with rfl | hb'
          · exact Real.log_nonneg (by norm_num)
          · have : b = 3 := Finset.mem_singleton.mp hb'
            subst this; exact Real.log_nonneg (by norm_num)
    _ ≤ 3 * Real.log 2 := by
        rw [Finset.sum_pair (by norm_num)]
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
        push_cast
        linarith

/-- The generic extra bound is dominated by `3 · extraBound`. -/
theorem BadInfo.extraG_le {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) (r m : ℕ) :
    extraG Lc Ecub cm (badLog I) r m ≤ 3 * extraBound r m :=
  (extraG_mono B.Lc_le (fun N => le_rfl) B.cm_le B.badLog_le (badLog_nonneg I) r m).trans
    (extraBound_three r m)

/-- The numerology bound is negligible: `extraG ≤ ε r²` eventually, uniformly in `m ≤ r`. -/
theorem BadInfo.extra_small {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m ≤ r, extraG Lc Ecub cm (badLog I) r m ≤ ε * (r : ℝ) ^ 2 :=
  extraG_small B.Lc_le (fun N => le_rfl) B.cm_le (badLog_nonneg I) B.badLog_le ε hε

/-- **`log Dhyb`, generic**: the level-1 weight `w` bounds `tropVal (HW lev p r m)` at the good primes. -/
theorem log_Dhyb_le_gen {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) {M : ℕ} [NeZero M]
    (Cs : Finset (ZMod M)) (R : ZMod M → ℕ) (r m : ℕ) (hr : 1 ≤ r) (w : ℕ → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hw : ∀ p, p.Prime → (tropVal (HW I.lev p r m) : ℝ) ≤ w p)
    (hcls : ∀ p, p.Prime → p ∉ I.cd.bad → (p : ZMod M) ∈ Cs)
    (hRb : ∀ c ∈ Cs, ∀ b ∈ I.cd.bad, (b : ZMod M) = c → b ≤ R c)
    (ht : ∀ c ∈ Cs, ∀ p, p.Prime → p ∉ I.cd.bad → (p : ZMod M) = c → R c < p → w p = 0) :
    Real.log (Dhyb I r m) ≤ extraG Lc Ecub cm (badLog I) r m + ∑ c ∈ Cs, clsSum M c w 0 (R c) := by
  rw [log_Dhyb]
  refine sum_Bnd_le_gen B Cs R r m (tropExp I r m) w hw0 (cntG I r m)
    (fun p hp => (cntG_le I r m p hp).trans (by rw [B.L_eq]))
    (fun p hp h => cntG_zero I r m p hp (by rw [B.L_eq]; exact h)) (fun p hp => ?_) hcls hRb ht
  have h := tropExp_leG B r m p hr hp
  have := hw p hp
  by_cases hb : p ∈ I.cd.bad
  · simpa [hb] using h
  · simp only [hb, if_false] at h ⊢
    linarith

/-- **All parameters of the hybrid numerology in one place.**
* `Lc`, `cm`, `bad`: the bound `L`, the `cOf` bound and the bad primes/`Ebd` (`BadInfo`);
* `M`, `Cs`: the modulus and the residue classes of the good primes;
* `mf`: the hybrid size `m = mf r ≤ r` (λ: `r / 8`);
* `Gd`, `Z`, `levels`: the good primes and the zero set of the levels (not necessarily an initial segment).
λ and the mirror: `(Lc, cm, M, Cs) = (4, 4, 4, {1, 3})`, `mf r = r / 8`, `Z q c = (c < kq q)`.
L(2, χ₋₃): `(Lc, cm, M, Cs) = (3, 2, 6, {1, 5})`, bad primes `{2, 3}`, `Z₁ = {0, 1, 3, 4, 5}`. -/
structure HybParams (I : HybInst Fr) where
  Lc : ℕ
  cm : ℕ
  bad : BadInfo I Lc cm
  M : ℕ
  [nz : NeZero M]
  Cs : Finset (ZMod M)
  cls : ∀ p, p.Prime → p ∉ I.cd.bad → (p : ZMod M) ∈ Cs
  mf : ℕ → ℕ
  mf_le : ∀ r, mf r ≤ r
  Gd : ℕ → Prop
  Z : ℕ → ℕ → Prop
  levels : LevelFacts I Gd Z

attribute [instance] HybParams.nz

/-- `log Dhyb` against the numerology and the class sums of a `HybParams`. -/
theorem HybParams.log_Dhyb_le {I : HybInst Fr} (P : HybParams I) (R : ZMod P.M → ℕ) (r : ℕ)
    (hr : 1 ≤ r) (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, p.Prime → (tropVal (HW I.lev p r (P.mf r)) : ℝ) ≤ w p)
    (hRb : ∀ c ∈ P.Cs, ∀ b ∈ I.cd.bad, (b : ZMod P.M) = c → b ≤ R c)
    (ht : ∀ c ∈ P.Cs, ∀ p, p.Prime → p ∉ I.cd.bad → (p : ZMod P.M) = c → R c < p → w p = 0) :
    Real.log (Dhyb I r (P.mf r)) ≤ extraG P.Lc Ecub P.cm (badLog I) r (P.mf r) +
      ∑ c ∈ P.Cs, clsSum P.M c w 0 (R c) :=
  log_Dhyb_le_gen P.bad P.Cs R r (P.mf r) hr w hw0 hw P.cls hRb ht

end CatalanFrames.HybCommon
