module

public import CatalanFrames.HybCommon.TropLog
public import CatalanFrames.HybCommon.TropT
public import CatalanFrames.HybCommon.Pieces

@[expose] public section

/-!
# The content bound `log DhybT ≤ (Λ8 + ε) r² - ∑ δ log p`, generic in the instance

For any block-valued hybrid instance `I` with `TropFacts I o` (offset `o ∈ {1, 3}`) and `BadInfo I`
(`L = 4`, `Ebd N = 4 N²`, bad primes inside `{2, 3}`, `cOf 2 = 4`, `cOf 3 = 0`):
`logDhybT_le_G` for the deficit-valid family `TfunG o I r`.  Both λ (`o = 1`) and the mirror
(`o = 3`) are instances; the piece tables `l3x`, `l1x` are shared and only the residue classes swap.
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- The numerology of the bad primes. -/
structure BadInfo (I : HybInst Fr) : Prop where
  L4 : I.cd.L = 4
  Ebd4 : ∀ N, I.Ebd N = 4 * N * N
  bad_sub : I.cd.bad ⊆ {2, 3}
  c2 : cOf I 2 = 4
  c3 : cOf I 3 = 0

/-- Level-count for non-bad primes. -/
noncomputable def cntG (I : HybInst Fr) (r m p : ℕ) : ℕ :=
  ((Finset.Icc 2 (Elev I r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card

lemma cntG_le (I : HybInst Fr) (r m p : ℕ) (hp : p.Prime) :
    cntG I r m p ≤ Nat.log 2 (4 * (r + 2 * m)) := by
  unfold cntG
  calc _ ≤ (Finset.Icc 2 (Nat.log 2 (4 * (r + 2 * m)))).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
        have h2 := Finset.mem_Icc.mp he1
        refine Finset.mem_Icc.mpr ⟨h2.1, ?_⟩
        apply Nat.le_log_of_pow_le (by norm_num)
        exact (Nat.pow_le_pow_left hp.two_le e).trans he2
    _ ≤ _ := by simp

lemma cntG_zero (I : HybInst Fr) (r m p : ℕ) (hp : p.Prime) (h : 4 * (r + 2 * m) < p ^ 2) :
    cntG I r m p = 0 := by
  unfold cntG
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hle
  have h2 := (Finset.mem_Icc.mp he).1
  have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos h2
  omega

lemma cnt_bad_G (I : HybInst Fr) (b r m : ℕ) (hb : 2 ≤ b) :
    ((Finset.Icc 1 (Elev I r m)).filter
      (fun e => b ^ e ≤ 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m))).card ≤
      Nat.log 2 (4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m)) := by
  calc _ ≤ (Finset.Icc 1 (Nat.log 2 (4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m)))).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
        have h2 := Finset.mem_Icc.mp he1
        refine Finset.mem_Icc.mpr ⟨h2.1, ?_⟩
        apply Nat.le_log_of_pow_le (by norm_num)
        exact (Nat.pow_le_pow_left hb e).trans he2
    _ ≤ _ := by simp

lemma Bnd_le_G {I : HybInst Fr} (B : BadInfo I) (r m : ℕ) : Bnd I r m ≤ 4 * (r + 2 * m) + 6 := by
  have : I.cd.bad.sup id ≤ 3 := by
    apply Finset.sup_le
    intro b hb
    have := B.bad_sub hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl <;> simp
  unfold Bnd
  rw [B.L4]
  omega

/-- The per-prime bound for the tropical exponent: the bad primes `2` and (optionally) `3`, and the
higher levels, go to the extra terms. -/
theorem tropExp_leG {I : HybInst Fr} (B : BadInfo I) (r p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) :
    (tropExp I r (r / 8) p : ℝ) ≤ (if p = 2 then ex2G r else 0) +
      (if (p ∈ I.cd.bad ∧ p ≠ 2) then ex3G r else 0) +
      ((2 * (r + r / 8) * cntG I r (r / 8) p : ℕ) : ℝ) +
      (if p = 2 ∨ (p ∈ I.cd.bad ∧ p ≠ 2) then 0 else WG I r p) := by
  have hn2 : (0 : ℝ) ≤ ((2 * (r + r / 8) * cntG I r (r / 8) p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE2 : 0 ≤ ex2G r := by unfold ex2G; positivity
  have hE3 : 0 ≤ ex3G r := by unfold ex3G; positivity
  by_cases h2 : p = 2
  · subst h2
    have hb := tropExp_le_bad I r (r / 8) 2
    rw [B.c2] at hb
    simp only [B.Ebd4] at hb
    have hcB := cnt_bad_G I 2 r (r / 8) (le_refl 2)
    have h1 : tropExp I r (r / 8) 2 ≤
        4 * (r + r / 8) + 2 * (r + r / 8) *
          Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) := by
      refine hb.trans ?_
      have := Nat.mul_le_mul_left (2 * (r + r / 8)) hcB
      omega
    have h1' : (tropExp I r (r / 8) 2 : ℝ) ≤
        4 * (r + r / 8 : ℕ) + 2 * (r + r / 8 : ℕ) *
          (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℕ) := by
      exact_mod_cast h1
    have hx : ¬ ((2 : ℕ) ∈ I.cd.bad ∧ (2 : ℕ) ≠ 2) := fun h => h.2 rfl
    rw [if_pos rfl, if_neg hx, if_pos (Or.inl rfl)]
    unfold ex2G
    push_cast at h1' hn2 ⊢
    nlinarith
  by_cases hX : p ∈ I.cd.bad ∧ p ≠ 2
  · have h3 : p = 3 := by
      have := B.bad_sub hX.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    subst h3
    have hb := tropExp_le_bad I r (r / 8) 3
    rw [B.c3] at hb
    simp only [B.Ebd4] at hb
    have hcB := cnt_bad_G I 3 r (r / 8) (by norm_num)
    have h1 : tropExp I r (r / 8) 3 ≤
        2 * (r + r / 8) *
          Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) := by
      refine hb.trans ?_
      have := Nat.mul_le_mul_left (2 * (r + r / 8)) hcB
      omega
    have h1' : (tropExp I r (r / 8) 3 : ℝ) ≤
        2 * (r + r / 8 : ℕ) *
          (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℕ) := by
      exact_mod_cast h1
    rw [if_neg (by norm_num : ¬ ((3 : ℕ) = 2)), if_pos hX, if_pos (Or.inr hX)]
    unfold ex3G
    push_cast at h1' hn2 ⊢
    linarith
  · have hb0 : p ∉ I.cd.bad := fun h => hX ⟨h, h2⟩
    have hb := tropExp_le I r (r / 8) p hr hp hb0
    rw [cOf_eq_zero I hp hb0, zero_mul, zero_add, B.L4] at hb
    rw [if_neg h2, if_neg hX, if_neg (not_or.mpr ⟨h2, hX⟩)]
    have hb' : (tropExp I r (r / 8) p : ℝ) ≤
        ((tropVal (HW I.lev p r (r / 8)) +
          2 * (r + r / 8) * cntG I r (r / 8) p : ℕ) : ℝ) := by
      exact_mod_cast hb
    push_cast at hb' ⊢
    have e : (tropVal (HW I.lev p r (r / 8)) : ℝ) = WG I r p := rfl
    linarith

section Totals

variable {I : HybInst Fr} {o : ℕ}

lemma WG_prefix (T : TropFacts I o) (r p : ℕ) : WG I r p ≤ 9 / 4 * r := by
  have hb := XG_D1 T r p
  have := real_of_int_bound (x := XG I r p) (r := r) (p := p) 4 9 0 0 (by norm_num) (by omega)
  norm_num at this
  show (XG I r p : ℝ) ≤ _
  linarith

lemma eNG_le {o : ℕ} (ho : o = 1 ∨ o = 3) {r p : ℕ} (hr : 16 ≤ r) : 4 * eNG o r p ≤ 9 * r := by
  rcases eNG_cases (o := o) (r := r) (p := p) ho hr with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
      ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
      ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
  · rw [h]; omega
  · rw [e]; rcases ho with rfl | rfl <;> omega
  · rw [e]; rcases ho with rfl | rfl <;> omega
  · rw [e]; unfold kBG; rcases ho with rfl | rfl <;> split_ifs <;> omega
  · rw [e]; rcases ho with rfl | rfl <;> omega
  · rw [e]; rcases ho with rfl | rfl <;> omega
  · rw [e]; omega

lemma eNG_small {o : ℕ} (ho : o = 1 ∨ o = 3) {r p : ℕ} (hr : 16 ≤ r) (hp : p ≤ 3) :
    eNG o r p = 0 := by
  rcases eNG_cases (o := o) (r := r) (p := p) ho hr with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
      ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
      ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
  · exact h
  all_goals first
    | (exfalso; rcases ho with rfl | rfl <;> omega)
    | (exfalso; rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> omega)

lemma eNG_tail {o : ℕ} (ho : o = 1 ∨ o = 3) {r p : ℕ} (hr : 16 ≤ r) (hp : 5 * r / 3 < p) :
    eNG o r p = 0 := by
  rcases eNG_cases (o := o) (r := r) (p := p) ho hr with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
      ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
      ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
  · exact h
  all_goals first
    | (exfalso; rcases ho with rfl | rfl <;> omega)
    | (exfalso; rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> omega)

lemma WTG_prefix (T : TropFacts I o) (r p : ℕ) (hr : 16 ≤ r) : WTG I o r p ≤ 9 / 4 * r := by
  refine max_le (WG_prefix T r p) ?_
  have := eNG_le (o := o) T.ho (r := r) (p := p) hr
  have h : (4 : ℝ) * (eNG o r p : ℝ) ≤ 9 * r := by exact_mod_cast this
  linarith

/-- The extended exponent `TfunG` against the per-prime bound. -/
theorem TfunG_leG (T : TropFacts I o) (B : BadInfo I) (r p : ℕ) (hr : 16 ≤ r) (hp : p.Prime) :
    (TfunG o I r p : ℝ) ≤ (if p = 2 then ex2G r else 0) +
      (if (p ∈ I.cd.bad ∧ p ≠ 2) then ex3G r else 0) +
      ((2 * (r + r / 8) * cntG I r (r / 8) p : ℕ) : ℝ) +
      (if p = 2 ∨ (p ∈ I.cd.bad ∧ p ≠ 2) then 0 else WTG I o r p) := by
  have h := tropExp_leG B r p (by omega) hp
  have hE2 : 0 ≤ ex2G r := by unfold ex2G; positivity
  have hE3 : 0 ≤ ex3G r := by unfold ex3G; positivity
  have hn : (0 : ℝ) ≤ ((2 * (r + r / 8) * cntG I r (r / 8) p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hW : 0 ≤ WTG I o r p := WTG_nonneg _ _ _ _
  have hWG : WG I r p ≤ WTG I o r p := le_max_left _ _
  have heN : (eNG o r p : ℝ) ≤ WTG I o r p := le_max_right _ _
  have hex : 0 ≤ (if p = 2 then ex2G r else 0) := by split_ifs <;> [exact hE2; exact le_rfl]
  have hex3 : 0 ≤ (if (p ∈ I.cd.bad ∧ p ≠ 2) then ex3G r else 0) := by
    split_ifs <;> [exact hE3; exact le_rfl]
  have hT : (TfunG o I r p : ℝ) = max (tropExp I r (r / 8) p : ℝ) (eNG o r p : ℝ) := by
    unfold TfunG; rw [Nat.cast_max]
  rw [hT]
  have hif : (if p = 2 ∨ (p ∈ I.cd.bad ∧ p ≠ 2) then (0 : ℝ) else WG I r p) ≤
      (if p = 2 ∨ (p ∈ I.cd.bad ∧ p ≠ 2) then 0 else WTG I o r p) := by
    by_cases hw : p = 2 ∨ (p ∈ I.cd.bad ∧ p ≠ 2)
    · simp [hw]
    · simp [hw, hWG]
  have hifnn : 0 ≤ (if p = 2 ∨ (p ∈ I.cd.bad ∧ p ≠ 2) then (0 : ℝ) else WTG I o r p) := by
    split_ifs <;> [exact le_rfl; exact hW]
  refine max_le (h.trans (by linarith)) ?_
  by_cases hw : p = 2 ∨ (p ∈ I.cd.bad ∧ p ≠ 2)
  · have hp3 : p ≤ 3 := by
      rcases hw with h2 | ⟨hb, _⟩
      · omega
      · have := B.bad_sub hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        omega
    have h0 : eNG o r p = 0 := eNG_small T.ho hr hp3
    rw [h0, Nat.cast_zero]
    linarith
  · rw [if_neg hw] at hifnn ⊢
    linarith

lemma XG_tail1 (T : TropFacts I o) (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : p % 4 = 4 - o)
    (ht : 5 * r < p) : XG I r p = 0 := by
  rcases T.ho with rfl | rfl
  · have hk := T.kq1 p hp h5 hm
    have := XG_D6 T r p hp h5 (by omega) (by omega)
    omega
  · have hk := T.kq1 p hp h5 hm
    have := XG_D6 T r p hp h5 (by omega) (by omega)
    omega

lemma XG_tail3 (T : TropFacts I o) (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : p % 4 = o)
    (ht : 5 * r / 3 < p) : XG I r p = 0 := by
  have hk := T.kq3 p hp h5 hm
  rcases T.ho with rfl | rfl
  · have := XG_D6 T r p hp h5 (by omega) (by omega)
    omega
  · have := XG_D6 T r p hp h5 (by omega) (by omega)
    omega

lemma isUnit_cJ1 (ho : o = 1 ∨ o = 3) : IsUnit (cJ1 o) := by
  rcases ho with rfl | rfl <;> decide

lemma isUnit_cJ3 (ho : o = 1 ∨ o = 3) : IsUnit (cJ3 o) := by
  rcases ho with rfl | rfl <;> decide

lemma two_ne_cJ1 (ho : o = 1 ∨ o = 3) : (2 : ZMod 4) ≠ cJ1 o := by
  rcases ho with rfl | rfl <;> decide

lemma two_ne_cJ3 (ho : o = 1 ∨ o = 3) : (2 : ZMod 4) ≠ cJ3 o := by
  rcases ho with rfl | rfl <;> decide

theorem class1_totalG (T : TropFacts I o) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (cJ1 o) (WTG I o r) 0 (5 * r) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε) := by
  have h := class_total (M := 4) (isUnit_cJ1 T.ho) (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l3x l3x_chain hε
  filter_upwards [h, eventually_ge_atTop 400] with r hr hr4
  have := hr (WTG I o r) (fun p _ _ _ => WTG_prefix T r p (by omega)) (by
    intro P hP
    unfold l3x at hP
    rcases List.mem_append.mp hP with h | h
    · simp only [ld1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [cwd1_0 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_1 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_2 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_3 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_4 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_5 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_6 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_7 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_8 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_9 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_10 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_11 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_12 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_13 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_14 T _ (two_ne_cJ1 T.ho) r hr4,
        cwd1_15 T _ (two_ne_cJ1 T.ho) r hr4]
    · simp only [l3, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      exacts [cwj1_1 T r hr4, cwj1_2 T r hr4, cwj1_3 T r hr4, cwj1_4 T r hr4, cwj1_5 T r hr4])
  rw [l3x_end, floor_frac] at this
  simpa [tot4] using this

theorem class3_totalG (T : TropFacts I o) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (cJ3 o) (WTG I o r) 0 (5 * r / 3) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε) := by
  have h := class_total (M := 4) (isUnit_cJ3 T.ho) (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l1x l1x_chain hε
  filter_upwards [h, eventually_ge_atTop 400] with r hr hr4
  have := hr (WTG I o r) (fun p _ _ _ => WTG_prefix T r p (by omega)) (by
    intro P hP
    unfold l1x at hP
    rcases List.mem_append.mp hP with h | h
    · simp only [ld1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [cwd1_0 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_1 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_2 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_3 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_4 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_5 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_6 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_7 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_8 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_9 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_10 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_11 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_12 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_13 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_14 T _ (two_ne_cJ3 T.ho) r hr4,
        cwd1_15 T _ (two_ne_cJ3 T.ho) r hr4]
    · simp only [l1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [cwj3_1 T r hr4, cwj3_2 T r hr4, cwj3_3 T r hr4, cwj3_4 T r hr4, cwj3_5 T r hr4,
        cwj3_6 T r hr4])
  rw [l1x_end, floor_frac] at this
  simpa [tot4] using this

/-- **The content bound for the glued deficit family (before the deficit sums).** -/
theorem logDhybT_le_G (T : TropFacts I o) (B : BadInfo I) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT I r (r / 8) (TfunG o I r) δ →
      Real.log (DhybT I r (r / 8) (TfunG o I r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
  have h1 := class1_totalG T (ε := ε / 4) (by positivity)
  have h3 := class3_totalG T (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 6) (by positivity)
  filter_upwards [h1, h3, hx, eventually_ge_atTop 400] with r hr1 hr3 hrx hr0 δ hδ
  have hr16 : 16 ≤ r := by omega
  rw [log_DhybT I r (r / 8) hδ]
  have hsub : (Finset.range (Bnd I r (r / 8))).filter Nat.Prime ⊆
      (Finset.range (4 * (r + 2 * (r / 8)) + 6)).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.range_mono (Bnd_le_G B r (r / 8)))
  have hTsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => (TfunG o I r p : ℝ) * Real.log p) (fun p hp _ =>
      mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)))
  have hbound : ∀ {R1 R3 : ℕ}, 3 ≤ R3 →
      (∀ p, p.Prime → 5 ≤ p → p % 4 = 1 → R1 < p → WTG I o r p = 0) →
      (∀ p, p.Prime → 5 ≤ p → p % 4 = 3 → R3 < p → WTG I o r p = 0) →
      ∑ p ∈ (Finset.range (4 * (r + 2 * (r / 8)) + 6)).filter Nat.Prime,
          (TfunG o I r p : ℝ) * Real.log p ≤
        3 * extraBound r (r / 8) + clsSum 4 (1 : ZMod 4) (WTG I o r) 0 R1 +
          clsSum 4 (3 : ZMod 4) (WTG I o r) 0 R3 := fun {R1 R3} hR3 ht1 ht3 =>
    sum_le_G r (by omega) (TfunG o I r) (WTG I o r) (WTG_nonneg _ _ _) (cntG I r (r / 8))
      (fun p hp => cntG_le I r (r / 8) p hp) (fun p hp h => cntG_zero I r (r / 8) p hp h)
      (fun p => p ∈ I.cd.bad ∧ p ≠ 2)
      (fun p hp => by
        have := B.bad_sub hp.1
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        omega)
      (fun p hp => by have h := TfunG_leG T B r p hr16 hp; convert h) R1 R3 hR3 ht1 ht3
  have hmain : ∑ p ∈ (Finset.range (4 * (r + 2 * (r / 8)) + 6)).filter Nat.Prime,
      (TfunG o I r p : ℝ) * Real.log p ≤ 3 * extraBound r (r / 8) +
        clsSum 4 (cJ1 o) (WTG I o r) 0 (5 * r) + clsSum 4 (cJ3 o) (WTG I o r) 0 (5 * r / 3) := by
    have w1 : ∀ p, p.Prime → 5 ≤ p → p % 4 = 4 - o → 5 * r < p → WTG I o r p = 0 := fun p hp h5 hm ht => by
      have hz := XG_tail1 T r p hp h5 hm ht
      have he := eNG_tail T.ho hr16 (r := r) (p := p) (by omega)
      simp [WTG, WG, hz, he]
    have w3 : ∀ p, p.Prime → 5 ≤ p → p % 4 = o → 5 * r / 3 < p → WTG I o r p = 0 := fun p hp h5 hm ht => by
      have hz := XG_tail3 T r p hp h5 hm ht
      have he := eNG_tail T.ho hr16 (r := r) (p := p) ht
      simp [WTG, WG, hz, he]
    rcases T.ho with rfl | rfl
    · have := hbound (R1 := 5 * r / 3) (R3 := 5 * r) (by omega)
        (fun p hp h5 hm ht => w3 p hp h5 hm ht) (fun p hp h5 hm ht => w1 p hp h5 hm ht)
      have e1 : cJ1 1 = (3 : ZMod 4) := by decide
      have e3 : cJ3 1 = (1 : ZMod 4) := by decide
      rw [e1, e3]; linarith
    · have := hbound (R1 := 5 * r) (R3 := 5 * r / 3) (by omega)
        (fun p hp h5 hm ht => w1 p hp h5 hm ht) (fun p hp h5 hm ht => w3 p hp h5 hm ht)
      have e1 : cJ1 3 = (1 : ZMod 4) := by decide
      have e3 : cJ3 3 = (3 : ZMod 4) := by decide
      rw [e1, e3]; exact this
  have hex := hrx (r / 8) (Nat.div_le_self r 8)
  have hc := const8
  have e : (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε / 4) +
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε / 4) =
      (r : ℝ) ^ 2 * (24994314577 / 6665218560 + ε / 2) := by
    rw [← mul_add]
    congr 1
    linarith
  nlinarith [hmain, hr3, hr1, hex, e, hTsum]

end Totals

end CatalanFrames.HybCommon
