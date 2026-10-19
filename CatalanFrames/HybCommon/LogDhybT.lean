module

public import CatalanFrames.HybCommon.Numer
public import CatalanFrames.HybCommon.TropT
public import CatalanFrames.HybCommon.Pieces

@[expose] public section

/-!
# The content bound `log DhybT ≤ (Λ8 + ε) r² - ∑ δ log p`, generic in the instance

For any block-valued hybrid instance `I` with `TropFacts I o` (offset `o ∈ {1, 3}`, modulus `4`) and
the numerology `BadInfo I Lc cm` (`Numer.lean`; the bad-prime, `L`, `Ebd`, `cOf` layer is generic):
`logDhybT_le_G` for the deficit-valid family `TfunG o I r`.  Both λ (`o = 1`) and the mirror
(`o = 3`) are instances; the piece tables `l3x`, `l1x` are shared and only the residue classes swap.
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- Modulus `4`: with `2` a bad prime, every good prime lies in the classes `{1, 3}`. -/
lemma cls_mod4 {I : HybInst Fr} {Lc cm : ℕ} (B : BadInfo I Lc cm) :
    ∀ p, p.Prime → p ∉ I.cd.bad → (p : ZMod 4) ∈ ({1, 3} : Finset (ZMod 4)) := by
  intro p hp hpb
  have h2 : p ≠ 2 := fun h => hpb (h ▸ B.two_mem)
  rcases prime_class4 hp h2 with ⟨h3', _⟩ | ⟨h1', _⟩
  · simp [h3']
  · simp [h1']

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
theorem TfunG_leG {Lc cm : ℕ} (T : TropFacts I o) (B : BadInfo I Lc cm) (r p : ℕ) (hr : 16 ≤ r)
    (hp : p.Prime) :
    (TfunG o I r p : ℝ) ≤ (if p ∈ I.cd.bad then exBad cm r (r / 8) else 0) +
      ((2 * (r + r / 8) * cntG I r (r / 8) p : ℕ) : ℝ) +
      (if p ∈ I.cd.bad then 0 else WTG I o r p) := by
  have h := tropExp_leG B r (r / 8) p (by omega) hp
  have hE : 0 ≤ exBad cm r (r / 8) := by unfold exBad; positivity
  have hn : (0 : ℝ) ≤ ((2 * (r + r / 8) * cntG I r (r / 8) p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hWG : WG I r p ≤ WTG I o r p := le_max_left _ _
  have heN : (eNG o r p : ℝ) ≤ WTG I o r p := le_max_right _ _
  have hT : (TfunG o I r p : ℝ) = max (tropExp I r (r / 8) p : ℝ) (eNG o r p : ℝ) := by
    unfold TfunG; rw [Nat.cast_max]
  rw [hT]
  by_cases hb : p ∈ I.cd.bad
  · have h0 : eNG o r p = 0 := eNG_small T.ho hr (B.bad_le p hb)
    rw [h0, Nat.cast_zero]
    simp only [hb, if_true] at h ⊢
    exact max_le h (by linarith)
  · simp only [hb, if_false] at h ⊢
    have e : (tropVal (HW I.lev p r (r / 8)) : ℝ) = WG I r p := rfl
    exact max_le (by linarith) (by linarith)

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
theorem logDhybT_le_G {Lc cm : ℕ} (T : TropFacts I o) (B : BadInfo I Lc cm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT I r (r / 8) (TfunG o I r) δ →
      Real.log (DhybT I r (r / 8) (TfunG o I r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
  have h1 := class1_totalG T (ε := ε / 4) (by positivity)
  have h3 := class3_totalG T (ε := ε / 4) (by positivity)
  have hx := B.extra_small (ε / 2) (by positivity)
  filter_upwards [h1, h3, hx, eventually_ge_atTop 400] with r hr1 hr3 hrx hr0 δ hδ
  have hr16 : 16 ≤ r := by omega
  rw [log_DhybT I r (r / 8) hδ]
  have hne : cJ1 o ≠ cJ3 o := by rcases T.ho with rfl | rfl <;> decide
  have w1 : ∀ p, p.Prime → 5 ≤ p → p % 4 = 4 - o → 5 * r < p → WTG I o r p = 0 := fun p hp h5 hm ht => by
    have hz := XG_tail1 T r p hp h5 hm ht
    have he := eNG_tail T.ho hr16 (r := r) (p := p) (by omega)
    simp [WTG, WG, hz, he]
  have w3 : ∀ p, p.Prime → 5 ≤ p → p % 4 = o → 5 * r / 3 < p → WTG I o r p = 0 := fun p hp h5 hm ht => by
    have hz := XG_tail3 T r p hp h5 hm ht
    have he := eNG_tail T.ho hr16 (r := r) (p := p) ht
    simp [WTG, WG, hz, he]
  have hsumT := sum_Bnd_le_gen B ({cJ1 o, cJ3 o} : Finset (ZMod 4))
    (fun c => if c = cJ1 o then 5 * r else 5 * r / 3) r (r / 8) (TfunG o I r) (WTG I o r)
    (WTG_nonneg _ _ _) (cntG I r (r / 8))
    (fun p hp => (cntG_le I r (r / 8) p hp).trans (by rw [B.L_eq]))
    (fun p hp h => cntG_zero I r (r / 8) p hp (by rw [B.L_eq]; exact h))
    (fun p hp => TfunG_leG T B r p hr16 hp)
    (fun p hp hpb => by
      have h2 : p ≠ 2 := fun h => hpb (h ▸ B.two_mem)
      rcases prime_class4 hp h2 with ⟨h3', _⟩ | ⟨h1', _⟩
      · rcases T.ho with rfl | rfl
        · simp [cJ1, cJ3, h3']
        · simp [cJ1, cJ3, h3']
      · rcases T.ho with rfl | rfl
        · simp [cJ1, cJ3, h1']
        · simp [cJ1, cJ3, h1'])
    (fun c hc b hb hbc => by
      have hb3 := B.bad_le b hb
      have hb2 := (I.cd.bad_prime b hb).two_le
      have hcc : c = cJ1 o ∨ c = cJ3 o := by simpa using hc
      have hb23 : b = 2 ∨ b = 3 := by omega
      rcases hb23 with rfl | rfl
      · exfalso
        rcases hcc with rfl | rfl
        · exact two_ne_cJ1 T.ho (by simpa using hbc)
        · exact two_ne_cJ3 T.ho (by simpa using hbc)
      · show 3 ≤ (if c = cJ1 o then 5 * r else 5 * r / 3)
        split_ifs <;> omega)
    (fun c hc p hp hpb hpc hlt => by
      have hcc : c = cJ1 o ∨ c = cJ3 o := by simpa using hc
      have hRc : 3 ≤ (if c = cJ1 o then 5 * r else 5 * r / 3) := by
        split_ifs <;> omega
      have h5 : 5 ≤ p := by
        have := hp.two_le
        have h4 : p ≠ 4 := fun h => by norm_num [h] at hp
        omega
      rcases hcc with rfl | rfl
      · rw [if_pos rfl] at hlt
        exact w1 p hp h5 (mod_j1 T hpc) hlt
      · rw [if_neg (Ne.symm hne)] at hlt
        exact w3 p hp h5 (mod_j3 T hpc) hlt)
  have hmain : ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
      (TfunG o I r p : ℝ) * Real.log p ≤ extraG Lc Ecub cm (badLog I) r (r / 8) +
        clsSum 4 (cJ1 o) (WTG I o r) 0 (5 * r) + clsSum 4 (cJ3 o) (WTG I o r) 0 (5 * r / 3) := by
    rw [Finset.sum_pair hne, if_pos rfl, if_neg (Ne.symm hne)] at hsumT
    linarith
  have hex := hrx (r / 8) (Nat.div_le_self r 8)
  have hc := const8
  have e : (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε / 4) +
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε / 4) =
      (r : ℝ) ^ 2 * (24994314577 / 6665218560 + ε / 2) := by
    rw [← mul_add]
    congr 1
    linarith
  nlinarith [hmain, hr3, hr1, hex, e]

end Totals

end CatalanFrames.HybCommon
