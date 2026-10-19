module

public import CatalanCore.Rect.PairFam
public import CatalanCore.Decay.Rect.DecayRect
public import CatalanCore.Arith.Hybrid.DefRank

@[expose] public section

/-!
# Content and decay of the two-member hybrid family from member-1 data (LAMASM)

The content and decay machinery of the repository is for the members `Frame.fullPoly r m`
(= `det Full(after r m)`).  The NV theorem needs, besides `after r m`, DO's second member
`afterTop r m` (one more common node `r + 2m`; degree `r + 1`).  Its content and decay are the
analytic inputs (C_hyb), (D_hyb) of DZ-audit item 4 for the second geometry and are NOT proved in
this repository: they are the hypotheses `Mem2Content` and `Mem2Decay`.

* `exists_diag` : a diagonal argument turning "for each `ε`, eventually a witness" into one
  `ε`-independent witness sequence (a single denominator `Dden` is needed by `HasContent`).
* `hasContent_hybPair` : member-1 content (an `ε`-independent deficit family `(T, δ)` with
  `log DhybT ≤ (Λ + ε) r²`) plus `Mem2Content Fr Λ` gives `HasContent (hybPairFam Fr 8) Λ`.
* `hasDecay_hybPair` : `HasDecay (hybridFamUp Fr (1/8)) D C` plus `Mem2Decay Fr D C` gives
  `HasDecay (hybPairFam Fr 8) D C`.
-/

open Filter Polynomial Finset Matrix CatalanCore.Arith.Hybrid

namespace CatalanCore.Rect

/-! ### A diagonal argument -/

theorem exists_diag {β : Type} [Nonempty β] (P : ℝ → ℕ → β → Prop)
    (hmono : ∀ ε ε' r b, ε ≤ ε' → P ε r b → P ε' r b)
    (h : ∀ ε > 0, ∀ᶠ r in atTop, ∃ b, P ε r b) :
    ∃ f : ℕ → β, ∀ ε > 0, ∀ᶠ r in atTop, P ε r (f r) := by
  classical
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ r, N ≤ r → ∃ b, P (1 / ((k : ℝ) + 1)) r b := fun k =>
    eventually_atTop.1 (h _ (by positivity))
  choose N hN using hN
  set M : ℕ → ℕ := fun k => max (N k) k with hM
  set kr : ℕ → ℕ := fun r => Nat.findGreatest (fun k => M k ≤ r) r with hkr
  refine ⟨fun r => if hh : ∃ b, P (1 / ((kr r : ℝ) + 1)) r b then hh.choose
    else Classical.choice ‹Nonempty β›, fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  rw [eventually_atTop]
  refine ⟨M K, fun r hr => ?_⟩
  have hKr : K ≤ r := (le_max_right _ _).trans hr
  have hk1 : K ≤ kr r := Nat.le_findGreatest hKr hr
  have hk2 : M (kr r) ≤ r := Nat.findGreatest_spec (P := fun k => M k ≤ r) hKr hr
  have hex : ∃ b, P (1 / ((kr r : ℝ) + 1)) r b := hN (kr r) r ((le_max_left _ _).trans hk2)
  simp only [dif_pos hex]
  refine hmono _ _ _ _ ?_ hex.choose_spec
  have hk1' : (K : ℝ) ≤ kr r := by exact_mod_cast hk1
  have : 1 / ((kr r : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-! ### Clearing denominators of a polynomial of bounded degree -/

theorem int_clear (P : ℚ[X]) (r : ℕ) (hP : P.natDegree ≤ r) (D : ℕ)
    (hD : ∀ i, ∃ z : ℤ, (D : ℚ) * P.coeff i = z) (p q : ℤ) (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ) ^ r * D * P.eval ((p : ℚ) / q) = z := by
  choose z hz using hD
  refine ⟨∑ i ∈ range (r + 1), z i * p ^ i * q ^ (r - i), ?_⟩
  rw [Polynomial.eval_eq_sum_range' (n := r + 1) (by omega), Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ r := by have := Finset.mem_range.1 hi; omega
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : (q : ℚ) ^ r = q ^ (r - i) * q ^ i := by rw [← pow_add]; congr 1; omega
  rw [← hz i, e, div_pow]
  field_simp

/-! ### Content -/

section Content

variable {Fr : Frame}

theorem natDegree_after_le (r m : ℕ) : ((after r m).fullPolyG Fr).natDegree ≤ r := by
  have := Geometry.natDegree_fullPolyG_le Fr (after r m)
  rwa [after_card_C] at this

theorem natDegree_afterTop_le (r m : ℕ) : ((afterTop r m).fullPolyG Fr).natDegree ≤ r + 1 := by
  have := Geometry.natDegree_fullPolyG_le Fr (afterTop r m)
  rwa [afterTop_card_C] at this

/-- Content of the second member (hypothesis; see the module doc). -/
def Mem2Content (Fr : Frame) (Λ : ℝ) : Prop :=
  ∃ D2 : ℕ → ℕ, (∀ r, 0 < D2 r) ∧
    (∀ r, 8 ∣ r → ∀ i, ∃ z : ℤ, (D2 r : ℚ) * ((afterTop r (r / 8)).fullPolyG Fr).coeff i = z) ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ r, 8 ∣ r → N₀ ≤ r → Real.log (D2 r) ≤ (Λ + ε) * (r : ℝ) ^ 2)

open Classical in
/-- The denominators of the pair family: member 1 uses the deficit denominator when its
hypothesis holds (always for large `r`), else the plain `Dhyb`. -/
noncomputable def pairDden (I : HybInst Fr) (T δ : ℕ → ℕ → ℕ) (D2 : ℕ → ℕ) :
    ℕ × Bool → ℕ
  | (r, false) => if DefHypT I r (r / 8) (T r) (δ r) then DhybT I r (r / 8) (T r) (δ r)
      else Dhyb I r (r / 8)
  | (r, true) => D2 r

theorem hasContent_hybPair (I : HybInst Fr) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (T δ : ℕ → ℕ → ℕ)
    (hdef : ∀ᶠ r in atTop, DefHypT I r (r / 8) (T r) (δ r))
    (hlog : ∀ ε > 0, ∀ᶠ r in atTop,
      Real.log (DhybT I r (r / 8) (T r) (δ r)) ≤ (Λ + ε) * (r : ℝ) ^ 2)
    (M2 : Mem2Content Fr Λ) : HasContent (hybPairFam Fr 8) Λ := by
  classical
  obtain ⟨D2, hD2pos, hD2int, hD2log⟩ := M2
  refine ⟨pairDden I T δ D2, ?_, ?_, ?_⟩
  · rintro ⟨r, b⟩
    cases b
    · simp only [pairDden]
      split_ifs
      · exact Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _
      · exact Dhyb_pos I r (r / 8)
    · exact hD2pos r
  · rintro ⟨r, b⟩ h8 p q hq
    cases b
    · have hdeg : (hybPairFam Fr 8).deg (r, false) = r := rfl
      have hQ : (hybPairFam Fr 8).evalQ (r, false) ((p : ℚ) / q) =
          (Fr.fullPoly r (r / 8)).eval ((p : ℚ) / q) := by
        simp [PolyFamily.evalQ, hybPairFam_Q_false]
      have hint : ∀ i, ∃ z : ℤ, (pairDden I T δ D2 (r, false) : ℚ) *
          (Fr.fullPoly r (r / 8)).coeff i = z := by
        intro i
        simp only [pairDden]
        split_ifs with h
        · exact DhybT_integral I r (r / 8) h i
        · exact Dhyb_integral I r (r / 8) i
      rw [hdeg, hQ]
      exact int_clear _ r (by simpa [det_full_after] using natDegree_after_le (Fr := Fr) r (r / 8))
        _ hint p q hq
    · have hdeg : (hybPairFam Fr 8).deg (r, true) = r + 1 := rfl
      have hQ : (hybPairFam Fr 8).evalQ (r, true) ((p : ℚ) / q) =
          ((afterTop r (r / 8)).fullPolyG Fr).eval ((p : ℚ) / q) := by
        simp [PolyFamily.evalQ, hybPairFam]
      rw [hdeg, hQ]
      exact int_clear _ (r + 1) (natDegree_afterTop_le r (r / 8)) (D2 r) (hD2int r h8) p q hq
  · intro ε hε
    obtain ⟨R1, hR1⟩ := eventually_atTop.1 hdef
    obtain ⟨R2, hR2⟩ := eventually_atTop.1 (hlog ε hε)
    obtain ⟨R3, hR3⟩ := hD2log ε hε
    refine ⟨max (max R1 R2) R3 + 1, ?_⟩
    rintro ⟨r, b⟩ h8 hr
    cases b
    · have hr' : max (max R1 R2) R3 + 1 ≤ r := hr
      have hd : DefHypT I r (r / 8) (T r) (δ r) := hR1 r (by omega)
      have e : pairDden I T δ D2 (r, false) = DhybT I r (r / 8) (T r) (δ r) := by
        simp only [pairDden]; exact if_pos hd
      rw [e]
      exact hR2 r (by omega)
    · have hr' : max (max R1 R2) R3 + 1 ≤ r + 1 := hr
      have h1 := hR3 r h8 (by omega)
      show Real.log (D2 r) ≤ (Λ + ε) * (((r + 1 : ℕ) : ℝ)) ^ 2
      push_cast
      have : (0 : ℝ) ≤ Λ + ε := by linarith
      nlinarith [sq_nonneg (r : ℝ), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

/-- An `ε`-independent deficit family from "for each `ε`, eventually some deficit family". -/
theorem contentFam_of_eps (I : HybInst Fr) (Λ : ℝ)
    (h : ∀ ε > 0, ∀ᶠ r in atTop, ∃ T δ : ℕ → ℕ, DefHypT I r (r / 8) T δ ∧
      Real.log (DhybT I r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    ∃ T δ : ℕ → ℕ → ℕ, (∀ᶠ r in atTop, DefHypT I r (r / 8) (T r) (δ r)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        Real.log (DhybT I r (r / 8) (T r) (δ r)) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  haveI : Nonempty ((ℕ → ℕ) × (ℕ → ℕ)) := ⟨(fun _ => 0, fun _ => 0)⟩
  obtain ⟨f, hf⟩ := exists_diag (β := (ℕ → ℕ) × (ℕ → ℕ))
    (fun ε r b => DefHypT I r (r / 8) b.1 b.2 ∧
      Real.log (DhybT I r (r / 8) b.1 b.2) ≤ (Λ + ε) * (r : ℝ) ^ 2)
    (fun ε ε' r b hε hb => ⟨hb.1, hb.2.trans (by nlinarith [sq_nonneg (r : ℝ)])⟩)
    (fun ε hε => (h ε hε).mono fun r ⟨T, δ, h1, h2⟩ => ⟨(T, δ), h1, h2⟩)
  refine ⟨fun r => (f r).1, fun r => (f r).2, ?_, fun ε hε => (hf ε hε).mono fun r hr => hr.2⟩
  exact (hf 1 one_pos).mono fun r hr => hr.1

end Content

/-! ### Decay -/

section Decay

variable {Fr : Frame}

/-- Decay of the second member (hypothesis; see the module doc): window `exp(-C r)`, bound
`exp(-(D - δ) r²)`. -/
def Mem2Decay (Fr : Frame) (D C : ℝ) : Prop :=
  ∀ δ > 0, ∃ N₀ : ℕ, ∀ r, 8 ∣ r → N₀ ≤ r → ∀ t : ℝ, |t| ≤ Real.exp (-C * (r : ℝ)) →
    |((afterTop r (r / 8)).fullPolyG Fr).aeval (Fr.const + t)| ≤
      Real.exp (-(D - δ) * (r : ℝ) ^ 2)

theorem hybridFamUp_adm (r : ℕ) (h8 : 8 ∣ r) :
    (hybridFamUp Fr (1 / 8)).Adm (r, r / 8) := by
  obtain ⟨k, rfl⟩ := h8
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 8)]
  show (1 / 8 : ℚ) * ((8 * k : ℕ) : ℚ) ≤ (k : ℚ) ∧ (k : ℚ) ≤ 1 / 8 * ((8 * k : ℕ) : ℚ) + 1
  push_cast
  constructor <;> linarith

theorem hasDecay_hybPair {D C : ℝ} (hC : 0 ≤ C) (hD1 : HasDecay (hybridFamUp Fr (1 / 8)) D C)
    (M2 : Mem2Decay Fr D C) : HasDecay (hybPairFam Fr 8) D C := by
  intro δ hδ
  obtain ⟨N1, H1⟩ := hD1 δ hδ
  obtain ⟨N2, H2⟩ := M2 (δ / 2) (half_pos hδ)
  refine ⟨max (max N1 N2) (⌈6 * |D - δ| / δ⌉₊ + 1) + 1, ?_⟩
  rintro ⟨r, b⟩ h8 hr t ht
  cases b
  · have hr' : max (max N1 N2) (⌈6 * |D - δ| / δ⌉₊ + 1) + 1 ≤ r := hr
    have key := H1 (r, r / 8) (hybridFamUp_adm r h8) (by
      show N1 ≤ r
      omega) t (by exact ht)
    have e1 : ∀ x : ℝ, (hybPairFam Fr 8).evalR (r, false) x =
        (hybridFamUp Fr (1 / 8)).evalR (r, r / 8) x := by
      intro x
      simp [PolyFamily.evalR, hybPairFam_Q_false, hybridFamUp, hybridFam_Q]
    rw [e1]
    exact key
  · have hr' : max (max N1 N2) (⌈6 * |D - δ| / δ⌉₊ + 1) + 1 ≤ r + 1 := hr
    have hrr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hwin : |t| ≤ Real.exp (-C * (r : ℝ)) := by
      refine ht.trans (Real.exp_le_exp.2 ?_)
      show -C * (((r + 1 : ℕ)) : ℝ) ≤ -C * r
      push_cast
      nlinarith
    have key := H2 r h8 (by omega) t hwin
    have hbig : 6 * |D - δ| / δ ≤ r := by
      have : (⌈6 * |D - δ| / δ⌉₊ : ℝ) ≤ r := by exact_mod_cast (by omega : ⌈6 * |D - δ| / δ⌉₊ ≤ r)
      exact (Nat.le_ceil _).trans this
    rw [div_le_iff₀ hδ] at hbig
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    have hA : (D - δ) ≤ |D - δ| := le_abs_self _
    have hcmp : (D - δ) * ((r : ℝ) + 1) ^ 2 ≤ (D - δ / 2) * (r : ℝ) ^ 2 := by
      nlinarith [abs_nonneg (D - δ), sq_nonneg (r : ℝ), mul_nonneg (abs_nonneg (D - δ)) hrr]
    have hfin : |((afterTop r (r / 8)).fullPolyG Fr).aeval (Fr.const + t)| ≤
        Real.exp (-(D - δ) * (((r + 1 : ℕ)) : ℝ) ^ 2) := by
      refine key.trans (Real.exp_le_exp.2 ?_)
      push_cast
      nlinarith [hcmp]
    simpa [PolyFamily.evalR, hybPairFam] using hfin

end Decay

end CatalanCore.Rect
