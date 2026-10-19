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

/-- Content of the second member for the admissible relation `A` (hypothesis; see the module
doc): one denominator `D2 r m` per member. -/
def Mem2ContentA (Fr : Frame) (A : ℕ → ℕ → Prop) (Λ : ℝ) : Prop :=
  ∃ D2 : ℕ → ℕ → ℕ, (∀ r m, 0 < D2 r m) ∧
    (∀ r m, A r m → ∀ i, ∃ z : ℤ,
      (D2 r m : ℚ) * ((afterTop r m).fullPolyG Fr).coeff i = z) ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ r m, A r m → N₀ ≤ r →
      Real.log (D2 r m) ≤ (Λ + ε) * (r : ℝ) ^ 2)

/-- Content of the second member, slope `1/8` (the λ, λ′ form; `Mem2ContentA` for `admDiv 8`). -/
def Mem2Content (Fr : Frame) (Λ : ℝ) : Prop :=
  ∃ D2 : ℕ → ℕ, (∀ r, 0 < D2 r) ∧
    (∀ r, 8 ∣ r → ∀ i, ∃ z : ℤ, (D2 r : ℚ) * ((afterTop r (r / 8)).fullPolyG Fr).coeff i = z) ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ r, 8 ∣ r → N₀ ≤ r → Real.log (D2 r) ≤ (Λ + ε) * (r : ℝ) ^ 2)

theorem Mem2Content.toA {Λ : ℝ} (h : Mem2Content Fr Λ) : Mem2ContentA Fr (admDiv 8) Λ := by
  obtain ⟨D2, h1, h2, h3⟩ := h
  refine ⟨fun r _ => D2 r, fun r _ => h1 r, ?_, ?_⟩
  · rintro r m ⟨h8, rfl⟩ i
    exact h2 r h8 i
  · intro ε hε
    obtain ⟨N₀, H⟩ := h3 ε hε
    exact ⟨N₀, fun r m ⟨h8, _⟩ hr => H r h8 hr⟩

open Classical in
/-- The denominators of the pair family, for an instance family `I r m`: member 1 uses the deficit denominator when its
hypothesis holds (always for large `r`), else the plain `Dhyb`. -/
noncomputable def pairDdenF (I : ℕ → ℕ → HybInst Fr) (T δ : ℕ → ℕ → ℕ → ℕ) (D2 : ℕ → ℕ → ℕ) :
    (ℕ × ℕ) × Bool → ℕ
  | ((r, m), false) => if DefHypT (I r m) r m (T r m) (δ r m) then DhybT (I r m) r m (T r m) (δ r m)
      else Dhyb (I r m) r m
  | ((r, m), true) => D2 r m

/-- **Content of the pair family for an admissible relation** (G3): member-1 deficit families
`(T r m, δ r m)` on `A` plus the second-member content. -/
theorem hasContent_hybPairF {A : ℕ → ℕ → Prop} (I : ℕ → ℕ → HybInst Fr) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (T δ : ℕ → ℕ → ℕ → ℕ)
    (hdef : ∀ᶠ r in atTop, ∀ m, A r m → DefHypT (I r m) r m (T r m) (δ r m))
    (hlog : ∀ ε > 0, ∀ᶠ r in atTop, ∀ m, A r m →
      Real.log (DhybT (I r m) r m (T r m) (δ r m)) ≤ (Λ + ε) * (r : ℝ) ^ 2)
    (M2 : Mem2ContentA Fr A Λ)
    [∀ r m, (I r m).DiagOK r m] : HasContent (hybPairFamA Fr A) Λ := by
  classical
  obtain ⟨D2, hD2pos, hD2int, hD2log⟩ := M2
  refine ⟨pairDdenF I T δ D2, ?_, ?_, ?_⟩
  · rintro ⟨⟨r, m⟩, b⟩
    cases b
    · simp only [pairDdenF]
      split_ifs
      · exact Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _
      · exact Dhyb_pos (I r m) r m
    · exact hD2pos r m
  · rintro ⟨⟨r, m⟩, b⟩ hA p q hq
    cases b
    · have hdeg : (hybPairFamA Fr A).deg ((r, m), false) = r := rfl
      have hQ : (hybPairFamA Fr A).evalQ ((r, m), false) ((p : ℚ) / q) =
          (Fr.fullPoly r m).eval ((p : ℚ) / q) := by
        simp [PolyFamily.evalQ, hybPairFamA_Q_false]
      have hint : ∀ i, ∃ z : ℤ, (pairDdenF I T δ D2 ((r, m), false) : ℚ) *
          (Fr.fullPoly r m).coeff i = z := by
        intro i
        simp only [pairDdenF]
        split_ifs with h
        · exact DhybT_integral (I r m) r m h i
        · exact Dhyb_integral (I r m) r m i
      rw [hdeg, hQ]
      exact int_clear _ r (by simpa [det_full_after] using natDegree_after_le (Fr := Fr) r m)
        _ hint p q hq
    · have hdeg : (hybPairFamA Fr A).deg ((r, m), true) = r + 1 := rfl
      have hQ : (hybPairFamA Fr A).evalQ ((r, m), true) ((p : ℚ) / q) =
          ((afterTop r m).fullPolyG Fr).eval ((p : ℚ) / q) := by
        simp [PolyFamily.evalQ, hybPairFamA]
      rw [hdeg, hQ]
      exact int_clear _ (r + 1) (natDegree_afterTop_le r m) (D2 r m) (hD2int r m hA) p q hq
  · intro ε hε
    obtain ⟨R1, hR1⟩ := eventually_atTop.1 hdef
    obtain ⟨R2, hR2⟩ := eventually_atTop.1 (hlog ε hε)
    obtain ⟨R3, hR3⟩ := hD2log ε hε
    refine ⟨max (max R1 R2) R3 + 1, ?_⟩
    rintro ⟨⟨r, m⟩, b⟩ hA hr
    cases b
    · have hr' : max (max R1 R2) R3 + 1 ≤ r := hr
      have hd : DefHypT (I r m) r m (T r m) (δ r m) := hR1 r (by omega) m hA
      have e : pairDdenF I T δ D2 ((r, m), false) = DhybT (I r m) r m (T r m) (δ r m) := by
        simp only [pairDdenF]; exact if_pos hd
      rw [e]
      exact hR2 r (by omega) m hA
    · have hr' : max (max R1 R2) R3 + 1 ≤ r + 1 := hr
      have h1 := hR3 r m hA (by omega)
      show Real.log (D2 r m) ≤ (Λ + ε) * (((r + 1 : ℕ) : ℝ)) ^ 2
      push_cast
      have : (0 : ℝ) ≤ Λ + ε := by linarith
      nlinarith [sq_nonneg (r : ℝ), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

/-- Fixed-instance form of `pairDdenF`. -/
noncomputable abbrev pairDdenA (I : HybInst Fr) (T δ : ℕ → ℕ → ℕ → ℕ) (D2 : ℕ → ℕ → ℕ) :
    (ℕ × ℕ) × Bool → ℕ := pairDdenF (fun _ _ => I) T δ D2

/-- Fixed-instance form of `hasContent_hybPairF`. -/
theorem hasContent_hybPairA {A : ℕ → ℕ → Prop} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (T δ : ℕ → ℕ → ℕ → ℕ)
    (hdef : ∀ᶠ r in atTop, ∀ m, A r m → DefHypT I r m (T r m) (δ r m))
    (hlog : ∀ ε > 0, ∀ᶠ r in atTop, ∀ m, A r m →
      Real.log (DhybT I r m (T r m) (δ r m)) ≤ (Λ + ε) * (r : ℝ) ^ 2)
    (M2 : Mem2ContentA Fr A Λ) : HasContent (hybPairFamA Fr A) Λ :=
  hasContent_hybPairF (fun _ _ => I) hΛ0 T δ hdef hlog M2

/-- An `ε`-independent deficit family from "for each `ε`, eventually some deficit family", on an
admissible relation `A` (G3). -/
theorem contentFamF_of_eps (I : ℕ → ℕ → HybInst Fr) (Λ : ℝ) (A : ℕ → ℕ → Prop)
    (h : ∀ ε > 0, ∀ᶠ r in atTop, ∀ m, A r m → ∃ T δ : ℕ → ℕ, DefHypT (I r m) r m T δ ∧
      Real.log (DhybT (I r m) r m T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    ∃ T δ : ℕ → ℕ → ℕ → ℕ, (∀ᶠ r in atTop, ∀ m, A r m → DefHypT (I r m) r m (T r m) (δ r m)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop, ∀ m, A r m →
        Real.log (DhybT (I r m) r m (T r m) (δ r m)) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  classical
  haveI : Nonempty (ℕ → (ℕ → ℕ) × (ℕ → ℕ)) := ⟨fun _ => (fun _ => 0, fun _ => 0)⟩
  obtain ⟨f, hf⟩ := exists_diag (β := ℕ → (ℕ → ℕ) × (ℕ → ℕ))
    (fun ε r b => ∀ m, A r m → DefHypT (I r m) r m (b m).1 (b m).2 ∧
      Real.log (DhybT (I r m) r m (b m).1 (b m).2) ≤ (Λ + ε) * (r : ℝ) ^ 2)
    (fun ε ε' r b hε hb m hA =>
      ⟨(hb m hA).1, (hb m hA).2.trans (by nlinarith [sq_nonneg (r : ℝ)])⟩)
    (fun ε hε => (h ε hε).mono fun r hr => by
      have : ∀ m, ∃ b : (ℕ → ℕ) × (ℕ → ℕ), A r m → DefHypT (I r m) r m b.1 b.2 ∧
          Real.log (DhybT (I r m) r m b.1 b.2) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
        intro m
        by_cases hA : A r m
        · obtain ⟨T, δ, h1, h2⟩ := hr m hA
          exact ⟨(T, δ), fun _ => ⟨h1, h2⟩⟩
        · exact ⟨(fun _ => 0, fun _ => 0), fun h => absurd h hA⟩
      choose b hb using this
      exact ⟨b, hb⟩)
  refine ⟨fun r m => (f r m).1, fun r m => (f r m).2, ?_,
    fun ε hε => (hf ε hε).mono fun r hr m hA => (hr m hA).2⟩
  exact (hf 1 one_pos).mono fun r hr m hA => (hr m hA).1

/-- Fixed-instance form of `contentFamF_of_eps`. -/
theorem contentFamA_of_eps (I : HybInst Fr) (Λ : ℝ) (A : ℕ → ℕ → Prop)
    (h : ∀ ε > 0, ∀ᶠ r in atTop, ∀ m, A r m → ∃ T δ : ℕ → ℕ, DefHypT I r m T δ ∧
      Real.log (DhybT I r m T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    ∃ T δ : ℕ → ℕ → ℕ → ℕ, (∀ᶠ r in atTop, ∀ m, A r m → DefHypT I r m (T r m) (δ r m)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop, ∀ m, A r m →
        Real.log (DhybT I r m (T r m) (δ r m)) ≤ (Λ + ε) * (r : ℝ) ^ 2 :=
  contentFamF_of_eps (fun _ _ => I) Λ A h

/-- The slope-`1/8` form (`m = r / 8`) of `contentFamA_of_eps`. -/
theorem contentFam_of_eps (I : HybInst Fr) (Λ : ℝ)
    (h : ∀ ε > 0, ∀ᶠ r in atTop, ∃ T δ : ℕ → ℕ, DefHypT I r (r / 8) T δ ∧
      Real.log (DhybT I r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    ∃ T δ : ℕ → ℕ → ℕ, (∀ᶠ r in atTop, DefHypT I r (r / 8) (T r) (δ r)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        Real.log (DhybT I r (r / 8) (T r) (δ r)) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  obtain ⟨T, δ, h1, h2⟩ := contentFamA_of_eps I Λ (fun r m => m = r / 8)
    (fun ε hε => (h ε hε).mono fun r ⟨T, δ, a, b⟩ m hm => ⟨T, δ, by subst hm; exact a,
      by subst hm; exact b⟩)
  exact ⟨fun r => T r (r / 8), fun r => δ r (r / 8), h1.mono fun r hr => hr _ rfl,
    fun ε hε => (h2 ε hε).mono fun r hr => hr _ rfl⟩

/-- The slope-`1/8` form of `hasContent_hybPairA`. -/
theorem hasContent_hybPair (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (T δ : ℕ → ℕ → ℕ)
    (hdef : ∀ᶠ r in atTop, DefHypT I r (r / 8) (T r) (δ r))
    (hlog : ∀ ε > 0, ∀ᶠ r in atTop,
      Real.log (DhybT I r (r / 8) (T r) (δ r)) ≤ (Λ + ε) * (r : ℝ) ^ 2)
    (M2 : Mem2Content Fr Λ) : HasContent (hybPairFam Fr 8) Λ :=
  hasContent_hybPairA I hΛ0 (fun r _ => T r) (fun r _ => δ r)
    (hdef.mono fun r h m ⟨_, hm⟩ => by subst hm; exact h)
    (fun ε hε => (hlog ε hε).mono fun r h m ⟨_, hm⟩ => by subst hm; exact h) M2.toA

end Content

/-! ### Decay -/

section Decay

variable {Fr : Frame}

/-- Decay of the first member on the relation `A`: window `exp(-C r)`, bound
`exp(-(D - δ) r²)`. -/
def Mem1DecayA (Fr : Frame) (A : ℕ → ℕ → Prop) (D C : ℝ) : Prop :=
  ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m, A r m → N₀ ≤ r → ∀ t : ℝ, |t| ≤ Real.exp (-C * (r : ℝ)) →
    |(Fr.fullPoly r m).aeval (Fr.const + t)| ≤ Real.exp (-(D - δ) * (r : ℝ) ^ 2)

/-- Decay of the second member on the relation `A` (hypothesis; see the module doc). -/
def Mem2DecayA (Fr : Frame) (A : ℕ → ℕ → Prop) (D C : ℝ) : Prop :=
  ∀ δ > 0, ∃ N₀ : ℕ, ∀ r m, A r m → N₀ ≤ r → ∀ t : ℝ, |t| ≤ Real.exp (-C * (r : ℝ)) →
    |((afterTop r m).fullPolyG Fr).aeval (Fr.const + t)| ≤
      Real.exp (-(D - δ) * (r : ℝ) ^ 2)

/-- Decay of the second member, slope `1/8` (`Mem2DecayA` for `admDiv 8`). -/
def Mem2Decay (Fr : Frame) (D C : ℝ) : Prop :=
  ∀ δ > 0, ∃ N₀ : ℕ, ∀ r, 8 ∣ r → N₀ ≤ r → ∀ t : ℝ, |t| ≤ Real.exp (-C * (r : ℝ)) →
    |((afterTop r (r / 8)).fullPolyG Fr).aeval (Fr.const + t)| ≤
      Real.exp (-(D - δ) * (r : ℝ) ^ 2)

theorem Mem2Decay.toA {D C : ℝ} (h : Mem2Decay Fr D C) : Mem2DecayA Fr (admDiv 8) D C := by
  intro δ hδ
  obtain ⟨N, H⟩ := h δ hδ
  exact ⟨N, fun r m ⟨h8, hm⟩ hr t ht => by subst hm; exact H r h8 hr t ht⟩

/-- Member-1 decay on `A` from the decay of a `hybridFamUp` family whose window contains `A`. -/
theorem Mem1DecayA.of_up {A : ℕ → ℕ → Prop} {α : ℚ}
    (hA : ∀ r m, A r m → (hybridFamUp Fr α).Adm (r, m)) {D C : ℝ}
    (h : HasDecay (hybridFamUp Fr α) D C) : Mem1DecayA Fr A D C := by
  intro δ hδ
  obtain ⟨N, H⟩ := h δ hδ
  refine ⟨N, fun r m hAr hr t ht => ?_⟩
  have key := H (r, m) (hA r m hAr) (by show N ≤ r; exact hr) t (by exact ht)
  have e : (hybridFamUp Fr α).evalR (r, m) (Fr.const + t) =
      (Fr.fullPoly r m).aeval (Fr.const + t) := by
    simp [PolyFamily.evalR, hybridFamUp, hybridFam_Q]
  change |(hybridFamUp Fr α).evalR (r, m) (Fr.const + t)| ≤ Real.exp (-(D - δ) * (r : ℝ) ^ 2) at key
  rw [e] at key
  exact key

theorem hybridFamUp_adm (r : ℕ) (h8 : 8 ∣ r) :
    (hybridFamUp Fr (1 / 8)).Adm (r, r / 8) := by
  obtain ⟨k, rfl⟩ := h8
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 8)]
  show (1 / 8 : ℚ) * ((8 * k : ℕ) : ℚ) ≤ (k : ℚ) ∧ (k : ℚ) ≤ 1 / 8 * ((8 * k : ℕ) : ℚ) + 1
  push_cast
  constructor <;> linarith

/-- **Decay of the pair family for an admissible relation** (G3): member-1 and member-2 decay. -/
theorem hasDecay_hybPairA {A : ℕ → ℕ → Prop} {D C : ℝ} (hC : 0 ≤ C)
    (M1 : Mem1DecayA Fr A D C) (M2 : Mem2DecayA Fr A D C) :
    HasDecay (hybPairFamA Fr A) D C := by
  intro δ hδ
  obtain ⟨N1, H1⟩ := M1 δ hδ
  obtain ⟨N2, H2⟩ := M2 (δ / 2) (half_pos hδ)
  refine ⟨max (max N1 N2) (⌈6 * |D - δ| / δ⌉₊ + 1) + 1, ?_⟩
  rintro ⟨⟨r, m⟩, b⟩ hA hr t ht
  cases b
  · have hr' : max (max N1 N2) (⌈6 * |D - δ| / δ⌉₊ + 1) + 1 ≤ r := hr
    have key := H1 r m hA (by omega) t (by exact ht)
    have e1 : ∀ x : ℝ, (hybPairFamA Fr A).evalR ((r, m), false) x =
        (Fr.fullPoly r m).aeval x := by
      intro x
      simp [PolyFamily.evalR, hybPairFamA_Q_false]
    rw [e1]
    exact key
  · have hr' : max (max N1 N2) (⌈6 * |D - δ| / δ⌉₊ + 1) + 1 ≤ r + 1 := hr
    have hrr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hwin : |t| ≤ Real.exp (-C * (r : ℝ)) := by
      refine ht.trans (Real.exp_le_exp.2 ?_)
      show -C * (((r + 1 : ℕ)) : ℝ) ≤ -C * r
      push_cast
      nlinarith
    have key := H2 r m hA (by omega) t hwin
    have hbig : 6 * |D - δ| / δ ≤ r := by
      have : (⌈6 * |D - δ| / δ⌉₊ : ℝ) ≤ r := by exact_mod_cast (by omega : ⌈6 * |D - δ| / δ⌉₊ ≤ r)
      exact (Nat.le_ceil _).trans this
    rw [div_le_iff₀ hδ] at hbig
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    have hA' : (D - δ) ≤ |D - δ| := le_abs_self _
    have hcmp : (D - δ) * ((r : ℝ) + 1) ^ 2 ≤ (D - δ / 2) * (r : ℝ) ^ 2 := by
      nlinarith [abs_nonneg (D - δ), sq_nonneg (r : ℝ), mul_nonneg (abs_nonneg (D - δ)) hrr]
    have hfin : |((afterTop r m).fullPolyG Fr).aeval (Fr.const + t)| ≤
        Real.exp (-(D - δ) * (((r + 1 : ℕ)) : ℝ) ^ 2) := by
      refine key.trans (Real.exp_le_exp.2 ?_)
      push_cast
      nlinarith [hcmp]
    simpa [PolyFamily.evalR, hybPairFamA] using hfin

/-- The slope-`1/8` form of `hasDecay_hybPairA`. -/
theorem hasDecay_hybPair {D C : ℝ} (hC : 0 ≤ C) (hD1 : HasDecay (hybridFamUp Fr (1 / 8)) D C)
    (M2 : Mem2Decay Fr D C) : HasDecay (hybPairFam Fr 8) D C :=
  hasDecay_hybPairA hC
    (Mem1DecayA.of_up (A := admDiv 8) (fun r m ⟨h8, hm⟩ => by subst hm; exact hybridFamUp_adm r h8)
      hD1) M2.toA

end Decay

end CatalanCore.Rect
