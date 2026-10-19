module

public import CatalanFrames.P6Hybrid.Mem2
public import CatalanFrames.P6Hybrid.Final
public import CatalanFrames.P6.Final
public import CatalanCore.Cert.SigmaP6H.Final
public import CatalanCore.Rect.PairNV
public import CatalanCore.Rect.PairBridge
public import CatalanCore.Rect.PairSel
public import CatalanCore.Measure.Exponent

@[expose] public section

/-!
# P6 hybrid: the measure of `L(2, χ₋₃)` (P6DECAY, assembly)

The pair family `hybPairFamA p6Frame A` (members `after r m`, `afterTop r m`), `A = P6Adm` (`r ≤ 8 m ≤ r + 8`,
headline `24.58`, fallback) or `A = P6Adm9` (`r ≤ 8 m ≤ r + 9`, headline `23.82`, no NV hole):

* decay `D = 3.7251`, `c = 6.6510` (`p6_hybrid_decay`, `p6_mem2_decay_of`, `hasDecay_hybPairA`);
* content `Λ = 10339/3072` (`p6_content` for the two choice functions, `p6_mem2Content`);
* unpinned NV with `g₁ = g₂ = 2/5`: prime class `S60` (dodges the hole `ℓ ≡ 43 (60)`), bad primes `ℓ ∣ q`
  (the hybrid has no Lemma-3 analogue yet, so `ℓ ∣ q` is excluded), window `s = 16/7`.

`measureExp = c (1/(D-Λ) + g s) = 24.5795…`; the round exponent `24.58` is stated.
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

/-- The P6 pair family. -/
noncomputable abbrev p6Fam : PolyFamily := hybPairFamA p6Frame P6Adm

theorem p6_adm9_real {r m : ℕ} (h : P6Adm9 r m) :
    ((1 / 8 : ℚ) : ℝ) * r ≤ m ∧ (m : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) * r + 9 / 8 := by
  obtain ⟨h1, h2⟩ := h
  have h1' : (r : ℝ) ≤ 8 * m := by exact_mod_cast h1
  have h2' : 8 * (m : ℝ) ≤ r + 9 := by exact_mod_cast h2
  push_cast
  constructor <;> linarith

/-- **Decay of the pair family** on every relation `A ⊆ P6Adm9` (window slack `9/8`). -/
theorem p6_pair_decay_of {A : ℕ → ℕ → Prop} (hA : ∀ r m, A r m → P6Adm9 r m) :
    HasDecay (hybPairFamA p6Frame A) (((37251 / 10000 : ℚ)) : ℝ) (((66510 / 10000 : ℚ)) : ℝ) :=
  hasDecay_hybPairA (by norm_num)
    (CatalanCore.Cert.SigmaP6H.p6_mem1_decay_slack (a := 9 / 8) (by norm_num)
      (fun r m h => p6_adm9_real (hA r m h)))
    (CatalanCore.Cert.SigmaP6H.p6_mem2_decay_slack (a := 9 / 8) (by norm_num)
      (fun r m h => p6_adm9_real (hA r m h)))

/-- **Decay of the pair family** (`r ≤ 8m ≤ r+8`). -/
theorem p6_pair_decay :
    HasDecay p6Fam (((37251 / 10000 : ℚ)) : ℝ) (((66510 / 10000 : ℚ)) : ℝ) :=
  p6_pair_decay_of (fun _ _ h => h.toAdm9)

/-- **Content of the pair family** (`Λ = 10339/3072`) on every relation `A ⊆ P6Adm9`. -/
theorem p6_pair_content_of {A : ℕ → ℕ → Prop} (hA : ∀ r m, A r m → P6Adm9 r m) :
    HasContent (hybPairFamA p6Frame A) (10339 / 3072 : ℝ) := by
  classical
  have h1 : P6ContentStmt (fun r => (r + 7) / 8) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  have h2 : P6ContentStmt (fun r => r / 8 + 1) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  have h3 : P6ContentStmt p6mfC :=
    p6_content _ (fun r => by unfold p6mfC; split_ifs <;> omega)
  have hall : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, A r m →
      Real.log (Dhyb (p6Inst r m) r m) ≤ (10339 / 3072 + ε) * (r : ℝ) ^ 2 := by
    intro ε hε
    filter_upwards [h1 ε hε, h2 ε hε, h3 ε hε] with r a b c m hm
    rcases (hA r m hm).cases with rfl | rfl | rfl
    · exact a
    · exact b
    · exact c
  refine hasContent_hybPairF (A := A) p6Inst (by norm_num)
    (fun r m p => tropExp (p6Inst r m) r m p) (fun _ _ _ => 0) ?_ ?_ (p6_mem2ContentA hA)
  · filter_upwards with r m _ p hp hb
    exact ⟨Nat.zero_le _, fun [Fact p.Prime] => by simpa using fullPoly_gle (p6Inst r m) p r m⟩
  · intro ε hε
    filter_upwards [hall ε hε] with r h m hm
    have e : DhybT (p6Inst r m) r m (fun p => tropExp (p6Inst r m) r m p) (fun _ => 0)
        = Dhyb (p6Inst r m) r m := by
      unfold DhybT Dhyb; simp
    rw [e]
    exact h m hm

/-- **Content of the pair family** (`Λ = 10339/3072`), `r ≤ 8m ≤ r+8`. -/
theorem p6_pair_content : HasContent p6Fam (10339 / 3072 : ℝ) :=
  p6_pair_content_of (fun _ _ h => h.toAdm9)

/-! ### Non-vanishing and the prime window -/

/-- The prime class: `ℓ mod 60 ∈ S60`. -/
def P6Cls (l : ℕ) : Prop := (l : ZMod 60) ∈ S60

/-- Bad primes: `ℓ ∣ q`. -/
def P6Bad (l q : ℕ) : Prop := l ∣ q

/-- The geometry of `p6_hyb_nonvanishing`: `ℓ = 6t + 1`, `r = 3t - 2m`, `1 ≤ m`, `2m + 1 ≤ t`. -/
def P6Good (ℓ r m : ℕ) : Prop := ∃ t, ℓ = 6 * t + 1 ∧ 1 ≤ t ∧ 1 ≤ m ∧ 2 * m + 1 ≤ t ∧ r = 3 * t - 2 * m

theorem p6_pairNV {Cls : ℕ → Prop} : PairNV p6Frame Cls (fun ℓ x => ¬ ℓ ∣ x.den) P6Good := by
  intro ℓ hℓ hc r m ⟨t, hl, ht, hm, hb, hr⟩ x hx h1 h2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  subst hr
  exact p6_hyb_nonvanishing hl ht m hm hb hx h1 h2

/-- **Unpinned NV** on any relation `A`, for any prime class `Cls`, from a selection of pairs
`r + 2m = 3t` (`ℓ = 6t+1`, `1 ≤ m`, `2m+1 ≤ t`, `r ≈ (2/5) ℓ`). -/
theorem p6_hasNVC_of {Cls : ℕ → Prop} {A : ℕ → ℕ → Prop}
    (hsel : ∀ ℓ : ℕ, ℓ.Prime → 61 ≤ ℓ → Cls ℓ → ∃ t r m : ℕ, ℓ = 6 * t + 1 ∧ r + 2 * m = 3 * t ∧
      A r m ∧ 1 ≤ m ∧ 2 * m + 1 ≤ t ∧ 5 * r ≤ 2 * ℓ ∧ 2 * ℓ ≤ 5 * r + 11) :
    HasNVC (hybPairFamA p6Frame A) Cls P6Bad (((2 / 5 : ℚ)) : ℝ) (((2 / 5 : ℚ)) : ℝ) := by
  refine hasNVC_pairA p6_pairNV
    (fun ℓ hℓ hc p q hq hcop hbad => not_dvd_den_of_not_dvd ℓ p q hq hbad) A _ _ 3 61 ?_
  intro ℓ hℓ hl0 hc
  obtain ⟨t, r, m, h1, h2, h3, h4, h5, h6', h7⟩ := hsel ℓ hℓ hl0 hc
  refine ⟨r, m, h3, ⟨t, h1, by omega, h4, h5, by omega⟩, ?_, ?_⟩
  · have h' : (2 : ℝ) * ℓ ≤ 5 * r + 11 := by exact_mod_cast h7
    push_cast; linarith
  · have h' : (5 : ℝ) * r ≤ 2 * ℓ := by exact_mod_cast h6'
    push_cast; linarith

theorem p6_hasNVC :
    HasNVC p6Fam P6Cls P6Bad (((2 / 5 : ℚ)) : ℝ) (((2 / 5 : ℚ)) : ℝ) := by
  refine p6_hasNVC_of ?_
  intro ℓ hℓ hl0 hc
  obtain ⟨h6, h60⟩ := mem_S60 hc
  obtain ⟨t, r, m, h1, h2, h3, h4, h5, h6'⟩ := pinned_pair_exists ℓ h6 h60 hl0
  exact ⟨t, r, m, h1, h2, ⟨h3, h4⟩, h5, h6', by omega, by omega⟩

/-- The window for the class `S60` and the rule `ℓ ∣ q` (weight 1): `s = 16/7`. -/
theorem p6_window : HasWindowC P6Cls P6Bad (((16 / 7 : ℚ)) : ℝ) := by
  have h := PrimeRule.hasWindowSet (PrimeRule.ofDvd 60 1 isUnit_one)
    (PrimeRule.ofDvd_badBound _ _ _) S60 S60_isUnit S60_nonempty (s := (((16 / 7 : ℚ)) : ℝ))
    (by simp [PrimeRule.ofDvd, S60_card, show Nat.totient 60 = 16 by decide])
  exact h

/-- **The measure of the P6 pair family**: exponent `24.58` (exact value `24.5795…`). -/
theorem p6_pair_measure : p6Fam.MeasureLB (((2458 / 100 : ℚ)) : ℝ) := by
  have hΛ : HasContent p6Fam (((10339 / 3072 : ℚ)) : ℝ) := by
    have e : (((10339 / 3072 : ℚ)) : ℝ) = 10339 / 3072 := by push_cast; norm_num
    rw [e]; exact p6_pair_content
  exact Measure.measure_of_family_leC p6Fam (c := 66510 / 10000) (Λ := 10339 / 3072)
    (D := 37251 / 10000) (g₁ := 2 / 5) (g₂ := 2 / 5) (s := 16 / 7) (E' := 2458 / 100)
    hΛ p6_pair_decay (by norm_num) (by norm_num) (by norm_num) ⟨by norm_num, le_rfl⟩ p6_hasNVC
    p6_window (by norm_num [measureExp])

/-- **Headline**: `μ(L(2, χ₋₃)) ≤ 24.58`. -/
theorem chi3_hybrid_measure :
    Measure.MeasureLBAt chi3L2 (((2458 / 100 : ℚ)) : ℝ) := by
  have h' : Measure.MeasureLBAt p6Frame.const (((2458 / 100 : ℚ)) : ℝ) := p6_pair_measure
  rw [chi3L2_eq]
  exact h'.affine (by norm_num) 4 0 (by norm_num)

#print axioms chi3_hybrid_measure

/-! ### The widened window: prime class `ℓ ≡ 1 (mod 6)`, window `s = 2` (P6GAP) -/

/-- The widened relation. -/
noncomputable abbrev p6FamW : PolyFamily := hybPairFamA p6Frame P6Adm9

/-- The prime class `ℓ ≡ 1 (mod 6)`. -/
def P6Cls1 (l : ℕ) : Prop := (l : ZMod 6) ∈ ({1} : Finset (ZMod 6))

theorem P6Cls1.mod6 {l : ℕ} (h : P6Cls1 l) : l % 6 = 1 := by
  have h' : (l : ZMod 6) = 1 := by simpa [P6Cls1] using h
  exact cls_one h'

theorem p6_hasNVC_wide :
    HasNVC p6FamW P6Cls1 P6Bad (((2 / 5 : ℚ)) : ℝ) (((2 / 5 : ℚ)) : ℝ) := by
  refine p6_hasNVC_of ?_
  intro ℓ hℓ hl0 hc
  obtain ⟨t, r, m, h1, h2, h3, h4, h5, h6', h7, h8⟩ := pinned_pair_exists_wide ℓ hc.mod6 hl0
  exact ⟨t, r, m, h1, h2, ⟨h3, h4⟩, h5, h6', h7, h8⟩

/-- The window for the class `1 (mod 6)` and the rule `ℓ ∣ q`: `s = 2`. -/
theorem p6_window_wide : HasWindowC P6Cls1 P6Bad (((2 : ℚ)) : ℝ) := by
  have h := PrimeRule.hasWindowSet (PrimeRule.ofDvd 6 1 isUnit_one)
    (PrimeRule.ofDvd_badBound _ _ _) ({1} : Finset (ZMod 6))
    (fun c hc => by
      have e : c = 1 := Finset.mem_singleton.mp (show c ∈ ({1} : Finset (ZMod 6)) from hc)
      rw [e]; exact isUnit_one)
    (Finset.singleton_nonempty 1)
    (s := (((2 : ℚ)) : ℝ))
    (by simp [PrimeRule.ofDvd, show Nat.totient 6 = 2 by decide])
  exact h

/-- **The measure of the widened P6 pair family**: exponent `23.82` (exact value `23.8194…`). -/
theorem p6_pair_measure_wide : p6FamW.MeasureLB (((2382 / 100 : ℚ)) : ℝ) := by
  have hΛ : HasContent p6FamW (((10339 / 3072 : ℚ)) : ℝ) := by
    have e : (((10339 / 3072 : ℚ)) : ℝ) = 10339 / 3072 := by push_cast; norm_num
    rw [e]; exact p6_pair_content_of (fun _ _ h => h)
  exact Measure.measure_of_family_leC p6FamW (c := 66510 / 10000) (Λ := 10339 / 3072)
    (D := 37251 / 10000) (g₁ := 2 / 5) (g₂ := 2 / 5) (s := 2) (E' := 2382 / 100)
    hΛ (p6_pair_decay_of (fun _ _ h => h)) (by norm_num) (by norm_num) (by norm_num)
    ⟨by norm_num, le_rfl⟩ p6_hasNVC_wide p6_window_wide (by norm_num [measureExp])

/-- **Headline (widened window)**: `μ(L(2, χ₋₃)) ≤ 23.82`. -/
theorem chi3_hybrid_measure_wide :
    Measure.MeasureLBAt chi3L2 (((2382 / 100 : ℚ)) : ℝ) := by
  have h' : Measure.MeasureLBAt p6Frame.const (((2382 / 100 : ℚ)) : ℝ) := p6_pair_measure_wide
  rw [chi3L2_eq]
  exact h'.affine (by norm_num) 4 0 (by norm_num)

#print axioms chi3_hybrid_measure_wide

end CatalanFrames.P6Hybrid
