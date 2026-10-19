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

The pair family `hybPairFamA p6Frame P6Adm` (members `after r m`, `afterTop r m`, `r ≤ 8 m ≤ r + 8`):

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

theorem p6_adm_up {r m : ℕ} (h : P6Adm r m) : (hybridFamUp p6Frame (1 / 8 : ℚ)).Adm (r, m) := by
  obtain ⟨h1, h2⟩ := h
  have h1' : (r : ℚ) ≤ 8 * m := by exact_mod_cast h1
  have h2' : 8 * (m : ℚ) ≤ r + 8 := by exact_mod_cast h2
  show (1 / 8 : ℚ) * (r : ℚ) ≤ m ∧ (m : ℚ) ≤ (1 / 8 : ℚ) * r + 1
  constructor <;> linarith

theorem p6_adm_real {r m : ℕ} (h : P6Adm r m) :
    ((1 / 8 : ℚ) : ℝ) * r ≤ m ∧ (m : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) * r + 1 := by
  obtain ⟨h1, h2⟩ := h
  have h1' : (r : ℝ) ≤ 8 * m := by exact_mod_cast h1
  have h2' : 8 * (m : ℝ) ≤ r + 8 := by exact_mod_cast h2
  push_cast
  constructor <;> linarith

/-- **Decay of the pair family.** -/
theorem p6_pair_decay :
    HasDecay p6Fam (((37251 / 10000 : ℚ)) : ℝ) (((66510 / 10000 : ℚ)) : ℝ) :=
  hasDecay_hybPairA (by norm_num)
    (Mem1DecayA.of_up (fun r m h => p6_adm_up h) CatalanCore.Cert.SigmaP6H.p6_hybrid_decay)
    (CatalanCore.Cert.SigmaP6H.p6_mem2_decay_of (fun r m h => p6_adm_real h))

/-- **Content of the pair family** (`Λ = 10339/3072`). -/
theorem p6_pair_content : HasContent p6Fam (10339 / 3072 : ℝ) := by
  classical
  have hA : P6ContentStmt (fun r => (r + 7) / 8) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  have hB : P6ContentStmt (fun r => r / 8 + 1) :=
    p6_content _ (fun r => ⟨by omega, by omega⟩)
  have hall : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, P6Adm r m →
      Real.log (Dhyb (p6Inst r m) r m) ≤ (10339 / 3072 + ε) * (r : ℝ) ^ 2 := by
    intro ε hε
    filter_upwards [hA ε hε, hB ε hε] with r h1 h2 m ⟨ha, hb⟩
    have : m = (r + 7) / 8 ∨ m = r / 8 + 1 := by omega
    rcases this with rfl | rfl
    · exact h1
    · exact h2
  refine hasContent_hybPairF (A := P6Adm) p6Inst (by norm_num)
    (fun r m p => tropExp (p6Inst r m) r m p) (fun _ _ _ => 0) ?_ ?_ p6_mem2Content
  · filter_upwards with r m _ p hp hb
    exact ⟨Nat.zero_le _, fun [Fact p.Prime] => by simpa using fullPoly_gle (p6Inst r m) p r m⟩
  · intro ε hε
    filter_upwards [hall ε hε] with r h m hm
    have e : DhybT (p6Inst r m) r m (fun p => tropExp (p6Inst r m) r m p) (fun _ => 0)
        = Dhyb (p6Inst r m) r m := by
      unfold DhybT Dhyb; simp
    rw [e]
    exact h m hm

/-! ### Non-vanishing and the prime window -/

/-- The prime class: `ℓ mod 60 ∈ S60`. -/
def P6Cls (l : ℕ) : Prop := (l : ZMod 60) ∈ S60

/-- Bad primes: `ℓ ∣ q`. -/
def P6Bad (l q : ℕ) : Prop := l ∣ q

/-- The geometry of `p6_hyb_nonvanishing`: `ℓ = 6t + 1`, `r = 3t - 2m`, `1 ≤ m`, `2m + 1 ≤ t`. -/
def P6Good (ℓ r m : ℕ) : Prop := ∃ t, ℓ = 6 * t + 1 ∧ 1 ≤ t ∧ 1 ≤ m ∧ 2 * m + 1 ≤ t ∧ r = 3 * t - 2 * m

theorem p6_pairNV : PairNV p6Frame P6Cls (fun ℓ x => ¬ ℓ ∣ x.den) P6Good := by
  intro ℓ hℓ hc r m ⟨t, hl, ht, hm, hb, hr⟩ x hx h1 h2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  subst hr
  exact p6_hyb_nonvanishing hl ht m hm hb hx h1 h2

theorem p6_hasNVC :
    HasNVC p6Fam P6Cls P6Bad (((2 / 5 : ℚ)) : ℝ) (((2 / 5 : ℚ)) : ℝ) := by
  refine hasNVC_pairA p6_pairNV
    (fun ℓ hℓ hc p q hq hcop hbad => not_dvd_den_of_not_dvd ℓ p q hq hbad) P6Adm _ _ 3 61 ?_
  intro ℓ hℓ hl0 hc
  obtain ⟨h6, h60⟩ := mem_S60 hc
  obtain ⟨t, r, m, h1, h2, h3, h4, h5, h6'⟩ := pinned_pair_exists ℓ h6 h60 hl0
  refine ⟨r, m, ⟨h3, h4⟩, ⟨t, h1, by omega, h5, h6', by omega⟩, ?_, ?_⟩
  · have : 2 * ℓ ≤ 5 * r + 10 := by omega
    have h' : (2 : ℝ) * ℓ ≤ 5 * r + 10 := by exact_mod_cast this
    push_cast; linarith
  · have : 5 * r ≤ 2 * ℓ := by omega
    have h' : (5 : ℝ) * r ≤ 2 * ℓ := by exact_mod_cast this
    push_cast; linarith

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

end CatalanFrames.P6Hybrid
