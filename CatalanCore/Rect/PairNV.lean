module

public import CatalanCore.Rect.PairFam
public import CatalanCore.Measure.Pinned
public import CatalanCore.NT.Rules
public import CatalanCore.Basic.ZModGood

@[expose] public section

/-!
# From the hybrid nonvanishing theorem to the pinned NV interface (LAMASM)

`HybPairNV Fr Cls Kf` is the hybrid nonvanishing theorem of a frame (`nv_hyb_nonvanishing` for λ,
`mir_hyb_nonvanishing` for λ′) in a uniform shape: for a prime `ℓ` of the class `Cls` with
threshold `K = Kf ℓ`, geometry parameters `1 ≤ m < K ≤ r`, `r + 2m + S = ℓ`, `K - m ≤ S`
(`S = s' + 1`), the two determinants `det Full(after r m)(x)`, `det Full(afterTop r m)(x)` do not
vanish simultaneously at `x ∈ ℤ_(ℓ)`.

`hasNVPin_hybPair` : pick `r = 8⌈N/8⌉`, `m = r/8` (so `r ∈ [N, N+8)`, the member `(r, b)` is
admissible with degree in `[N, N+9)`); for `ℓ ∈ [8N/5, 39N/10]` the geometric hypotheses hold, and
`ℓ ∤ q` makes `p/q ∈ ℤ_(ℓ)`.  Hence `HasNVPin (hybPairFam Fr 8) (ofDvd 4 c) (8/5) (39/10)`.

`measure_hybPair` : content + decay + this give the measure `c/(D-Λ)` (pinned deduction, `κ = 0`),
valid when `2 (D - Λ) < 23/10`.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Rect

variable (Fr : Frame)

/-- The hybrid nonvanishing theorem of a frame, uniformly. -/
def HybPairNV (Cls : ℕ → Prop) (Kf : ℕ → ℕ) : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → Cls ℓ → ∀ (m s' r : ℕ),
    1 ≤ m → m < Kf ℓ → Kf ℓ ≤ r → r + 2 * m + (s' + 1) = ℓ → Kf ℓ - m ≤ s' + 1 →
    ∀ x : ℚ, ¬ ℓ ∣ x.den →
      ((after r m).Full Fr x).det = 0 → ((afterTop r m).Full Fr x).det = 0 → False

theorem not_dvd_den_of_not_dvd (l : ℕ) (p q : ℤ) (hq : 0 < q) (h : ¬ l ∣ q.natAbs) :
    ¬ l ∣ ((p : ℚ) / q).den := by
  intro hd
  apply h
  refine hd.trans ?_
  have h1 := Rat.den_dvd p q
  rw [Rat.divInt_eq_div] at h1
  exact Int.natCast_dvd.mp h1 |>.trans (dvd_refl _)

theorem hasNVPin_hybPair {c : ℕ} (hc4 : c < 4) (hc : IsUnit (c : ZMod 4)) {Kf : ℕ → ℕ}
    (hK : ∀ l, l.Prime → l % 4 = c → l ≤ 4 * Kf l ∧ 4 * Kf l ≤ l + 3)
    (hNV : HybPairNV Fr (fun l => l % 4 = c) Kf) :
    HasNVPin (hybPairFam Fr 8) (PrimeRule.ofDvd 4 (c : ZMod 4) hc) ((8 / 5 : ℚ) : ℝ)
      ((39 / 10 : ℚ) : ℝ) := by
  refine ⟨9, 200, ?_⟩
  intro l hl hlr N hN hα hβ p q hq hcop hbad
  have hlmod : l % 4 = c := by
    have := (ZMod.natCast_eq_natCast_iff' l c 4).1 hlr
    rwa [Nat.mod_eq_of_lt hc4] at this
  have hbad' : ¬ l ∣ q.natAbs := by simpa [PrimeRule.ofDvd] using hbad
  push_cast at hα hβ
  set m := ⌈N / 8⌉₊ with hm
  have h1 : N / 8 ≤ (m : ℝ) := Nat.le_ceil _
  have h2 : (m : ℝ) < N / 8 + 1 := Nat.ceil_lt_add_one (by linarith)
  obtain ⟨hK1, hK2⟩ := hK l hl hlmod
  set K := Kf l with hKdef
  have hA : 64 * m ≤ 5 * l + 64 := by
    have : (64 * m : ℝ) ≤ 5 * l + 64 := by linarith
    exact_mod_cast this
  have hB : 5 * l ≤ 156 * m := by
    have : (5 * l : ℝ) ≤ 156 * m := by linarith
    exact_mod_cast this
  have hC : 25 ≤ m := by
    have : (25 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  haveI : Fact l.Prime := ⟨hl⟩
  have hx : ¬ l ∣ ((p : ℚ) / q).den := not_dvd_den_of_not_dvd l p q hq hbad'
  have hexists := hybPairFam_exists_ne Fr 8 (8 * m) ((p : ℚ) / q) (by
    intro ⟨h1', h2'⟩
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 8)] at h1' h2'
    exact hNV l hl hlmod m (l - 10 * m - 1) (8 * m) (by omega) (by omega) (by omega) (by omega)
      (by omega) _ hx h1' h2')
  obtain ⟨b, hb⟩ := hexists
  refine ⟨(8 * m, b), dvd_mul_right 8 m, ?_, ?_, hb⟩
  · show N ≤ ((8 * m + (if b then 1 else 0) : ℕ) : ℝ)
    push_cast
    split_ifs <;> linarith
  · show ((8 * m + (if b then 1 else 0) : ℕ) : ℝ) ≤ N + 9
    push_cast
    split_ifs <;> linarith

/-- **Measure from content, decay and NV, for the two-member hybrid family** (`κ = 0`, pinned
degree): exponent `c / (D - Λ)`. -/
theorem measure_hybPair {c : ℕ} (hc4 : c < 4) (hc : IsUnit (c : ZMod 4)) {Kf : ℕ → ℕ}
    (hK : ∀ l, l.Prime → l % 4 = c → l ≤ 4 * Kf l ∧ 4 * Kf l ≤ l + 3)
    (hNV : HybPairNV Fr (fun l => l % 4 = c) Kf) {Λ D C E : ℚ}
    (hΛ : HasContent (hybPairFam Fr 8) (Λ : ℝ)) (hD : HasDecay (hybPairFam Fr 8) (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E) :
    (hybPairFam Fr 8).MeasureLB (E : ℝ) := by
  refine Measure.measure_of_family_pin_le (hybPairFam Fr 8) hΛ hD hη hC
    (PrimeRule.ofDvd 4 (c : ZMod 4) hc) (by norm_num : (0 : ℚ) < 8 / 5) (by norm_num) ?_
    (hasNVPin_hybPair Fr hc4 hc hK hNV) (PrimeRule.ofDvd_hasWindow 4 _ hc) hE
  have : (PrimeRule.ofDvd 4 (c : ZMod 4) hc).s = 2 := by
    simp [PrimeRule.s, PrimeRule.ofDvd, show Nat.totient 4 = 2 by decide]
  rw [this]
  linarith

end CatalanCore.Rect
