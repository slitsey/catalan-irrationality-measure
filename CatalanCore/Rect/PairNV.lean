module

public import CatalanCore.Rect.PairFam
public import CatalanCore.Measure.Pinned
public import CatalanCore.NT.Rules
public import CatalanCore.Basic.ZModGood

@[expose] public section

/-!
# From the hybrid nonvanishing theorem to the NV interfaces (LAMASM, G3)

**Generic layer (G3).**  `PairNV Fr Cls Reg Good` is the hybrid nonvanishing theorem of a frame in
a uniform shape: for a prime `ℓ` of the class `Cls`, geometry parameters `(r, m)` with
`Good ℓ r m`, and `x` regular for `ℓ` (`Reg ℓ x`, e.g. `x ∈ ℤ_(ℓ)`), the two determinants
`det Full(after r m)(x)`, `det Full(afterTop r m)(x)` do not vanish simultaneously.

* `hasNVPinC_pairA` : pinned NV (`HasNVPinC`) of `hybPairFamA Fr A` from `PairNV` and a
  *selection* hypothesis (for a prime `ℓ` and target degree `N`, an admissible `(r, m)` with
  `Good ℓ r m` and `N ≤ r ≤ N + C`);
* `hasNVC_pairA` : the unpinned `HasNVC` (degree `≈ g ℓ`), same shape of selection.

The prime class `Cls` and the badness predicate `Bad` are abstract (a residue class, a union of
classes, a class with a sub-class removed); `Reg` links the two (`hReg`).

**λ / λ′ instances.**  `HybPairNV Fr Cls Kf` is the two-level form `ℓ + … = 4 K` consumed by
`nv_hyb_nonvanishing`/`mir_hyb_nonvanishing`; `HybPairNV.toPairNV` embeds it in `PairNV`.
`hasNVPin_hybPair` : pick `r = 8⌈N/8⌉`, `m = r/8` for `ℓ ∈ [8N/5, 39N/10]`;
`measure_hybPair` : content + decay + this give the measure `c/(D-Λ)` (pinned deduction, `κ = 0`),
valid when `2 (D - Λ) < 23/10`.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Rect

variable (Fr : Frame)

/-! ### Generic layer -/

/-- The hybrid nonvanishing theorem of a frame, uniformly: class `Cls`, geometry predicate
`Good`, regularity `Reg` of the evaluation point. -/
def PairNV (Cls : ℕ → Prop) (Reg : ℕ → ℚ → Prop) (Good : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → Cls ℓ → ∀ r m : ℕ, Good ℓ r m → ∀ x : ℚ, Reg ℓ x →
    ((after r m).Full Fr x).det = 0 → ((afterTop r m).Full Fr x).det = 0 → False

variable {Fr}

/-- `PairNV` for a smaller class. -/
theorem PairNV.of_cls {Cls Cls' : ℕ → Prop} {Reg : ℕ → ℚ → Prop} {Good : ℕ → ℕ → ℕ → Prop}
    (h : PairNV Fr Cls Reg Good) (hc : ∀ l, Cls' l → Cls l) : PairNV Fr Cls' Reg Good :=
  fun ℓ hℓ hl => h ℓ hℓ (hc ℓ hl)

/-- One of the two members at `(r, m)` does not vanish at `x`. -/
theorem pairNV_member {Cls : ℕ → Prop} {Reg : ℕ → ℚ → Prop} {Good : ℕ → ℕ → ℕ → Prop}
    (hNV : PairNV Fr Cls Reg Good) (A : ℕ → ℕ → Prop) {ℓ : ℕ} (hℓ : ℓ.Prime) (hc : Cls ℓ)
    {r m : ℕ} (hG : Good ℓ r m) {x : ℚ} (hx : Reg ℓ x) :
    ∃ b : Bool, (hybPairFamA Fr A).evalQ ((r, m), b) x ≠ 0 :=
  hybPairFamA_exists_ne A r m x fun ⟨h1, h2⟩ => hNV ℓ hℓ hc r m hG x hx h1 h2

/-- **Pinned NV of the pair family** from `PairNV` and a selection of admissible members of
degree in `[N, N + C]`. -/
theorem hasNVPinC_pairA {Cls : ℕ → Prop} {Bad : ℕ → ℕ → Prop} {Reg : ℕ → ℚ → Prop}
    {Good : ℕ → ℕ → ℕ → Prop} (hNV : PairNV Fr Cls Reg Good)
    (hReg : ∀ ℓ, ℓ.Prime → Cls ℓ → ∀ p q : ℤ, 0 < q → IsCoprime p q → ¬ Bad ℓ q.natAbs →
      Reg ℓ ((p : ℚ) / q))
    (A : ℕ → ℕ → Prop) (α β C N₁ : ℝ)
    (hSel : ∀ ℓ : ℕ, ℓ.Prime → Cls ℓ → ∀ N : ℝ, N₁ ≤ N → α * N ≤ ℓ → (ℓ : ℝ) ≤ β * N →
      ∃ r m : ℕ, A r m ∧ Good ℓ r m ∧ N ≤ (r : ℝ) ∧ (r : ℝ) + 1 ≤ N + C) :
    HasNVPinC (hybPairFamA Fr A) Cls Bad α β := by
  refine ⟨C, N₁, fun ℓ hℓ hc N hN h1 h2 p q hq hcop hbad => ?_⟩
  obtain ⟨r, m, hA, hG, hr1, hr2⟩ := hSel ℓ hℓ hc N hN h1 h2
  obtain ⟨b, hb⟩ := pairNV_member hNV A hℓ hc hG (hReg ℓ hℓ hc p q hq hcop hbad)
  refine ⟨((r, m), b), hA, ?_, ?_, hb⟩
  · show N ≤ ((r + (if b then 1 else 0) : ℕ) : ℝ)
    push_cast
    split_ifs <;> linarith
  · show ((r + (if b then 1 else 0) : ℕ) : ℝ) ≤ N + C
    push_cast
    split_ifs <;> linarith

/-- **Unpinned NV of the pair family** (degree `≈ g ℓ`) from `PairNV` and a selection of admissible
members with `g₁ ℓ - C ≤ r` and `r + 1 ≤ g₂ ℓ + C`. -/
theorem hasNVC_pairA {Cls : ℕ → Prop} {Bad : ℕ → ℕ → Prop} {Reg : ℕ → ℚ → Prop}
    {Good : ℕ → ℕ → ℕ → Prop} (hNV : PairNV Fr Cls Reg Good)
    (hReg : ∀ ℓ, ℓ.Prime → Cls ℓ → ∀ p q : ℤ, 0 < q → IsCoprime p q → ¬ Bad ℓ q.natAbs →
      Reg ℓ ((p : ℚ) / q))
    (A : ℕ → ℕ → Prop) (g₁ g₂ C : ℝ) (l₀ : ℕ)
    (hSel : ∀ ℓ : ℕ, ℓ.Prime → l₀ ≤ ℓ → Cls ℓ →
      ∃ r m : ℕ, A r m ∧ Good ℓ r m ∧ g₁ * ℓ - C ≤ (r : ℝ) ∧ (r : ℝ) + 1 ≤ g₂ * ℓ + C) :
    HasNVC (hybPairFamA Fr A) Cls Bad g₁ g₂ := by
  refine ⟨C, l₀, fun ℓ hℓ hl0 hc p q hq hcop hbad => ?_⟩
  obtain ⟨r, m, hA, hG, hr1, hr2⟩ := hSel ℓ hℓ hl0 hc
  obtain ⟨b, hb⟩ := pairNV_member hNV A hℓ hc hG (hReg ℓ hℓ hc p q hq hcop hbad)
  refine ⟨((r, m), b), hA, ?_, ?_, hb⟩
  · show g₁ * ℓ - C ≤ ((r + (if b then 1 else 0) : ℕ) : ℝ)
    push_cast
    split_ifs <;> linarith
  · show ((r + (if b then 1 else 0) : ℕ) : ℝ) ≤ g₂ * ℓ + C
    push_cast
    split_ifs <;> linarith

variable (Fr)

/-! ### The two-level form of λ and λ′ -/

/-- The hybrid nonvanishing theorem of a frame, in the two-level form: `ℓ` prime of the class
`Cls` with threshold `K = Kf ℓ`, `1 ≤ m < K ≤ r`, `r + 2m + S = ℓ`, `K - m ≤ S`
(`S = s' + 1`).  Used by `nv_hyb_nonvanishing` and `mir_hyb_nonvanishing`. -/
def HybPairNV (Cls : ℕ → Prop) (Kf : ℕ → ℕ) : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → Cls ℓ → ∀ (m s' r : ℕ),
    1 ≤ m → m < Kf ℓ → Kf ℓ ≤ r → r + 2 * m + (s' + 1) = ℓ → Kf ℓ - m ≤ s' + 1 →
    ∀ x : ℚ, ¬ ℓ ∣ x.den →
      ((after r m).Full Fr x).det = 0 → ((afterTop r m).Full Fr x).det = 0 → False

/-- The geometry predicate of the two-level form. -/
def twoLevelGood (Kf : ℕ → ℕ) (ℓ r m : ℕ) : Prop :=
  1 ≤ m ∧ m < Kf ℓ ∧ Kf ℓ ≤ r ∧ ∃ s' : ℕ, r + 2 * m + (s' + 1) = ℓ ∧ Kf ℓ - m ≤ s' + 1

variable {Fr}

theorem HybPairNV.toPairNV {Cls : ℕ → Prop} {Kf : ℕ → ℕ} (h : HybPairNV Fr Cls Kf) :
    PairNV Fr Cls (fun ℓ x => ¬ ℓ ∣ x.den) (twoLevelGood Kf) :=
  fun ℓ hℓ hc r m ⟨h1, h2, h3, s', h4, h5⟩ x hx e1 e2 =>
    h ℓ hℓ hc m s' r h1 h2 h3 h4 h5 x hx e1 e2

theorem not_dvd_den_of_not_dvd (l : ℕ) (p q : ℤ) (hq : 0 < q) (h : ¬ l ∣ q.natAbs) :
    ¬ l ∣ ((p : ℚ) / q).den := by
  intro hd
  apply h
  refine hd.trans ?_
  have h1 := Rat.den_dvd p q
  rw [Rat.divInt_eq_div] at h1
  exact Int.natCast_dvd.mp h1 |>.trans (dvd_refl _)

variable (Fr) in
theorem hasNVPin_hybPair {c : ℕ} (hc4 : c < 4) (hc : IsUnit (c : ZMod 4)) {Kf : ℕ → ℕ}
    (hK : ∀ l, l.Prime → l % 4 = c → l ≤ 4 * Kf l ∧ 4 * Kf l ≤ l + 3)
    (hNV : HybPairNV Fr (fun l => l % 4 = c) Kf) :
    HasNVPin (hybPairFam Fr 8) (PrimeRule.ofDvd 4 (c : ZMod 4) hc) ((8 / 5 : ℚ) : ℝ)
      ((39 / 10 : ℚ) : ℝ) := by
  have hmod : ∀ l : ℕ, (l : ZMod 4) = (c : ZMod 4) → l % 4 = c := fun l hlr => by
    have := (ZMod.natCast_eq_natCast_iff' l c 4).1 hlr
    rwa [Nat.mod_eq_of_lt hc4] at this
  refine hasNVPinC_pairA (Cls := fun l => (l : ZMod 4) = (c : ZMod 4))
    (Reg := fun ℓ x => ¬ ℓ ∣ x.den) (Good := twoLevelGood Kf)
    (hNV.toPairNV.of_cls hmod) (fun ℓ _ _ p q hq _ hbad =>
      not_dvd_den_of_not_dvd ℓ p q hq (by simpa [PrimeRule.ofDvd] using hbad)) (admDiv 8)
    _ _ 9 200 ?_
  intro l hl hlr N hN hα hβ
  have hlmod : l % 4 = c := hmod l hlr
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
  refine ⟨8 * m, m, ⟨dvd_mul_right 8 m, (Nat.mul_div_cancel_left _ (by norm_num)).symm⟩,
    ⟨by omega, by omega, by omega, l - 10 * m - 1, by omega, by omega⟩, ?_, ?_⟩
  · push_cast; linarith
  · push_cast; linarith

variable (Fr) in
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
