module

public import CatalanCore.Uniform.Bank.Plane1.Inst
public import CatalanCore.Uniform.Content.BankShared.KTerm.Content
public import CatalanCore.Uniform.Content.BankShared.KTerm.Pre
public import CatalanCore.Uniform.Content.BankShared.KTerm.Trop
public import CatalanCore.Arith.Hybrid.Values
public import CatalanCore.Arith.Hybrid.PieceTools
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Class

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The content of the plane frames (wave H4; ledger P106, P107, P108, P109)

For every plane frame `planeFrame σ a b c h0` the content of the even-scale family `AltEven (1/6) Fr depth`
is `HasScaledContent … Λ` for the `Λ` of any bank `kd : KBankData` that passes `kcheck`, whose catalogue
consists of the branches of this file, and whose parameters satisfy the small-prime and shift conditions.  The
bank is **weight free**: `plane_content` quantifies over all weights at once, and the catalogue is the same for
`S⁺` and `S⁻` up to `ρ`.

**The plane catalogue** (Proposition 3.2 and Theorem W of the plane theorem, in the `KBranch` language of the
`k`-shift route, `vk 0 = k_A` with `3 k_A = j p + ρ`, `vk 1 = k_B` with `2 k_B = j p + 1`, `k = min (k_A, k_B)`):

| name | price | conditions |
|---|---|---|
| `kbD1`, `kbD1x` | `2 (r + m)`, `2 r + 2 m - δ_p(m)` | none |
| `kbD2` | `2 r + 2 m - 2 X + min (2 m, X)`, `X = (k + p - r)₊` | `2 m < p ≤ r` |
| `kbD45` | `2 (r - k)₊ + 2 m + (2 m - (p - r))₊` | `r < p` |
| `kbD6` | `(2 m - (k - r))₊` | `r + 2 m ≤ p`, `k_A, k_B ≥ r` |
| `kbT0` (tail) | `0` | `r + 2 m < k_A`, `r + 2 m < k_B` |
| `kbrPre n j₀ [j₁, j₂]` | the prefix window (Theorem W), `KBundle.prefix_valid` | none |

There are no windows (`M3D`): they are the prefix branches with `n = 0` (Lemma 5.1). `plane_trop_valid` proves
the first six; the prefix branches are `KBundle.prefix_valid`; `plane_cat_valid` assembles them
(`KCatValid` for a catalogue drawn from these). -/

namespace CatalanCore.Uniform.Bank.Plane1
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.SmallPrimes
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanCore.Rect

/-! ### The branches -/

open KExpr in
/-- `min (k_A, k_B)`: the first singular index. -/
def kbK : KExpr := mn (vk 0) (vk 1)

open KExpr in
/-- `2 r + 2 m`. -/
def kb2rm : KExpr := add (smul 2 vr) (smul 2 vm)

open KExpr in
/-- `D1`: `2 (r + m)`. -/
def kbD1 : KBranch := ⟨smul 2 (add vr vm), [], 0⟩

open KExpr in
/-- `D1x`: `2 r + 2 m - δ_p(m)`. -/
def kbD1x : KBranch := ⟨tsub kb2rm (dist vm), [], 0⟩

open KExpr in
/-- `X = (k + p - r)₊`. -/
def kbX : KExpr := tsub (add kbK vp) vr

open KExpr in
/-- `D2` (`2 m < p ≤ r`): `2 r + 2 m - 2 X + min (2 m, X)`. -/
def kbD2 : KBranch :=
  ⟨tsub (add kb2rm (mn (smul 2 vm) kbX)) (smul 2 kbX),
    [⟨0, 1, -2, [0, 0], -1, false⟩, ⟨1, -1, 0, [0, 0], 0, false⟩], 0⟩

open KExpr in
/-- `D45` (`r < p`): `2 (r - k) + 2 m + (2 m - (p - r))`. -/
def kbD45 : KBranch :=
  ⟨add (add (smul 2 (tsub vr kbK)) (smul 2 vm)) (tsub (smul 2 vm) (tsub vp vr)),
    [⟨-1, 1, 0, [0, 0], -1, false⟩], 0⟩

open KExpr in
/-- `D6` (`r + 2 m ≤ p`, `k ≥ r`): `2 m - (k - r)`. -/
def kbD6 : KBranch :=
  ⟨tsub (smul 2 vm) (tsub kbK vr),
    [⟨-1, 1, -2, [0, 0], 0, false⟩, ⟨-1, 0, 0, [1, 0], 0, false⟩, ⟨-1, 0, 0, [0, 1], 0, false⟩], 0⟩

open KExpr in
/-- `T0` (the tail branch, price `0` on `N < k_A`, `N < k_B`). -/
def kbT0 : KBranch := ⟨cst 0, [⟨-1, 0, -2, [1, 0], 0, true⟩, ⟨-1, 0, -2, [0, 1], 0, true⟩], 0⟩

/-- The six tropical branches of the plane catalogue. -/
def planeTrop : List KBranch := [kbD1, kbD1x, kbD2, kbD45, kbD6, kbT0]

/-! ### Level facts at a prime -/

section Levels

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

theorem lsing_plane_iff (q : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    (∃ i : Fin (planeFrame σ a b c h0).d, q ∣ lin (planeFrame σ a b c h0) i t) ↔
      (q ∣ 3 * t - σ.rho ∨ q ∣ 2 * t - 1 ∨ q ∣ t) := by
  constructor
  · rintro ⟨⟨k, hk⟩, hd⟩
    rw [lin_plane σ a b c h0 ⟨k, hk⟩ ht] at hd
    have hk3 : k < 3 := hk
    interval_cases k
    · exact Or.inl hd
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr hd)
  · rintro (h | h | h)
    · exact ⟨⟨0, by show 0 < 3; norm_num⟩, by rw [lin_plane σ a b c h0 _ ht]; exact h⟩
    · exact ⟨⟨1, by show 1 < 3; norm_num⟩, by rw [lin_plane σ a b c h0 _ ht]; exact h⟩
    · exact ⟨⟨2, by show 2 < 3; norm_num⟩, by rw [lin_plane σ a b c h0 _ ht]; exact h⟩

/-- **The first singular index.**  At a prime `p ≥ 5` with `3 k_A = j p + ρ`, `2 k_B = j' p + 1`,
`0 < k_A, k_B < p`, the level `lev p c` vanishes exactly below `min (k_A, k_B)`. -/
theorem plane_lev_zero_iff {p kA kB jA jB : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hA : 3 * kA = jA * p + σ.rho) (hB : 2 * kB = jB * p + 1) (hA0 : 0 < kA) (hAp : kA < p)
    (hB0 : 0 < kB) (hBp : kB < p) (c' : ℕ) :
    levF (planeFrame σ a b c h0) p c' = 0 ↔ c' < min kA kB := by
  classical
  have hr := rho_le σ
  have hr0 := rho_pos σ
  unfold levF
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro hall
    by_contra hge
    push Not at hge
    rcases le_total kA kB with hle | hle
    · have hm : min kA kB = kA := min_eq_left hle
      rw [hm] at hge
      apply hall (x := kA) (Finset.mem_Icc.mpr ⟨hA0, hge⟩)
      refine (lsing_plane_iff σ a b c h0 p hA0).2 (Or.inl ⟨jA, ?_⟩)
      rw [Nat.mul_comm p jA]; omega
    · have hm : min kA kB = kB := min_eq_right hle
      rw [hm] at hge
      apply hall (x := kB) (Finset.mem_Icc.mpr ⟨hB0, hge⟩)
      refine (lsing_plane_iff σ a b c h0 p hB0).2 (Or.inr (Or.inl ⟨jB, ?_⟩))
      rw [Nat.mul_comm p jB]; omega
  · intro hlt t ht hs
    have ht' := Finset.mem_Icc.mp ht
    have hs' := (lsing_plane_iff σ a b c h0 p ht'.1).1 hs
    have htA : t < kA := lt_of_le_of_lt ht'.2 (lt_of_lt_of_le hlt (min_le_left _ _))
    have htB : t < kB := lt_of_le_of_lt ht'.2 (lt_of_lt_of_le hlt (min_le_right _ _))
    rcases hs' with h | h | h
    · have h1 : p ∣ 3 * kA - σ.rho := ⟨jA, by rw [Nat.mul_comm p jA]; omega⟩
      have h2 := Nat.dvd_sub h1 h
      have e : 3 * kA - σ.rho - (3 * t - σ.rho) = 3 * (kA - t) := by omega
      rw [e] at h2
      rcases hp.dvd_mul.1 h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3; omega
      · have := Nat.le_of_dvd (by omega) h3; omega
    · have h1 : p ∣ 2 * kB - 1 := ⟨jB, by rw [Nat.mul_comm p jB]; omega⟩
      have h2 := Nat.dvd_sub h1 h
      have e : 2 * kB - 1 - (2 * t - 1) = 2 * (kB - t) := by omega
      rw [e] at h2
      rcases hp.dvd_mul.1 h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3; omega
      · have := Nat.le_of_dvd (by omega) h3; omega
    · have := Nat.le_of_dvd (by omega) h; omega

/-- The level is positive from `p` on (`p` itself is singular). -/
theorem plane_lev_high {p c' : ℕ} (hp : 1 ≤ p) (h : p ≤ c') : 0 < levF (planeFrame σ a b c h0) p c' :=
  levF_pos (Finset.mem_Icc.mpr ⟨hp, h⟩)
    ⟨⟨2, by show 2 < 3; norm_num⟩, by rw [lin_plane σ a b c h0 _ hp]; exact dvd_refl p⟩

end Levels

/-! ### Validity of the tropical branches -/

section TropValid

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

/-- Border bounds of `altGeom (1/6)` at an even scale: `r ≤ 12 m + 6`, `12 m < r + 6`. -/
theorem plane_border {r : ℕ} (hr : r % 2 = 0) :
    r ≤ 12 * (altGeom planeC planeC_pos).borderSize r + 6 ∧
      12 * (altGeom planeC planeC_pos).borderSize r < r + 6 := by
  obtain ⟨h1, h2⟩ := altGeom_border_nat planeC planeC_pos 1 6 (by norm_num) (by norm_num [planeC]) hr
  constructor <;> omega

/-- For every slope `c ≤ 1` and even `r`: `2 m ≤ r + 1`, and `2 m ≤ r` when `r` is positive. -/
theorem border_two_m_le (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {r : ℕ} (hr : r % 2 = 0) (hr0 : 0 < r) :
    2 * (altGeom c hc).borderSize r ≤ r := by
  obtain ⟨-, h2⟩ := altGeom_border c hc hr
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr0
  have h3 : 2 * ((altGeom c hc).borderSize r : ℚ) < (r : ℚ) + 1 := by
    have : c * r ≤ r := by nlinarith
    linarith
  have h4 : 2 * (altGeom c hc).borderSize r < r + 1 := by exact_mod_cast h3
  omega

/-- **The tropical branches of the plane catalogue are valid**, for every plane frame and every slope
`c ≤ 1` of the alternating geometry (the plane is `c = 1/6`; special rows use their own `α`). -/
theorem plane_trop_valid (cs : ℚ) (hcs : 0 < cs) (hcs1 : cs ≤ 1) (depth Q0 Pbad N0 : ℕ) (hQ0 : 3 ≤ Q0)
    (hP : 6 ≤ Pbad) :
    KCatValid cs hcs (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0 Pbad N0
      planeTrop := by
  intro br hbr i hi hr0 p hpf hPb _ hqN kv hroots hcond
  have hr := hi.2
  have h7 : 7 ≤ p := by omega
  set r := i.1 with hrdef
  set m := (altGeom cs hcs).borderSize r with hmdef
  have hp2 := odd_of_ge_seven (Fact.out : p.Prime) h7
  have hsq : 3 * (r + 2 * m) < p * p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hQ0) hqN
  have hm2 : 2 * m ≤ r := border_two_m_le cs hcs hcs1 hr hr0
  obtain ⟨⟨jA, eA, hjA0, hjA3, hkA0, hkAp⟩, ⟨jB, eB, hjB0, hjB2, hkB0, hkBp⟩⟩ :=
    (planeBundle σ a b c h0).roots_facts hroots
  have eA' : 3 * kv 0 = jA * p + σ.rho := eA
  have hG : GLE p (tropVal (HW ((planeBundle σ a b c h0).inst r m).lev p r m))
      ((AltEven cs hcs (planeFrame σ a b c h0) depth).Q i) :=
    (planeBundle σ a b c h0).gle_trop cs hcs depth i hr hr0 p (by omega) hsq
  have hlow : ∀ c' : ℕ, ((planeBundle σ a b c h0).inst r m).lev p c' = 0 ↔ c' < min (kv 0) (kv 1) :=
    fun c' => plane_lev_zero_iff σ a b c h0 (Fact.out) (by omega) eA' eB hkA0 hkAp hkB0 hkBp c'
  have hh : ∀ c' : ℕ, p ≤ c' → 0 < ((planeBundle σ a b c h0).inst r m).lev p c' :=
    fun c' hc' => plane_lev_high σ a b c h0 (by omega) hc'
  simp only [planeTrop, List.mem_cons, List.not_mem_nil, or_false] at hbr
  rcases hbr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hG.mono (XGm_D1 _ _ _ _), by simp only [kbD1, KExpr.evalN, zero_mul, add_zero]; exact le_refl _⟩
  · refine ⟨_, hG.mono (val_D1x (lev := ((planeBundle σ a b c h0).inst r m).lev) p r hp2 (by omega) m), ?_⟩
    simp only [kbD1x, kb2rm, KExpr.evalN, zero_mul, add_zero]
    exact le_refl _
  · -- D2
    have hc1 := hcond ⟨0, 1, -2, [0, 0], -1, false⟩ (by simp [kbD2])
    have hc2 := hcond ⟨1, -1, 0, [0, 0], 0, false⟩ (by simp [kbD2])
    simp only [KCond.Holds, KCond.L, dot] at hc1 hc2
    norm_num at hc1 hc2
    obtain ⟨u, L, h1, h2, h3, h4, h5⟩ := val_D2 (lev := ((planeBundle σ a b c h0).inst r m).lev) p r m
      (min (kv 0) (kv 1)) (by omega) hh (by omega) (by omega) (by omega) hlow
    refine ⟨_, hG.mono h5, ?_⟩
    simp only [kbD2, kb2rm, kbX, kbK, KExpr.evalN, zero_mul, add_zero]
    omega
  · -- D45
    have hc1 := hcond ⟨-1, 1, 0, [0, 0], -1, false⟩ (by simp [kbD45])
    simp only [KCond.Holds, KCond.L, dot] at hc1
    norm_num at hc1
    refine ⟨_, hG.mono (val_D45 (lev := ((planeBundle σ a b c h0).inst r m).lev) p r m (min (kv 0) (kv 1))
      (by omega) (by omega) hlow), ?_⟩
    simp only [kbD45, kbK, KExpr.evalN, zero_mul, add_zero]
    exact le_refl _
  · -- D6
    have hc1 := hcond ⟨-1, 1, -2, [0, 0], 0, false⟩ (by simp [kbD6])
    have hc2 := hcond ⟨-1, 0, 0, [1, 0], 0, false⟩ (by simp [kbD6])
    have hc3 := hcond ⟨-1, 0, 0, [0, 1], 0, false⟩ (by simp [kbD6])
    simp only [KCond.Holds, KCond.L, dot] at hc1 hc2 hc3
    norm_num at hc1 hc2 hc3
    refine ⟨_, hG.mono (val_D6 (lev := ((planeBundle σ a b c h0).inst r m).lev) p r m (min (kv 0) (kv 1))
      (by omega) (by omega) hlow), ?_⟩
    simp only [kbD6, kbK, KExpr.evalN, zero_mul, add_zero]
    exact le_refl _
  · -- T0
    have hc1 := hcond ⟨-1, 0, -2, [1, 0], 0, true⟩ (by simp [kbT0])
    have hc2 := hcond ⟨-1, 0, -2, [0, 1], 0, true⟩ (by simp [kbT0])
    simp only [KCond.Holds, KCond.L, dot] at hc1 hc2
    norm_num at hc1 hc2
    have hv := val_D6 (lev := ((planeBundle σ a b c h0).inst r m).lev) p r m (min (kv 0) (kv 1))
      (by omega) (by omega) hlow
    refine ⟨0, hG.mono (by omega), ?_⟩
    simp only [kbT0, KExpr.evalN, zero_mul, add_zero]
    exact le_refl _

end TropValid

/-! ### The catalogue and the small primes -/

section Catalogue

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

/-- A branch of the plane catalogue: a tropical branch of `planeTrop` or a prefix branch. -/
def PlaneBranch (br : KBranch) : Prop :=
  br ∈ planeTrop ∨ ∃ n j0 j1 j2 : ℕ, br = kbrPre n j0 [j1, j2]

/-- **Every catalogue made of plane branches is valid** (P106, P107), for every plane frame at once. -/
theorem plane_cat_valid (cs : ℚ) (hcs : 0 < cs) (hcs1 : cs ≤ 1) (depth Q0 Pbad N0 : ℕ) (hQ0 : 3 ≤ Q0)
    (hP : 6 ≤ Pbad) (cat : List KBranch) (hcat : ∀ br ∈ cat, PlaneBranch br) :
    KCatValid cs hcs (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0 Pbad N0
      cat := by
  intro br hbr
  rcases hcat br hbr with h | ⟨n, j0, j1, j2, rfl⟩
  · exact plane_trop_valid σ a b c h0 cs hcs hcs1 depth Q0 Pbad N0 hQ0 hP br h
  · exact (planeBundle σ a b c h0).prefix_valid cs hcs depth Q0 Pbad N0 n j0 j1 j2 hQ0 hP
      _ (List.mem_singleton_self _)

/-- **The small-prime prefix bound of the plane frames** (P108, `PreValid`): for `p ∤ 6` with `p ≤ r / 68`
some clearing exponent is at most `(5/2) r + X r p`, `X` the budget `sqrtLog 5 10 + unit`. -/
theorem plane_preValid (depth : ℕ) :
    PreValid planeC planeC_pos (planeFrame σ a b c h0) depth 6
      (SmallBudget.add (SmallBudget.sqrtLog 5 10) SmallBudget.unit) (1 / 68) (5 / 2) := by
  intro i hi p hpf hpM h
  have hp : p.Prime := Fact.out
  have e1 : (((1 / 68 : ℚ)) : ℝ) = ((1 : ℕ) : ℝ) / ((68 : ℕ) : ℝ) := by norm_num
  rw [e1, floor_frac 1 68 i.1] at h
  have h68 : 68 * p ≤ i.1 := by omega
  have h5 : 5 ≤ p := by
    have h2 : p ≠ 2 := fun h => hpM (by rw [h]; norm_num)
    have h3 : p ≠ 3 := fun h => hpM (by rw [h]; norm_num)
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    have := hp.two_le
    omega
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := plane_border (r := i.1) hr2
  have hR : (12 * (altGeom planeC planeC_pos).borderSize i.1 : ℝ) < i.1 + 6 := by exact_mod_cast hb2
  obtain ⟨n, hn, hle⟩ := (planeBundle σ a b c h0).pre_gle planeC planeC_pos depth i hr2 (by omega) p h5
    5 10 3 (5 / 2) (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : (((5 / 2 : ℚ)) : ℝ) = 5 / 2 := by norm_num
  rw [e2]
  exact hle

/-- Monotonicity of `PreValid`: a larger modulus (with `6 ∣ M'`), a smaller `t₀`, a larger `α₀`. -/
theorem PreValid_mono {c : ℚ} {hc : 0 < c} {Fr : Frame} {depth : ℕ} {B : SmallBudget} {t0 t0' α α' : ℚ}
    {M M' : ℕ} (hM : M ∣ M') (ht : t0' ≤ t0) (hα : α ≤ α')
    (h : PreValid c hc Fr depth M B t0 α) : PreValid c hc Fr depth M' B t0' α' := by
  intro i hi p hpf hpM hp
  have hpM' : ¬ p ∣ M := fun hd => hpM (hd.trans hM)
  have hp' : p ≤ ⌊(t0 : ℝ) * i.1⌋₊ := by
    refine hp.trans (Nat.floor_le_floor ?_)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (Nat.cast_nonneg _)
  obtain ⟨n, hn, hb⟩ := h i hi p hpM' hp'
  refine ⟨n, hn, hb.trans ?_⟩
  have : (α : ℝ) * i.1 ≤ (α' : ℝ) * i.1 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hα) (Nat.cast_nonneg _)
  linarith

end Catalogue

/-! ### The content theorem (P109) -/

section ContentThm

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

/-- The crude-exponent frame constant of a plane frame reads the shifts only: `≤ 23`. -/
theorem cFr_plane : cFr (planeFrame σ a b c h0) ≤ 23 := by
  have e : cFr (planeFrame σ a b c h0) = cFr (planeFrame σ 1 1 (-2) (by norm_num)) := rfl
  rw [e]
  cases σ <;> decide +kernel

/-- **The scaled content of the plane family** (P109), for every plane frame at once: a bank `kd` that passes
`kcheck`, has the shifts `[(3, ρ, 1), (2, 1, 1)]` of the support, `c = 2 α = 1/6`, a catalogue of plane branches,
`Q ≥ 3`, `P_bad ≥ 6`, `6 ∣ M`, `t₀ ≤ 1/68`, `α₀' ≥ 5/2`, `c_F ≥ 23`, gives
`HasScaledContent (AltEven (1/6) Fr depth) scale Λ` with `Λ = kd.Λ`, whatever the weights are. -/
theorem plane_content (kd : KBankData) (hkd : kcheck kd = true)
    (hshifts : kd.shifts = (planeBundle σ a b c h0).shifts) (hα : planeC = 2 * kd.α)
    (hcat : ∀ br ∈ kd.kcat, PlaneBranch br) (hQ : 3 ≤ kd.Q) (hP : 6 ≤ kd.Pbad) (hM : 6 ∣ kd.M)
    (ht0 : kd.t0 ≤ 1 / 68) (hα0 : 5 / 2 ≤ kd.α0b) (hcF : 23 ≤ kd.cF) (depth : ℕ)
    (hdepth : depth ≤ kd.depth) :
    HasScaledContent (AltEven planeC planeC_pos (planeFrame σ a b c h0) depth)
      (altGeom planeC planeC_pos).scale (kd.Λ : ℝ) := by
  refine hasScaledContent_of_kcheck kd hkd planeC planeC_pos planeC_le_one hα (planeFrame σ a b c h0)
    depth hdepth ((cFr_plane σ a b c h0).trans hcF)
    (SmallBudget.add (SmallBudget.sqrtLog 5 10) SmallBudget.unit) 0 ?_ ?_
  · rw [hshifts]
    exact plane_cat_valid σ a b c h0 planeC planeC_pos planeC_le_one depth kd.Q kd.Pbad 0 hQ hP kd.kcat hcat
  · exact PreValid_mono hM ht0 hα0 (plane_preValid σ a b c h0 depth)

end ContentThm

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.plane_trop_valid
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_cat_valid
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_preValid
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_content
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_lev_zero_iff
