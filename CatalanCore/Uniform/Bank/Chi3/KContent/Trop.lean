module

public import CatalanCore.Uniform.Bank.Chi3.KContent.Data.Head
public import CatalanCore.Uniform.Content.BankShared.KTerm.Content
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
public import CatalanFrames.P6Hybrid.ZDual
public import CatalanFrames.P6Hybrid.Level

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The tropical branches of chi_{-3} on the k-shift route: `D1, D1x, Z0, Z1, T0` (lane K)

Adapters from the old P6 lemmas to `KCatValid`:

* `p6_gle_trop`: at a prime `p ≥ 5` with `3 N < p²`, every member of `AltEven c p6Frame` is `p ^ tropVal (HW lev p r m)`-integral
  for the P6 instance `p6Inst r m` of the scale (the T-layer bridge `T_gle` of `TwoTerm.Trop`, with the instance at `(r, m)`
  since `p6Inst` depends on them);
* `D1` (`trop_D1`), `D1x` (`val_D1x`), `Z0`, `Z1` (`p6_trop_Z`, the `Sv` count with `k_q = min (k_A, k_B)`) and the
  tail branch `T0` (price `0` when `N < k_A, k_B`, `Sv = 2r + 2m`).

The pole indices are the roots of the shifts `3 k_A = j p + 2`, `2 k_B = j' p + 1` (`p6_roots`: `k_B = (p + 1)/2`,
`k_A = (p + 2)/3` for `p ≡ 1 (6)`, `(2 p + 2)/3` for `p ≡ 5 (6)`). -/

namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.KTerm
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanFrames.P6 CatalanFrames.P6Hybrid CatalanCore.Rect

theorem c12_pos : (0 : ℚ) < 1 / 2 := by norm_num

/-- **The tropical bridge at the instance `p6Inst r m`.** -/
theorem p6_gle_trop (c : ℚ) (hc : 0 < c) (depth : ℕ) (i : ((altGeom c hc).family p6Frame depth).ι)
    (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hsq : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p) :
    GLE p (tropVal (HW (p6Inst i.1 ((altGeom c hc).borderSize i.1)).lev p i.1
      ((altGeom c hc).borderSize i.1))) (((altGeom c hc).family p6Frame depth).Q i) := by
  obtain ⟨r, S⟩ := i
  set m := (altGeom c hc).borderSize r with hm
  haveI := p6Inst_diagOK r m
  have hQ := altGeom_member_commonMinor c hc p6Frame depth hr S
  have hG0 := commonMinorPoly_gle (p6Inst r m) p r m (retainedFin (altGeom_hybShape c hc hr) S)
  have hG : GLE p (tropExp (p6Inst r m) r m p) (((altGeom c hc).family p6Frame depth).Q ⟨r, S⟩) := hQ ▸ hG0
  have hbad : p ∉ (p6Inst r m).cd.bad := by
    intro hb
    have := (p6_badInfo r m).bad_le p hb
    omega
  have hcnt : cntG (p6Inst r m) r m p = 0 := by
    apply cntG_zero _ _ _ _ hp.out
    rw [(p6_badInfo r m).L_eq, pow_two]
    exact hsq
  have hle := tropExp_le_good (p6Inst r m) r m p hr1 hp.out hbad
  rw [hcnt] at hle
  simp only [Nat.cast_zero, mul_zero, zero_add] at hle
  have hle' : tropExp (p6Inst r m) r m p ≤ tropVal (HW (p6Inst r m).lev p r m) := by
    exact_mod_cast hle
  exact hG.mono hle'

/-- The roots of the two shifts of chi_{-3} at a prime `p ≡ ±1 (6)`. -/
theorem p6_roots {p k0 k1 : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) (h7 : 7 ≤ p)
    (h0 : ∃ j, 3 * k0 = j * p + 2 ∧ 0 < j ∧ j < 3 ∧ 0 < k0 ∧ k0 < p)
    (h1 : ∃ j, 2 * k1 = j * p + 1 ∧ 0 < j ∧ j < 2 ∧ 0 < k1 ∧ k1 < p) :
    k1 = (p + 1) / 2 ∧ (p % 6 = 1 → k0 = (p + 2) / 3) ∧ (p % 6 = 5 → k0 = (2 * p + 2) / 3) := by
  obtain ⟨j0, e0, a0, b0, -, -⟩ := h0
  obtain ⟨j1, e1, a1, b1, -, -⟩ := h1
  have hj1 : j1 = 1 := by omega
  subst hj1
  refine ⟨by omega, fun h => ?_, fun h => ?_⟩
  · interval_cases j0 <;> omega
  · interval_cases j0 <;> omega

/-- `min (k_A, k_B) = k_q6`, and `Sv` against the expression `kSv0`, `kSv1`. -/
theorem p6_kq {p k0 k1 : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) (h7 : 7 ≤ p)
    (h0 : ∃ j, 3 * k0 = j * p + 2 ∧ 0 < j ∧ j < 3 ∧ 0 < k0 ∧ k0 < p)
    (h1 : ∃ j, 2 * k1 = j * p + 1 ∧ 0 < j ∧ j < 2 ∧ 0 < k1 ∧ k1 < p) :
    min k0 k1 = kq6 p ∧ k1 = (p + 1) / 2 := by
  obtain ⟨e1, e0a, e0b⟩ := p6_roots hp h7 h0 h1
  refine ⟨?_, e1⟩
  unfold kq6
  rcases hp with h | h
  · rw [if_pos h, e0a h, e1]; omega
  · rw [if_neg (by omega), e0b h, e1]; omega

theorem evalN_kSv0 (r p m : ℕ) (kv : ℕ → ℕ) :
    kSv0.evalN r p m kv = (min (min (kv 0) (kv 1)) r - (r - p)) + (min (min (kv 0) (kv 1)) r - (r + 2 * m - p)) +
      (min (min (kv 0) (kv 1)) (r + 2 * m) - max (r + 2 * m - p) r) := rfl

theorem evalN_kSv1 (r p m : ℕ) (kv : ℕ → ℕ) :
    kSv1.evalN r p m kv = kSv0.evalN r p m kv +
      (min p (r + 2 * m) - max (max (kv 1) (r + 2 * m - p)) r) := rfl

/-- The branch theorems of `D1, D1x, Z0, Z1, T0`. -/
theorem kcat_trop_valid (depth : ℕ) (N0 : ℕ) :
    KCatValid (1 / 2) c12_pos p6Frame depth kShifts 6 6 N0 [kD1, kD1x, kZ0, kZ1, kT0] := by
  intro b hb i hi hr0 p _ hPb _ hqN kv hroots hcond
  have hr := hi.2
  have h7 : 7 ≤ p := by omega
  set r := i.1 with hrdef
  set m := (altGeom (1 / 2) c12_pos).borderSize r with hmdef
  have hp3 : p % 2 = 1 := by
    have := (Fact.out : p.Prime).eq_one_or_self_of_dvd 2
    by_contra h
    have h2 : 2 ∣ p := by omega
    rcases this h2 with h | h <;> omega
  have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by
    have h3 : p % 3 ≠ 0 := by
      intro h
      have h3 : 3 ∣ p := by omega
      rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 3 h3 with h | h <;> omega
    omega
  have hsq : 3 * (r + 2 * m) < p * p := by omega
  have hG : GLE p (tropVal (HW (p6Inst r m).lev p r m)) ((AltEven (1 / 2) c12_pos p6Frame depth).Q i) :=
    p6_gle_trop (1 / 2) c12_pos depth i hr hr0 p (by omega) hsq
  have hr0' : (0 : ℕ) < kShifts.length := by decide
  have hk0 := hroots 0 (by decide)
  have hk1 := hroots 1 (by decide)
  have hkk := p6_kq hp6 h7 (by simpa [kShifts, KTerm.shAt] using hk0) (by simpa [kShifts, KTerm.shAt] using hk1)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hG.mono (XGm_D1 _ _ _ _), by simp only [kD1, KExpr.evalN, zero_mul, add_zero]; exact le_refl _⟩
  · refine ⟨_, hG.mono (val_D1x (lev := (p6Inst r m).lev) p r hp3 (by omega) m), ?_⟩
    simp only [kD1x, k2rm, KExpr.evalN, zero_mul, add_zero]
    exact le_refl _
  · -- Z0
    have hc1 := hcond ⟨-1, 2, -2, [0, 0], 0, false⟩ (by simp [kZ0])
    simp only [KCond.Holds, KCond.L, dot] at hc1
    norm_num at hc1
    have hN : r + 2 * m ≤ 2 * p := by omega
    have hZ := p6_trop_Z (r := r) (m := m) (Fact.out) (by omega) hp6 hN
    refine ⟨2 * r + 2 * m - Sv r m p, hG.mono (by omega), ?_⟩
    have e1 := hkk.1
    simp only [kZ0, k2rm, KExpr.evalN, zero_mul, add_zero, evalN_kSv0, e1]
    unfold Sv
    split_ifs <;> omega
  · -- Z1
    have hc1 := hcond ⟨-1, 2, -2, [0, 0], 0, false⟩ (by simp [kZ1])
    have hc2 := hcond ⟨0, 0, 0, [-1, 1], -1, false⟩ (by simp [kZ1])
    simp only [KCond.Holds, KCond.L, dot] at hc1 hc2
    norm_num at hc1 hc2
    have hN : r + 2 * m ≤ 2 * p := by omega
    have hZ := p6_trop_Z (r := r) (m := m) (Fact.out) (by omega) hp6 hN
    refine ⟨2 * r + 2 * m - Sv r m p, hG.mono (by omega), ?_⟩
    have e1 := hkk.1
    have e2 := hkk.2
    obtain ⟨-, ea, eb⟩ := p6_roots hp6 h7 (by simpa [kShifts, KTerm.shAt] using hk0) (by simpa [kShifts, KTerm.shAt] using hk1)
    have hp1 : p % 6 = 1 := by
      rcases hp6 with h | h
      · exact h
      · have := eb h; omega
    simp only [kZ1, k2rm, KExpr.evalN, zero_mul, add_zero, evalN_kSv1, evalN_kSv0, e1, e2]
    unfold Sv
    split_ifs <;> omega
  · -- T0
    have hc1 := hcond ⟨-1, 0, -2, [1, 0], 0, true⟩ (by simp [kT0])
    have hc2 := hcond ⟨-1, 0, -2, [0, 1], 0, true⟩ (by simp [kT0])
    simp only [KCond.Holds, KCond.L, dot] at hc1 hc2
    norm_num at hc1 hc2
    have hk0p : kv 0 < p := by
      obtain ⟨j, -, -, -, -, h⟩ := hk0
      exact h
    have hN : r + 2 * m ≤ 2 * p := by omega
    have hZ := p6_trop_Z (r := r) (m := m) (Fact.out) (by omega) hp6 hN
    refine ⟨2 * r + 2 * m - Sv r m p, hG.mono (by omega), ?_⟩
    have e1 := hkk.1
    simp only [kT0, KExpr.evalN, zero_mul, add_zero]
    unfold Sv
    split_ifs <;> omega

end CatalanCore.Uniform.Bank.Chi3.KContent
