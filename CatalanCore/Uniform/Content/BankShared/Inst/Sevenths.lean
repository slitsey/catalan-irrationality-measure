import CatalanCore.Uniform.Content.BankShared.Inst.TwoTerm
import CatalanCore.Uniform.Bank.Sevenths.TwoTerm
import CatalanCore.Uniform.Content.BankShared.Check.UF
set_option Elab.async false

/-! # The sevenths frames from the generic two-term instance (lane C6L, gap C6)

Instantiation only: `seventhsFrameAt a` (Codex, `Bank/Sevenths/Frame`, read only) with its two-term data
`sevenths_twoTerm a` (`q = 7`, `o = u = 7 - (a + 1)`) and norm `49` is `ShiftData`, so the generic
`twoTermInst` applies to all six members.

* all six members: `seventhsShift`, `seventhsInst`, `seventhsInst_levels` (good primes `p > 7`), `seventhsInst_norm`,
  `seventhsInst_hP`, `seventhsInst_hkq`, `seventhsInst_bad_le`;
* members `a + 1 ∈ {1, 2, 3, 4}` (`a.val < 4`): `seventhsInst_arithmetic : ArithmeticInfo _ 7 2`, and the catalogue
  validity `seventhsInst_catValid_bank`, `seventhsInst_catValid_bankUF` (`catValid_bank(UF)` instantiated);
* members `a + 1 ∈ {5, 6}`: `seventhsInst_not_arithmetic` (no `ArithmeticInfo` for this instance, at `N = 1`),
  and for member `5` the stronger `seventhsFive_not_arithmetic`: NO hybrid instance of `seventhsFrameAt 4`
  has `ArithmeticInfo` (`Δ₁ = -2/5` forces `Ebd 1 ≥ 5`, while `Ebd 1 + 1 ≤ Ecub 1 = 5`). -/

namespace CatalanCore.Uniform.Content.BankShared.Inst
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Basic CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.RankProducer
  CatalanFrames.HybCommon CatalanFrames.HybGen
open CatalanFrames.Fifths (ShiftData)
open CatalanCore.Uniform.Bank.Sevenths (seventhsFrameAt seventhNumerator sevenths_twoTerm)

theorem seventhsFrameAt_norm (a : Fin 6) : (seventhsFrameAt a).norm = 49 := rfl

/-- The sevenths frames as `ShiftData` (`q = 7`, `u = 7 - (a + 1)`, norm `49`). -/
theorem seventhsShift (a : Fin 6) : ShiftData (seventhsFrameAt a) 7 (7 - seventhNumerator a) :=
  shift_ofTwoTerm (by norm_num) (sevenths_twoTerm a) (by rw [seventhsFrameAt_norm]; norm_num)

/-- The hybrid instance of `seventhsFrameAt a`: the generic two-term instance at `q = 7`. -/
noncomputable abbrev seventhsInst (a : Fin 6) : HybInst (seventhsFrameAt a) :=
  twoTermInst (seventhsShift a)

/-! ### All six members -/

theorem seventhsInst_levels (a : Fin 6) :
    LevelFacts (seventhsInst a) (fun p => 7 < p) (fun Q c => c < (seventhsInst a).cd.kq Q) :=
  twoTerm_levels (seventhsShift a)

theorem seventhsInst_norm (a : Fin 6) : (seventhsFrameAt a).norm = ((7 * 7 : ℕ) : ℚ) :=
  twoTerm_norm (seventhsShift a)

theorem seventhsInst_hP (a : Fin 6) {Pbad : ℕ} (h : 13 ≤ Pbad) :
    ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ 7 * 7 ∧ 5 ≤ p ∧ 2 * 7 ≤ p ∧ p ∉ (seventhsInst a).cd.bad ∧ 7 < p ∧ p ≠ 2 :=
  twoTerm_hP (seventhsShift a) (by omega) (by omega)

theorem seventhsInst_hkq (a : Fin 6) {Pbad : ℕ} (h : 7 ≤ Pbad) :
    ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, 7 * k = j * p + (7 - seventhNumerator a) → 0 < j →
      j < 7 → 0 < k → k < p → (seventhsInst a).cd.kq p = k :=
  twoTerm_hkq (seventhsShift a) h

theorem seventhsInst_bad_le (a : Fin 6) {p : ℕ} (hp : p ∈ (seventhsInst a).cd.bad) : p ≤ 7 :=
  twoTerm_bad_le (seventhsShift a) hp

/-! ### Members `1, 2, 3, 4`: arithmetic data and the catalogue -/

theorem seventhsInst_arithmetic (a : Fin 6) (ha : a.val < 4) : ArithmeticInfo (seventhsInst a) 7 2 :=
  twoTerm_arithmetic_small (seventhsShift a) (by norm_num) (by unfold seventhNumerator; omega)
    (by norm_num)

/-- **`catValid_bank` at the sevenths members `1, …, 4`** (table T, LP1, LP2, rank, windows `wins`). -/
theorem seventhsInst_catValid_bank (a : Fin 6) (ha : a.val < 4) (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1)
    (depth Pbad K : ℕ) (hPbad : 13 ≤ Pbad) (hK : 2 ≤ c * K) (wins : List (ℕ × ℕ)) :
    CatValid c hc (seventhsFrameAt a) depth 7 (7 - seventhNumerator a) Pbad
      (NFr (1 / (seventhsFrameAt a).norm) (-1 / (seventhsFrameAt a).norm) 7 K)
      (tableT ++ ([brLP1, brLP2, brRank] ++ wins.map (fun w => brWin w.1 w.2))) :=
  catValid_bank (seventhsInst a) (seventhsInst_arithmetic a ha) (seventhsInst_levels a) c hc hc1
    (sevenths_twoTerm a) (seventhsInst_norm a) depth Pbad K hK (by norm_num) le_rfl
    (seventhsInst_hP a hPbad) (seventhsInst_hkq a (by omega)) wins

/-- **`catValid_bankUF` at the sevenths members `1, …, 4`** (with the UF branch `brS`). -/
theorem seventhsInst_catValid_bankUF (a : Fin 6) (ha : a.val < 4) (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1)
    (depth Pbad K N1 : ℕ) (hPbad : 13 ≤ Pbad) (hK : 2 ≤ c * K)
    (hN1 : ((7 : ℕ) : ℚ) * (2 + c) ≤ c * N1) (wins : List (ℕ × ℕ)) :
    CatValid c hc (seventhsFrameAt a) depth 7 (7 - seventhNumerator a) Pbad
      (max (NFr (1 / (seventhsFrameAt a).norm) (-1 / (seventhsFrameAt a).norm) 7 K) N1)
      (tableT ++ ([brLP1, brLP2, brRank, brS] ++ wins.map (fun w => brWin w.1 w.2))) :=
  catValid_bankUF (seventhsInst a) (seventhsInst_arithmetic a ha) (seventhsInst_levels a) c hc hc1
    (sevenths_twoTerm a) (seventhsInst_norm a) depth Pbad K N1 hK hN1 (by norm_num) le_rfl
    (seventhsInst_hP a hPbad) (seventhsInst_hkq a (by omega)) wins

/-! ### Members `5, 6`: the obstruction -/

/-- Members `5, 6` (`u ∈ {2, 1}`): `Ebd 1 + 1 = 8 - u > 5 = Ecub 1`, so the generic instance has no
`ArithmeticInfo`. -/
theorem seventhsInst_not_arithmetic (a : Fin 6) (ha : 4 ≤ a.val) (Lc cm : ℕ) :
    ¬ ArithmeticInfo (seventhsInst a) Lc cm :=
  twoTerm_not_arithmetic (seventhsShift a) (by unfold seventhNumerator; omega) Lc cm

/-- `1/p` is not `p`-integral. -/
theorem inv_not_mem_locRing (p : ℕ) [Fact p.Prime] : ((p : ℚ))⁻¹ ∉ LocRing p := by
  rw [mem_locRing, Rat.inv_natCast_den]
  have hp := (Fact.out : p.Prime)
  simp [hp.ne_zero]

/-- Member `5`: `Δ₁ = 1 - 7/5 = -2/5`. -/
theorem seventhsFrameAt_four_delta_one : (seventhsFrameAt 4).Delta 1 = -2 / 5 := by
  rw [(sevenths_twoTerm 4).delta_eq 1 le_rfl, show seventhNumerator 4 = 5 from rfl]
  norm_num

/-- **No-go for member `5`**: no hybrid instance of `seventhsFrameAt 4` has `ArithmeticInfo`.  If
`Ebd 1 + 1 ≤ Ecub 1 = 5`, then `Ebd 1 < 5¹`, and `off_val` at `(p, E, N, lo, hi) = (5, 0, 1, 0, 1)` (an empty
level sum) says `Δ₁ = -2/5 ∈ ℤ₍₅₎`, false. -/
theorem seventhsFive_not_arithmetic (I : HybInst (seventhsFrameAt 4)) (Lc cm : ℕ) :
    ¬ ArithmeticInfo I Lc cm := by
  intro B
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hb : I.Ebd 1 + 1 ≤ 5 := by simpa [Ecub] using B.Ebd_le 1
  have hE : I.Ebd 1 < 5 ^ (0 + 1) := by
    rw [show (5 : ℕ) ^ (0 + 1) = 5 by norm_num]
    omega
  have h := I.off_val 5 0 1 0 1 hE (by norm_num) (by norm_num) le_rfl
  have hl : levels I.lev 5 0 0 1 = 0 := by
    unfold levels
    rw [Finset.Icc_eq_empty_of_lt (by norm_num), Finset.sum_empty]
  have hI : Finset.Ioc 0 1 = ({1} : Finset ℕ) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  have key : (-2 / 5 : ℚ) ∈ LocRing 5 := by
    convert h using 1
    rw [hl, hI, Finset.sum_singleton, seventhsFrameAt_four_delta_one]
    norm_num
  have h2 : ((2 : ℕ) : ℚ) * (-2 / 5) + 1 ∈ LocRing 5 :=
    (LocRing 5).add_mem ((LocRing 5).mul_mem (natq_mem 5 2) key) (LocRing 5).one_mem
  have e : ((2 : ℕ) : ℚ) * (-2 / 5) + 1 = ((5 : ℕ) : ℚ)⁻¹ := by norm_num
  rw [e] at h2
  exact inv_not_mem_locRing 5 h2

end CatalanCore.Uniform.Content.BankShared.Inst
