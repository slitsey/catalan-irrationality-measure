import CatalanCore.Uniform.Bank.FifthsContent.AutoData
import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
import CatalanFrames.Fifths.ContentHyb
import CatalanCore.Uniform.Bank.Fifths.Final
import CatalanCore.Uniform.Bank.Fifths.Frame
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false

/-! # Automatic content of the four fifths frames (lane C1L)

The content of `fifths1 … fifths4` (members `a = 1 … 4`, offsets `u = 5 - a`) from the one bank check
(`hasScaledContent_of_check`):

* data: `AutoData.bankData` (C1's generated UF template, `n = 100`), `bank_check : check bankData = true`;
* instance hypotheses: `fifths_catValid` (`catValid_bankUF` at `fifthsInst T`, `fifths_arithmetic T`,
  `fifths_levels T`, two-term data of `ShiftData`, norm `25`, bad primes `{2, 3, 5}`, good primes `p ≥ 7`,
  `P_bad = 9`, `K = 9`, `N1 = 50`) and `fifths_preValid` (`pre_gle_any`, `p ≤ r/900`, `α0 = 20/9`);
* `fifthsK_content_auto`: `HasScaledContent ((F5.family fifthsK depth).restrictAdm even) F5.scale Λ_fin`,
  `Λ_fin = bankData.Λ` (`bankData_Λ`), for every depth `≤ 64`;
* `fifths_mu_le : c5 / (D5 - Λ_fin) ≤ 59983/2500` (`D5`, `c5` of `Bank/Fifths/Final`). -/

namespace CatalanCore.Uniform.Bank.FifthsContent.Auto
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.RankProducer
  CatalanCore.Uniform.Content.Smith
open CatalanFrames.Fifths hiding fifths1 fifths2 fifths3 fifths4

/-! ### Instance hypotheses of the fifths frames -/

theorem fifths1_shift : ShiftData fifths1 5 4 := CatalanFrames.Fifths.fifths1_data
theorem fifths2_shift : ShiftData fifths2 5 3 := CatalanFrames.Fifths.fifths2_data
theorem fifths3_shift : ShiftData fifths3 5 2 := CatalanFrames.Fifths.fifths3_data
theorem fifths4_shift : ShiftData fifths4 5 1 := CatalanFrames.Fifths.fifths4_data

/-- The two-term data of a fifths frame (`q = 5`, `o = u`). -/
theorem shift_twoTerm {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) : TwoTermData Fr 5 u where
  o_pos := T.hu0
  o_lt := T.hu1
  delta_eq t ht := by
    rw [T.delta t (by omega), cast_linear (k := t) T.hu1 (by omega)]
  dsq_eq t ht := by
    rw [T.dsq t (by omega), cast_linear (k := t) T.hu1 (by omega)]

theorem cFr_fifths1 : cFr fifths1 ≤ 49 := by decide +kernel
theorem cFr_fifths2 : cFr fifths2 ≤ 49 := by decide +kernel
theorem cFr_fifths3 : cFr fifths3 ≤ 49 := by decide +kernel
theorem cFr_fifths4 : cFr fifths4 ≤ 49 := by decide +kernel

/-- The branch catalogue of `bankData` is valid on every fifths frame (`ShiftData Fr 5 u`, `o = u`). -/
theorem fifths_catValid {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) :
    CatValid (2 / 9) two_ninths_pos Fr depth 5 u 9 (max (NFr (1 / Fr.norm) (-1 / Fr.norm) 5 9) 50)
      bankData.cat := by
  have hu0 := T.hu0
  have hu1 := T.hu1
  exact catValid_bankUF (fifthsInst T) (fifths_arithmetic T).L_eq (fifths_levels T) (2 / 9) two_ninths_pos
    (by norm_num) (shift_twoTerm T) (nm := 5 * 5) (by rw [T.norm_eq]; norm_num) depth 9 9 50
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega, by omega,
      not_bad_of_levels (fifths_levels T) hp (show 7 ≤ p by omega), (show 7 ≤ p by omega), by omega⟩)
    (fun p hp h j k hk hj0 hjq _ _ => by
      have h7 : 7 ≤ p := by omega
      have hb := (fifths_good T hp h7).2
      obtain ⟨h1, -⟩ := kq_eq_poleIndex (fifthsCD T) (fun _ => rfl) (by omega) (by omega) hp (by omega) hb
        (fifths_kq_att T p hp.isPrimePow hb)
      have hk' : 5 * k = j * p + (5 - (5 - u)) := by rw [show 5 - (5 - u) = u by omega]; exact hk
      have h2 := (rootClass_unique hp (by omega) (by omega) (by omega) hjq hk').2
      show (fifthsCD T).kq p = k
      rw [h1, h2])
    [(5, 5), (5, 6), (6, 6), (6, 7), (7, 7), (7, 8), (8, 8), (8, 9), (9, 9), (9, 10)]

/-- The prefix bound of every fifths frame (`pre_gle_any`), for `p ≤ r/900`, `α0 = 20/9`. -/
theorem fifths_preValid {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PreValid (2 / 9) two_ninths_pos Fr depth 10 (SmallBudget.add (SmallBudget.sqrtLog 7 122) SmallBudget.unit)
      (qq 1 900) (qq 20 9) := by
  intro i hi p _ _ h
  have hp : p.Prime := Fact.out
  have e1 : ((qq 1 900 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((900 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 1 900 i.1] at h
  have h900 : 900 * p ≤ i.1 := by omega
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (2 / 9) two_ninths_pos 2 9 (by norm_num) (by norm_num) hr2
  have hR : (9 : ℝ) * (2 * ((altGeom (2 / 9) two_ninths_pos).borderSize i.1 : ℝ)) < 2 * i.1 + 9 := by
    exact_mod_cast hb2
  have hbad : p ∈ (fifthsInst T).cd.bad → p * p ≤ 7 * i.1 := by
    intro hpb
    have hp5 : p ≤ 5 := by
      simp [fifthsInst, HybInst.ofSing, fifthsCD, badPrimes] at hpb
      omega
    have : p * p ≤ 5 * 5 := Nat.mul_le_mul hp5 hp5
    omega
  obtain ⟨n, hn, hle⟩ := pre_gle_any (fifthsInst T) (fifths_arithmetic T).L_eq (2 / 9) two_ninths_pos
    (by norm_num) depth i hr2 (by omega) p 7 122 3 49 (20 / 9) (by norm_num) hcF (by norm_num) hbad
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 20 9 : ℚ) : ℝ) = 20 / 9 := by norm_num [qq]
  rw [e2]
  exact hle

/-! ### The content of the four fifths frames -/

/-- **Automatic content of `fifths1`** (member `a = 1`, `u = 4`). -/
theorem fifths1_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent ((F5.family fifths1 depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (2 / 9) two_ninths_pos (by norm_num) (by decide +kernel)
    fifths1 depth hd cFr_fifths1 1 (by decide) _ _ (fifths_catValid fifths1_shift depth)
    (fifths_preValid fifths1_shift depth cFr_fifths1)

/-- **Automatic content of `fifths2`** (member `a = 2`, `u = 3`). -/
theorem fifths2_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent ((F5.family fifths2 depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (2 / 9) two_ninths_pos (by norm_num) (by decide +kernel)
    fifths2 depth hd cFr_fifths2 2 (by decide) _ _ (fifths_catValid fifths2_shift depth)
    (fifths_preValid fifths2_shift depth cFr_fifths2)

/-- **Automatic content of `fifths3`** (member `a = 3`, `u = 2`). -/
theorem fifths3_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent ((F5.family fifths3 depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (2 / 9) two_ninths_pos (by norm_num) (by decide +kernel)
    fifths3 depth hd cFr_fifths3 3 (by decide) _ _ (fifths_catValid fifths3_shift depth)
    (fifths_preValid fifths3_shift depth cFr_fifths3)

/-- **Automatic content of `fifths4`** (member `a = 4`, `u = 1`). -/
theorem fifths4_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent ((F5.family fifths4 depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (2 / 9) two_ninths_pos (by norm_num) (by decide +kernel)
    fifths4 depth hd cFr_fifths4 4 (by decide) _ _ (fifths_catValid fifths4_shift depth)
    (fifths_preValid fifths4_shift depth cFr_fifths4)

/-- **The fifths μ target**: `c5 / (D5 - Λ_fin) ≤ 59983/2500` with the finite UF constant `Λ_fin = bankData.Λ`. -/
theorem fifths_mu_le : (c5 : ℝ) / ((D5 : ℝ) - (bankData.Λ : ℝ)) ≤ ((59983 / 2500 : ℚ) : ℝ) := by
  have h1 : bankData.Λ < D5 := by rw [bankData_Λ]; unfold D5; norm_num
  have h2 : c5 ≤ 59983 / 2500 * (D5 - bankData.Λ) := by rw [bankData_Λ]; unfold c5 D5; norm_num
  have hpos : (0 : ℝ) < (D5 : ℝ) - (bankData.Λ : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 h1; linarith
  rw [div_le_iff₀ hpos]
  have h3 := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at h3 ⊢
  linarith

#print axioms fifths1_content_auto
#print axioms fifths2_content_auto
#print axioms fifths3_content_auto
#print axioms fifths4_content_auto
#print axioms fifths_mu_le
#print axioms bank_check
#print axioms bankData_Λ

end CatalanCore.Uniform.Bank.FifthsContent.Auto
