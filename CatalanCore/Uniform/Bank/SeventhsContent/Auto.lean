module

public import CatalanCore.Uniform.Bank.SeventhsContent.AutoData
public import CatalanCore.Uniform.Content.BankShared.Inst.Sevenths
public import CatalanCore.Uniform.Bank.Sevenths.Final
public import CatalanCore.Arith.Hybrid.PieceTools
public import CatalanCore.Uniform.Content.BankShared.Check.Prefix

@[expose] public section
set_option Elab.async false

/-! # Automatic content of the six sevenths frames (lane C1L)

The content of `seventhsFrameAt a` (members `a + 1 = 1 … 6`, offsets `o = 7 - (a + 1)`) from the one bank check
(`hasScaledContent_of_check`):

* data: `AutoData.bankData` (C1's generated UF template, prefix truncation `n = 100`, LP2 widened, prefix branches `n ≤ 8`),
  `bank_check : check bankData = true`;
* instance hypotheses: `sevenths_catValid` (`catValid_bankUFwP` at `seventhsInst a`, `P_bad = 13`, `K = 12`,
  `N1 = 91`, windows `(6,6) … (12,13)`, prefix branches `bankPres`) and `sevenths_preValid` (`pre_gle_any` at `seventhsInst a`,
  `p ≤ r/1000`, `α0 = 13/6`);
* `sevenths_content_auto a`: `HasScaledContent ((F7.family (seventhsFrameAt a) depth).restrictAdm even) F7.scale
  Λ_fin`, `Λ_fin = bankData.Λ` (`bankData_Λ`), every depth `≤ 64`;
* `sevenths_mu_le : c7 / (D7 - Λ_fin) ≤ 2801` ( `D7`, `c7` of `Bank/Sevenths/Final`), exact. -/

namespace CatalanCore.Uniform.Bank.SeventhsContent.Auto
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.BankShared.Inst CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith
  CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Bank.Sevenths (F7 one_sixth_pos seventhsFrameAt seventhNumerator D7 c7 sevenths_twoTerm)

/-! ### Instance hypotheses of the sevenths frames -/

theorem cFr_sevenths : ∀ a : Fin 6, cFr (seventhsFrameAt a) ≤ 81 := by decide +kernel

theorem sevenths_mem (a : Fin 6) : seventhNumerator a ∈ bankData.members := by
  fin_cases a <;> decide

/-- The branch catalogue of `bankData` is valid on every sevenths frame. -/
theorem sevenths_catValid (a : Fin 6) (depth : ℕ) :
    CatValid (1 / 6) one_sixth_pos (seventhsFrameAt a) depth 7 (7 - seventhNumerator a) 13
      (max (NFr (1 / (seventhsFrameAt a).norm) (-1 / (seventhsFrameAt a).norm) 7 12) 91) bankData.cat :=
  by
  rw [bankData_cat]
  exact catValid_bankUFwP (seventhsInst a) (seventhsInst_L a) (seventhsInst_levels a) (1 / 6) one_sixth_pos
    (by norm_num) (sevenths_twoTerm a) (nm := 7 * 7) (seventhsInst_norm a) depth 13 12 91
    (by norm_num) (by norm_num) (by norm_num) le_rfl (seventhsInst_hP a (by omega))
    (seventhsInst_hkq a (by omega)) bankWins bankPres

/-- The prefix bound of every sevenths frame (`pre_gle_any`), for `p ≤ r/1000`, `α0 = 13/6`. -/
theorem sevenths_preValid (a : Fin 6) (depth : ℕ) :
    PreValid (1 / 6) one_sixth_pos (seventhsFrameAt a) depth 14
      (SmallBudget.add (SmallBudget.sqrtLog 9 186) SmallBudget.unit) (qq 1 1000) (qq 13 6) := by
  intro i hi p _ _ h
  have hp : p.Prime := Fact.out
  have e1 : ((qq 1 1000 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 1 1000 i.1] at h
  have h1000 : 1000 * p ≤ i.1 := by omega
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (1 / 6) one_sixth_pos 1 6 (by norm_num) (by norm_num) hr2
  have hR : (6 : ℝ) * (2 * ((altGeom (1 / 6) one_sixth_pos).borderSize i.1 : ℝ)) < 1 * i.1 + 6 := by
    exact_mod_cast hb2
  have hbad : p ∈ (seventhsInst a).cd.bad → p * p ≤ 9 * i.1 := by
    intro hpb
    have hp7 : p ≤ 7 := seventhsInst_bad_le a hpb
    have : p * p ≤ 7 * 7 := Nat.mul_le_mul hp7 hp7
    omega
  obtain ⟨n, hn, hle⟩ := pre_gle_any (seventhsInst a) (seventhsInst_L a) (1 / 6) one_sixth_pos
    (by norm_num) depth i hr2 (by omega) p 9 186 4 81 (13 / 6) (by norm_num) (cFr_sevenths a) (by norm_num) hbad
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 13 6 : ℚ) : ℝ) = 13 / 6 := by norm_num [qq]
  rw [e2]
  exact hle

/-! ### The content of the six sevenths frames -/

/-- **Automatic content of `seventhsFrameAt a`** (member `a + 1`), every depth `≤ 64`. -/
theorem sevenths_content_auto (a : Fin 6) (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent ((F7.family (seventhsFrameAt a) depth).restrictAdm (fun i => i.1 % 2 = 0)) F7.scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (1 / 6) one_sixth_pos (by norm_num) (by decide +kernel)
    (seventhsFrameAt a) depth hd (cFr_sevenths a) (seventhNumerator a) (sevenths_mem a) _ _
    (sevenths_catValid a depth) (sevenths_preValid a depth)

/-- **The sevenths μ target**, exactly: `c7 / (D7 - Λ_fin) ≤ 2801` with the finite UF constant
`Λ_fin = bankData.Λ`. -/
theorem sevenths_mu_le : (c7 : ℝ) / ((D7 : ℝ) - (bankData.Λ : ℝ)) ≤ ((2801 : ℚ) : ℝ) := by
  have h1 : bankData.Λ < D7 := by rw [bankData_Λ]; unfold D7; norm_num
  have h2 : c7 ≤ 2801 * (D7 - bankData.Λ) := by rw [bankData_Λ]; unfold c7 D7; norm_num
  have hpos : (0 : ℝ) < (D7 : ℝ) - (bankData.Λ : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 h1; linarith
  rw [div_le_iff₀ hpos]
  have h3 := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at h3 ⊢
  linarith

#print axioms sevenths_content_auto
#print axioms sevenths_mu_le
#print axioms bank_check
#print axioms bankData_Λ

end CatalanCore.Uniform.Bank.SeventhsContent.Auto
