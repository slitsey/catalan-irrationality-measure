module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data
public import CatalanCore.Uniform.Bank.ThirdsContent.Auto
public import CatalanCore.Uniform.Bank.Thirds.Numerics

@[expose] public section
set_option Elab.async false

/-! # Thirds acceptance test of automatic content, with UF (lane C1L)

The data `AutoUF.bankData` (C1's generated UF template, `bank_check : check bankData = true`) and the instance
hypotheses of the thirds frames (`thirds_catValidUF` = `catValid_bankUF` at the thirds instance, with
`N0 = max NFr 23`, `(3/10) · 23 ≥ 3 (2 + 3/10)`; `thirds_preValid`) give the content of both thirds frames with
`Λ_fin = bankData.Λ` (`bankData_Λ`), and the target `uf_mu_le : ctT / (DtT - Λ_fin) ≤ 47499 / 5000`. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanFrames.Thirds CatalanCore.Uniform.Bank.ThirdsContent
  CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Bank.ThirdsContent.Auto CatalanCore.Uniform.Content.RankProducer

/-- **The thirds μ target**: `c / (D - Λ_fin) ≤ 47499 / 5000` with the finite UF constant `Λ_fin = bankData.Λ`
(`DtT`, `ctT` of `Bank/Thirds/Numerics`). -/
theorem uf_mu_le : (ctT : ℝ) / ((DtT : ℝ) - (bankData.Λ : ℝ)) ≤ ((47499 / 5000 : ℚ) : ℝ) := by
  have h1 : bankData.Λ < DtT := by rw [bankData_Λ]; unfold DtT; norm_num
  have h2 : ctT ≤ 47499 / 5000 * (DtT - bankData.Λ) := by rw [bankData_Λ]; unfold ctT DtT; norm_num
  have hpos : (0 : ℝ) < (DtT : ℝ) - (bankData.Λ : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 h1; linarith
  rw [div_le_iff₀ hpos]
  have h3 := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at h3 ⊢
  linarith

/-- The branch catalogue of `bankData` is valid on every thirds frame. -/
theorem thirds_catValidUF {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ) :
    CatValid (3 / 10) c310_pos Fr depth 3 e 5 (max (NFr (1 / Fr.norm) (-1 / Fr.norm) 3 7) 23) bankData.cat := by
  have he := T.he
  rw [bankData_cat]
  apply catValid_append
  · apply catValid_append
    · exact catValid_bankUFwP (thirdsInst T) (arith_of_bad (thirds_badInfo T)).L_eq (thirds_levels T) (3 / 10)
        c310_pos (by norm_num) (ThirdsData.twoTerm T) (nm := 3 * 3) (by rw [T.norm_eq]; norm_num) depth 5 7 23
        (by norm_num) (by norm_num) (by norm_num) le_rfl
        (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega, by omega,
          not_bad_of_levels (thirds_levels T) hp (show 5 ≤ p by omega), (show 5 ≤ p by omega), by omega⟩)
        (fun p hp h j k hk hj0 hjq _ _ => by
          have h5 : 5 ≤ p := by omega
          have hb := (thirds_good T hp h5).2
          obtain ⟨h1, -⟩ := kq_eq_poleIndex (thirdsCD T) (fun _ => rfl) (by omega) (by omega) hp (by omega) hb
            (thirds_kq_att T p hp.isPrimePow hb)
          have hk' : 3 * k = j * p + (3 - (3 - e)) := by rw [show 3 - (3 - e) = e by omega]; exact hk
          have h2 := (rootClass_unique hp (by omega) (by omega) (by omega) hjq hk').2
          show (thirdsCD T).kq p = k
          rw [h1, h2])
        bankWins bankPres
    · exact CatalanCore.Uniform.Content.UFSimple.WrapCheck.catValid_wrap (3 / 10) c310_pos (ThirdsData.twoTerm T) (nm := 3 * 3) (by rw [T.norm_eq]; norm_num) depth 5 _ (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega⟩)
  · exact CatalanCore.Uniform.Content.UFSimple.catValid_prefixBranches (3 / 10) c310_pos (ThirdsData.twoTerm T) (nm := 3 * 3) (by rw [T.norm_eq]; norm_num) depth 5 _ 24 (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega⟩)

/-- **Automatic content of `thirdsAc`** (member `a = 1`), with UF. -/
theorem thirdsAc_content_autoUF (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent (FamE thirdsAc depth) G310.scale ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (3 / 10) c310_pos (by norm_num) (by decide +kernel) thirdsAc
    depth hd cFr_thirdsAc_le 1 (by decide) thirdsBudget _ (thirds_catValidUF thirdsAc_data depth)
    (thirds_preValid thirdsAc_data depth)

/-- **Automatic content of `thirdsBc`** (member `a = 2`), with UF. -/
theorem thirdsBc_content_autoUF (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent (FamE thirdsBc depth) G310.scale ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (3 / 10) c310_pos (by norm_num) (by decide +kernel) thirdsBc
    depth hd cFr_thirdsBc_le 2 (by decide) thirdsBudget _ (thirds_catValidUF thirdsBc_data depth)
    (thirds_preValid thirdsBc_data depth)

#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Auto.thirdsAc_content_auto
#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Auto.thirdsBc_content_auto
#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Auto.noUF_Λ
#print axioms thirdsAc_content_autoUF
#print axioms thirdsBc_content_autoUF
#print axioms bankData_Λ
#print axioms bank_check
#print axioms uf_mu_le

end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
