import CatalanCore.Uniform.Bank.Chi3.KContent.Data
import CatalanCore.Uniform.Bank.Chi3.KContent.Win
import CatalanCore.Uniform.Bank.Chi3.KContent.Pre
set_option Elab.async false

/-! # The content of chi_{-3} through `hasScaledContent_of_kcheck` (lane K)

* `kCat_valid`: the k-shift catalogue `kCat = [D1, D1x, Z0, Z1, T0] ++ windows ++ prefixes` is `KCatValid` for `p6Frame`
  (`kcat_trop_valid`, `kbrWin_valid`, `kbrPre_valid`);
* `chi3_k_content`: **`HasScaledContent (AltEven (1/2) p6Frame depth) scale Λ_fin`**, `Λ_fin = kData.Λ`
  (`4.0959277673…`, the prefix layer included), from `kdata_check`, `kCat_valid`, `p6_preValid`, `cFr p6Frame ≤ 60`.
  No rank layer and no scale restriction: all even scales. -/

namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.SmallPrimes CatalanFrames.P6

theorem kCat_valid (depth N0 : ℕ) :
    KCatValid (1 / 2) c12_pos p6Frame depth kShifts 6 6 N0 kCat := by
  intro b hb
  simp only [kCat, List.mem_append, List.mem_map] at hb
  rcases hb with (hb | ⟨w, -, rfl⟩) | ⟨x, -, rfl⟩
  · exact kcat_trop_valid depth N0 b hb
  · exact kbrWin_valid depth N0 w.1 w.2.1 w.2.2 _ (List.mem_singleton_self _)
  · exact kbrPre_valid depth N0 x.1 x.2.1 x.2.2.1 x.2.2.2 _ (List.mem_singleton_self _)

theorem cFr_p6 : cFr p6Frame ≤ 60 := by decide +kernel

/-- **The scaled content of chi_{-3}** (all even scales, prefix layer included), `Λ_fin = kData.Λ`. -/
theorem chi3_k_content (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent (AltEven (1 / 2) c12_pos p6Frame depth) (altGeom (1 / 2) c12_pos).scale
      ((kData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_kcheck kData kdata_check (1 / 2) c12_pos (by norm_num)
    (by norm_num [kData, kHead, qq]) p6Frame depth hd cFr_p6
    (SmallBudget.add (SmallBudget.sqrtLog 5 10) SmallBudget.unit) 0 (kCat_valid depth 0) (p6_preValid depth)

end CatalanCore.Uniform.Bank.Chi3.KContent

#print axioms CatalanCore.Uniform.Bank.Chi3.KContent.kCat_valid
#print axioms CatalanCore.Uniform.Bank.Chi3.KContent.chi3_k_content
