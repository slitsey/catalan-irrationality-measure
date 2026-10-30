import CatalanCore.Uniform.Bank.Lambda.Final
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
def LamNoUFFinite : ℚ := (8479532582477447788992327107148305961395141369811453104814067831114559898464942556695845663 / 2409239920235187604567612619963152910231388448465408815920335870837385843290552786192800000)
theorem finite_Lam_lt_D : (LamNoUFFinite : ℝ) < (DL : ℝ) := by
  norm_num [LamNoUFFinite, DL]
theorem finite_noUF_X_le :
    (cL : ℝ) / ((DL : ℝ) - (LamNoUFFinite : ℝ)) ≤ ((159693 / 5000 : ℚ) : ℝ) := by
  norm_num [LamNoUFFinite, DL, cL]
#print axioms finite_Lam_lt_D
#print axioms finite_noUF_X_le
end CatalanCore.Uniform.Bank.Lambda
