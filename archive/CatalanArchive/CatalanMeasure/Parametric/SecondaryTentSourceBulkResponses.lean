module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceModularTrace

/-! Clean actual-source bulk responses of the five fixed seeds. -/
@[expose] public section
namespace CatalanMeasure.Parametric
noncomputable section

theorem secondaryTent_source_bulk_constant {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J : Fin 4) :
    (secondaryTentSourceMacroTrace p J.val
      (fun k => (secondaryTentSeedCoefficients k 0:ZMod p))).coeff 5 = 747824613120 := by
  rw [secondaryTent_source_fixed_macro_modular hp J 0]
  fin_cases J <;> norm_num [secondaryTentSourceFixedResponseInteger]

theorem secondaryTent_source_bulk_kernel_one {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J : Fin 4) :
    (secondaryTentSourceMacroTrace p J.val
      (fun k => (secondaryTentSeedCoefficients k 1:ZMod p))).coeff 5 = 0 := by
  rw [secondaryTent_source_fixed_macro_modular hp J 1]
  fin_cases J <;> norm_num [secondaryTentSourceFixedResponseInteger]

theorem secondaryTent_source_bulk_kernel_two {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J : Fin 4) :
    (secondaryTentSourceMacroTrace p J.val
      (fun k => (secondaryTentSeedCoefficients k 2:ZMod p))).coeff 5 = 0 := by
  rw [secondaryTent_source_fixed_macro_modular hp J 2]
  fin_cases J <;> norm_num [secondaryTentSourceFixedResponseInteger]

theorem secondaryTent_source_bulk_initial {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J : Fin 4) :
    (secondaryTentSourceMacroTrace p J.val
      (fun k => (secondaryTentSeedCoefficients k 3:ZMod p))).coeff 5 =
      if J=0 then 747824613120 else 0 := by
  rw [secondaryTent_source_fixed_macro_modular hp J 3]
  fin_cases J <;> norm_num [secondaryTentSourceFixedResponseInteger]

theorem secondaryTent_source_bulk_boundary {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J : Fin 4) :
    (secondaryTentSourceMacroTrace p J.val
      (fun k => (secondaryTentSeedCoefficients k 4:ZMod p))).coeff 5 =
      if J=3 then -23101261920 else 0 := by
  rw [secondaryTent_source_fixed_macro_modular hp J 4]
  fin_cases J <;> norm_num [secondaryTentSourceFixedResponseInteger]

end
end CatalanMeasure.Parametric
