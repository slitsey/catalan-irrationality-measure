import CatalanCore.Uniform.Bank.Sevenths.Profile.Template
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.BankShared.SawPrefix Finset

theorem sevenths_profile_class_sum (a : Fin 6) (C : ℝ) :
    (∑ c ∈ unitClasses 14, listInt (finiteProfile (rootForClass a c) C)) =
      listInt (profile1 C) + listInt (profile2 C) + listInt (profile3 C) +
        listInt (profile4 C) + listInt (profile5 C) + listInt (profile6 C) := by
  rw [unitClasses_fourteen]
  fin_cases a <;>
    norm_num [rootForClass, seventhNumerator, finiteProfile,
      profile1_mass, profile2_mass, profile3_mass, profile4_mass, profile5_mass, profile6_mass] <;> ring

theorem seventhsTemplateN_mass (a : Fin 6) (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    contentConstant 14 (seventhsTemplateN a C hC n) =
      (13 / 6 : ℝ) * ((1 / 12 : ℝ) / ((n : ℝ) + 1)) + listInt (pieces (1 / 12) C n) +
      (listInt (profile1 C) + listInt (profile2 C) + listInt (profile3 C) +
        listInt (profile4 C) + listInt (profile5 C) + listInt (profile6 C)) / 6 := by
  have hm (c : ZMod 14) : (seventhsTemplateN a C hC n c).mass =
      (13 / 6 : ℝ) * ((1 / 12 : ℝ) / ((n : ℝ) + 1)) + listInt (pieces (1 / 12) C n) +
      listInt (finiteProfile (rootForClass a c) C) := by
    rw [seventhsTemplateN, appendTemplate_mass, fullProfile_mass]
    ring
  have hc : (unitClasses 14).card = 6 := by rw [unitClasses_fourteen]; decide
  unfold contentConstant
  simp_rw [hm]
  rw [Finset.sum_add_distrib, Finset.sum_const, sevenths_profile_class_sum, hc,
    show Nat.totient 14 = 6 by decide]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The same finite depth works for every additive coverage constant. -/
theorem exists_sevenths_template_mass (a : Fin 6) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ C : ℝ, ∀ hC : 0 ≤ C,
      contentConstant 14 (seventhsTemplateN a C hC n) ≤ Lam7 + ε := by
  obtain ⟨n, hn⟩ := exists_mass_slack (1 / 12) 0 ε hε
  refine ⟨n, fun C hC => ?_⟩
  have he : listInt (pieces (1 / 12) C n) = listInt (pieces (1 / 12) 0 n) := by
    rw [pieces_mass, pieces_mass]
  rw [seventhsTemplateN_mass, he]
  have hmass := sevenths_profile_mass C
  norm_num only at hn
  linarith

#print axioms seventhsTemplateN_mass
#print axioms exists_sevenths_template_mass
end CatalanCore.Uniform.Bank.Sevenths
