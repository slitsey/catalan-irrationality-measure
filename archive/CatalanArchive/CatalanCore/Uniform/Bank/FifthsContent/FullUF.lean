import CatalanCore.Uniform.Bank.FifthsContent.Full
import CatalanCore.Uniform.Bank.FifthsContent.ProfileUF.J1
import CatalanCore.Uniform.Bank.FifthsContent.ProfileUF.J2
import CatalanCore.Uniform.Bank.FifthsContent.ProfileUF.J3
import CatalanCore.Uniform.Bank.FifthsContent.ProfileUF.J4
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member

noncomputable def profileOfU : ℕ → List Piece
  | 1 => profileU1
  | 2 => profileU2
  | 3 => profileU3
  | _ => profileU4

def profileMassU : ℕ → ℚ
  | 1 => profileU1Mass
  | 2 => profileU2Mass
  | 3 => profileU3Mass
  | _ => profileU4Mass

theorem profileOfU_chain (j : ℕ) : Chain (1 / 9) (profileOfU j) := by
  match j with
  | 1 => exact profileU1_chain
  | 2 => exact profileU2_chain
  | 3 => exact profileU3_chain
  | n + 4 => exact profileU4_chain
  | 0 => exact profileU4_chain

theorem profileOfU_end (j : ℕ) : lastEnd (1 / 9) (profileOfU j) = (63 / 10) := by
  match j with
  | 1 => exact profileU1_end
  | 2 => exact profileU2_end
  | 3 => exact profileU3_end
  | n + 4 => exact profileU4_end
  | 0 => exact profileU4_end

theorem profileOfU_mass (j : ℕ) : listInt (profileOfU j) = (profileMassU j : ℝ) := by
  match j with
  | 1 => exact profileU1_mass
  | 2 => exact profileU2_mass
  | 3 => exact profileU3_mass
  | n + 4 => exact profileU4_mass
  | 0 => exact profileU4_mass

noncomputable def fullListU (j : ℕ) : List Piece := prefix0 ++ (prefix1 ++ (prefix2 ++ (prefix3 ++ (prefix4 ++ (prefix5 ++ (profileOfU j))))))

theorem fullListU_chain (j : ℕ) : Chain (1 / 900) (fullListU j) := by
  unfold fullListU
  rw [chain_app]
  refine ⟨prefix0_chain, ?_⟩
  rw [prefix0_end]
  rw [chain_app]
  refine ⟨prefix1_chain, ?_⟩
  rw [prefix1_end]
  rw [chain_app]
  refine ⟨prefix2_chain, ?_⟩
  rw [prefix2_end]
  rw [chain_app]
  refine ⟨prefix3_chain, ?_⟩
  rw [prefix3_end]
  rw [chain_app]
  refine ⟨prefix4_chain, ?_⟩
  rw [prefix4_end]
  rw [chain_app]
  refine ⟨prefix5_chain, ?_⟩
  rw [prefix5_end]
  exact profileOfU_chain j

theorem fullListU_end (j : ℕ) : lastEnd (1 / 900) (fullListU j) = (63 / 10) := by
  unfold fullListU
  rw [lastEnd_app, prefix0_end]
  rw [lastEnd_app, prefix1_end]
  rw [lastEnd_app, prefix2_end]
  rw [lastEnd_app, prefix3_end]
  rw [lastEnd_app, prefix4_end]
  rw [lastEnd_app, prefix5_end]
  exact profileOfU_end j

theorem fullListU_mass (j : ℕ) : listInt (fullListU j) = ((prefixMass + profileMassU j : ℚ) : ℝ) := by
  unfold fullListU
  simp only [listInt_app, prefix0_mass, prefix1_mass, prefix2_mass, prefix3_mass, prefix4_mass, prefix5_mass]
  rw [profileOfU_mass j]
  push_cast [prefixMass]
  ring

noncomputable def tmplJU (j : ℕ) : Template where
  α0 := 20 / 9
  t1 := (1 / 900)
  l := fullListU j
  hα0 := by norm_num
  ht1 := by norm_num
  chain := fullListU_chain j

theorem tmplJU_tend (j : ℕ) : (tmplJU j).tend = 63 / 10 := fullListU_end j

theorem tmplJU_mass (j : ℕ) :
    (tmplJU j).mass = (((20 / 9) * (1 / 900) + prefixMass + profileMassU j : ℚ) : ℝ) := by
  unfold Template.mass tmplJU
  simp only
  rw [fullListU_mass j]
  push_cast
  ring

theorem mem_fullListU {j : ℕ} {P : Piece} (h : P ∈ fullListU j) :
    P ∈ prefix0 ∨ P ∈ prefix1 ∨ P ∈ prefix2 ∨ P ∈ prefix3 ∨ P ∈ prefix4 ∨ P ∈ prefix5 ∨ P ∈ profileOfU j := by
  unfold fullListU at h
  simp only [List.mem_append] at h
  tauto

def LamFinU : ℚ := (226487317556495767233335592038683783233726064567902721267191853461042592340729364136428383 / 64435803527044876027822469599957910382131945767919188614473133903999894959704878762798000)

theorem LamFinU_eq : (20 / 9) * (1 / 900) + prefixMass + (profileMassU 1 + profileMassU 2 + profileMassU 3 + profileMassU 4) / 4 = LamFinU := by
  norm_num [prefix0Mass, prefix1Mass, prefix2Mass, prefix3Mass, prefix4Mass, prefix5Mass, profileU1Mass, profileU2Mass, profileU3Mass, profileU4Mass, prefixMass, profileMassU, LamFinU]

#print axioms fullListU_chain
#print axioms tmplJU_mass
end CatalanCore.Uniform.Bank.FifthsContent
