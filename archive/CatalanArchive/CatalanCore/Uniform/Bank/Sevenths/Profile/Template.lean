import CatalanCore.Uniform.Bank.Sevenths.Profile.Mass
import CatalanCore.Uniform.Bank.Sevenths.Classes
import CatalanCore.Uniform.Content.BankShared.SawTemplate
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.BankShared.SawPrefix

noncomputable def finiteProfile (j : ℕ) (C : ℝ) : List Piece :=
  if j = 1 then profile1 C else if j = 2 then profile2 C else
  if j = 3 then profile3 C else if j = 4 then profile4 C else
  if j = 5 then profile5 C else profile6 C

theorem finiteProfile_chain (j : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Chain (1 / 12) (finiteProfile j C) := by
  unfold finiteProfile
  split_ifs <;> first | exact profile1_chain C hC | exact profile2_chain C hC |
    exact profile3_chain C hC | exact profile4_chain C hC |
    exact profile5_chain C hC | exact profile6_chain C hC

theorem finiteProfile_end (j : ℕ) (C s : ℝ) :
    lastEnd s (finiteProfile j C) = 49 / 6 := by
  unfold finiteProfile
  split_ifs <;> rfl

noncomputable def tailPiece (C : ℝ) : Piece :=
  { s := 49 / 6, t := 14, α := 0, β := 0, C := C }

noncomputable def fullProfile (j : ℕ) (C : ℝ) : List Piece :=
  finiteProfile j C ++ [tailPiece C]

theorem fullProfile_chain (j : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Chain (1 / 12) (fullProfile j C) := by
  rw [fullProfile, chain_append]
  refine ⟨finiteProfile_chain j C hC, ?_⟩
  rw [finiteProfile_end]
  norm_num [tailPiece, Chain, hC]

theorem fullProfile_end (j : ℕ) (C s : ℝ) : lastEnd s (fullProfile j C) = 14 := by
  rw [fullProfile, lastEnd_append, finiteProfile_end]
  rfl

theorem fullProfile_mass (j : ℕ) (C : ℝ) :
    listInt (fullProfile j C) = listInt (finiteProfile j C) := by
  rw [fullProfile, listInt_append]
  simp [listInt, Piece.int, tailPiece]

noncomputable def seventhsTemplateN (a : Fin 6) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) (c : ZMod 14) : Template :=
  appendTemplate (1 / 12) C (by norm_num) hC n
    (fullProfile (rootForClass a c) C) (fullProfile_chain _ C hC)

theorem seventhsTemplateN_end (a : Fin 6) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) (c : ZMod 14) : (seventhsTemplateN a C hC n c).tend = 14 := by
  rw [seventhsTemplateN, appendTemplate_end, fullProfile_end]

#print axioms fullProfile_chain
#print axioms seventhsTemplateN_end
end CatalanCore.Uniform.Bank.Sevenths
