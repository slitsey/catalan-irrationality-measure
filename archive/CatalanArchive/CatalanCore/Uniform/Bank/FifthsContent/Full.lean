import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P0
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P1
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P2
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P3
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P4
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P5
import CatalanCore.Uniform.Bank.FifthsContent.Profile.J1
import CatalanCore.Uniform.Bank.FifthsContent.Profile.J2
import CatalanCore.Uniform.Bank.FifthsContent.Profile.J3
import CatalanCore.Uniform.Bank.FifthsContent.Profile.J4
import CatalanCore.Uniform.Content.Member.Template
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member

theorem chain_app : ∀ (l1 l2 : List Piece) (s0 : ℝ),
    Chain s0 (l1 ++ l2) ↔ Chain s0 l1 ∧ Chain (lastEnd s0 l1) l2
  | [], l2, s0 => by simp [Chain, lastEnd]
  | P :: l, l2, s0 => by
    simp only [List.cons_append, Chain, lastEnd]
    rw [chain_app l l2 P.t]
    tauto

theorem lastEnd_app : ∀ (l1 l2 : List Piece) (s0 : ℝ),
    lastEnd s0 (l1 ++ l2) = lastEnd (lastEnd s0 l1) l2
  | [], l2, s0 => by simp [lastEnd]
  | P :: l, l2, s0 => by simp only [List.cons_append, lastEnd]; exact lastEnd_app l l2 P.t

theorem listInt_app : ∀ (l1 l2 : List Piece), listInt (l1 ++ l2) = listInt l1 + listInt l2
  | [], l2 => by simp [listInt]
  | P :: l, l2 => by simp only [List.cons_append, listInt]; rw [listInt_app l l2]; ring

/-- The class envelope of the pole index `j` (`j = 1, 2, 3, 4`). -/
noncomputable def profileOf : ℕ → List Piece
  | 1 => profile1
  | 2 => profile2
  | 3 => profile3
  | _ => profile4

def profileMass : ℕ → ℚ
  | 1 => profile1Mass
  | 2 => profile2Mass
  | 3 => profile3Mass
  | _ => profile4Mass

theorem profileOf_chain (j : ℕ) : Chain (1 / 9) (profileOf j) := by
  match j with
  | 1 => exact profile1_chain
  | 2 => exact profile2_chain
  | 3 => exact profile3_chain
  | n + 4 => exact profile4_chain
  | 0 => exact profile4_chain

theorem profileOf_end (j : ℕ) : lastEnd (1 / 9) (profileOf j) = (63 / 10) := by
  match j with
  | 1 => exact profile1_end
  | 2 => exact profile2_end
  | 3 => exact profile3_end
  | n + 4 => exact profile4_end
  | 0 => exact profile4_end

theorem profileOf_mass (j : ℕ) : listInt (profileOf j) = (profileMass j : ℝ) := by
  match j with
  | 1 => exact profile1_mass
  | 2 => exact profile2_mass
  | 3 => exact profile3_mass
  | n + 4 => exact profile4_mass
  | 0 => exact profile4_mass

/-- Sawtooth prefix on `[1/(9N), 1/9]`, the class envelope, and the zero tail. -/
noncomputable def fullList (j : ℕ) : List Piece := prefix0 ++ (prefix1 ++ (prefix2 ++ (prefix3 ++ (prefix4 ++ (prefix5 ++ (profileOf j))))))

def prefixMass : ℚ := prefix0Mass + prefix1Mass + prefix2Mass + prefix3Mass + prefix4Mass + prefix5Mass

theorem fullList_chain (j : ℕ) : Chain (1 / 900) (fullList j) := by
  unfold fullList
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
  exact profileOf_chain j

theorem fullList_end (j : ℕ) : lastEnd (1 / 900) (fullList j) = (63 / 10) := by
  unfold fullList
  rw [lastEnd_app, prefix0_end]
  rw [lastEnd_app, prefix1_end]
  rw [lastEnd_app, prefix2_end]
  rw [lastEnd_app, prefix3_end]
  rw [lastEnd_app, prefix4_end]
  rw [lastEnd_app, prefix5_end]
  exact profileOf_end j

theorem fullList_mass (j : ℕ) : listInt (fullList j) = ((prefixMass + profileMass j : ℚ) : ℝ) := by
  unfold fullList
  simp only [listInt_app, prefix0_mass, prefix1_mass, prefix2_mass, prefix3_mass, prefix4_mass, prefix5_mass]
  rw [profileOf_mass j]
  push_cast [prefixMass]
  ring

/-- The class template of the pole index `j` (constant `20/9` on `(0, 1/(9N)]`). -/
noncomputable def tmplJ (j : ℕ) : Template where
  α0 := 20 / 9
  t1 := (1 / 900)
  l := fullList j
  hα0 := by norm_num
  ht1 := by norm_num
  chain := fullList_chain j

theorem tmplJ_tend (j : ℕ) : (tmplJ j).tend = 63 / 10 := fullList_end j

theorem tmplJ_mass (j : ℕ) :
    (tmplJ j).mass = (((20 / 9) * (1 / 900) + prefixMass + profileMass j : ℚ) : ℝ) := by
  unfold Template.mass tmplJ
  simp only
  rw [fullList_mass j]
  push_cast
  ring

theorem mem_fullList {j : ℕ} {P : Piece} (h : P ∈ fullList j) :
    P ∈ prefix0 ∨ P ∈ prefix1 ∨ P ∈ prefix2 ∨ P ∈ prefix3 ∨ P ∈ prefix4 ∨ P ∈ prefix5 ∨ P ∈ profileOf j := by
  unfold fullList at h
  simp only [List.mem_append] at h
  tauto


def LamFin5 : ℚ := (1813874724013455348830085364588619843636174961262284458493785019823042753897083294682378489 / 515486428216359008222579756799663283057055566143353508915785071231999159677639030102384000)

theorem LamFin5_eq : (20 / 9) * (1 / 900) + prefixMass + (profileMass 1 + profileMass 2 + profileMass 3 + profileMass 4) / 4 = LamFin5 := by
  norm_num [prefix0Mass, prefix1Mass, prefix2Mass, prefix3Mass, prefix4Mass, prefix5Mass, profile1Mass, profile2Mass, profile3Mass, profile4Mass, prefixMass, profileMass, LamFin5]

#print axioms fullList_chain
#print axioms fullList_end
#print axioms tmplJ_mass
end CatalanCore.Uniform.Bank.FifthsContent
