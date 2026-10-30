import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P0
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P1
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P2
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P3
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P4
import CatalanCore.Uniform.Bank.FifthsContent.Prefix.P5
import CatalanCore.Uniform.Bank.FifthsContent.Profile.C1
import CatalanCore.Uniform.Bank.FifthsContent.Profile.C3
import CatalanCore.Uniform.Bank.FifthsContent.Profile.C7
import CatalanCore.Uniform.Bank.FifthsContent.Profile.C9
import CatalanCore.Uniform.Bank.Fifths.Final
import CatalanCore.Uniform.Bank.FifthsContent.Units10
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

/-- Sawtooth prefix on `[1/(9N), 1/9]` followed by the class envelope `prof C0`. -/
noncomputable def fullList (prof : ℝ → List Piece) (C0 : ℝ) : List Piece := prefix0 C0 ++ (prefix1 C0 ++ (prefix2 C0 ++ (prefix3 C0 ++ (prefix4 C0 ++ (prefix5 C0 ++ (prof C0))))))

def prefixMass : ℚ := prefix0Mass + prefix1Mass + prefix2Mass + prefix3Mass + prefix4Mass + prefix5Mass

theorem fullList_chain (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0) (hprof : Chain (1 / 9) (prof C0)) :
    Chain (1 / 900) (fullList prof C0) := by
  unfold fullList
  rw [chain_app]
  refine ⟨prefix0_chain C0 hC, ?_⟩
  rw [prefix0_end]
  rw [chain_app]
  refine ⟨prefix1_chain C0 hC, ?_⟩
  rw [prefix1_end]
  rw [chain_app]
  refine ⟨prefix2_chain C0 hC, ?_⟩
  rw [prefix2_end]
  rw [chain_app]
  refine ⟨prefix3_chain C0 hC, ?_⟩
  rw [prefix3_end]
  rw [chain_app]
  refine ⟨prefix4_chain C0 hC, ?_⟩
  rw [prefix4_end]
  rw [chain_app]
  refine ⟨prefix5_chain C0 hC, ?_⟩
  rw [prefix5_end]
  exact hprof

theorem fullList_end (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0) (e : ℝ)
    (hprof : lastEnd (1 / 9) (prof C0) = e) : lastEnd (1 / 900) (fullList prof C0) = e := by
  unfold fullList
  rw [lastEnd_app, prefix0_end]
  rw [lastEnd_app, prefix1_end]
  rw [lastEnd_app, prefix2_end]
  rw [lastEnd_app, prefix3_end]
  rw [lastEnd_app, prefix4_end]
  rw [lastEnd_app, prefix5_end]
  exact hprof

theorem fullList_mass (prof : ℝ → List Piece) (C0 : ℝ) (m : ℚ) (hprof : listInt (prof C0) = (m : ℝ)) :
    listInt (fullList prof C0) = ((prefixMass + m : ℚ) : ℝ) := by
  unfold fullList
  simp only [listInt_app, prefix0_mass, prefix1_mass, prefix2_mass, prefix3_mass, prefix4_mass, prefix5_mass]
  rw [hprof]
  push_cast [prefixMass]
  ring

/-- The class template (constant `20/9` on `(0, 1/(9N)]`). -/
noncomputable def tmplF (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0) (hprof : Chain (1 / 9) (prof C0)) :
    Template where
  α0 := 20 / 9
  t1 := (1 / 900)
  l := fullList prof C0
  hα0 := by norm_num
  ht1 := by norm_num
  chain := fullList_chain prof C0 hC hprof

theorem tmplF_mass (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0) (hprof : Chain (1 / 9) (prof C0))
    (m : ℚ) (hm : listInt (prof C0) = (m : ℝ)) :
    (tmplF prof C0 hC hprof).mass = (((1 / 405) + prefixMass + m : ℚ) : ℝ) := by
  unfold Template.mass tmplF
  simp only
  rw [fullList_mass prof C0 m hm]
  push_cast
  ring

/-- The template of the unit class `c` of `ZMod 10`. -/
noncomputable def tmpl5 (C0 : ℝ) (hC : 0 ≤ C0) (c : ZMod 10) : Template :=
  if c = 1 then tmplF profile1 C0 hC (profile1_chain C0 hC)
  else if c = 3 then tmplF profile3 C0 hC (profile3_chain C0 hC)
  else if c = 7 then tmplF profile7 C0 hC (profile7_chain C0 hC)
  else tmplF profile9 C0 hC (profile9_chain C0 hC)

def LamFin5 : ℚ := (1813874724013455348830085364588619843636174961262284458493785019823042753897083294682378489 / 515486428216359008222579756799663283057055566143353508915785071231999159677639030102384000)

theorem contentConstant_tmpl5 (C0 : ℝ) (hC : 0 ≤ C0) :
    contentConstant 10 (tmpl5 C0 hC) = (LamFin5 : ℝ) := by
  have t1 : (tmpl5 C0 hC 1).mass = (((1 / 405) + prefixMass + profile1Mass : ℚ) : ℝ) := by
    unfold tmpl5; rw [if_pos rfl]; exact tmplF_mass _ _ _ _ _ (profile1_mass C0)
  have t3 : (tmpl5 C0 hC 3).mass = (((1 / 405) + prefixMass + profile3Mass : ℚ) : ℝ) := by
    unfold tmpl5; rw [if_neg (by decide), if_pos rfl]; exact tmplF_mass _ _ _ _ _ (profile3_mass C0)
  have t7 : (tmpl5 C0 hC 7).mass = (((1 / 405) + prefixMass + profile7Mass : ℚ) : ℝ) := by
    unfold tmpl5; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]; exact tmplF_mass _ _ _ _ _ (profile7_mass C0)
  have t9 : (tmpl5 C0 hC 9).mass = (((1 / 405) + prefixMass + profile9Mass : ℚ) : ℝ) := by
    unfold tmpl5; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]; exact tmplF_mass _ _ _ _ _ (profile9_mass C0)
  unfold contentConstant
  rw [unitClasses_ten, totient_ten]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, t1, t3, t7, t9]
  have hq : (((1 / 405) + prefixMass + profile1Mass : ℚ) : ℝ) + (((1 / 405) + prefixMass + profile3Mass : ℚ) : ℝ) +
      (((1 / 405) + prefixMass + profile7Mass : ℚ) : ℝ) + (((1 / 405) + prefixMass + profile9Mass : ℚ) : ℝ) =
      ((4 * LamFin5 : ℚ) : ℝ) := by
    rw [← Rat.cast_add, ← Rat.cast_add, ← Rat.cast_add]
    congr 1
    norm_num [prefix0Mass, prefix1Mass, prefix2Mass, prefix3Mass, prefix4Mass, prefix5Mass, profile1Mass, profile3Mass, profile7Mass, profile9Mass, prefixMass, LamFin5]
  rw [hq]; push_cast; ring

#print axioms fullList_chain
#print axioms tmplF_mass
end CatalanCore.Uniform.Bank.FifthsContent
