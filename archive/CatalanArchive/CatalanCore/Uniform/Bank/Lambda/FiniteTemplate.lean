import CatalanCore.Uniform.Bank.Lambda.Prefix.Ends
import CatalanCore.Uniform.Bank.Lambda.FiniteRate
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda
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
  | P :: l, l2, s0 => by
    simp only [List.cons_append, lastEnd]
    exact lastEnd_app l l2 P.t

theorem listInt_app : ∀ (l1 l2 : List Piece), listInt (l1 ++ l2) = listInt l1 + listInt l2
  | [], l2 => by simp [listInt]
  | P :: l, l2 => by
    simp only [List.cons_append, listInt]
    rw [listInt_app l l2]
    ring

noncomputable def fullList (prof : ℝ → List Piece) (C0 : ℝ) : List Piece :=
  prefix0 C0 ++ (prefix1 C0 ++ (prefix2 C0 ++ (prefix3 C0 ++
    (prefix4 C0 ++ (prefix5 C0 ++ prof C0)))))

def prefixMass : ℚ := prefix0Mass + prefix1Mass + prefix2Mass + prefix3Mass + prefix4Mass + prefix5Mass

theorem fullList_chain (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0)
    (hprof : Chain (1 / 10) (prof C0)) : Chain (1 / 1000) (fullList prof C0) := by
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

theorem fullList_end (prof : ℝ → List Piece) (C0 : ℝ)
    (hprof : ∀ s0, lastEnd s0 (prof C0) = 24 / 5) :
    lastEnd (1 / 1000) (fullList prof C0) = 24 / 5 := by
  unfold fullList
  rw [lastEnd_app, prefix0_end]
  rw [lastEnd_app, prefix1_end]
  rw [lastEnd_app, prefix2_end]
  rw [lastEnd_app, prefix3_end]
  rw [lastEnd_app, prefix4_end]
  rw [lastEnd_app, prefix5_end]
  exact hprof _

theorem fullList_mass (prof : ℝ → List Piece) (C0 : ℝ) (m : ℚ)
    (hm : listInt (prof C0) = (m : ℝ)) :
    listInt (fullList prof C0) = ((prefixMass + m : ℚ) : ℝ) := by
  unfold fullList
  simp only [listInt_app, prefix0_mass, prefix1_mass, prefix2_mass, prefix3_mass, prefix4_mass, prefix5_mass]
  rw [hm]
  push_cast [prefixMass]
  ring

noncomputable def finiteTemplate (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0)
    (hprof : Chain (1 / 10) (prof C0)) : Template where
  α0 := 11 / 5
  t1 := 1 / 1000
  l := fullList prof C0
  hα0 := by norm_num
  ht1 := by norm_num
  chain := fullList_chain prof C0 hC hprof

theorem finiteTemplate_mass (prof : ℝ → List Piece) (C0 : ℝ) (hC : 0 ≤ C0)
    (hprof : Chain (1 / 10) (prof C0)) (m : ℚ)
    (hm : listInt (prof C0) = (m : ℝ)) :
    (finiteTemplate prof C0 hC hprof).mass = ((11 / 5000 + prefixMass + m : ℚ) : ℝ) := by
  unfold Template.mass finiteTemplate
  simp only
  rw [fullList_mass prof C0 m hm]
  push_cast
  ring

/-- The two classes of odd primes use the complete no-UF envelopes. -/
noncomputable def tmpl4 (C0 : ℝ) (hC : 0 ≤ C0) (c : ZMod 4) : Template :=
  if c = 1 then finiteTemplate profile1 C0 hC (profile1_chain C0 hC)
  else finiteTemplate profile3 C0 hC (profile3_chain C0 hC)

theorem unitClasses_four : unitClasses 4 = {1, 3} := by
  ext c
  rw [mem_unitClasses]
  have h : ∀ c : ZMod 4, IsUnit c ↔ Nat.Coprime c.val 4 := fun c => by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact ZMod.isUnit_iff_coprime _ _
  rw [h]
  revert c
  decide

theorem tmpl4_mass (C0 : ℝ) (hC : 0 ≤ C0) :
    contentConstant 4 (tmpl4 C0 hC) = (LamNoUFFinite : ℝ) := by
  have h1 := finiteTemplate_mass profile1 C0 hC (profile1_chain C0 hC) profile1Mass (profile1_mass C0)
  have h3 := finiteTemplate_mass profile3 C0 hC (profile3_chain C0 hC) profile3Mass (profile3_mass C0)
  unfold contentConstant
  rw [unitClasses_four]
  rw [Finset.sum_insert (by decide : (1 : ZMod 4) ∉ ({3} : Finset (ZMod 4))),
    Finset.sum_singleton]
  have h31 : (3 : ZMod 4) ≠ 1 := by decide
  simp only [tmpl4, ite_true, if_neg h31]
  rw [h1, h3]
  rw [show Nat.totient 4 = 2 by decide]
  norm_num [prefixMass, prefix0Mass, prefix1Mass, prefix2Mass, prefix3Mass,
    prefix4Mass, prefix5Mass, profile1Mass, profile3Mass, LamNoUFFinite]

theorem tmpl4_end (C0 : ℝ) (hC : 0 ≤ C0) (c : ZMod 4) :
    (tmpl4 C0 hC c).tend = 24 / 5 := by
  unfold tmpl4 Template.tend finiteTemplate
  split_ifs
  · exact fullList_end profile1 C0 (profile1_end C0)
  · exact fullList_end profile3 C0 (profile3_end C0)

#print axioms tmpl4_mass
#print axioms tmpl4_end
end CatalanCore.Uniform.Bank.Lambda
