module

public import CatalanCore.Uniform.Content.Member.HasContent
public import CatalanCore.Uniform.Content.Member.Entries
public import CatalanCore.Uniform.Content.Member.Rank
public import CatalanCore.Uniform.Content.Member.Smith

@[expose] public section

/-! Axiom audit and an instance test for lane H5 (deletion-member content).

The instance test applies the generic assembler `ContentCover.hasContent_of_cover` to the trivial
family `Q i = 1` with price `0` and the empty template: it checks that the hypothesis package is
satisfiable (not vacuous) and that the class and scale plumbing closes. -/

open CatalanCore CatalanCore.Arith.Hybrid Polynomial

namespace CatalanCore.Uniform.Content.Member.Audit

noncomputable def toyFam : PolyFamily where
  const := 0
  ι := ℕ
  deg := id
  Adm := fun _ => True
  Q := fun _ => 1

def toyTmpl : Template := ⟨0, 1, [], le_refl _, one_pos, trivial⟩

noncomputable def toyCover : ContentCover toyFam id 1 where
  tmpl := fun _ => toyTmpl
  price := fun _ _ => 0
  K := 0
  hK := le_refl _
  gle := fun _ _ p _ => show GLE p 0 (1 : ℚ[X]) from GLE.one
  tail := fun _ _ _ _ _ _ _ _ => rfl
  pre := fun _ _ _ _ _ _ _ _ => by simp [toyTmpl]
  cov := fun _ _ _ _ P hP => by simp [toyTmpl] at hP
  exc := fun _ _ _ _ _ => by simp

/-- The assembler is applicable: `HasContent` of the toy family, with `Λ = 1² · 0`. -/
theorem toy_hasContent :
    HasContent toyFam (1 ^ 2 * contentConstant 1 toyCover.tmpl) :=
  ContentCover.hasContent_of_cover toyCover
    (γ := 1) (γ' := 1) (K0 := 0) (K1 := 0) (fun i => by simp [toyFam])
    zero_le_one one_pos le_rfl le_rfl
    (fun i _ => by simp [toyFam, toyCover]) (fun i _ => by simp [toyFam, toyCover])

#print axioms toy_hasContent
#print axioms ContentCover.hasContent_of_cover
#print axioms hasContent_blockGeom
#print axioms hasContent_of_debitLayers
#print axioms member_gle_trop
#print axioms fullN_eq_loewner
#print axioms mn_eq_loewner
#print axioms member_gle_rank
#print axioms lpd_member
#print axioms lpd_member_debit
#print axioms fullN_entry_gle
#print axioms gle_layerMin
#print axioms DebitLayer.trop
#print axioms DebitLayer.tropRat
#print axioms DebitLayer.lpd
#print axioms DebitLayer.smith
#print axioms sd_first_layer
#print axioms DebitLayer.smithSD

end CatalanCore.Uniform.Content.Member.Audit
