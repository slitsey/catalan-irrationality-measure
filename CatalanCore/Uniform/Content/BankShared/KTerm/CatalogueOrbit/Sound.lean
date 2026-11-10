module

public import CatalanCore.Uniform.Content.BankShared.KTerm.CatalogueOrbit.Data
public import CatalanCore.Uniform.Content.BankShared.KTerm.LegacyTranslation

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1200000

/-! Tagged catalogue orbit soundness composes the accepted seed theorem.
Sorting preserves membership; numerical chain and mass checks remain separate. -/
namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Content.BankShared.Check Polynomial

noncomputable def CatalogueOrbitLaw.translation {C : List KBranch} (law : CatalogueOrbitLaw C)
    (b a Ω idx : ℕ) : Transl (law.shiftB b) (law.shiftA a) (law.shiftK b a) Ω (law.palette idx) :=
  match law with
  | .constant indices => identityTranslation Ω (CatalogueOrbitLaw.palette (C := C) idx (.constant indices))
  | .d1x => d1xTranslation b a Ω
  | .pre ν j0 j1 => legacyPreTranslation b a Ω idx ν j0 j1
  | .wrap ν hν => wrapPrefixTranslation b a Ω idx ν hν

theorem CatalogueSeed.facts {D : KBankData} (hpar : KParams D) {c : ℚ} {hc : 0<c}
    {const : ℝ} {depth : ℕ} {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]}
    (hdepth : depth≤D.depth) {L N0 j : ℕ} (hL : L≤N0)
    {C : List KBranch} (S : CatalogueSeed C) (b a Ω idx : ℕ)
    (hab : D.α*S.law.shiftB b=S.law.shiftA a)
    (hallowed : S.law.Allowed (KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0) idx)
    (hok : seedOK D (S.law.palette idx) j L (S.toSeed b a Ω)=true) :
    ∀ z∈S.pieces b a Ω D.cF,PieceBasic z.1 ∧ PieceCov D c hc const depth Q N0 j z.1 := by
  have hvalid : ∀ law : CatalogueOrbitLaw C,
      law.Allowed (KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0) idx →
      ∀ n, KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0
        ((law.palette idx).map ((law.translation b a Ω idx).ρ n)) := by
    intro law hallowed n
    cases law with
    | constant indices =>
        intro br hbr
        simp only [CatalogueOrbitLaw.translation,identityTranslation,List.map_id_fun,List.map_map,Function.comp_def,CatalogueOrbitLaw.palette] at hbr
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbr
        exact hallowed _ (List.getElem_mem i.isLt)
    | d1x =>
        simpa only [CatalogueOrbitLaw.translation,CatalogueOrbitLaw.palette,
          d1xTranslation,List.map_cons,List.map_nil,CatalogueOrbitLaw.Allowed] using hallowed
    | pre ν j0 j1 =>
        simpa only [CatalogueOrbitLaw.translation,CatalogueOrbitLaw.palette,
          legacyPreTranslation,Transl.ofFamily,List.map_cons,List.map_nil,if_pos rfl,ite_true] using
          hallowed (ν+a*n)
    | wrap ν hν =>
        simpa only [CatalogueOrbitLaw.translation,CatalogueOrbitLaw.palette,
          wrapPrefixTranslation,Transl.ofFamily,List.map_cons,List.map_nil,if_pos rfl,ite_true] using
          hallowed (ν+a*n) (by omega)
  exact seed_facts hpar hdepth hL (S.toSeed b a Ω) hab (S.law.translation b a Ω idx) (hvalid S.law hallowed) hok

theorem catalogueHead_facts {D : KBankData} (hpar : KParams D) {c : ℚ} {hc : 0<c}
    {const : ℝ} {depth : ℕ} {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]}
    (hdepth : depth≤D.depth) {L N0 j : ℕ} (hL : L≤N0)
    {C : List KBranch} (seeds : List (CatalogueSeed C)) (b a Ω idx : ℕ)
    (hab : ∀ S∈seeds,D.α*S.law.shiftB b=S.law.shiftA a)
    (hallowed : ∀ S∈seeds,S.law.Allowed (KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0) idx)
    (hok : ∀ S∈seeds,seedOK D (S.law.palette idx) j L (S.toSeed b a Ω)=true) :
    ∀ z∈catalogueHead b a Ω D.cF seeds,PieceBasic z.1 ∧ PieceCov D c hc const depth Q N0 j z.1 := by
  intro z hz
  simp only [catalogueHead,List.mem_mergeSort,List.mem_flatMap] at hz
  obtain ⟨S,hS,hz⟩ := hz
  exact S.facts hpar hdepth hL b a Ω idx (hab S hS) (hallowed S hS) (hok S hS) z hz

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.CatalogueOrbitLaw.translation
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.CatalogueSeed.facts
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.catalogueHead_facts
