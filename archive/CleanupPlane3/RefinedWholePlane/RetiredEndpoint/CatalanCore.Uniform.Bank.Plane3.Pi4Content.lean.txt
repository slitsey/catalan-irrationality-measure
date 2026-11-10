module

public import CatalanCore.Uniform.Bank.Plane3.Arithmetic
public import CatalanCore.Uniform.Bank.Plane3.Pi4Data
public import CatalanCore.Uniform.Bank.Plane3.Pi4Contract

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! Pure datum content from the arbitrary-order catalogue and refined period row.
The accepted periodic low cells and their generic translation remain unchanged. -/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support
open CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
open CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.KTerm

theorem pi4_content_hpole (const : ℝ) :
    HasScaledContent
      (AltEvenFam (1/10) (by norm_num) const 1
        (SeqFamily.poly (hpoleF 4 (coefficients 0 15)) (hpoleE 4 (coefficients 0 15))
          (altGeom (1/10) (by norm_num)).geometry))
      (altGeom (1/10) (by norm_num)).scale (pi4Lambda:ℝ) := by
  let D := pi4Bank
  let Tm : List (ℕ × KTmplP) := [(1,pi4PCTemplate)]
  have hpar : KParams D := kparams_of pi4_params
  have hheads : ∀ x ∈ D.tmpls,ktmplHead D x.1 x.2 = true := by
    intro x hx
    simp only [D,pi4Bank,List.mem_singleton] at hx
    subst x
    exact pi4_heads
  have hcells : ∀ x ∈ Tm,∀ y ∈ x.2.cells,
      cellOKb D plane3BaseCatalogue x.1 x.2.N 20 64 y = true := by
    intro x hx y hy
    simp only [Tm,List.mem_singleton] at hx
    subst x
    simp only [pi4PCTemplate,List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact pi4_cell0
    · exact pi4_cell1
  have hhead : ∀ x ∈ Tm,∀ y ∈ x.2.head,
      pieceOK (D.cat x.1) D.Q D.α ((x.1:ℚ)/D.Q) D.depth D.cF D.Pbad y.1 y.2 = true := by
    intro x hx y hy
    simp only [Tm,List.mem_singleton] at hx
    subst x
    simp only [pi4PCTemplate,List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pi4Piece2_check
    · exact pi4Piece3_check
    · exact pi4Piece4_check
    · exact pi4Piece5_check
    · exact pi4Piece6_check
    · exact pi4Piece7_check
    · exact pi4Piece8_check
    · exact pi4Piece9_check
    · exact pi4Piece10_check
    · exact pi4Piece11_check
    · exact pi4Piece12_check
    · exact pi4Piece13_check
    · exact pi4Piece14_check
    · exact pi4Piece15_check
    · exact pi4Piece16_check
    · exact pi4Piece17_check
    · exact pi4Piece18_check
    · exact pi4Piece19_check
    · exact pi4Piece20_check
    · exact pi4Piece21_check
    · exact pi4Piece22_check
    · exact pi4Piece23_check
    · exact pi4Piece24_check
    · exact pi4Piece25_check
    · exact pi4Piece26_check
    · exact pi4Piece27_check
    · exact pi4Piece28_check
    · exact pi4Piece29_check
    · exact pi4Piece30_check
    · exact pi4Piece31_check
    · exact pi4Piece32_check
    · exact pi4Piece33_check
    · exact pi4Piece34_check
    · exact pi4Piece35_check
    · exact pi4Piece36_check
    · exact pi4Piece37_check
    · exact pi4Piece38_check
  have hcat : KCatValidFam (1/10) (by norm_num) const 1
      (SeqFamily.poly (hpoleF 4 (coefficients 0 15)) (hpoleE 4 (coefficients 0 15))
        (altGeom (1/10) (by norm_num)).geometry)
      D.shifts D.Q D.Pbad (coefficientThreshold 0 15) D.kcat := by
    exact hpole_refined_catalogue 4 (by decide) (coefficients 0 15) (1/10)
      (by norm_num) const 1 [⟨2,1,1⟩,⟨2,1,1⟩] 2 2 (coefficientThreshold 0 15)
      (by decide) (by decide) (fun p _ hp => coefficients_mem 0 15 hp)
      pi4Chambers (by intro j hj; norm_num [pi4Chambers] at hj; omega)
  haveI : NeZero D.M := ⟨by change (2:ℕ)≠0; decide⟩
  exact hasScaledContent_of_periodic_control D hpar pi4_class hheads
    (1/10) (by norm_num) (by norm_num [D,pi4Bank,plane3Bank]) const 1 _ (by rfl)
    (hpole_alt_control 4 (by decide) (coefficients 0 15) (1/10) (by norm_num)
      (by norm_num) const 1 2)
    (Content.SmallPrimes.SmallBudget.sqrtLog (prefixCutoff 0 15) (32*crudeFactor 0 15))
    (coefficientThreshold 0 15) (by norm_num [D,pi4Bank,plane3Bank]) plane3Translation Tm rfl
    (fun x hx y hy => (cellOKb_facts (by change (1:ℕ)≤2; decide : 1≤D.Q)
      (by norm_num [D,pi4Bank,plane3Bank]) (hcells x hx y hy)).1)
    (fun x hx y hy => (cellOKb_facts (by change (1:ℕ)≤2; decide : 1≤D.Q)
      (by norm_num [D,pi4Bank,plane3Bank]) (hcells x hx y hy)).2)
    hhead hcat (plane3_translated_catalogue 0 15 (1/10) (by norm_num) const 1)
    (plane3_pre 0 15 const 1)

theorem pi4_content : HasScaledContent
    (pi4Family.restrictAdm (fun n => SeqFamily.scale P3G.geometry n%2=0))
    (SeqFamily.scale P3G.geometry) (pi4Lambda:ℝ) := by
  change HasScaledContent
    (((altGeom (1/10) (by norm_num)).seqFamily
      (datum 0 15 (by norm_num)).f (datum 0 15 (by norm_num)).e
      (datum 0 15 (by norm_num)).xi 1).restrictAdm
        (fun n => SeqFamily.scale (altGeom (1/10) (by norm_num)).geometry n%2=0))
    (SeqFamily.scale (altGeom (1/10) (by norm_num)).geometry) (pi4Lambda:ℝ)
  rw [datum_f,datum_e]
  exact pi4_content_hpole _
end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_content_hpole
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_content
