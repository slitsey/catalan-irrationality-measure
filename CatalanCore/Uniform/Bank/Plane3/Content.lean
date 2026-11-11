module

public import CatalanCore.Uniform.Bank.Plane3.Arithmetic

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Plane 3: finite refined periodic content (Q09)
The accepted numeric bank is connected to the actual family, with all rational
coefficients, every common deletion, and every finite depth. No ND assumption.
-/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support
open CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
open CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.KTerm

/- These elementary depth transports use only zero debit. They do not alter
the shared checker, its proof, or any frozen contract. -/
private theorem stripOK_zero_debit (cat : List Branch)
    (hz : ∀ br ∈ cat, br.debit = 0) (q : ℕ) (α κ : ℚ) (depth : ℕ)
    (P : QPiece) (br : Branch) (R e : ℚ) (st : Strip) :
    stripOK cat q α κ depth P br R e st = stripOK cat q α κ 0 P br R e st := by
  unfold stripOK
  cases h : nth cat st.yi with
  | none => rfl
  | some y =>
    have hy := hz y (nth_mem cat st.yi h)
    simp only [hy, Nat.zero_mul, zero_mul, Nat.cast_zero, add_zero]

private theorem pieceOK_zero_debit (cat : List Branch)
    (hz : ∀ br ∈ cat, br.debit = 0) (q : ℕ) (α κ : ℚ) (depth cF Pbad : ℕ)
    (P : QPiece) (cert : Cert) :
    pieceOK cat q α κ depth cF Pbad P cert = pieceOK cat q α κ 0 cF Pbad P cert := by
  unfold pieceOK
  cases h : nth cat cert.bi with
  | none => rfl
  | some br =>
    have hb := hz br (nth_mem cat cert.bi h)
    simp only [hb, Nat.zero_mul, zero_mul, Nat.cast_zero, add_zero]
    simp_rw [stripOK_zero_debit cat hz q α κ depth]

private theorem catalogue_debit : ∀ br ∈ plane3Catalogue,br.debit=0 := by
  intro br hb
  change br ∈ IntegerPoleRows.catalogue 4 ++ plane3Chambers.flatMap (HPolePeriodRows.refinedBranches 4) at hb
  rcases List.mem_append.mp hb with hb | hb
  · simp only [IntegerPoleRows.catalogue,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rfl
  · obtain ⟨j,hj,hb⟩ := List.mem_flatMap.mp hb
    simp only [HPolePeriodRows.refinedBranches,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl | rfl <;> rfl

private theorem compiled_debit (depth j : ℕ) :
    ∀ br ∈ (plane3Bank depth).cat j, br.debit = 0 := by
  intro br hb
  obtain ⟨b, hmem, heq⟩ := List.mem_map.mp hb
  subst br
  exact catalogue_debit b hmem

private theorem base_compiled_debit (depth j : ℕ) :
    ∀ br ∈ plane3BaseCatalogue.map
      (KBranch.compile (plane3Bank depth).tS ((plane3Bank depth).bS j) (plane3Bank depth).cS),
      br.debit = 0 := by
  intro br hb
  obtain ⟨b, hmem, heq⟩ := List.mem_map.mp hb
  subst br
  simp only [plane3BaseCatalogue, List.mem_singleton] at hmem
  subst b
  rfl

private theorem head_depth (depth : ℕ) (P : QPiece) (cert : Cert)
    (h : pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 P cert = true) :
    pieceOK ((plane3Bank depth).cat 1) 2 (13/200) (1/2) depth 1 2 P cert = true := by
  rw [pieceOK_zero_debit _ (compiled_debit depth 1)]
  exact h

private theorem cell_depth (depth : ℕ) (y : QPiece × Cert)
    (h : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816 y = true) :
    cellOKb (plane3Bank depth) plane3BaseCatalogue 1 3 200 816 y = true := by
  unfold cellOKb
  change (pieceOK _ 2 (13/200) (1/2) depth 1 2 y.1 y.2 && _) = true
  rw [pieceOK_zero_debit _ (base_compiled_debit depth 1)]
  exact h

theorem plane3_content_hpole (v u : ℚ) (const : ℝ) (depth : ℕ) :
    HasScaledContent
      (AltEvenFam (13/100) (by norm_num) const depth
        (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
          (altGeom (13/100) (by norm_num)).geometry))
      (altGeom (13/100) (by norm_num)).scale
      (plane3Lambda:ℝ) := by
  let D := plane3Bank depth
  let Tm : List (ℕ × KTmplP) := [(1,plane3PCTemplate)]
  have hpar : KParams D := kparams_of plane3_params
  have hheads : ∀ x ∈ D.tmpls, ktmplHead D x.1 x.2 = true := by
    intro x hx
    simp only [D, plane3Bank, List.mem_singleton] at hx
    subst x
    exact plane3_heads
  have hcells : ∀ x ∈ Tm, ∀ y ∈ x.2.cells,
      cellOKb D plane3BaseCatalogue x.1 x.2.N 200 816 y = true := by
    intro x hx y hy
    simp only [Tm, List.mem_singleton] at hx
    subst x
    simp only [plane3PCTemplate, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_depth depth _ plane3_cell0
    · exact cell_depth depth _ plane3_cell1
    · exact cell_depth depth _ plane3_cell2
    · exact cell_depth depth _ plane3_cell3
    · exact cell_depth depth _ plane3_cell4
    · exact cell_depth depth _ plane3_cell5
    · exact cell_depth depth _ plane3_cell6
    · exact cell_depth depth _ plane3_cell7
    · exact cell_depth depth _ plane3_cell8
    · exact cell_depth depth _ plane3_cell9
    · exact cell_depth depth _ plane3_cell10
    · exact cell_depth depth _ plane3_cell11
    · exact cell_depth depth _ plane3_cell12
    · exact cell_depth depth _ plane3_cell13
    · exact cell_depth depth _ plane3_cell14
    · exact cell_depth depth _ plane3_cell15
    · exact cell_depth depth _ plane3_cell16
    · exact cell_depth depth _ plane3_cell17
    · exact cell_depth depth _ plane3_cell18
    · exact cell_depth depth _ plane3_cell19
    · exact cell_depth depth _ plane3_cell20
    · exact cell_depth depth _ plane3_cell21
    · exact cell_depth depth _ plane3_cell22
    · exact cell_depth depth _ plane3_cell23
    · exact cell_depth depth _ plane3_cell24
    · exact cell_depth depth _ plane3_cell25
  have hhead : ∀ x ∈ Tm, ∀ y ∈ x.2.head,
      pieceOK (D.cat x.1) D.Q D.α ((x.1 : ℚ)/D.Q) D.depth D.cF D.Pbad y.1 y.2 = true := by
    intro x hx y hy
    simp only [Tm, List.mem_singleton] at hx
    subst x
    simp only [plane3PCTemplate, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact head_depth depth _ _ contentPiece26_check
    · exact head_depth depth _ _ contentPiece27_check
    · exact head_depth depth _ _ contentPiece28_check
    · exact head_depth depth _ _ contentPiece29_check
    · exact head_depth depth _ _ contentPiece30_check
    · exact head_depth depth _ _ contentPiece31_check
    · exact head_depth depth _ _ contentPiece32_check
    · exact head_depth depth _ _ contentPiece33_check
    · exact head_depth depth _ _ contentPiece34_check
    · exact head_depth depth _ _ contentPiece35_check
    · exact head_depth depth _ _ contentPiece36_check
    · exact head_depth depth _ _ contentPiece37_check
    · exact head_depth depth _ _ contentPiece38_check
    · exact head_depth depth _ _ contentPiece39_check
    · exact head_depth depth _ _ contentPiece40_check
    · exact head_depth depth _ _ contentPiece41_check
    · exact head_depth depth _ _ contentPiece42_check
    · exact head_depth depth _ _ contentPiece43_check
    · exact head_depth depth _ _ contentPiece44_check
    · exact head_depth depth _ _ contentPiece45_check
    · exact head_depth depth _ _ contentPiece46_check
    · exact head_depth depth _ _ contentPiece47_check
    · exact head_depth depth _ _ contentPiece48_check
    · exact head_depth depth _ _ contentPiece49_check
    · exact head_depth depth _ _ contentPiece50_check
    · exact head_depth depth _ _ contentPiece51_check
    · exact head_depth depth _ _ contentPiece52_check
    · exact head_depth depth _ _ contentPiece53_check
    · exact head_depth depth _ _ contentPiece54_check
  haveI : NeZero D.M := ⟨by change (2 : ℕ) ≠ 0; decide⟩
  exact hasScaledContent_of_periodic_control D hpar plane3_class hheads
    (13/100) (by norm_num) (by norm_num [D, plane3Bank]) const depth _ (by rfl)
    (hpole_alt_control 4 (by decide) (coefficients v u) (13/100) (by norm_num)
      (by norm_num) const depth 2)
    (Content.SmallPrimes.SmallBudget.sqrtLog (prefixCutoff v u) (32*crudeFactor v u))
    (coefficientThreshold v u) (by norm_num [D,plane3Bank]) plane3Translation Tm rfl
    (fun x hx y hy => (cellOKb_facts (by change (1 : ℕ) ≤ 2; decide : 1 ≤ D.Q) (by norm_num [D,plane3Bank])
      (hcells x hx y hy)).1)
    (fun x hx y hy => (cellOKb_facts (by change (1 : ℕ) ≤ 2; decide : 1 ≤ D.Q) (by norm_num [D,plane3Bank])
      (hcells x hx y hy)).2)
    hhead (plane3_catalogue v u (13/100) (by norm_num) const depth)
    (plane3_translated_catalogue v u (13/100) (by norm_num) const depth)
    (plane3_pre v u const depth)

theorem plane3_content (v u : ℚ) (hu : u ≠ 0) (depth : ℕ) :
  HasScaledContent
    (((Content.Shape.altGeom (13/100) (by norm_num)).seqFamily
      (Plane3.datum v u hu).f (Plane3.datum v u hu).e (Plane3.datum v u hu).xi depth).restrictAdm
        (fun n => SeqFamily.scale (Content.Shape.altGeom (13/100) (by norm_num)).geometry n % 2 = 0))
    (SeqFamily.scale (Content.Shape.altGeom (13/100) (by norm_num)).geometry)
    (plane3Lambda:ℝ) := by
  rw [datum_f, datum_e]
  exact plane3_content_hpole v u (datum v u hu).xi depth

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_content_hpole
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_content
