module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.EntriesData
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.ListDot
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open Finset
def columnPairs : List (List ℤ × List ℤ) := [(momentColumn0.map Int.ofNat,zetaColumn0.map Int.ofNat),
(momentColumn1.map Int.ofNat,zetaColumn1.map Int.ofNat),
(momentColumn2.map Int.ofNat,zetaColumn2.map Int.ofNat),
(momentColumn3.map Int.ofNat,zetaColumn3.map Int.ofNat),
(momentColumn4.map Int.ofNat,zetaColumn4.map Int.ofNat),
(momentColumn5.map Int.ofNat,zetaColumn5.map Int.ofNat),
(momentColumn6.map Int.ofNat,zetaColumn6.map Int.ofNat),
(momentColumn7.map Int.ofNat,zetaColumn7.map Int.ofNat),
(momentColumn8.map Int.ofNat,zetaColumn8.map Int.ofNat),
(momentColumn9.map Int.ofNat,zetaColumn9.map Int.ofNat),
(momentColumn10.map Int.ofNat,zetaColumn10.map Int.ofNat),
(momentColumn11.map Int.ofNat,zetaColumn11.map Int.ofNat),
(momentColumn12.map Int.ofNat,zetaColumn12.map Int.ofNat),
(momentColumn13.map Int.ofNat,zetaColumn13.map Int.ofNat),
(momentColumn14.map Int.ofNat,zetaColumn14.map Int.ofNat),
(momentColumn15.map Int.ofNat,zetaColumn15.map Int.ofNat),
(momentColumn16.map Int.ofNat,zetaColumn16.map Int.ofNat),
(momentColumn17.map Int.ofNat,zetaColumn17.map Int.ofNat),
(momentColumn18.map Int.ofNat,zetaColumn18.map Int.ofNat),
(momentColumn19.map Int.ofNat,zetaColumn19.map Int.ofNat),
(momentColumn20.map Int.ofNat,zetaColumn20.map Int.ofNat),
(momentColumn21.map Int.ofNat,zetaColumn21.map Int.ofNat),
(momentColumn22.map Int.ofNat,zetaColumn22.map Int.ofNat),
(momentColumn23.map Int.ofNat,zetaColumn23.map Int.ofNat),
(momentColumn24.map Int.ofNat,zetaColumn24.map Int.ofNat),
(momentColumn25.map Int.ofNat,zetaColumn25.map Int.ofNat),
(momentColumn26.map Int.ofNat,zetaColumn26.map Int.ofNat),
(momentColumn27.map Int.ofNat,zetaColumn27.map Int.ofNat),
(momentColumn28.map Int.ofNat,zetaColumn28.map Int.ofNat),
(momentColumn29.map Int.ofNat,zetaColumn29.map Int.ofNat),
(momentColumn30.map Int.ofNat,zetaColumn30.map Int.ofNat),
(momentColumn31.map Int.ofNat,zetaColumn31.map Int.ofNat),
(momentColumn32.map Int.ofNat,zetaColumn32.map Int.ofNat),
(momentColumn33.map Int.ofNat,zetaColumn33.map Int.ofNat),
(momentColumn34.map Int.ofNat,zetaColumn34.map Int.ofNat),
(momentColumn35.map Int.ofNat,zetaColumn35.map Int.ofNat),
(momentColumn36.map Int.ofNat,zetaColumn36.map Int.ofNat),
(momentColumn37.map Int.ofNat,zetaColumn37.map Int.ofNat),
(momentColumn38.map Int.ofNat,zetaColumn38.map Int.ofNat),
(momentColumn39.map Int.ofNat,zetaColumn39.map Int.ofNat),
(momentColumn40.map Int.ofNat,zetaColumn40.map Int.ofNat),
(momentColumn41.map Int.ofNat,zetaColumn41.map Int.ofNat),
(momentColumn42.map Int.ofNat,zetaColumn42.map Int.ofNat),
(momentColumn43.map Int.ofNat,zetaColumn43.map Int.ofNat),
(momentColumn44.map Int.ofNat,zetaColumn44.map Int.ofNat),
(momentColumn45.map Int.ofNat,zetaColumn45.map Int.ofNat),
(momentColumn46.map Int.ofNat,zetaColumn46.map Int.ofNat),
(momentColumn47.map Int.ofNat,zetaColumn47.map Int.ofNat),
(momentColumn48.map Int.ofNat,zetaColumn48.map Int.ofNat),
(momentColumn49.map Int.ofNat,zetaColumn49.map Int.ofNat),
(momentColumn50.map Int.ofNat,zetaColumn50.map Int.ofNat),
(momentColumn51.map Int.ofNat,zetaColumn51.map Int.ofNat),
(momentColumn52.map Int.ofNat,zetaColumn52.map Int.ofNat),
(momentColumn53.map Int.ofNat,zetaColumn53.map Int.ofNat),
(momentColumn54.map Int.ofNat,zetaColumn54.map Int.ofNat),
(momentColumn55.map Int.ofNat,zetaColumn55.map Int.ofNat),
(momentColumn56.map Int.ofNat,zetaColumn56.map Int.ofNat),
(momentColumn57.map Int.ofNat,zetaColumn57.map Int.ofNat),
(momentColumn58.map Int.ofNat,zetaColumn58.map Int.ofNat),
(momentColumn59.map Int.ofNat,zetaColumn59.map Int.ofNat),
(momentColumn60.map Int.ofNat,zetaColumn60.map Int.ofNat),
(momentColumn61.map Int.ofNat,zetaColumn61.map Int.ofNat),
(momentColumn62.map Int.ofNat,zetaColumn62.map Int.ofNat),
(momentColumn63.map Int.ofNat,zetaColumn63.map Int.ofNat),
(momentColumn64.map Int.ofNat,zetaColumn64.map Int.ofNat),
(momentColumn65.map Int.ofNat,zetaColumn65.map Int.ofNat),
(momentColumn66.map Int.ofNat,zetaColumn66.map Int.ofNat),
(momentColumn67.map Int.ofNat,zetaColumn67.map Int.ofNat),
(momentColumn68.map Int.ofNat,zetaColumn68.map Int.ofNat),
(momentColumn69.map Int.ofNat,zetaColumn69.map Int.ofNat),
(momentColumn70.map Int.ofNat,zetaColumn70.map Int.ofNat),
(momentColumn71.map Int.ofNat,zetaColumn71.map Int.ofNat),
(momentColumn72.map Int.ofNat,zetaColumn72.map Int.ofNat),
(momentColumn73.map Int.ofNat,zetaColumn73.map Int.ofNat),
(momentColumn74.map Int.ofNat,zetaColumn74.map Int.ofNat),
(momentColumn75.map Int.ofNat,zetaColumn75.map Int.ofNat),
(momentColumn76.map Int.ofNat,zetaColumn76.map Int.ofNat),
(momentColumn77.map Int.ofNat,zetaColumn77.map Int.ofNat),
(momentColumn78.map Int.ofNat,zetaColumn78.map Int.ofNat),
(momentColumn79.map Int.ofNat,zetaColumn79.map Int.ofNat),
(momentColumn80.map Int.ofNat,zetaColumn80.map Int.ofNat),
(momentColumn81.map Int.ofNat,zetaColumn81.map Int.ofNat),
(momentColumn82.map Int.ofNat,zetaColumn82.map Int.ofNat),
(momentColumn83.map Int.ofNat,zetaColumn83.map Int.ofNat),
(momentColumn84.map Int.ofNat,zetaColumn84.map Int.ofNat),
(momentColumn85.map Int.ofNat,zetaColumn85.map Int.ofNat),
(momentColumn86.map Int.ofNat,zetaColumn86.map Int.ofNat),
(momentColumn87.map Int.ofNat,zetaColumn87.map Int.ofNat),
(momentColumn88.map Int.ofNat,zetaColumn88.map Int.ofNat),
(momentColumn89.map Int.ofNat,zetaColumn89.map Int.ofNat),
(momentColumn90.map Int.ofNat,zetaColumn90.map Int.ofNat),
(momentColumn91.map Int.ofNat,zetaColumn91.map Int.ofNat),
(momentColumn92.map Int.ofNat,zetaColumn92.map Int.ofNat),
(momentColumn93.map Int.ofNat,zetaColumn93.map Int.ofNat),
(momentColumn94.map Int.ofNat,zetaColumn94.map Int.ofNat),
(momentColumn95.map Int.ofNat,zetaColumn95.map Int.ofNat)]
theorem columnPairs_getD (k : Fin 96) : columnPairs.getD k.val ([],[]) =
    ((momentTable k).map Int.ofNat,(zetaTable k).map Int.ofNat) := by
  fin_cases k <;> rfl
theorem momentTable_length (k : Fin 96) : (momentTable k).length=130 := by
  fin_cases k <;> rfl
theorem zetaTable_length (k : Fin 96) : (zetaTable k).length=130 := by
  fin_cases k <;> rfl
theorem rowP_length : ∀ r : Fin 97,(proposedPCoefficients r).length≤130 := by decide +kernel
theorem rowD_length : ∀ r : Fin 97,(proposedDCoefficients r).length≤130 := by decide +kernel

def contractionList (r : Fin 97) : List ℤ :=
  columnPairs.map (fun pair =>(intDot (proposedPCoefficients r) pair.1 -
    506*intDot (proposedDCoefficients r) pair.2)%1009)

theorem list_map_getD {α β : Type*} (f : α → β) (xs : List α) (i : ℕ) (d : α) :
    (xs.map f).getD i (f d)=f (xs.getD i d) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,Option.getD_map]

theorem contractionList_getD (r : Fin 97) (k : Fin 96) :
    (contractionList r).getD k.val 0=contractionInt r k%1009 := by
  unfold contractionList
  have hzero : (intDot (proposedPCoefficients r) ([]:List ℤ)-
      506*intDot (proposedDCoefficients r) ([]:List ℤ))%1009=0 := by
    cases proposedPCoefficients r <;> cases proposedDCoefficients r <;> simp [intDot]
  rw [← hzero,list_map_getD (fun pair : List ℤ × List ℤ =>
    (intDot (proposedPCoefficients r) pair.1-506*intDot (proposedDCoefficients r) pair.2)%1009)
    columnPairs k.val ([],[]),columnPairs_getD]
  simp only [Prod.fst,Prod.snd]
  rw [intDot_eq_sum_fin _ _ (rowP_length r) (by simp [momentTable_length]),
    intDot_eq_sum_fin _ _ (rowD_length r) (by simp [zetaTable_length])]
  unfold contractionInt
  congr 2
  · apply sum_congr rfl
    intro i _
    have hh := list_map_getD Int.ofNat (momentTable k) i.val 0
    simp only [Int.ofNat_zero,Int.ofNat_eq_natCast] at hh
    rw [hh]
  · congr 1
    apply sum_congr rfl
    intro i _
    have hh := list_map_getD Int.ofNat (zetaTable k) i.val 0
    simp only [Int.ofNat_zero,Int.ofNat_eq_natCast] at hh
    rw [hh]

end CatalanMeasure.Parametric.ProposedBase
