module
public import CatalanCore.Uniform.NV.StepGeometry
@[expose] public section
namespace CatalanCore.Uniform.NV
open Finset

/-- Actual successive step-L edges; missing intermediate nodes cannot be skipped. -/
def StepReaches (Z : Finset ℕ) (L a b : ℕ) : Prop :=
  ∃ j : ℕ, b = a+j*L ∧ ∀ i ≤ j,a+i*L ∈ Z

/-- Finite step chains have a reachable terminal. -/
theorem exists_reachable_terminal (Z : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (a : ℕ) (ha : a ∈ Z) : ∃ b ∈ stepEnds Z L,StepReaches Z L a b := by
  have hex : ∃ j : ℕ,a+j*L ∉ Z := by
    refine ⟨Z.sup id+1,?_⟩
    intro hin
    have hbound : a+(Z.sup id+1)*L ≤ Z.sup id := Finset.le_sup (f := id) hin
    have hmul : Z.sup id+1 ≤ (Z.sup id+1)*L := Nat.le_mul_of_pos_right _ hL
    omega
  let j := Nat.find hex
  have hj : a+j*L ∉ Z := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    have hnot : a ∉ Z := by simpa [hz] using hj
    exact hnot ha
  have hprev : a+(j-1)*L ∈ Z := by
    by_contra hn
    exact Nat.find_min hex (by omega) hn
  have he : a+(j-1)*L+L = a+j*L := by
    calc
      a+(j-1)*L+L = a+((j-1)+1)*L := by ring
      _ = a+j*L := by rw [Nat.sub_add_cancel (show 1 ≤ j by omega)]
  refine ⟨a+(j-1)*L,mem_stepEnds.mpr ⟨hprev,?_⟩,j-1,rfl,?_⟩
  · simpa only [he] using hj
  · intro i hi
    by_contra hn
    exact Nat.find_min hex (by omega) hn

/-- The terminal of a reachable chain is unique. Thus terminal nodes, counted
by componentCount, are canonical labels of the actual finite step components. -/
theorem reachable_terminal_unique (Z : Finset ℕ) (L a b c : ℕ)
    (hb : b ∈ stepEnds Z L) (hc : c ∈ stepEnds Z L)
    (hab : StepReaches Z L a b) (hac : StepReaches Z L a c) : b = c := by
  obtain ⟨j,hbval,hj⟩ := hab
  obtain ⟨k,hcval,hk⟩ := hac
  rcases lt_trichotomy j k with hlt | heq | hgt
  · exfalso
    have hm := hk (j+1) (by omega)
    have he : b+L = a+(j+1)*L := by rw [hbval];ring
    exact (mem_stepEnds.mp hb).2 (he.symm ▸ hm)
  · simpa [hbval,hcval,heq]
  · exfalso
    have hm := hj (k+1) (by omega)
    have he : c+L = a+(k+1)*L := by rw [hcval];ring
    exact (mem_stepEnds.mp hc).2 (he.symm ▸ hm)
end CatalanCore.Uniform.NV


