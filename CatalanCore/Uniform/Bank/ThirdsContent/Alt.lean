module

public import CatalanCore.Uniform.Bank.ThirdsContent.Family
public import CatalanCore.Uniform.Content.BankShared.Reindex
public import CatalanCore.Uniform.Bank.Thirds.Geom

@[expose] public section
set_option Elab.async false

/-! # Crude clearing on the alternating geometries (lane B, B4b)

For `altGeom c` with `0 < c ≤ 1` and every even scale, every member of the family is
`p ^ Ecrude (cFr Fr) r p`-integral for every prime `p`.  Instantiated at `G310` (thirds). -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid Polynomial Finset
  CatalanCore.Uniform CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.Shape

theorem altGeom_borderSize_le (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {r : ℕ} (hr : r % 2 = 0) :
    (altGeom c hc).borderSize r ≤ r := by
  rw [altGeom_borderSize c hc hr]
  refine (min_le_left _ _).trans ?_
  apply Nat.ceil_le.2
  have : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  nlinarith

theorem altGeom_gle_Ecrude (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (Fr : Frame) (depth : ℕ)
    (i : ((altGeom c hc).family Fr depth).ι) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime] :
    GLE p (Ecrude (cFr Fr) i.1 p) (((altGeom c hc).family Fr depth).Q i) := by
  have hbs := altGeom_borderSize_le c hc hc1 hr
  have hX := altGeom_X c hc hr
  have hY := altGeom_Y c hc hr
  have hC := altGeom_C c hc i.1
  have hk : ((altGeom c hc).geometry i.1).k = (altGeom c hc).borderSize i.1 :=
    geometry_k_eq_borderSize _ _
  refine polynomial_gle_Ecrude Fr (altGeom c hc).geometry i ?_ ?_ p
  · intro a ha
    simp only [Finset.mem_union] at ha
    rcases ha with (ha | ha) | ha
    · rw [hC, Finset.mem_range] at ha; omega
    · rw [hX, Finset.mem_image, ] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      rw [Finset.mem_range] at hj; omega
    · rw [hY, Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      rw [Finset.mem_range] at hj; omega
  · have h1 : i.2.card ≤ i.1 := by
      have := Finset.card_le_univ i.2
      have hc : ((altGeom c hc).geometry i.1).C.card = i.1 := by rw [hC, Finset.card_range]
      rw [Fintype.card_coe] at this
      omega
    omega

end CatalanCore.Uniform.Bank.ThirdsContent
