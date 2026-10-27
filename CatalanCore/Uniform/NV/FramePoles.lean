module
public import CatalanCore.Uniform.NV.PoleSource
public import CatalanCore.Frame.Spec
@[expose] public section
open Polynomial Finset
namespace CatalanCore.Uniform.NV

abbrev FramePoleIndex (Fr : Frame) (L : ℕ) := Fin Fr.d × Fin L

def framePole (Fr : Frame) (L : ℕ) (u : FramePoleIndex Fr L) : ℚ :=
  -Fr.μ u.1-(u.2.val:ℚ)
def framePoleWeight (Fr : Frame) (L : ℕ) (u : FramePoleIndex Fr L) : ℚ :=
  (Fr.w u.1:ℚ)/Fr.norm

theorem framePole_injective (Fr : Frame) (L : ℕ) : Function.Injective (framePole Fr L) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  change -Fr.μ i-(j.val:ℚ) = -Fr.μ k-(l.val:ℚ) at h
  have hjl : j.val ≤ l.val := by
    have he : (j.val:ℚ) < (l.val:ℚ)+1 := by
      have hi := Fr.hμ i
      have hk := Fr.hμ k
      linarith
    have hn : j.val < l.val+1 := by exact_mod_cast he
    omega
  have hlj : l.val ≤ j.val := by
    have he : (l.val:ℚ) < (j.val:ℚ)+1 := by
      have hi := Fr.hμ i
      have hk := Fr.hμ k
      linarith
    have hn : l.val < j.val+1 := by exact_mod_cast he
    omega
  have hj : j = l := Fin.ext (Nat.le_antisymm hjl hlj)
  have hi : i = k := by
    have hm : Fr.μ i = Fr.μ k := by rw [hj] at h;linarith
    by_contra hn
    exact Fr.hμinj i k hn hm
  exact Prod.ext hi hj

noncomputable def framePoleSet (Fr : Frame) (L : ℕ) : Finset ℚ :=
  univ.image (framePole Fr L)
noncomputable def frameResidue (Fr : Frame) (L : ℕ) : ℚ → ℚ :=
  Function.extend (framePole Fr L) (framePoleWeight Fr L) (fun _ => 0)

@[simp] theorem frameResidue_atPole (Fr : Frame) (L : ℕ) (u : FramePoleIndex Fr L) :
    frameResidue Fr L (framePole Fr L u) = framePoleWeight Fr L u :=
  (framePole_injective Fr L).extend_apply (framePoleWeight Fr L) _ u

theorem framePoleSet_card (Fr : Frame) (L : ℕ) : (framePoleSet Fr L).card = Fr.d*L := by
  rw [framePoleSet,Finset.card_image_of_injective _ (framePole_injective Fr L),Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]

theorem frameResidue_sum (Fr : Frame) (L : ℕ) :
    ∑ a ∈ framePoleSet Fr L,frameResidue Fr L a = 0 := by
  unfold framePoleSet
  rw [Finset.sum_image]
  · simp only [frameResidue_atPole]
    rw [Fintype.sum_prod_type]
    simp only [framePoleWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hw : (∑ i : Fin Fr.d,(Fr.w i:ℚ)) = 0 := by exact_mod_cast Fr.hw
    rw [← Finset.mul_sum,← Finset.sum_div,hw,zero_div,mul_zero]
  · exact fun _ _ _ _ h => framePole_injective Fr L h

theorem frameResidue_ne_zero (Fr : Frame) (L : ℕ) (hw : ∀ i, Fr.w i ≠ 0)
    (a : ℚ) (ha : a ∈ framePoleSet Fr L) : frameResidue Fr L a ≠ 0 := by
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ha
  rw [frameResidue_atPole]
  exact div_ne_zero (by exact_mod_cast hw u.1) (ne_of_gt Fr.hnorm)

theorem framePole_strip (Fr : Frame) (L : ℕ) (a : ℚ) (ha : a ∈ framePoleSet Fr L) :
    -(L:ℚ) ≤ a ∧ a < 0 := by
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ha
  have hμ := Fr.hμ u.1
  have hj : (u.2.val:ℚ)+1 ≤ L := by exact_mod_cast (show u.2.val+1 ≤ L by omega)
  have hj0 : 0 ≤ (u.2.val:ℚ) := Nat.cast_nonneg _
  dsimp [framePole]
  constructor <;> linarith

theorem frame_pole_certificate (Fr : Frame) (L : ℕ) (hL : 1 ≤ L)
    (hw : ∀ i, Fr.w i ≠ 0) (a : ℚ) (ha : a ∈ framePoleSet Fr L) :
    IsolatedStepPole (L:ℚ) a (poleDenominator (framePoleSet Fr L))
      (poleNumerator (framePoleSet Fr L) (frameResidue Fr L)) := by
  apply pole_table_isolated (framePoleSet Fr L) (frameResidue Fr L) (L:ℚ) a
  · exact_mod_cast (show 0 < L by omega)
  · exact ha
  · exact frameResidue_ne_zero Fr L hw a ha
  · exact framePole_strip Fr L

theorem sum_framePoleSet (Fr : Frame) (L : ℕ) (F : ℚ → ℚ → ℚ) :
    (∑ a ∈ framePoleSet Fr L,F a (frameResidue Fr L a)) =
      ∑ u : FramePoleIndex Fr L,F (framePole Fr L u) (framePoleWeight Fr L u) := by
  unfold framePoleSet
  rw [Finset.sum_image]
  · simp only [frameResidue_atPole]
  · exact fun _ _ _ _ h => framePole_injective Fr L h

theorem framePoleSet_nonempty (Fr : Frame) (L : ℕ) (hd : 1 ≤ Fr.d) (hL : 1 ≤ L) :
    (framePoleSet Fr L).Nonempty := by
  let u : FramePoleIndex Fr L := (⟨0,by omega⟩,⟨0,by omega⟩)
  exact ⟨framePole Fr L u,Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩⟩

theorem frame_pole_count_ge_two (Fr : Frame) (L : ℕ) (hd : 1 ≤ Fr.d) (hL : 1 ≤ L)
    (hw : ∀ i, Fr.w i ≠ 0) : 2 ≤ Fr.d*L := by
  have hn := framePoleSet_nonempty Fr L hd hL
  have hpos := Finset.Nonempty.card_pos hn
  rw [← framePoleSet_card]
  by_contra hsmall
  have hc : (framePoleSet Fr L).card = 1 := by omega
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
  have hsum := frameResidue_sum Fr L
  rw [ha,Finset.sum_singleton] at hsum
  exact frameResidue_ne_zero Fr L hw a (by rw [ha];simp) hsum

/-- The full generic frame source data are explicit finite polynomials. -/
theorem frame_pole_degrees (Fr : Frame) (L : ℕ) :
    (poleDenominator (framePoleSet Fr L)).natDegree = Fr.d*L ∧
    (poleNumerator (framePoleSet Fr L) (frameResidue Fr L)).natDegree ≤ Fr.d*L-2 := by
  constructor
  · rw [degree_poleDenominator,framePoleSet_card]
  · simpa only [framePoleSet_card] using degree_poleNumerator
      (framePoleSet Fr L) (frameResidue Fr L) (frameResidue_sum Fr L)
end CatalanCore.Uniform.NV


