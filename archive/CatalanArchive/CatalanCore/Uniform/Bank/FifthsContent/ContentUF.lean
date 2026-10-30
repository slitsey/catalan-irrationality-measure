import CatalanCore.Uniform.Bank.FifthsContent.Content5
import CatalanCore.Uniform.Bank.FifthsContent.FullUF
import CatalanCore.Uniform.Bank.FifthsContent.CoversUF.J1
import CatalanCore.Uniform.Bank.FifthsContent.CoversUF.J2
import CatalanCore.Uniform.Bank.FifthsContent.CoversUF.J3
import CatalanCore.Uniform.Bank.FifthsContent.CoversUF.J4
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The UF fifths content (lane B, B5c)

`fifths_content_UF`: `HasScaledContent (even-scale F5 family) F5.scale LamFin5` for each fifths
frame (`ShiftData Fr 5 u`), from `alt_content_of_bounds`, the sawtooth/table-T/M3D covers of the
template pieces, and the LP piece covers (`depth ≤ 1000`). -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid CatalanFrames.Fifths

/-- The UF template of the unit class `c` of `ZMod 10`. -/
noncomputable def tmplUU (u : ℕ) (c : ZMod 10) : Template := tmplJU (classIndex u c.val)

theorem mass_tmplUU {u : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5) :
    contentConstant 10 (tmplUU u) = (LamFinU : ℝ) := by
  unfold contentConstant
  rw [unitClasses_ten, totient_ten]
  have h1 : (1 : ZMod 10).val = 1 := by decide
  have h3 : (3 : ZMod 10).val = 3 := by decide
  have h7 : (7 : ZMod 10).val = 7 := by decide
  have h9 : (9 : ZMod 10).val = 9 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [tmplUU, tmplJU_mass, h1, h3, h7, h9]
  have key : ∀ u, 1 ≤ u → u < 5 →
      (profileMassU (classIndex u 1) + profileMassU (classIndex u 3) + profileMassU (classIndex u 7) +
        profileMassU (classIndex u 9)) =
      profileMassU 1 + profileMassU 2 + profileMassU 3 + profileMassU 4 := by
    intro u h0 h1'
    interval_cases u <;> simp [classIndex, profileMassU] <;> ring
  rw [← LamFinU_eq]
  push_cast
  have := key u hu0 hu1
  have : ((profileMassU (classIndex u 1) : ℚ) : ℝ) + (profileMassU (classIndex u 3) : ℚ) +
      (profileMassU (classIndex u 7) : ℚ) + (profileMassU (classIndex u 9) : ℚ) =
      (profileMassU 1 : ℚ) + (profileMassU 2 : ℚ) + (profileMassU 3 : ℚ) + (profileMassU 4 : ℚ) := by
    exact_mod_cast this
  push_cast at this ⊢
  linarith

theorem fifths_content_UF {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ)
    (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    HasScaledContent (AltE (2 / 9) two_ninths_pos Fr depth) F5.scale (LamFinU : ℝ) := by
  have hu0 := T.hu0
  have hu1 := T.hu1
  refine alt_content_of_bounds (2 / 9) two_ninths_pos (by norm_num) Fr depth 10 (LamFinU : ℝ) B5
    (fun _ => tmplUU u) (63 / 10) ?_ ?_ ?_ ?_ ?_
  · intro ε hε
    rw [mass_tmplUU hu0 hu1]; linarith
  · intro ε hε c hc
    show (tmplJU _).tend ≤ _
    rw [tmplJU_tend]
  · -- tail
    intro ε hε i hi c hc p hp hpc hlt hpf
    have hlt' : 63 * i.1 / 10 < p := by
      have : F5.scale i = i.1 := rfl
      have h2 : (tmplUU u c).tend = 63 / 10 := tmplJU_tend _
      rw [h2, this, floor_63] at hlt
      exact hlt
    refine tail5 T depth (classIndex u c.val) (classIndex_range (q := c.val) hu0 hu1 (by
      have := unit_val hc; omega)).1 i hi p hp ?_ hlt'
    · intro hr1
      refine kq_eq T hc p ?_ hpc
      obtain ⟨hr, -, -⟩ := member_dom depth hi
      omega
  · -- prefix
    intro ε hε i hi c hc p h1 hp hpc hpf
    exact pre5 T depth hcF i hi p hp (by
      have : F5.scale i = i.1 := rfl
      have h2 : (tmplUU u c).t1 = 1 / 900 := rfl
      rw [h2] at h1
      exact h1)
  · -- covers
    intro ε hε i hi c hc P hP p hs ht hp hpc hpf
    have hP' : P ∈ fullListU (classIndex u c.val) := hP
    have hs0 : (1 / 900 : ℝ) ≤ P.s :=
      chain_mem_s _ _ (fullListU_chain _) P hP'
    have hk : R0 ≤ i.1 → 5 * (fifthsInst T).cd.kq p = classIndex u c.val * p + u := by
      intro hR
      refine kq_eq T hc p ?_ hpc
      have hsc : F5.scale i = i.1 := rfl
      have h3 : ⌊(1 / 900 : ℝ) * (i.1 : ℝ)⌋₊ ≤ ⌊P.s * (F5.scale i : ℝ)⌋₊ := by
        rw [hsc]
        exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hs0 (Nat.cast_nonneg _))
      rw [floor_900] at h3
      unfold R0 at hR
      omega
    obtain ⟨hj1, hj4⟩ : 1 ≤ classIndex u c.val ∧ classIndex u c.val ≤ 4 := by
      have hv := unit_val hc
      exact classIndex_range hu0 hu1 (by omega)
    rcases mem_fullListU hP' with h | h | h | h | h | h | h
    · exact covPrefix0 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix1 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix2 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix3 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix4 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix5 T depth hcF _ P h i hi p hs ht hp hk
    · generalize classIndex u c.val = j at *
      have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hj with rfl | rfl | rfl | rfl
      · exact covProfileU1 T depth hcF hdepth P h i hi p hs ht hp hk
      · exact covProfileU2 T depth hcF hdepth P h i hi p hs ht hp hk
      · exact covProfileU3 T depth hcF hdepth P h i hi p hs ht hp hk
      · exact covProfileU4 T depth hcF hdepth P h i hi p hs ht hp hk

#print axioms fifths_content_UF
end CatalanCore.Uniform.Bank.FifthsContent
