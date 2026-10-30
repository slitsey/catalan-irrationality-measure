import CatalanCore.Uniform.Bank.FifthsContent.Full
import CatalanCore.Uniform.Bank.FifthsContent.Covers.J1
import CatalanCore.Uniform.Bank.FifthsContent.Covers.J2
import CatalanCore.Uniform.Bank.FifthsContent.Covers.J3
import CatalanCore.Uniform.Bank.FifthsContent.Covers.J4
import CatalanCore.Uniform.Bank.FifthsContent.Covers.P0
import CatalanCore.Uniform.Bank.FifthsContent.Covers.P1
import CatalanCore.Uniform.Bank.FifthsContent.Covers.P2
import CatalanCore.Uniform.Bank.FifthsContent.Covers.P3
import CatalanCore.Uniform.Bank.FifthsContent.Covers.P4
import CatalanCore.Uniform.Bank.FifthsContent.Covers.P5
import CatalanCore.Uniform.Bank.FifthsContent.Pre
import CatalanCore.Uniform.Bank.FifthsContent.Units10
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The no-UF fifths content (lane B, B5c)

`fifths_content_noUF`: `HasScaledContent (even-scale F5 family) F5.scale LamFin5` for each fifths
frame (`ShiftData Fr 5 u`), from `alt_content_of_bounds`, the sawtooth/table-T/M3D covers of the
template pieces, and the LP piece covers (`depth ≤ 1000`). -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid CatalanFrames.Fifths

/-- The template of the unit class `c` of `ZMod 10` for the frame with shift offset `u`. -/
noncomputable def tmplU (u : ℕ) (c : ZMod 10) : Template := tmplJ (classIndex u c.val)

theorem classIndex_range {u q : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5) (hq : q % 5 ≠ 0) :
    1 ≤ classIndex u q ∧ classIndex u q ≤ 4 := by
  unfold classIndex
  split_ifs <;> omega

theorem unit_val {c : ZMod 10} (hc : IsUnit c) : c.val = 1 ∨ c.val = 3 ∨ c.val = 7 ∨ c.val = 9 := by
  have h : c ∈ unitClasses 10 := mem_unitClasses.2 hc
  rw [unitClasses_ten] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp <;> decide

theorem kq_eq {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) {c : ZMod 10} (hc : IsUnit c) (p : ℕ)
    (hp5 : 5 ≤ p) (hpc : (p : ZMod 10) = c) :
    5 * (fifthsInst T).cd.kq p = classIndex u c.val * p + u := by
  have hmod : p % 10 = c.val := by rw [← hpc, ZMod.val_natCast]
  have hv := unit_val hc
  have hp5' : p % 5 = c.val % 5 := by omega
  have hunit : p % 5 ≠ 0 := by omega
  have hs := (firstRoot_spec T.hu0 T.hu1 hp5 hunit).1
  have hj : classIndex u p = classIndex u c.val := by simp only [classIndex, hp5']
  rw [hj] at hs
  exact hs

theorem chain_mem_s : ∀ (l : List Piece) (s0 : ℝ), Chain s0 l → ∀ P ∈ l, s0 ≤ P.s
  | [], _, _, P, hP => by simp at hP
  | Q :: l, s0, h, P, hP => by
    obtain ⟨h1, -, h3, -, -, -, h7⟩ := h
    rcases List.mem_cons.1 hP with rfl | hP
    · exact h1.ge
    · have := chain_mem_s l Q.t h7 P hP
      linarith

theorem floor_63 (r : ℕ) : ⌊(63 / 10 : ℝ) * (r : ℝ)⌋₊ = 63 * r / 10 := by
  have := floor_frac 63 10 r
  simpa using this

theorem floor_900 (r : ℕ) : ⌊(1 / 900 : ℝ) * (r : ℝ)⌋₊ = r / 900 := by
  have := floor_frac 1 900 r
  simpa using this

theorem mass_tmplU {u : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5) :
    contentConstant 10 (tmplU u) = (LamFin5 : ℝ) := by
  unfold contentConstant
  rw [unitClasses_ten, totient_ten]
  have h1 : (1 : ZMod 10).val = 1 := by decide
  have h3 : (3 : ZMod 10).val = 3 := by decide
  have h7 : (7 : ZMod 10).val = 7 := by decide
  have h9 : (9 : ZMod 10).val = 9 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [tmplU, tmplJ_mass, h1, h3, h7, h9]
  have key : ∀ u, 1 ≤ u → u < 5 →
      (profileMass (classIndex u 1) + profileMass (classIndex u 3) + profileMass (classIndex u 7) +
        profileMass (classIndex u 9)) =
      profileMass 1 + profileMass 2 + profileMass 3 + profileMass 4 := by
    intro u h0 h1'
    interval_cases u <;> simp [classIndex, profileMass] <;> ring
  rw [← LamFin5_eq]
  push_cast
  have := key u hu0 hu1
  have : ((profileMass (classIndex u 1) : ℚ) : ℝ) + (profileMass (classIndex u 3) : ℚ) +
      (profileMass (classIndex u 7) : ℚ) + (profileMass (classIndex u 9) : ℚ) =
      (profileMass 1 : ℚ) + (profileMass 2 : ℚ) + (profileMass 3 : ℚ) + (profileMass 4 : ℚ) := by
    exact_mod_cast this
  push_cast at this ⊢
  linarith

theorem fifths_content_noUF {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ)
    (hcF : cFr Fr ≤ 49) (hdepth : depth ≤ 1000) :
    HasScaledContent (AltE (2 / 9) two_ninths_pos Fr depth) F5.scale (LamFin5 : ℝ) := by
  have hu0 := T.hu0
  have hu1 := T.hu1
  refine alt_content_of_bounds (2 / 9) two_ninths_pos (by norm_num) Fr depth 10 (LamFin5 : ℝ) B5
    (fun _ => tmplU u) (63 / 10) ?_ ?_ ?_ ?_ ?_
  · intro ε hε
    rw [mass_tmplU hu0 hu1]; linarith
  · intro ε hε c hc
    show (tmplJ _).tend ≤ _
    rw [tmplJ_tend]
  · -- tail
    intro ε hε i hi c hc p hp hpc hlt hpf
    have hlt' : 63 * i.1 / 10 < p := by
      have : F5.scale i = i.1 := rfl
      have h2 : (tmplU u c).tend = 63 / 10 := tmplJ_tend _
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
      have h2 : (tmplU u c).t1 = 1 / 900 := rfl
      rw [h2] at h1
      exact h1)
  · -- covers
    intro ε hε i hi c hc P hP p hs ht hp hpc hpf
    have hP' : P ∈ fullList (classIndex u c.val) := hP
    have hs0 : (1 / 900 : ℝ) ≤ P.s :=
      chain_mem_s _ _ (fullList_chain _) P hP'
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
    rcases mem_fullList hP' with h | h | h | h | h | h | h
    · exact covPrefix0 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix1 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix2 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix3 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix4 T depth hcF _ P h i hi p hs ht hp hk
    · exact covPrefix5 T depth hcF _ P h i hi p hs ht hp hk
    · generalize classIndex u c.val = j at *
      have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hj with rfl | rfl | rfl | rfl
      · exact covProfile1 T depth hcF hdepth P h i hi p hs ht hp hk
      · exact covProfile2 T depth hcF hdepth P h i hi p hs ht hp hk
      · exact covProfile3 T depth hcF hdepth P h i hi p hs ht hp hk
      · exact covProfile4 T depth hcF hdepth P h i hi p hs ht hp hk

#print axioms fifths_content_noUF
end CatalanCore.Uniform.Bank.FifthsContent
