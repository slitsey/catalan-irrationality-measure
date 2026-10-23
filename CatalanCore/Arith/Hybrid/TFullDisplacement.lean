module
public import CatalanCore.Arith.Hybrid.SchurDisplacement
public import CatalanCore.Arith.Hybrid.ChainAlgebra
@[expose] public section
open Finset Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid

/-- The cumulative of the actual frame: `∑_{k ≤ a} Δ_k`. -/
noncomputable def fullPrefix (Fr : Frame) (a : ℕ) : ℚ := ∑ k ∈ Icc 1 a, Fr.Delta k

/-- The Loewner commutator of the actual frame entries, with no hypothesis on the frame:
`norm (b - a) Mn(a, b) = ∑_{k ≤ b} Δ_k - ∑_{k ≤ a} Δ_k`. -/
theorem Mn_loewner (Fr : Frame) (a b : ℕ) :
    Fr.norm * ((b:ℚ) - a) * Fr.Mn a b = fullPrefix Fr b - fullPrefix Fr a := by
  have hn : Fr.norm ≠ 0 := ne_of_gt Fr.hnorm
  have he (n : ℕ) : Icc 1 n = Ioc 0 n := by ext k; simp only [mem_Icc, mem_Ioc]; omega
  have sub_lt {a b : ℕ} (h : a ≤ b) :
      fullPrefix Fr b - fullPrefix Fr a = ∑ k ∈ Ioc a b, Fr.Delta k := by
    unfold fullPrefix
    rw [he, he, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) h]
    ring
  rcases lt_trichotomy a b with h | rfl | h
  · rw [sub_lt h.le]
    unfold Frame.Mn
    rw [if_neg h.ne, min_eq_left h.le, max_eq_right h.le]
    have : ((b:ℚ) - a) ≠ 0 := by
      have : (a:ℚ) < b := by exact_mod_cast h
      linarith
    field_simp
  · simp
  · have h' : b ≤ a := h.le
    have := sub_lt h'
    unfold Frame.Mn
    rw [if_neg h.ne', min_eq_right h', max_eq_left h']
    have hne : ((a:ℚ) - b) ≠ 0 := by
      have : (b:ℚ) < a := by exact_mod_cast h
      linarith
    have e : fullPrefix Fr b - fullPrefix Fr a = -∑ k ∈ Ioc b a, Fr.Delta k := by
      rw [← this]; ring
    rw [e]
    field_simp
    ring

theorem C_loewner (Fr : Frame) (a b : ℕ) :
    C Fr.norm * (C (b:ℚ) - C (a:ℚ)) * C (Fr.Mn a b) = C (fullPrefix Fr b) - C (fullPrefix Fr a) := by
  have h := congrArg (C : ℚ →+* ℚ[X]) (Mn_loewner Fr a b)
  simpa only [map_mul, map_sub] using h

namespace ChainModel
open LemmaE
variable {p r : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

/-- **Displacement identity for the actual scaled Schur complement.**  With
`g = det Q`, `N = Nmat`, and the four one-node moments (`Cz = ` row `z` of the block `C`,
`By = ` column `y` of the block `B`), the entries of `Tscaled` are rank-two Cauchy-like:
`g · norm · (y - z) · T_zy = α_z β'_y - β_z α'_y`. -/
theorem T_displacement (z y : Z) :
    (Q Fr p r xs ys).det * (C Fr.norm * (C (ys y : ℚ) - C (xs z : ℚ))) *
      Tscaled (Q Fr p r xs ys).det (full Fr p r xs ys).toBlocks₁₁ (full Fr p r xs ys).toBlocks₁₂
        (full Fr p r xs ys).toBlocks₂₁ (full Fr p r xs ys).toBlocks₂₂
        (Nmat p (fun _ : Fin r => 1) (full Fr p r xs ys).toBlocks₁₁) z y =
    ((Q Fr p r xs ys).det - ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i *
        ∑ k, Nmat p (fun _ : Fin r => 1) (full Fr p r xs ys).toBlocks₁₁ i k) *
      ((Q Fr p r xs ys).det * C (fullPrefix Fr (ys y)) -
        ∑ j, (∑ k, C (fullPrefix Fr k.val) *
          Nmat p (fun _ : Fin r => 1) (full Fr p r xs ys).toBlocks₁₁ k j) *
          (full Fr p r xs ys).toBlocks₁₂ j y) -
    ((Q Fr p r xs ys).det * C (fullPrefix Fr (xs z)) -
        ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i *
          ∑ k, Nmat p (fun _ : Fin r => 1) (full Fr p r xs ys).toBlocks₁₁ i k *
            C (fullPrefix Fr k.val)) *
      ((Q Fr p r xs ys).det - ∑ j, (∑ k, Nmat p (fun _ : Fin r => 1)
          (full Fr p r xs ys).toBlocks₁₁ k j) * (full Fr p r xs ys).toBlocks₁₂ j y) := by
  have hAN := LemmaE.AN_eq p (fun _ : Fin r => 1) (full Fr p r xs ys).toBlocks₁₁
  have hNA := LemmaE.NA_eq p (fun _ : Fin r => 1) (full Fr p r xs ys).toBlocks₁₁
  have H := schur_displacement (full Fr p r xs ys).toBlocks₁₁
    (Nmat p (fun _ : Fin r => 1) (full Fr p r xs ys).toBlocks₁₁)
    (full Fr p r xs ys).toBlocks₁₂ (full Fr p r xs ys).toBlocks₂₁ (full Fr p r xs ys).toBlocks₂₂
    (Q Fr p r xs ys).det (C Fr.norm) hAN hNA
    (fun i : Fin r => C (i.val : ℚ)) (fun i : Fin r => C (fullPrefix Fr i.val))
    (fun z => C (xs z : ℚ)) (fun z => C (fullPrefix Fr (xs z)))
    (fun y => C (ys y : ℚ)) (fun y => C (fullPrefix Fr (ys y)))
    (by
      intro i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [full_A_apply_ne i j hij]
        exact C_loewner Fr i.val j.val)
    (by
      intro i y
      rw [full_B_apply]
      exact C_loewner Fr i.val (ys y))
    (by
      intro z i
      rw [full_C_apply]
      exact C_loewner Fr (xs z) i.val)
    (by
      intro z y
      rw [full_D_apply]
      exact C_loewner Fr (xs z) (ys y)) z y
  simpa only [Tscaled, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using H

end ChainModel

#print axioms Mn_loewner
end CatalanCore.Arith.Hybrid
