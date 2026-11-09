module

public import CatalanCore.Uniform.Bank.Plane2.Bound
public import CatalanCore.Uniform.Decay.Jet.Gram
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Data.Fintype.Sigma

@[expose] public section
set_option Elab.async false

/-! # Third-plane datum and reference instance (Q09,Q10,Q12,Q13)
The support and pole order are instance data. All rational coefficients remain
parameters; integer denominator-cleared instances are obtained by casting.
The reference and its geometric proofs are reused from the existing plane2 bank.
-/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support
open CatalanCore.Uniform.Decay.Jet CatalanCore.Uniform.Bank.Plane2
open Finset

def datum (v u : ℚ) (hu : u ≠ 0) : PoleDatum where
  n := 1
  hn := by decide
  s := fun _ => 1
  w := fun _ => 3
  coeff := fun _ j => if j = 2 then -v else if j = 3 then 2 * u else 0
  hs := by intro i; norm_num
  hinj := fun i j _ => Subsingleton.elim i j
  hw := by intro i; decide
  coeff_zero := by intro i; norm_num
  coeff_above := by intro i j hj; simp [show j ≠ 2 by omega, show j ≠ 3 by omega]
  top_ne := by intro i; simpa using mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hu
  balance := by simp

theorem datum_d (v u : ℚ) (hu : u ≠ 0) : (datum v u hu).d = 3 := by
  change (∑ _i : Fin 1, 3) = 3
  rw [Fin.sum_univ_one]

theorem tail_three : PoleDatum.hurwitzTail 3 1 = (riemannZeta 3).re := by
  simpa [PoleDatum.hurwitzTail] using riemannZeta_three_re.symm

theorem tail_four : PoleDatum.hurwitzTail 4 1 = Real.pi ^ 4 / 90 := by
  calc
    _ = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4 := by
      simpa [PoleDatum.hurwitzTail] using hasSum_zeta_four.summable.tsum_eq_zero_add.symm
    _ = _ := hasSum_zeta_four.tsum_eq

theorem datum_xi (v u : ℚ) (hu : u ≠ 0) :
    (datum v u hu).xi = -2 * (v : ℝ) * (riemannZeta 3).re + (u : ℝ) * Real.pi ^ 4 / 15 := by
  have hI : (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} := by decide
  change (∑ _i : Fin 1, ∑ j ∈ Finset.Icc (1 : ℕ) 3,
    (j : ℝ) * ((if j = 2 then -v else if j = 3 then 2 * u else 0 : ℚ) : ℝ) *
      PoleDatum.hurwitzTail (j + 1) 1) = _
  rw [Fin.sum_univ_one]
  simp [hI, tail_three, tail_four]
  ring

noncomputable def split (v u : ℚ) (hu : u ≠ 0) : PoleGramSplit (datum v u hu) :=
  Classical.choose (pole_gram_split_minimal (datum v u hu))

theorem split_count (v u : ℚ) (hu : u ≠ 0) (i : Fin (datum v u hu).n) :
    (split v u hu).count i = 3 :=
  (Classical.choose_spec (pole_gram_split_minimal (datum v u hu))).1 i

theorem split_weight_ne (v u : ℚ) (hu : u ≠ 0) (q : (split v u hu).Role) :
    (split v u hu).weight q ≠ 0 :=
  (Classical.choose_spec (pole_gram_split_minimal (datum v u hu))).2 q

noncomputable def role (v u : ℚ) (hu : u ≠ 0) : Fin p2ref.d ≃ (split v u hu).Role where
  toFun := fun j => ⟨(⟨0, by change (0 : ℕ) < 1; decide⟩ : Fin (datum v u hu).n), ⟨j.val,
    lt_of_lt_of_eq (show j.val < 3 from j.isLt)
      (split_count v u hu (⟨0, by change (0 : ℕ) < 1; decide⟩ : Fin (datum v u hu).n)).symm⟩⟩
  invFun := fun q => ⟨q.2.val, lt_of_lt_of_eq q.2.isLt (split_count v u hu q.1)⟩
  left_inv := by intro j; apply Fin.ext; rfl
  right_inv := by
    rintro ⟨i, ⟨j, hj⟩⟩
    have hi : i = (⟨0, by change (0 : ℕ) < 1; decide⟩ : Fin (datum v u hu).n) := by
      apply Fin.ext
      change i.val = 0
      have h : i.val < 1 := i.isLt
      omega
    subst i
    rfl

noncomputable def refMatch (v u : ℚ) (hu : u ≠ 0) :
    PoleRefMatch (datum v u hu) (split v u hu) p2ref where
  role := role v u hu
  side := by
    intro N0 m q _
    have hxs : (p2ref.xs : ℝ) = 1 / 4 := by norm_num [p2ref]
    simp only [datum, Rat.cast_one, hxs]
    have hlo := p2ref_mu_ge q
    have hhi : (p2ref.μ q : ℝ) ≤ 1 := by
      rcases p2ref_mu_real q with h | h | h <;> rw [h] <;> norm_num
    by_cases h : N0 ≤ m
    · have hn : (N0 : ℝ) ≤ m := by exact_mod_cast h
      constructor <;> intro _ <;> linarith
    · have hn : (m : ℝ) + 1 ≤ N0 := by exact_mod_cast (show m + 1 ≤ N0 by omega)
      constructor <;> intro hlt <;> linarith

theorem datum_nv (v u : ℚ) (hu : u ≠ 0) (c : ℚ) (hc : 0 < c)
    (depth : ℕ) (hdepth : 1 ≤ depth) :
    ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, ((Content.Shape.altGeom c hc).seqFamily (datum v u hu).f
        (datum v u hu).e (datum v u hu).xi depth).Adm n ∧
        SeqFamily.scale (Content.Shape.altGeom c hc).geometry n = 2 * s ∧
        ((Content.Shape.altGeom c hc).seqFamily (datum v u hu).f
          (datum v u hu).e (datum v u hu).xi depth).evalQ n x ≠ 0 :=
  pole_altGeom_seqFamily_nv0_even (datum v u hu) c hc (datum v u hu).xi depth
    (by simpa [datum_d] using hdepth)

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.datum_xi
#print axioms CatalanCore.Uniform.Bank.Plane3.refMatch
#print axioms CatalanCore.Uniform.Bank.Plane3.datum_nv
