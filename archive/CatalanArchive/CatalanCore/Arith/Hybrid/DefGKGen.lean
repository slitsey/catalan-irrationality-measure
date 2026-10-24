module

public import CatalanCore.Arith.Hybrid.RankGLE
public import CatalanCore.Arith.Hybrid.LamEntries
public import CatalanArchive.CatalanCore.Arith.Hybrid.LemmaE.Model
public import CatalanCore.Arith.Hybrid.LemmaE.Cong

@[expose] public section

/-!
# GK, generic vector algebra shared by the class-1 and class-3 settings

For two rational constants `a₁, a₂` the partner vector `avecG a₁ a₂ p r u` is `a₁` at `u - 2p`,
`a₂` at `u - p`, and `0` elsewhere.  This file proves, once, everything about the partners
`α, β` and the entry algebra of `D - αB - Cβ + αAβ` that does not depend on the values of
`a₁, a₂` or on the singular set: `sum_avecG`, the entry formulas `entL`, ..., `entDelta`, and the
bounds `hL_boundG`, `hL'_boundG`, `hDelta_boundG`, whose class-specific inputs are hypotheses.
The class files `DefGK{Vec,Fin,Delta}{1,3}` are thin instances.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid.GKGen

section Gen

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m : ℕ}

/-- The partner vector of the label `u`: `a₁` at `u - 2p`, `a₂` at `u - p`. -/
noncomputable def avecG (a1 a2 : ℚ) (p r u : ℕ) (c : Fin r) : ℚ :=
  if (c : ℕ) + 2 * p = u then a1 else if (c : ℕ) + p = u then a2 else 0

lemma sum_avecG (a1 a2 : ℚ) (u : ℕ) (hu : 2 * p ≤ u) (hur : u - p < r) (hp0 : 0 < p)
    (f : ℕ → ℚ) :
    ∑ c : Fin r, avecG a1 a2 p r u c * f c = a1 * f (u - 2 * p) + a2 * f (u - p) := by
  classical
  have h1 : u - 2 * p < r := by omega
  have hne : (⟨u - 2 * p, h1⟩ : Fin r) ≠ ⟨u - p, hur⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [Finset.sum_eq_add (⟨u - 2 * p, h1⟩ : Fin r) ⟨u - p, hur⟩ hne]
  · have e1 : avecG a1 a2 p r u ⟨u - 2 * p, h1⟩ = a1 := by
      unfold avecG; simp only; rw [if_pos (by omega)]
    have e2 : avecG a1 a2 p r u ⟨u - p, hur⟩ = a2 := by
      unfold avecG; simp only; rw [if_neg (by omega), if_pos (by omega)]
    rw [e1, e2]
  · intro c _ hc
    have h2 : (c : ℕ) + 2 * p ≠ u := by
      intro h; apply hc.1; apply Fin.ext; simp; omega
    have h3 : (c : ℕ) + p ≠ u := by
      intro h; apply hc.2; apply Fin.ext; simp; omega
    unfold avecG; rw [if_neg h2, if_neg h3]; simp
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

lemma avec_disjG (a1 a2 : ℚ) (u w : ℕ) (hne : u ≠ w) (h1 : u < w + p) (h2 : w < u + p)
    (c : Fin r) : avecG a1 a2 p r u c * avecG a1 a2 p r w c = 0 := by
  unfold avecG
  split_ifs <;> first | (exfalso; omega) | simp

lemma sum_avec_disjG (a1 a2 : ℚ) (u w : ℕ) (hne : u ≠ w) (h1 : u < w + p) (h2 : w < u + p) :
    ∑ c : Fin r, avecG a1 a2 p r u c * avecG a1 a2 p r w c = 0 :=
  Finset.sum_eq_zero fun c _ => avec_disjG a1 a2 u w hne h1 h2 c

/-- The rational `X0`. -/
noncomputable def X0G (a1 a2 : ℚ) (Fr : Frame) (p u w : ℕ) : ℚ :=
  Fr.Mn u w - (a1 * Fr.Mn (u - 2 * p) w + a2 * Fr.Mn (u - p) w)
    - (a1 * Fr.Mn u (w - 2 * p) + a2 * Fr.Mn u (w - p))
    + (a1 * (a1 * Fr.Mn (u - 2 * p) (w - 2 * p) + a2 * Fr.Mn (u - p) (w - 2 * p))
      + a2 * (a1 * Fr.Mn (u - 2 * p) (w - p) + a2 * Fr.Mn (u - p) (w - p)))

/-- Row partners (zone rows `r + 2i`). -/
noncomputable def alphaMG (av : ℕ → Fin r → ℚ) (m : ℕ) : Matrix (Fin m) (Fin r) ℚ[X] :=
  Matrix.of fun i c => C (av (r + 2 * (i : ℕ)) c)

/-- Column partners (zone columns `r + 2j + 1`). -/
noncomputable def betaMG (av : ℕ → Fin r → ℚ) (m : ℕ) : Matrix (Fin r) (Fin m) ℚ[X] :=
  Matrix.of fun c j => C (av (r + 2 * (j : ℕ) + 1) c)

section Entries

variable (av : ℕ → Fin r → ℚ)

lemma entL (i : Fin m) (c : Fin r) :
    ((Matrix.of (fullEntry Fr r m)).toBlocks₂₁ - alphaMG av m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) i c =
      C (Fr.Mn (r + 2 * (i : ℕ)) (c : ℕ) -
        ∑ c' : Fin r, av (r + 2 * (i : ℕ)) c' * Fr.Mn (c' : ℕ) (c : ℕ)) -
        C (av (r + 2 * (i : ℕ)) c) * X := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, alphaMG, Matrix.of_apply, Matrix.toBlocks₂₁,
    Matrix.toBlocks₁₁, fullEntry, Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← C_mul, ← map_sum, map_sub, zero_add]
  ring

lemma entL' (c : Fin r) (j : Fin m) :
    ((Matrix.of (fullEntry Fr r m)).toBlocks₁₂ - (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ *
        betaMG av m) c j =
      C (Fr.Mn (c : ℕ) (r + 2 * (j : ℕ) + 1) -
        ∑ c' : Fin r, Fr.Mn (c : ℕ) (c' : ℕ) * av (r + 2 * (j : ℕ) + 1) c') -
        C (av (r + 2 * (j : ℕ) + 1) c) * X := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, betaMG, Matrix.of_apply, Matrix.toBlocks₁₂,
    Matrix.toBlocks₁₁, fullEntry, Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, ← C_mul, ← map_sum, map_sub, zero_add]
  ring

lemma alphaA_entry (i : Fin m) (c : Fin r) :
    (alphaMG av m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) i c =
      C (∑ c' : Fin r, av (r + 2 * (i : ℕ)) c' * Fr.Mn (c' : ℕ) (c : ℕ)) +
        C (av (r + 2 * (i : ℕ)) c) * X := by
  simp only [Matrix.mul_apply, alphaMG, Matrix.of_apply, Matrix.toBlocks₁₁, fullEntry,
    Frame.hybRow, Frame.hybCol, Sum.elim_inl]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← C_mul, ← map_sum, zero_add]
  ring

lemma alphaB_entry (i j : Fin m) :
    (alphaMG av m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₂) i j =
      C (∑ c : Fin r, av (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (r + 2 * (j : ℕ) + 1)) := by
  simp only [Matrix.mul_apply, alphaMG, Matrix.of_apply, Matrix.toBlocks₁₂, fullEntry,
    Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr, zero_add, ← C_mul, ← map_sum]

lemma Cbeta_entry (i j : Fin m) :
    ((Matrix.of (fullEntry Fr r m)).toBlocks₂₁ * betaMG av m) i j =
      C (∑ c : Fin r, Fr.Mn (r + 2 * (i : ℕ)) (c : ℕ) * av (r + 2 * (j : ℕ) + 1) c) := by
  simp only [Matrix.mul_apply, betaMG, Matrix.of_apply, Matrix.toBlocks₂₁, fullEntry,
    Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr, zero_add, ← C_mul, ← map_sum]

lemma alphaAbeta_entry (i j : Fin m) :
    (alphaMG av m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ * betaMG av m) i j =
      C (∑ c' : Fin r, (∑ c : Fin r, av (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (c' : ℕ)) *
          av (r + 2 * (j : ℕ) + 1) c') +
        C (∑ c : Fin r, av (r + 2 * (i : ℕ)) c * av (r + 2 * (j : ℕ) + 1) c) * X := by
  rw [Matrix.mul_apply]
  have h : ∀ c' : Fin r, (alphaMG av m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) i c' *
      betaMG av m c' j =
      C ((∑ c : Fin r, av (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (c' : ℕ)) *
        av (r + 2 * (j : ℕ) + 1) c') +
      C (av (r + 2 * (i : ℕ)) c' * av (r + 2 * (j : ℕ) + 1) c') * X := by
    intro c'
    rw [alphaA_entry]
    simp only [betaMG, Matrix.of_apply]
    rw [C_mul, C_mul]; ring
  rw [Finset.sum_congr rfl (fun c' _ => h c'), Finset.sum_add_distrib, ← map_sum,
    ← Finset.sum_mul, ← map_sum]

lemma entDelta (i j : Fin m) :
    ((Matrix.of (fullEntry Fr r m)).toBlocks₂₂ - alphaMG av m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₂ -
      (Matrix.of (fullEntry Fr r m)).toBlocks₂₁ * betaMG av m +
      alphaMG av m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ * betaMG av m) i j =
    C (Fr.Mn (r + 2 * (i : ℕ)) (r + 2 * (j : ℕ) + 1) -
        ∑ c : Fin r, av (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (r + 2 * (j : ℕ) + 1) -
        ∑ c : Fin r, Fr.Mn (r + 2 * (i : ℕ)) (c : ℕ) * av (r + 2 * (j : ℕ) + 1) c +
        ∑ c' : Fin r, (∑ c : Fin r, av (r + 2 * (i : ℕ)) c * Fr.Mn (c : ℕ) (c' : ℕ)) *
          av (r + 2 * (j : ℕ) + 1) c') +
      C (∑ c : Fin r, av (r + 2 * (i : ℕ)) c * av (r + 2 * (j : ℕ) + 1) c) * X := by
  simp only [Matrix.add_apply, Matrix.sub_apply, alphaB_entry, Cbeta_entry, alphaAbeta_entry,
    Matrix.toBlocks₂₂, Matrix.of_apply, fullEntry, Frame.hybRow, Frame.hybCol, Sum.elim_inr,
    zero_add, map_sub, map_add]
  ring

end Entries

/-! ### The bounds -/

lemma gn_C_mul_X_leG {x : ℚ} (hx : Int1 p (C x)) : gn p (C x * X) ≤ 1 := by
  rw [gn_mul, gn_X, mul_one]; exact hx

/-- `hL` of `tcore_vec`.  Hypotheses: the partners are `p`-integral, and the column bound. -/
theorem hL_boundG (av : ℕ → Fin r → ℚ) (hav : ∀ u c, Int1 p (C (av u c)))
    (hlb : ∀ u, r ≤ u → u < r + 2 * m → ∀ c : Fin r,
      gn p (C (Fr.Mn u (c : ℕ) - ∑ c' : Fin r, av u c' * Fr.Mn (c' : ℕ) (c : ℕ))) ≤ p)
    (i : Fin m) (c : Fin r) :
    gn p (((Matrix.of (fullEntry Fr r m)).toBlocks₂₁ - alphaMG av m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) i c) ≤ p := by
  have hi := i.2
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  rw [entL]
  refine (gn_sub_le _ _).trans (max_le ?_ ?_)
  · exact hlb (r + 2 * (i : ℕ)) (by omega) (by omega) c
  · exact (gn_C_mul_X_leG (hav _ c)).trans hp1

/-- `hL'` of `tcore_vec`. -/
theorem hL'_boundG (av : ℕ → Fin r → ℚ) (hav : ∀ u c, Int1 p (C (av u c)))
    (hlb : ∀ u, r ≤ u → u < r + 2 * m → ∀ c : Fin r,
      gn p (C (Fr.Mn u (c : ℕ) - ∑ c' : Fin r, av u c' * Fr.Mn (c' : ℕ) (c : ℕ))) ≤ p)
    (c : Fin r) (j : Fin m) :
    gn p (((Matrix.of (fullEntry Fr r m)).toBlocks₁₂ - (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ *
        betaMG av m) c j) ≤ p := by
  have hj := j.2
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  rw [entL']
  refine (gn_sub_le _ _).trans (max_le ?_ ?_)
  · have := hlb (r + 2 * (j : ℕ) + 1) (by omega) (by omega) c
    have e : Fr.Mn (c : ℕ) (r + 2 * (j : ℕ) + 1) -
        ∑ c' : Fin r, Fr.Mn (c : ℕ) (c' : ℕ) * av (r + 2 * (j : ℕ) + 1) c' =
        Fr.Mn (r + 2 * (j : ℕ) + 1) (c : ℕ) -
        ∑ c' : Fin r, av (r + 2 * (j : ℕ) + 1) c' * Fr.Mn (c' : ℕ) (c : ℕ) := by
      rw [Mn_symm (c : ℕ)]
      congr 1
      refine Finset.sum_congr rfl (fun c' _ => ?_)
      rw [mul_comm, Mn_symm (c : ℕ)]
    rw [e]; exact this
  · exact (gn_C_mul_X_leG (hav _ c)).trans hp1

/-- `hΔ` of `tcore_vec`.  Hypothesis: the integrality of `X0G` on distinct zone labels. -/
theorem hDelta_boundG (a1 a2 : ℚ) (hr : 2 * p < r) (hN : r + 2 * m ≤ 3 * p)
    (hD : ∀ u w : ℕ, r ≤ u → u < r + 2 * m → r ≤ w → w < r + 2 * m → u ≠ w →
      Int1 p (C (X0G a1 a2 Fr p u w)))
    (i j : Fin m) :
    Int1 p (((Matrix.of (fullEntry Fr r m)).toBlocks₂₂ - alphaMG (avecG a1 a2 p r) m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₂ -
      (Matrix.of (fullEntry Fr r m)).toBlocks₂₁ * betaMG (avecG a1 a2 p r) m +
      alphaMG (avecG a1 a2 p r) m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ *
        betaMG (avecG a1 a2 p r) m) i j) := by
  have hi := i.2; have hj := j.2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  set u := r + 2 * (i : ℕ) with hu
  set w := r + 2 * (j : ℕ) + 1 with hw
  have hne : u ≠ w := by omega
  rw [entDelta, sum_avec_disjG a1 a2 u w hne (by omega) (by omega)]
  simp only [map_zero, zero_mul, add_zero]
  have s1 : ∑ c : Fin r, avecG a1 a2 p r u c * Fr.Mn (c : ℕ) w =
      a1 * Fr.Mn (u - 2 * p) w + a2 * Fr.Mn (u - p) w :=
    sum_avecG a1 a2 u (by omega) (by omega) hp0 (fun n => Fr.Mn n w)
  have s2 : ∑ c : Fin r, Fr.Mn u (c : ℕ) * avecG a1 a2 p r w c =
      a1 * Fr.Mn u (w - 2 * p) + a2 * Fr.Mn u (w - p) := by
    calc ∑ c : Fin r, Fr.Mn u (c : ℕ) * avecG a1 a2 p r w c
        = ∑ c : Fin r, avecG a1 a2 p r w c * Fr.Mn u (c : ℕ) :=
          Finset.sum_congr rfl (fun c _ => mul_comm _ _)
      _ = _ := sum_avecG a1 a2 w (by omega) (by omega) hp0 (fun n => Fr.Mn u n)
  have s3 : ∑ c' : Fin r, (∑ c : Fin r, avecG a1 a2 p r u c * Fr.Mn (c : ℕ) (c' : ℕ)) *
        avecG a1 a2 p r w c' =
      a1 * (a1 * Fr.Mn (u - 2 * p) (w - 2 * p) + a2 * Fr.Mn (u - p) (w - 2 * p)) +
        a2 * (a1 * Fr.Mn (u - 2 * p) (w - p) + a2 * Fr.Mn (u - p) (w - p)) := by
    calc ∑ c' : Fin r, (∑ c : Fin r, avecG a1 a2 p r u c * Fr.Mn (c : ℕ) (c' : ℕ)) *
          avecG a1 a2 p r w c'
        = ∑ c' : Fin r, avecG a1 a2 p r w c' *
            (a1 * Fr.Mn (u - 2 * p) (c' : ℕ) + a2 * Fr.Mn (u - p) (c' : ℕ)) := by
          refine Finset.sum_congr rfl (fun c' _ => ?_)
          rw [mul_comm]; congr 1
          exact sum_avecG a1 a2 u (by omega) (by omega) hp0 (fun n => Fr.Mn n (c' : ℕ))
      _ = _ := sum_avecG a1 a2 w (by omega) (by omega) hp0
          (fun n => a1 * Fr.Mn (u - 2 * p) n + a2 * Fr.Mn (u - p) n)
  rw [s1, s2, s3]
  have := hD u w (by omega) (by omega) (by omega) (by omega) hne
  convert this using 2
  unfold X0G
  ring

end Gen

end CatalanCore.Arith.Hybrid.GKGen
