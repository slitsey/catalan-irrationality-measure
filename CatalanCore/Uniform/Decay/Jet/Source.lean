module

public import CatalanCore.Uniform.Decay.Jet.Gram
public import CatalanCore.Uniform.Decay.Jet.PoleSource
public import CatalanCore.Uniform.Decay.Jet.PoleIntegral
public import CatalanCore.Uniform.Decay.Jet.PoleHead
public import CatalanCore.Uniform.Decay.Jet.Decay
public import CatalanCore.Uniform.Decay.Jet.Field
public import CatalanCore.Uniform.Support.Datum
public import CatalanCore.Uniform.Support.SeqFamily
public import CatalanCore.Uniform.Decay.Polygon.Bounds
public import CatalanCore.Uniform.Decay.Polygon.Data
public import CatalanCore.Uniform.Decay.PolyChain.Integ
public import CatalanCore.Uniform.Support.Theorem

@[expose] public section
set_option Elab.async false

/-!
# The jet source of a datum (lane H, wave H2c; ledger N5, S15)

For a support datum `D` (`Support.Datum`) and a reference frame `Fr` matched to it (`RefMatch`: every
reference shift is the matched shift of a datum shift or the helper of a double shift), the source
representation of the Löwner matrix `Φ(ξ)` of the datum over the polygon space `Fr.XT N0` of the reference
(`Decay.Space`), in the form `Decay.Jet.Decay` consumes (`JetRep`):

* `datumJet`, `datum_phi_eq`: the jet frame of the datum and `lw D.f D.e x y + [x = y] D.xi = TentJ x y`;
* `RefMatch.atom_sum`: the atoms of the reference carry the head of the Gram formula, the double shifts split
  by the rank-one identity (`Gram.head_term_split`) into the two labels `(s, n)`, `(s*, n)`;
* `RefMatch.jet_entry`: `∫ W · rows_a · rows_b dμ = TentJ a b`, from `Gram.gram_formula` and the polygon
  integrals of the source `srcJ`; `jet_andreief`: the Andréief bound;
* `norm_E2cf_le`, `norm_wUpJ_le`, `norm_wLowJ_le` (N5): the exponential bound `‖E‖ ≤ C e^{-2π |Im z|}` on the
  physical path for the whole weight `E = E_a + E_b`, and the weight bound `jW_weight`;
* `RefMatch.jetField_xt`: Lemma J on the polygon space (`Jet.Field`), from the lattice hypotheses `JetSetup`;
* `RefMatch.jetRep`, `RefMatch.jetFamily`: the `JetRep` of every large scale with uniform constants.
-/

open Finset MeasureTheory Set Filter Complex
open CatalanCore.Uniform.Support

namespace CatalanCore.Uniform.Decay.Jet

open CatalanCore



/-- The simple part of the jet frame of a datum, with the contour data `(xs, δ0, n0off)`. -/
noncomputable def datumFrame (D : Datum) (xs δ0 : ℚ) (n0 : ℕ) : Frame where
  d := D.n
  μ := D.s
  w := D.a
  norm := 1
  xs := xs
  δ0 := δ0
  n0off := n0
  hμ := D.hs
  hμinj := fun i j h => fun hij => h (D.hinj hij)
  hw := D.hbal
  hnorm := one_pos

/-- The jet frame of a datum. -/
noncomputable def datumJet (D : Datum) (xs δ0 : ℚ) (n0 : ℕ) : JetFrame where
  toFrame := datumFrame D xs δ0 n0
  b := D.b

theorem datumJet_toFrame (D : Datum) (xs δ0 : ℚ) (n0 : ℕ) :
    (datumJet D xs δ0 n0).toFrame = datumFrame D xs δ0 n0 := rfl

theorem datum_delta_eq (D : Datum) (xs δ0 : ℚ) (n0 k : ℕ) :
    (datumFrame D xs δ0 n0).Delta (k + 1) + (datumJet D xs δ0 n0).DeltaB (k + 1) = D.delta k := by
  unfold Frame.Delta JetFrame.DeltaB Datum.delta datumJet datumFrame
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Int.cast_id]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem datum_dsq_eq (D : Datum) (xs δ0 : ℚ) (n0 k : ℕ) :
    (datumFrame D xs δ0 n0).Dsq (k + 1) + (datumJet D xs δ0 n0).DsqB (k + 1) = -D.delta1 k := by
  unfold Frame.Dsq JetFrame.DsqB Datum.delta1 datumJet datumFrame
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Int.cast_id]
  rw [mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem datum_const_eq (D : Datum) (xs δ0 : ℚ) (n0 : ℕ) :
    (datumFrame D xs δ0 n0).const + (datumJet D xs δ0 n0).constB = D.xi := by
  unfold Frame.const JetFrame.constB Datum.xi datumJet datumFrame
  simp only [Rat.cast_one, div_one, Int.cast_id]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold JetFrame.hurwitzTail3 hurwitzTail3
  ring

theorem datum_f_sub (D : Datum) (xs δ0 : ℚ) (n0 m M : ℕ) (h : m ≤ M) :
    ∑ k ∈ Finset.Ioc m M, (((datumFrame D xs δ0 n0).Delta k + (datumJet D xs δ0 n0).DeltaB k : ℚ) : ℝ)
      = ((D.f M - D.f m : ℚ) : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 : ∑ k ∈ Finset.Ioc m (m + n), (((datumFrame D xs δ0 n0).Delta k +
      (datumJet D xs δ0 n0).DeltaB k : ℚ) : ℝ) =
      ∑ j ∈ Finset.range n, (((datumFrame D xs δ0 n0).Delta (m + j + 1) +
      (datumJet D xs δ0 n0).DeltaB (m + j + 1) : ℚ) : ℝ) := JetFrame.sum_Ioc_shift' m _ n
  have e2 : D.f (m + n) - D.f m = ∑ k ∈ Finset.Ico m (m + n), D.delta k := by
    unfold Datum.f
    rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_right m n)]
  rw [e1, e2, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Rat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg _ (datum_delta_eq D xs δ0 n0 (m + j))

theorem datum_phi_eq (D : Datum) (xs δ0 : ℚ) (n0 x y : ℕ) :
    (lw D.f D.e x y : ℝ) + (if x = y then D.xi else 0) = (datumJet D xs δ0 n0).TentJ x y := by
  have hnorm : (((datumJet D xs δ0 n0).norm : ℚ) : ℝ) = 1 := by
    simp [datumJet, datumFrame]
  by_cases hxy : x = y
  · subst hxy
    have h := JetFrame.norm_mul_TentJ_diag (datumJet D xs δ0 n0) x
    rw [hnorm, one_mul] at h
    simp only [datumJet_toFrame] at h
    have hc := datum_const_eq D xs δ0 n0
    have hs : ∑ k ∈ Finset.Icc 1 x, ((((datumFrame D xs δ0 n0).Dsq k +
        (datumJet D xs δ0 n0).DsqB k : ℚ)) : ℝ) = ((D.e x : ℚ) : ℝ) := by
      rw [JetFrame.sum_Icc_shift' (fun k => ((((datumFrame D xs δ0 n0).Dsq k +
        (datumJet D xs δ0 n0).DsqB k : ℚ)) : ℝ)) x]
      have : D.e x = ∑ k ∈ Finset.range x, (((datumFrame D xs δ0 n0).Dsq (k + 1) +
          (datumJet D xs δ0 n0).DsqB (k + 1) : ℚ)) := by
        unfold Datum.e
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => (datum_dsq_eq D xs δ0 n0 k).symm ▸ rfl
      rw [this, Rat.cast_sum]
    have hjc : ((datumFrame D xs δ0 n0).const : ℝ) + (datumJet D xs δ0 n0).constB = D.xi := hc
    simp only [lw, if_true]
    push_cast
    have hcst : (datumFrame D xs δ0 n0).const + (datumJet D xs δ0 n0).constB = D.xi := hc
    rw [h, hs, hcst]
    push_cast
    ring
  · simp only [lw, if_neg hxy, if_neg hxy]
    have h := JetFrame.norm_mul_TentJ_offdiag (datumJet D xs δ0 n0) hxy
    rw [hnorm, one_mul] at h
    simp only [datumJet_toFrame] at h
    rw [add_zero, h]
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · rw [max_eq_right hlt.le, min_eq_left hlt.le, datum_f_sub D xs δ0 n0 x y hlt.le]
      push_cast
      have : ((y : ℝ) - x) ≠ 0 := sub_ne_zero.2 (Ne.symm (by exact_mod_cast hxy))
      field_simp
    · rw [max_eq_left hgt.le, min_eq_right hgt.le, datum_f_sub D xs δ0 n0 y x hgt.le]
      push_cast
      have : ((x : ℝ) - y) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hxy)
      have : ((y : ℝ) - x) ≠ 0 := sub_ne_zero.2 (Ne.symm (by exact_mod_cast hxy))
      field_simp
      ring





/-- How the atoms of a reference frame carry the jet of a datum (S04): every reference shift is either the
matched shift of a datum shift (`inl i`) or the helper of a double shift (`inr j`). -/
structure RefMatch (D : Datum) (Fr : Frame) where
  role : Fin Fr.d ≃ Fin D.n ⊕ {i : Fin D.n // D.b i ≠ 0}
  idx_mu : ∀ i, Fr.μ (role.symm (Sum.inl i)) = D.s i
  side : ∀ (N0 m : ℕ) (j : {i : Fin D.n // D.b i ≠ 0}),
    ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (role.symm (Sum.inr j)) : ℝ)) ↔
      ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (D.s j.1 : ℝ))

namespace RefMatch

variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

/-- The datum shift an atom of the reference stands for. -/
def dix (q : Fin Fr.d) : Fin D.n := Sum.elim id Subtype.val (R.role q)

/-- Weight of the atom `q`. -/
noncomputable def Wq (q : Fin Fr.d) : ℂ :=
  match R.role q with
  | Sum.inl i => if D.b i = 0 then (D.a i : ℂ) else -((D.b i : ℂ) / 2)
  | Sum.inr j => (D.b j.1 : ℂ) / 2

/-- Coefficient of `u` in the row of the atom `q`. -/
noncomputable def kapq (q : Fin Fr.d) : ℂ :=
  match R.role q with
  | Sum.inl i => if D.b i = 0 then 1 else 1 - (D.a i : ℂ) / (2 * (D.b i : ℂ))
  | Sum.inr j => 1 + (D.a j.1 : ℂ) / (2 * (D.b j.1 : ℂ))

/-- Coefficient of `u'` in the row of the atom `q`. -/
noncomputable def epsq (q : Fin Fr.d) : ℂ :=
  match R.role q with
  | Sum.inl i => if D.b i = 0 then 0 else 1
  | Sum.inr _ => -1

/-- The datum position `-(m + s)` of the atom `(m, q)`. -/
noncomputable def dpos (m : ℕ) (q : Fin Fr.d) : ℂ := -(m : ℂ) - (D.s (R.dix q) : ℂ)

/-- The row of the atom `(m, q)` at the node `t`: `kap · (c - t)⁻¹ + eps · (-(c - t)⁻²)`. -/
noncomputable def arow (m : ℕ) (q : Fin Fr.d) (t : ℕ) : ℂ :=
  R.kapq q * (R.dpos m q - (t : ℂ))⁻¹ + R.epsq q * (-((R.dpos m q - (t : ℂ))⁻¹) ^ 2)

/-- The atom term of the entry `(a, b)`. -/
noncomputable def aterm (m : ℕ) (q : Fin Fr.d) (a b : ℕ) : ℂ :=
  R.Wq q * R.arow m q a * R.arow m q b




theorem sum_subtype_ne (f : {i : Fin D.n // D.b i ≠ 0} → ℂ) :
    ∑ j, f j = ∑ i, (if hb : D.b i ≠ 0 then f ⟨i, hb⟩ else 0) := by
  classical
  set F : Fin D.n → ℂ := fun i => if hb : D.b i ≠ 0 then f ⟨i, hb⟩ else 0 with hF
  calc ∑ j, f j = ∑ j : {i : Fin D.n // D.b i ≠ 0}, F j.1 :=
        Finset.sum_congr rfl fun j _ => by simp [hF, j.2]
    _ = ∑ i ∈ Finset.univ.filter (fun i => D.b i ≠ 0), F i :=
        (Finset.sum_subtype (Finset.univ.filter (fun i => D.b i ≠ 0)) (fun i => by simp) F).symm
    _ = ∑ i, F i := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : D.b i ≠ 0 <;> simp [hF, h]

/-- The term of one datum shift `i` at the head `m`. -/
noncomputable def hterm (m : ℕ) (i : Fin D.n) (a b : ℕ) : ℂ :=
  (D.a i : ℂ) * kk a b (-(m : ℂ) - (D.s i : ℂ)) - (D.b i : ℂ) * dkk a b (-(m : ℂ) - (D.s i : ℂ))

theorem nat_ne (m : ℕ) (i : Fin D.n) (a : ℕ) : (-(m : ℂ) - (D.s i : ℂ)) - (a : ℂ) ≠ 0 := by
  have hs := (D.hs i).1
  have e : (-(m : ℂ) - (D.s i : ℂ)) - (a : ℂ) = (((-((m : ℝ) + (D.s i : ℝ) + a)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  have : (0 : ℝ) < (D.s i : ℝ) := by exact_mod_cast hs
  have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  exact_mod_cast (by linarith : (-((m : ℝ) + (D.s i : ℝ) + a)) ≠ 0)

/-- Atom term of the matched label of `i`. -/
theorem aterm_idx (m : ℕ) (i : Fin D.n) (a b : ℕ) (hb : D.b i = 0) :
    R.aterm m (R.role.symm (Sum.inl i)) a b = hterm m i a b := by
  have hdi : R.dix (R.role.symm (Sum.inl i)) = i := by simp [dix]
  have h1 := nat_ne (D := D) m i a
  have h2 := nat_ne (D := D) m i b
  unfold aterm arow Wq kapq epsq dpos hterm
  simp only [Equiv.apply_symm_apply, hdi, hb, if_true, Int.cast_zero, zero_mul, add_zero, zero_mul,
    mul_zero, kk, dkk]
  push_cast
  field_simp
  ring

theorem aterm_pair (m : ℕ) (j : {i : Fin D.n // D.b i ≠ 0}) (a b : ℕ) :
    R.aterm m (R.role.symm (Sum.inl j.1)) a b + R.aterm m (R.role.symm (Sum.inr j)) a b =
      hterm m j.1 a b := by
  have hdi : R.dix (R.role.symm (Sum.inl j.1)) = j.1 := by simp [dix]
  have hdj : R.dix (R.role.symm (Sum.inr j)) = j.1 := by simp [dix]
  have h1 := nat_ne (D := D) m j.1 a
  have h2 := nat_ne (D := D) m j.1 b
  have hb : (D.b j.1 : ℂ) ≠ 0 := by exact_mod_cast j.2
  have hsplit := head_term_split a b h1 h2 (D.a j.1 : ℂ) (D.b j.1 : ℂ) hb
  unfold hterm
  rw [hsplit]
  unfold aterm arow Wq kapq epsq dpos
  simp only [Equiv.apply_symm_apply, hdi, hdj, j.2, if_false, ne_eq, not_false_eq_true]
  have e1 : (D.b j.1 = 0) ↔ False := by simp [j.2]
  simp only [e1, if_false, ux, dux]
  field_simp
  ring

end RefMatch


namespace RefMatch
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

/-- **The atom sum is the head sum of the datum.**  The atoms of the reference carry the head of the Gram
formula of the datum, split by the rank-one identity at the double shifts. -/
theorem atom_sum (N0 a b : ℕ) :
    ∑ p ∈ Fr.atomIdx N0, R.aterm p.1 p.2 a b =
      (datumJet D Fr.xs Fr.δ0 Fr.n0off).headSum N0 a b := by
  classical
  unfold Frame.atomIdx JetFrame.headSum
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => ?_
  -- re-index the atoms of the reference by the roles
  have e1 : ∑ q : Fin Fr.d, (if ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ q : ℝ))
        then R.aterm m q a b else 0) =
      ∑ x : Fin D.n ⊕ {i : Fin D.n // D.b i ≠ 0},
        (if ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm x) : ℝ))
          then R.aterm m (R.role.symm x) a b else 0) :=
    (Equiv.sum_comp R.role.symm (fun q => if ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ q : ℝ))
        then R.aterm m q a b else 0)).symm
  rw [e1, Fintype.sum_sum_type, sum_subtype_ne, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hμi : Fr.μ (R.role.symm (Sum.inl i)) = D.s i := R.idx_mu i
  have hcond : (¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm (Sum.inl i)) : ℝ))) ↔
      ¬ ((N0 : ℝ) + ((datumJet D Fr.xs Fr.δ0 Fr.n0off).xs : ℝ) < (m : ℝ) +
        ((datumJet D Fr.xs Fr.δ0 Fr.n0off).μ i : ℝ)) := by
    rw [hμi]; rfl
  by_cases hbi : D.b i = 0
  · have hn : ¬ (D.b i ≠ 0) := not_not.2 hbi
    simp only [hn, dif_neg, not_false_eq_true, add_zero]
    by_cases hc : (N0 : ℝ) + ((datumJet D Fr.xs Fr.δ0 Fr.n0off).xs : ℝ) < (m : ℝ) +
        ((datumJet D Fr.xs Fr.δ0 Fr.n0off).μ i : ℝ)
    · have : ¬ ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm (Sum.inl i)) : ℝ)) := by
        intro h; exact h (by rw [hμi]; exact hc)
      simp [hc, this]
    · have h' : ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm (Sum.inl i)) : ℝ)) := by
        rw [hμi]; exact hc
      simp only [hc, h', if_false, not_false_eq_true, if_true]
      rw [aterm_idx R m i a b hbi]
      simp [hterm, datumJet, datumFrame, hbi]
  · have hn : D.b i ≠ 0 := hbi
    simp only [hn, dif_pos, ne_eq, not_false_eq_true]
    have hside := R.side N0 m ⟨i, hn⟩
    by_cases hc : (N0 : ℝ) + ((datumJet D Fr.xs Fr.δ0 Fr.n0off).xs : ℝ) < (m : ℝ) +
        ((datumJet D Fr.xs Fr.δ0 Fr.n0off).μ i : ℝ)
    · have h1 : (N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm (Sum.inl i)) : ℝ) := by
        rw [hμi]; exact hc
      have h2 : (N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm (Sum.inr ⟨i, hn⟩)) : ℝ) :=
        hside.2 hc
      simp [hc, h1, h2]
    · have h1 : ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm (Sum.inl i)) : ℝ)) := by
        rw [hμi]; exact hc
      have h2 : ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm (Sum.inr ⟨i, hn⟩)) : ℝ)) :=
        fun h => hc (hside.1 h)
      simp only [hc, h1, h2, if_false, not_false_eq_true, if_true]
      have := aterm_pair R m ⟨i, hn⟩ a b
      rw [this]
      simp [hterm, datumJet, datumFrame]

end RefMatch

end CatalanCore.Uniform.Decay.Jet

/-! ### The jet source on the polygon space of the reference -/

open CatalanCore.Uniform.Decay.Polygon
open CatalanLambda.Decay (rayPt rayI contL sumM integrable_sumM_iff integral_sumM)

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

/-- Upper jet weight `-(2πi)⁻¹ (E_a + E_b)(γ) γ'`. -/
noncomputable def wUpJ (R : RefMatch D Fr) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (r : ℝ) : ℂ :=
  -((2 * Real.pi * I)⁻¹ * (((datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.EC
      (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r) +
      (datumJet D Fr.xs Fr.δ0 Fr.n0off).E2cf (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r)) *
      pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r))

/-- Lower jet weight `(2πi)⁻¹ (E_a + E_b)(γ̄) γ̄'`. -/
noncomputable def wLowJ (R : RefMatch D Fr) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (r : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * (((datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.EC
      (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r) +
      (datumJet D Fr.xs Fr.δ0 Fr.n0off).E2cf
        (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r)) *
      pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r)

/-- The jet weights on the polygon space: the atom weights `Wq`, and the two ray weights. -/
noncomputable def jW (N0 : ℕ) (pts : List ℂ) (d : ℂ) : Fr.XT N0 → ℂ :=
  Sum.elim (fun p => R.Wq p.1.2)
    (Sum.elim (fun r => R.wUpJ N0 pts d r.1) (fun r => R.wLowJ N0 pts d r.1))

/-- The centres: the datum positions at the atoms, the path points on the rays. -/
noncomputable def jCtr (N0 : ℕ) (pts : List ℂ) (d : ℂ) : Fr.XT N0 → ℂ :=
  Sum.elim (fun p => R.dpos p.1.1 p.1.2)
    (Sum.elim (fun r => pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1)
      (fun r => pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r.1))

/-- The coefficient of `u`. -/
noncomputable def jKap (N0 : ℕ) : Fr.XT N0 → ℂ :=
  Sum.elim (fun p => R.kapq p.1.2) (fun _ => 1)

/-- The coefficient of `u'`. -/
noncomputable def jEps (N0 : ℕ) : Fr.XT N0 → ℂ :=
  Sum.elim (fun p => R.epsq p.1.2) (fun _ => 0)

/-- The row functions. -/
noncomputable def jRows (N0 : ℕ) (pts : List ℂ) (d : ℂ) (t : ℕ) (z : Fr.XT N0) : ℂ :=
  jrow (R.jCtr N0 pts d) (R.jKap N0) (R.jEps N0) t z

theorem jRows_inl (N0 : ℕ) (pts : List ℂ) (d : ℂ) (t : ℕ) (p : ↥(Fr.atomIdx N0)) :
    R.jRows N0 pts d t (Sum.inl p) = R.arow p.1.1 p.1.2 t := by
  simp [jRows, jrow, jCtr, jKap, jEps, arow]

theorem jRows_up (N0 : ℕ) (pts : List ℂ) (d : ℂ) (t : ℕ) (r : Decay.RayP) :
    R.jRows N0 pts d t (Sum.inr (Sum.inl r)) =
      (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1 - (t : ℂ))⁻¹ := by
  simp [jRows, jrow, jCtr, jKap, jEps]

theorem jRows_low (N0 : ℕ) (pts : List ℂ) (d : ℂ) (t : ℕ) (r : Decay.RayP) :
    R.jRows N0 pts d t (Sum.inr (Sum.inr r)) =
      (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r.1 - (t : ℂ))⁻¹ := by
  simp [jRows, jrow, jCtr, jKap, jEps]

end RefMatch
end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

section Entry

variable (hC : (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK)
include hC

theorem upperJ_path (N0 a b : ℕ) {pts : List ℂ} {d : ℂ} (h : PolyOK pts d) :
    IntegrableOn (fun u => (datumJet D Fr.xs Fr.δ0 Fr.n0off).srcJ a b
        (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u) * pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), (datumJet D Fr.xs Fr.δ0 Fr.n0off).srcJ a b
        (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u) * pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u
        = polyI ((datumJet D Fr.xs Fr.δ0 Fr.n0off).srcJ a b) ((Fr.xstar N0 : ℝ) : ℂ) pts d :=
  pathInt_of_deform (σ := 1) (by simp) (diskR_pos hC)
    (JetFrame.srcJ_differentiableOn_halfP _ 1 a b) (JetFrame.srcJ_differentiableOn_ball _ hC N0 a b)
    pts h.upper' (by simpa using h.tail)
    (add_nonneg Khi_nonneg (JetFrame.KhiB_nonneg _)) (JetFrame.srcJ_decay _ (by simp) a b)

theorem lowerJ_path (N0 a b : ℕ) {pts : List ℂ} {d : ℂ} (h : PolyOK pts d) :
    IntegrableOn (fun u => (datumJet D Fr.xs Fr.δ0 Fr.n0off).srcJ a b
        (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u) *
        pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), (datumJet D Fr.xs Fr.δ0 Fr.n0off).srcJ a b
        (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u) *
        pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u
        = polyI ((datumJet D Fr.xs Fr.δ0 Fr.n0off).srcJ a b) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts)
            (starRingEnd ℂ d) :=
  pathInt_of_deform (σ := -1) (by simp) (diskR_pos hC)
    (JetFrame.srcJ_differentiableOn_halfP _ (-1) a b) (JetFrame.srcJ_differentiableOn_ball _ hC N0 a b)
    (conjL pts) h.lower (by simpa using h.tail)
    (add_nonneg Khi_nonneg (JetFrame.KhiB_nonneg _)) (JetFrame.srcJ_decay _ (by simp) a b)


theorem jet_integrable_entry (N0 a b : ℕ) {pts : List ℂ} {d : ℂ} (h : PolyOK pts d) :
    Integrable (fun z => R.jW N0 pts d z * R.jRows N0 pts d a z * R.jRows N0 pts d b z)
      (Fr.muT N0) := by
  unfold Frame.muT
  rw [integrable_sumM_iff, integrable_sumM_iff]
  refine ⟨Integrable.of_finite, ?_, ?_⟩
  · have hi := ((upperJ_path hC N0 a b h).1).const_mul (-(2 * Real.pi * I)⁻¹)
    refine Integrable.congr ((Decay.integrable_comap_Ioi (fun r => R.wUpJ N0 pts d r
      * (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r - a)⁻¹
      * (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r - b)⁻¹)).2
      (IntegrableOn.congr_fun hi (fun r _ => ?_) measurableSet_Ioi))
      (Filter.Eventually.of_forall fun x => ?_)
    · simp only [wUpJ, JetFrame.srcJ, JetFrame.srcB, srcF]; ring
    · simp only [jW, Sum.elim_inr, Sum.elim_inl, jRows_up]
  · have hi := ((lowerJ_path hC N0 a b h).1).const_mul ((2 * Real.pi * I)⁻¹)
    refine Integrable.congr ((Decay.integrable_comap_Ioi (fun r => R.wLowJ N0 pts d r
      * (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r - a)⁻¹
      * (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r - b)⁻¹)).2
      (IntegrableOn.congr_fun hi (fun r _ => ?_) measurableSet_Ioi))
      (Filter.Eventually.of_forall fun x => ?_)
    · simp only [wLowJ, JetFrame.srcJ, JetFrame.srcB, srcF]; ring
    · simp only [jW, Sum.elim_inr, Sum.elim_inl, jRows_low]

/-- **The entries of the datum as an integral over the polygon space of the reference.** -/
theorem jet_entry (N0 a b : ℕ) {pts : List ℂ} {d : ℂ} (h : PolyOK pts d) :
    ∫ z, R.jW N0 pts d z * R.jRows N0 pts d a z * R.jRows N0 pts d b z ∂(Fr.muT N0)
      = (((datumJet D Fr.xs Fr.δ0 Fr.n0off).TentJ a b : ℝ) : ℂ) := by
  have hint := jet_integrable_entry R hC N0 a b h
  unfold Frame.muT at hint ⊢
  rw [integral_sumM _ _ _ hint]
  have hint2 := ((integrable_sumM_iff _ _ _).1 hint).2
  rw [integral_sumM _ _ _ hint2]
  rw [integral_count]
  have hA : ∑ p : ↥(Fr.atomIdx N0), (R.jW N0 pts d (Sum.inl p) * R.jRows N0 pts d a (Sum.inl p)
        * R.jRows N0 pts d b (Sum.inl p)) =
      (datumJet D Fr.xs Fr.δ0 Fr.n0off).headSum N0 a b := by
    rw [← atom_sum R N0 a b]
    rw [← Finset.sum_coe_sort (Fr.atomIdx N0) (fun p => R.aterm p.1 p.2 a b)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [jW, Sum.elim_inl, jRows_inl, aterm]
  set γ := pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts
  set γ' := pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts
  set η := pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts)
  set η' := pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts)
  have hU : ∫ x : Decay.RayP, (R.jW N0 pts d (Sum.inr (Sum.inl x))
        * R.jRows N0 pts d a (Sum.inr (Sum.inl x)) * R.jRows N0 pts d b (Sum.inr (Sum.inl x)))
        ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), R.wUpJ N0 pts d r * (γ r - a)⁻¹ * (γ r - b)⁻¹ := by
    have := integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
      (fun r => R.wUpJ N0 pts d r * (γ r - a)⁻¹ * (γ r - b)⁻¹)
    simpa only [jW, jRows_up, Sum.elim_inr, Sum.elim_inl] using this
  have hL : ∫ x : Decay.RayP, (R.jW N0 pts d (Sum.inr (Sum.inr x))
        * R.jRows N0 pts d a (Sum.inr (Sum.inr x)) * R.jRows N0 pts d b (Sum.inr (Sum.inr x)))
        ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), R.wLowJ N0 pts d r * (η r - a)⁻¹ * (η r - b)⁻¹ := by
    have := integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
      (fun r => R.wLowJ N0 pts d r * (η r - a)⁻¹ * (η r - b)⁻¹)
    simpa only [jW, jRows_low, Sum.elim_inr, Sum.elim_inl] using this
  have eU : ∫ r in Ioi (0 : ℝ), R.wUpJ N0 pts d r * (γ r - a)⁻¹ * (γ r - b)⁻¹
      = -(2 * Real.pi * I)⁻¹ * polyI ((datumJet D Fr.xs Fr.δ0 Fr.n0off).srcJ a b)
          ((Fr.xstar N0 : ℝ) : ℂ) pts d := by
    rw [← (upperJ_path hC N0 a b h).2, ← integral_const_mul]
    congr 1; funext r
    simp only [wUpJ, JetFrame.srcJ, JetFrame.srcB, srcF, γ, γ']; ring
  have eL : ∫ r in Ioi (0 : ℝ), R.wLowJ N0 pts d r * (η r - a)⁻¹ * (η r - b)⁻¹
      = (2 * Real.pi * I)⁻¹ * polyI ((datumJet D Fr.xs Fr.δ0 Fr.n0off).srcJ a b)
          ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) (starRingEnd ℂ d) := by
    rw [← (lowerJ_path hC N0 a b h).2, ← integral_const_mul]
    congr 1; funext r
    simp only [wLowJ, JetFrame.srcJ, JetFrame.srcB, srcF, η, η']; ring
  rw [hA, hU, hL, eU, eL]
  have hg := JetFrame.gram_formula (datumJet D Fr.xs Fr.δ0 Fr.n0off) hC N0 a b pts h.upper h.tail
  have hnorm : (((datumJet D Fr.xs Fr.δ0 Fr.n0off).norm : ℚ) : ℝ) = 1 := by
    simp [datumJet, datumFrame]
  rw [hnorm, one_mul] at hg
  have e : (fun z : ℂ => ((datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.EC z +
      (datumJet D Fr.xs Fr.δ0 Fr.n0off).E2cf z) * kk a b z) =
      (datumJet D Fr.xs Fr.δ0 Fr.n0off).srcJ a b := by
    funext z; unfold JetFrame.srcJ JetFrame.srcB kk srcF; ring
  rw [e] at hg
  have hxs : (datumJet D Fr.xs Fr.δ0 Fr.n0off).xstar N0 = Fr.xstar N0 := rfl
  rw [hxs] at hg
  rw [hg]
  unfold conjL
  ring

end Entry

end RefMatch
end CatalanCore.Uniform.Decay.Jet

/-! ### The ray weights of the jet -/

namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore

/-- `E_b` is exponentially small where the sines are large. -/
theorem norm_E2cf_le (JF : JetFrame) {κ : ℝ} (hκ : 0 < κ) {z : ℂ}
    (hsin : ∀ i, κ * Real.exp (Real.pi * |z.im|) ≤
      ‖Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ)))‖) :
    ‖JF.E2cf z‖ ≤ (Real.pi ^ 2 * (∑ i, |(JF.b i : ℝ)|) / κ ^ 2) *
      Real.exp (-(2 * Real.pi * |z.im|)) := by
  unfold JetFrame.E2cf
  refine (norm_sum_le _ _).trans ?_
  have hE : 0 < Real.exp (Real.pi * |z.im|) := Real.exp_pos _
  have hE2 : Real.exp (-(2 * Real.pi * |z.im|)) = (Real.exp (Real.pi * |z.im|))⁻¹ ^ 2 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    push_cast; ring
  rw [hE2]
  have hsum : (Real.pi ^ 2 * (∑ i, |(JF.b i : ℝ)|) / κ ^ 2) * (Real.exp (Real.pi * |z.im|))⁻¹ ^ 2 =
      ∑ i, |(JF.b i : ℝ)| * Real.pi ^ 2 / κ ^ 2 * (Real.exp (Real.pi * |z.im|))⁻¹ ^ 2 := by
    rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_mul]
    ring
  rw [hsum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hs := hsin i
  have hspos : 0 < κ * Real.exp (Real.pi * |z.im|) := by positivity
  have hb : ‖(JF.b i : ℂ)‖ = |(JF.b i : ℝ)| := by
    rw [show ((JF.b i : ℤ) : ℂ) = (((JF.b i : ℤ) : ℝ) : ℂ) by simp, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hb]
  have h1 : (κ * Real.exp (Real.pi * |z.im|)) ^ 2 ≤ ‖Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ)))‖ ^ 2 :=
    pow_le_pow_left₀ hspos.le hs 2
  have h2 : Real.pi ^ 2 / ‖Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ)))‖ ^ 2 ≤
      Real.pi ^ 2 / (κ * Real.exp (Real.pi * |z.im|)) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  calc |(JF.b i : ℝ)| * (Real.pi ^ 2 / ‖Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ)))‖ ^ 2)
      ≤ |(JF.b i : ℝ)| * (Real.pi ^ 2 / (κ * Real.exp (Real.pi * |z.im|)) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |(JF.b i : ℝ)| * Real.pi ^ 2 / κ ^ 2 * (Real.exp (Real.pi * |z.im|))⁻¹ ^ 2 := by
        field_simp

end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

/-- The ray constant of the jet weights: the cotangent constant of the datum's simple part plus the
`1/sin²` constant of its double part, at the first-edge slope `q`. -/
noncomputable def rayK (q : ℝ) : ℝ :=
  CP (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame q +
    Real.pi ^ 2 * (∑ i, |(D.b i : ℝ)|) / (kappaP (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame q) ^ 2

theorem rayK_nonneg (hC : (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK) (q : ℝ) :
    0 ≤ rayK (D := D) (Fr := Fr) q := by
  have hk := kappaP_pos hC q
  unfold rayK CP
  positivity

theorem norm_wUpJ_le (hC : (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK) (N0 : ℕ)
    {pts : List ℂ} {d : ℂ} (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im) {u : ℝ} (hu : 0 ≤ u) :
    ‖R.wUpJ N0 pts d u‖ ≤
      rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) *
        Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖ := by
  set JF := datumJet D Fr.xs Fr.δ0 Fr.n0off with hJF
  have hE : ‖JF.toFrame.EC (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)‖ ≤
      CP JF.toFrame (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) *
        Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) :=
    norm_EC_path (Fr := JF.toFrame) hC N0 hlow hd hu
  have hB := norm_E2cf_le JF (kappaP_pos hC (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d))
    (z := pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)
    (fun i => path_sin_lower (Fr := JF.toFrame) hC N0 hlow hd hu i)
  have h2 : ‖(2 * Real.pi * I : ℂ)⁻¹‖ = 1 / (2 * Real.pi) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]; simp
  unfold wUpJ
  rw [norm_neg, norm_mul, norm_mul, h2]
  have hpi := Real.pi_pos
  have hsum : ‖JF.toFrame.EC (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u) +
      JF.E2cf (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)‖ ≤
      rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) *
        Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) := by
    refine (norm_add_le _ _).trans ?_
    have hB' : ‖JF.E2cf (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)‖ ≤
        (Real.pi ^ 2 * (∑ i, |(D.b i : ℝ)|) /
          (kappaP JF.toFrame (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)) ^ 2) *
          Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) := hB
    refine (add_le_add hE hB').trans (le_of_eq ?_)
    unfold rayK
    rw [← hJF]
    ring
  calc 1 / (2 * Real.pi) * (‖JF.toFrame.EC (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u) +
        JF.E2cf (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)‖ *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖)
      ≤ 1 / (2 * Real.pi) * ((rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) *
          Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|))) *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖) := by
        gcongr
    _ = _ := by ring

end RefMatch
end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

theorem norm_wLowJ_le (hC : (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK) (N0 : ℕ)
    {pts : List ℂ} {d : ℂ} (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im) {u : ℝ} (hu : 0 ≤ u) :
    ‖R.wLowJ N0 pts d u‖ ≤
      rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) *
        Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖ := by
  set JF := datumJet D Fr.xs Fr.δ0 Fr.n0off with hJF
  have hE := norm_EC_path_lower (Fr := JF.toFrame) hC N0 hlow hd hu
  rw [conjL_conj_path (Fr := JF.toFrame), Complex.conj_im, abs_neg] at hE
  have hE' : ‖JF.toFrame.EC (starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u))‖ ≤
      CP JF.toFrame (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) *
        Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) := hE
  have hB := norm_E2cf_le JF (kappaP_pos hC (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d))
    (z := pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)
    (fun i => path_sin_lower (Fr := JF.toFrame) hC N0 hlow hd hu i)
  have hB' : ‖JF.E2cf (starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u))‖ ≤
      (Real.pi ^ 2 * (∑ i, |(D.b i : ℝ)|) /
        (kappaP JF.toFrame (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)) ^ 2) *
        Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) := by
    rw [JetFrame.E2cf_conj, Complex.norm_conj]; exact hB
  have h2 : ‖(2 * Real.pi * I : ℂ)⁻¹‖ = 1 / (2 * Real.pi) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]; simp
  unfold wLowJ
  rw [norm_mul, norm_mul, h2, conjL_conj_der (Fr := Fr), Complex.norm_conj, conjL_conj_path (Fr := Fr)]
  have hpi := Real.pi_pos
  have hsum : ‖JF.toFrame.EC (starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)) +
      JF.E2cf (starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u))‖ ≤
      rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) *
        Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add hE' hB').trans (le_of_eq ?_)
    unfold rayK
    rw [← hJF]
    ring
  calc 1 / (2 * Real.pi) * (‖JF.toFrame.EC (starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)) +
        JF.E2cf (starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u))‖ *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖)
      ≤ 1 / (2 * Real.pi) * ((rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) *
          Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|))) *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖) := by
        gcongr
    _ = _ := by ring

end RefMatch
end CatalanCore.Uniform.Decay.Jet

/-! ### The hypotheses of the jet source and the jet field -/

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

/-- The reference hypotheses (S04, F1-F3) in the form the jet field uses, with the constants `ρ, a, a0, g,
d₀` of the lattice. -/
structure JetSetup (N0 : ℕ) (pts : List ℂ) (d : ℂ) (ρ a a0 g d₀ : ℝ) : Prop where
  ρ_pos : 0 < ρ
  a_pos : 0 < a
  a_le : a ≤ 1
  a0_pos : 0 < a0
  g_pos : 0 < g
  d0_pos : 0 < d₀
  hw : ∀ q, Fr.w q ≠ 0
  sepR : ∀ (m m' : ℕ) (q q' : Fin Fr.d), (m, q) ≠ (m', q') →
    g ≤ |((m : ℝ) + (Fr.μ q : ℝ)) - ((m' : ℝ) + (Fr.μ q' : ℝ))|
  helper_dist : ∀ j : {i : Fin D.n // D.b i ≠ 0},
    |(Fr.μ (R.role.symm (Sum.inr j)) : ℝ) - (D.s j.1 : ℝ)| ≤ 1 / 2
  a_rho : ∀ i, a + ρ ≤ (D.s i : ℝ)
  rho_gap : 2 * ρ ≤ g
  a0_mu : ∀ q, a0 ≤ (Fr.μ q : ℝ)
  a0_one : a0 ≤ 1
  rayim_up : ∀ r : Decay.RayP, (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im ≠ 0
  rayim_low : ∀ r : Decay.RayP, (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r.1).im ≠ 0
  rayR : ∀ z z' : Fr.XT N0, (polyPt Fr N0 pts d z).im = 0 → (polyPt Fr N0 pts d z').im ≠ 0 →
    d₀ ≤ ‖polyPt Fr N0 pts d z' - polyPt Fr N0 pts d z‖

end RefMatch
end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

theorem pos0_atom (N0 : ℕ) (pts : List ℂ) (d : ℂ) (p : ↥(Fr.atomIdx N0)) :
    polyPt Fr N0 pts d (Sum.inl p) = (((-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ))) : ℝ) : ℂ) := by
  simp [polyPt, Frame.atomPos]

theorem ctr_atom (N0 : ℕ) (pts : List ℂ) (d : ℂ) (p : ↥(Fr.atomIdx N0)) :
    R.jCtr N0 pts d (Sum.inl p) = (((-((p.1.1 : ℝ) + (D.s (R.dix p.1.2) : ℝ))) : ℝ) : ℂ) := by
  simp [jCtr, dpos]
  ring

theorem mu_of_dix_inl (q : Fin Fr.d) (i : Fin D.n) (h : R.role q = Sum.inl i) :
    (Fr.μ q : ℝ) = (D.s i : ℝ) := by
  have : q = R.role.symm (Sum.inl i) := by rw [← h]; simp
  rw [this, R.idx_mu i]

theorem dix_inl (q : Fin Fr.d) (i : Fin D.n) (h : R.role q = Sum.inl i) : R.dix q = i := by
  simp [dix, h]

theorem dix_inr (q : Fin Fr.d) (j : {i : Fin D.n // D.b i ≠ 0}) (h : R.role q = Sum.inr j) :
    R.dix q = j.1 := by
  simp [dix, h]

theorem epsq_cases (q : Fin Fr.d) :
    (R.epsq q = 0 ∧ ∃ i, R.role q = Sum.inl i ∧ D.b i = 0) ∨ R.epsq q = 1 ∨ R.epsq q = -1 := by
  unfold epsq
  rcases h : R.role q with i | j
  · by_cases hb : D.b i = 0
    · left; exact ⟨by simp [hb], i, rfl, hb⟩
    · right; left; simp [hb]
  · right; right; rfl

theorem kapq_of_eps_zero (q : Fin Fr.d) (h : R.epsq q = 0) : R.kapq q = 1 ∧ R.dpos 0 q = R.dpos 0 q := by
  refine ⟨?_, rfl⟩
  unfold epsq at h
  unfold kapq
  rcases hr : R.role q with i | j
  · rw [hr] at h
    by_cases hb : D.b i = 0
    · simp [hb]
    · simp [hb] at h
  · rw [hr] at h
    simp at h

end RefMatch
end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

/-- The coefficient bound `Bk` of the jet rows. -/
noncomputable def kapBound : ℝ := 1 + ∑ q : Fin Fr.d, ‖R.kapq q‖

theorem norm_ofReal_sub (x y : ℝ) : ‖((x : ℝ) : ℂ) - ((y : ℝ) : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **The jet field on the polygon space of the reference.** -/
theorem jetField_xt {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ} (hS : SourceRep Fr N0 pts d C V)
    {ρ a a0 g d₀ : ℝ} (st : R.JetSetup N0 pts d ρ a a0 g d₀) :
    ∀ (k : ℕ) (s : Fin k → ℕ), Function.Injective s → ∀ z : Fin k → Fr.XT N0,
      ‖(Matrix.of fun i l : Fin k => R.jRows N0 pts d (s i) (z l)).det‖ ≤
        Real.exp (k * (jetC1 R.kapBound ρ a g d₀ (ρ + 1 / 2) +
          jetC2 g d₀ (ρ + 1 / 2) * Real.log ((k : ℝ) + 1))) *
          ‖CatalanLambda.Decay.cexpr (fun l => polyPt Fr N0 pts d (z l)) (fun i => (s i : ℂ))‖ := by
  have hBk : 0 ≤ R.kapBound := by
    unfold kapBound
    have : 0 ≤ ∑ q : Fin Fr.d, ‖R.kapq q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hlab : ∀ p p' : ↥(Fr.atomIdx N0), p ≠ p' →
      g ≤ |((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)) - ((p'.1.1 : ℝ) + (Fr.μ p'.1.2 : ℝ))| := by
    intro p p' hne
    exact st.sepR p.1.1 p'.1.1 p.1.2 p'.1.2 (fun h => hne (Subtype.ext h))
  refine jet_field (polyPt Fr N0 pts d) (R.jCtr N0 pts d) (R.jKap N0) (R.jEps N0)
    (ρ := ρ) (a := a) (a0 := a0) (g := g) (d₀ := d₀) (eJ := ρ + 1 / 2) (Bk := R.kapBound)
    st.ρ_pos st.a_pos st.a_le st.a0_pos st.g_pos st.d0_pos (by have := st.ρ_pos; positivity) hBk
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hkap
    intro z
    rcases z with p | r | r
    · simp only [jKap, Sum.elim_inl]
      unfold kapBound
      have := Finset.single_le_sum (f := fun q => ‖R.kapq q‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ p.1.2)
      linarith
    all_goals
      simp only [jKap, Sum.elim_inr, norm_one]
      unfold kapBound
      have : 0 ≤ ∑ q : Fin Fr.d, ‖R.kapq q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      linarith
  · -- heps
    intro z
    rcases z with p | r | r
    · simp only [jEps, Sum.elim_inl]
      rcases R.epsq_cases p.1.2 with ⟨h, _⟩ | h | h <;> simp [h]
    all_goals simp [jEps]
  · -- hplain
    intro z hz
    rcases z with p | r | r
    · simp only [jEps, Sum.elim_inl] at hz
      refine ⟨by simp only [jKap, Sum.elim_inl]; exact (R.kapq_of_eps_zero p.1.2 hz).1, ?_⟩
      rcases R.epsq_cases p.1.2 with ⟨_, i, hi, _⟩ | h | h
      · rw [ctr_atom, pos0_atom, R.dix_inl _ i hi, R.mu_of_dix_inl _ i hi]
      · rw [h] at hz; exact absurd hz one_ne_zero
      · rw [h] at hz; exact absurd hz (by norm_num)
    all_goals simp [jKap, jCtr, polyPt]
  · -- hJre
    intro z hz
    rcases z with p | r | r
    · rw [ctr_atom, pos0_atom]
      refine ⟨by simp, by simp, ?_⟩
      rw [norm_ofReal_sub]
      have key : |(-((p.1.1 : ℝ) + (D.s (R.dix p.1.2) : ℝ))) - (-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)))| ≤ 1 / 2 := by
        have e : (-((p.1.1 : ℝ) + (D.s (R.dix p.1.2) : ℝ))) - (-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)))
            = (Fr.μ p.1.2 : ℝ) - (D.s (R.dix p.1.2) : ℝ) := by ring
        rw [e]
        rcases hr : R.role p.1.2 with i | j
        · rw [R.mu_of_dix_inl _ i hr, R.dix_inl _ i hr]; simp
        · rw [R.dix_inr _ j hr]
          have := st.helper_dist j
          have hq : p.1.2 = R.role.symm (Sum.inr j) := by rw [← hr]; simp
          rw [hq]; exact this
      linarith
    all_goals exact absurd (by simp [jEps]) hz
  · -- hpos
    intro z z' h
    rcases z with p | r | r <;> rcases z' with p' | r' | r'
    · by_cases hp : p = p'
      · subst hp; exact ⟨rfl, rfl, rfl⟩
      · exfalso
        rw [pos0_atom, pos0_atom] at h
        have h' := Complex.ofReal_injective h
        have := hlab p p' hp
        have h0 : ((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)) - ((p'.1.1 : ℝ) + (Fr.μ p'.1.2 : ℝ)) = 0 := by linarith
        rw [h0, abs_zero] at this
        linarith [st.g_pos]
    · exfalso
      have := st.rayim_up r'
      rw [pos0_atom] at h
      have h2 : (polyPt Fr N0 pts d (Sum.inr (Sum.inl r'))).im = 0 := by rw [← h]; simp
      exact this h2
    · exfalso
      have := st.rayim_low r'
      rw [pos0_atom] at h
      have h2 : (polyPt Fr N0 pts d (Sum.inr (Sum.inr r'))).im = 0 := by rw [← h]; simp
      exact this h2
    · exfalso
      have := st.rayim_up r
      rw [pos0_atom] at h
      have h2 : (polyPt Fr N0 pts d (Sum.inr (Sum.inl r))).im = 0 := by rw [h]; simp
      exact this h2
    · exact ⟨h, rfl, rfl⟩
    · exact ⟨h, rfl, rfl⟩
    · exfalso
      have := st.rayim_low r
      rw [pos0_atom] at h
      have h2 : (polyPt Fr N0 pts d (Sum.inr (Sum.inr r))).im = 0 := by rw [h]; simp
      exact this h2
    · exact ⟨h, rfl, rfl⟩
    · exact ⟨h, rfl, rfl⟩
  · -- hsepι
    intro z z' hne h1 h2
    rcases z with p | r | r <;> rcases z' with p' | r' | r'
    · have hp : p ≠ p' := fun hh => hne (by rw [hh])
      have := hlab p p' hp
      rw [pos0_atom, pos0_atom]
      simp only [Complex.ofReal_re]
      have e : (-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ))) - (-((p'.1.1 : ℝ) + (Fr.μ p'.1.2 : ℝ))) =
          -(((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)) - ((p'.1.1 : ℝ) + (Fr.μ p'.1.2 : ℝ))) := by ring
      rw [e, abs_neg]; exact this
    all_goals first
      | exact absurd h2 (st.rayim_up _) | exact absurd h2 (st.rayim_low _)
      | exact absurd h1 (st.rayim_up _) | exact absurd h1 (st.rayim_low _)
  · -- hrayι
    exact fun z z' h1 h2 => st.rayR z z' h1 h2
  · -- hnode0
    intro z t
    rcases z with p | r | r
    · rw [pos0_atom, ← Complex.ofReal_natCast, norm_ofReal_sub]
      have h1 : (0 : ℝ) ≤ (p.1.1 : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
      have h3 := st.a0_mu p.1.2
      have e : (-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ))) - (t : ℝ) =
          -(((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)) + (t : ℝ)) := by ring
      rw [e, abs_neg, abs_of_nonneg (by have := Frame.mu_pos (Fr := Fr) p.1.2; linarith)]
      linarith
    · have := hS.node_dist r.1 (le_of_lt r.2) (t : ℝ) (Nat.cast_nonneg t)
      rw [Complex.ofReal_natCast] at this
      exact st.a0_one.trans this
    · have := hS.node_dist r.1 (le_of_lt r.2) (t : ℝ) (Nat.cast_nonneg t)
      rw [Complex.ofReal_natCast] at this
      simp only [polyPt, Sum.elim_inr]
      rw [hS.conj_pt]
      have e : (starRingEnd ℂ) (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1) - (t : ℂ) =
          (starRingEnd ℂ) (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1 - (t : ℂ)) := by simp
      rw [e, Complex.norm_conj]
      exact st.a0_one.trans this
  · -- hnodeJ
    intro z hz t
    rcases z with p | r | r
    · rw [ctr_atom, ← Complex.ofReal_natCast, norm_ofReal_sub]
      have h1 : (0 : ℝ) ≤ (p.1.1 : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
      have h3 := st.a_rho (R.dix p.1.2)
      have hs := (D.hs (R.dix p.1.2)).1
      have e : (-((p.1.1 : ℝ) + (D.s (R.dix p.1.2) : ℝ))) - (t : ℝ) =
          -(((p.1.1 : ℝ) + (D.s (R.dix p.1.2) : ℝ)) + (t : ℝ)) := by ring
      have hs' : (0 : ℝ) < (D.s (R.dix p.1.2) : ℝ) := by exact_mod_cast hs
      rw [e, abs_neg, abs_of_nonneg (by linarith)]
      linarith
    all_goals exact absurd (by simp [jEps]) hz
  · -- htight
    intro z z' hne h1 h2 _
    have hat : ∀ w : Fr.XT N0, R.jEps N0 w ≠ 0 → ∃ p, w = Sum.inl p := by
      intro w hw
      rcases w with p | r | r
      · exact ⟨p, rfl⟩
      · exact absurd (by simp [jEps]) hw
      · exact absurd (by simp [jEps]) hw
    obtain ⟨p, rfl⟩ := hat z h1
    obtain ⟨p', rfl⟩ := hat z' h2
    have hp : p ≠ p' := fun hh => hne (by rw [hh])
    have := hlab p p' hp
    rw [pos0_atom, pos0_atom, norm_ofReal_sub]
    have e : (-((p'.1.1 : ℝ) + (Fr.μ p'.1.2 : ℝ))) - (-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ))) =
        -(((p'.1.1 : ℝ) + (Fr.μ p'.1.2 : ℝ)) - ((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ))) := by ring
    rw [e, abs_neg, abs_sub_comm]
    linarith [st.rho_gap]

end RefMatch
end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore CatalanCore.Uniform.Decay.PolyChain
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

theorem vq_ray_eq (A s g e : ℝ) (hA : 0 < A) :
    A ^ e * (Real.exp (-((2 * Real.pi * e) * s)) * g) * (A ^ (1 - e) * Real.exp (-((1 - e) * (2 * Real.pi * s))))
      = A * (Real.exp (-(2 * Real.pi * s)) * g) := by
  have h1 : A ^ e * A ^ (1 - e) = A := by
    rw [← Real.rpow_add hA]; simp
  have h2 : Real.exp (-((2 * Real.pi * e) * s)) * Real.exp (-((1 - e) * (2 * Real.pi * s))) =
      Real.exp (-(2 * Real.pi * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc A ^ e * (Real.exp (-((2 * Real.pi * e) * s)) * g) * (A ^ (1 - e) * Real.exp (-((1 - e) * (2 * Real.pi * s))))
      = (A ^ e * A ^ (1 - e)) * (Real.exp (-((2 * Real.pi * e) * s)) *
        Real.exp (-((1 - e) * (2 * Real.pi * s)))) * g := by ring
    _ = _ := by rw [h1, h2]; ring

/-- The weight constant of the jet source. -/
noncomputable def cwOf (q : ℝ) : ℝ := 1 + ∑ i : Fin Fr.d, ‖R.Wq i‖ + rayK (D := D) (Fr := Fr) q / (2 * Real.pi)

theorem one_le_cwOf (hC : (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK) (q : ℝ) :
    1 ≤ R.cwOf q := by
  have h1 : 0 ≤ ∑ i : Fin Fr.d, ‖R.Wq i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : 0 ≤ rayK (D := D) (Fr := Fr) q / (2 * Real.pi) := by
    have := rayK_nonneg (D := D) (Fr := Fr) hC q
    positivity
  unfold cwOf; linarith

end RefMatch
end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore CatalanCore.Uniform.Decay.PolyChain
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

section Assembly

variable {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}

/-- The weight bound `‖W‖ ≤ cw · vP qP`. -/
theorem jW_weight (hC : (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK)
    (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im)
    (st : ∀ q, Fr.w q ≠ 0) {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (z : Fr.XT N0) :
    ‖R.jW N0 pts d z‖ ≤ R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) *
      (vP Fr N0 pts d C e z * qP Fr N0 pts d C e z) := by
  have hcw := R.one_le_cwOf hC (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
  have hA := amp_pos C
  have hA1 := one_le_amp C
  have hK := rayK_nonneg (D := D) (Fr := Fr) hC (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
  rcases z with p | r | r
  · simp only [jW, Sum.elim_inl, vP, qP, mul_one]
    have h1 : (1 : ℝ) ≤ |(Fr.w p.1.2 : ℝ)| := by
      have := st p.1.2
      have : (1 : ℤ) ≤ |Fr.w p.1.2| := Int.one_le_abs this
      exact_mod_cast this
    have h2 : ‖R.Wq p.1.2‖ ≤ ∑ i : Fin Fr.d, ‖R.Wq i‖ :=
      Finset.single_le_sum (f := fun i => ‖R.Wq i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
    have h3 : ∑ i : Fin Fr.d, ‖R.Wq i‖ + 1 ≤ R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) := by
      unfold cwOf
      have : 0 ≤ rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) := by
        positivity
      linarith
    have hw0 : (0 : ℝ) ≤ |(Fr.w p.1.2 : ℝ)| := abs_nonneg _
    nlinarith [norm_nonneg (R.Wq p.1.2)]
  · have hu : 0 ≤ r.1 := le_of_lt r.2
    have hb := R.norm_wUpJ_le hC N0 hlow hd hu
    simp only [jW, Sum.elim_inr, Sum.elim_inl, vP, qP, vPath, gam, gamD]
    rw [vq_ray_eq (amp C) _ _ e hA]
    refine hb.trans ?_
    have hex : 0 ≤ Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖ := by positivity
    have hk2 : rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) ≤
        R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * amp C := by
      have hS0 : 0 ≤ ∑ i : Fin Fr.d, ‖R.Wq i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hcwK : rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) ≤
          R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) := by
        unfold cwOf; linarith
      calc _ ≤ R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) := hcwK
        _ = R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hA1 (by linarith)
    calc rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) *
          Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
          ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖
        = (rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi)) *
          (Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
          ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖) := by ring
      _ ≤ (R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * amp C) *
          (Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
          ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖) := mul_le_mul_of_nonneg_right hk2 hex
      _ = _ := by ring
  · have hu : 0 ≤ r.1 := le_of_lt r.2
    have hb := R.norm_wLowJ_le hC N0 hlow hd hu
    simp only [jW, Sum.elim_inr, vP, qP, vPath, gam, gamD]
    rw [vq_ray_eq (amp C) _ _ e hA]
    refine hb.trans ?_
    have hex : 0 ≤ Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖ := by positivity
    have hk2 : rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) ≤
        R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * amp C := by
      have hS0 : 0 ≤ ∑ i : Fin Fr.d, ‖R.Wq i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hcwK : rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) ≤
          R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) := by
        unfold cwOf; linarith
      calc _ ≤ R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) := hcwK
        _ = R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hA1 (by linarith)
    calc rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) *
          Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
          ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖
        = (rayK (D := D) (Fr := Fr) (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi)) *
          (Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
          ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖) := by ring
      _ ≤ (R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * amp C) *
          (Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
          ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖) := mul_le_mul_of_nonneg_right hk2 hex
      _ = _ := by ring

end Assembly

end RefMatch
end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

theorem jet_andreief (hC : (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK) (N0 : ℕ)
    {pts : List ℂ} {d : ℂ} (h : PolyOK pts d) (k : ℕ) (s t : Fin k → ℕ) :
    ‖(Matrix.of fun i j : Fin k => (((datumJet D Fr.xs Fr.δ0 Fr.n0off).TentJ (s i) (t j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * ∫ z : Fin k → Fr.XT N0,
        (∏ l, ‖R.jW N0 pts d (z l)‖) *
          (‖(Matrix.of fun i l : Fin k => R.jRows N0 pts d (s i) (z l)).det‖ *
            ‖(Matrix.of fun j l : Fin k => R.jRows N0 pts d (t j) (z l)).det‖)
          ∂(Measure.pi fun _ => Fr.muT N0) := by
  have hb := CatalanLambda.Decay.norm_det_le_andreief (Fr.muT N0) (R.jW N0 pts d)
    (fun (i : Fin k) z => R.jRows N0 pts d (s i) z) (fun (j : Fin k) z => R.jRows N0 pts d (t j) z)
    (fun i j => jet_integrable_entry R hC N0 (s i) (t j) h)
  have hM : (Matrix.of fun i j : Fin k => ∫ z, R.jW N0 pts d z * R.jRows N0 pts d (s i) z *
        R.jRows N0 pts d (t j) z ∂(Fr.muT N0)) =
      Matrix.of fun i j : Fin k => (((datumJet D Fr.xs Fr.δ0 Fr.n0off).TentJ (s i) (t j) : ℝ) : ℂ) := by
    ext i j; exact jet_entry R hC N0 (s i) (t j) h
  rw [hM] at hb
  refine hb.trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  ring

end RefMatch
end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore CatalanCore.Uniform.Decay.PolyChain CatalanCore.Uniform.Decay.Assembly
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

/-- **The jet source of a datum over the polygon space of the reference, at one scale.** -/
noncomputable def jetRep {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hC : (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK)
    (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im) (hPoly : PolyOK pts d)
    (hS : SourceRep Fr N0 pts d C V) {ρ a a0 g d₀ : ℝ} (st : R.JetSetup N0 pts d ρ a a0 g d₀) :
    JetRep Fr N0 pts d C where
  W := R.jW N0 pts d
  rows := fun t z => R.jRows N0 pts d t z
  Φ := fun x y => (datumJet D Fr.xs Fr.δ0 Fr.n0off).TentJ x y
  cw := R.cwOf (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
  hcw := R.one_le_cwOf hC _
  c1 := jetC1 R.kapBound ρ a g d₀ (ρ + 1 / 2)
  c2 := jetC2 g d₀ (ρ + 1 / 2)
  hc1 := by
    have hBk : 0 ≤ R.kapBound := by
      unfold kapBound
      have : 0 ≤ ∑ q : Fin Fr.d, ‖R.kapq q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      linarith
    exact jetC1_nonneg st.ρ_pos st.a_pos st.a_le st.g_pos st.d0_pos
      (by have := st.ρ_pos; positivity) hBk
  hc2 := jetC2_nonneg st.g_pos st.d0_pos (by have := st.ρ_pos; positivity)
  weight := fun e he0 he1 z => R.jW_weight (C := C) hC hlow hd st.hw he0 he1 z
  andreief := fun k s t _ _ => R.jet_andreief hC N0 hPoly k s t
  jet := fun k s hs z => R.jetField_xt hS st k s hs z

/-- **The jet sources of all large scales, with uniform constants.** -/
theorem jetFamily {P : RatPolygon} (hP : P.OK) (hCr : Fr.ContourOK)
    (hCd : (datumJet D Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK) {ρ a a0 g d₀ : ℝ}
    (hsetup : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) →
      R.JetSetup (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir ρ a a0 g d₀) :
    ∃ J : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) →
      JetRep Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (CP Fr (P.qRat : ℝ)),
      (∀ r hr x y, (J r hr).Φ x y = (lw D.f D.e x y : ℝ) + (if x = y then D.xi else 0)) ∧
      (∀ r hr, (J r hr).cw = R.cwOf (P.qRat : ℝ)) ∧
      (∀ r hr, (J r hr).c1 = jetC1 R.kapBound ρ a g d₀ (ρ + 1 / 2)) ∧
      (∀ r hr, (J r hr).c2 = jetC2 g d₀ (ρ + 1 / 2)) := by
  have key : ∀ (r : ℕ) (hr : Rmin Fr P ≤ (r : ℝ)), ∃ Jr : JetRep Fr (N0Of Fr P.r0 r) (physL Fr P r)
      P.tailDir (CP Fr (P.qRat : ℝ)),
      (∀ x y, Jr.Φ x y = (lw D.f D.e x y : ℝ) + (if x = y then D.xi else 0)) ∧
      Jr.cw = R.cwOf (P.qRat : ℝ) ∧ Jr.c1 = jetC1 R.kapBound ρ a g d₀ (ρ + 1 / 2) ∧
      Jr.c2 = jetC2 g d₀ (ρ + 1 / 2) := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ r := (le_max_left _ _).trans hr
    have hrpos : (0 : ℝ) < r := by linarith
    have hinv : (P.invIm : ℝ) ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hr
    obtain ⟨hS, _⟩ := polygonRep_scaled hCr hP hr
    have hhigh := high_of_ge hP hinv
    have hone := RatPolygon.physPts_high (Fr.xstar (N0Of Fr P.r0 r)) r hhigh
    rw [physPts_eq_scaled] at hone
    have hlow : ∀ z ∈ physL Fr P r, 1 / 8 ≤ z.im := fun z hz => by linarith [hone z hz]
    have hPoly : PolyOK (physL Fr P r) P.tailDir := by
      have := RatPolygon.polyOK hP (Fr.xstar (N0Of Fr P.r0 r)) hrpos
      rw [physPts_eq_scaled] at this
      exact this
    have hq : qFirst ((Fr.xstar (N0Of Fr P.r0 r) : ℝ) : ℂ) (physL Fr P r) P.tailDir = (P.qRat : ℝ) := by
      have := RatPolygon.qFirst_phys hP (Fr.xstar (N0Of Fr P.r0 r)) hrpos
      rw [physPts_eq_scaled] at this
      exact this
    refine ⟨R.jetRep hCd hlow (RatPolygon.tailDir_im_pos hP) hPoly hS (hsetup r hr), ?_, ?_, rfl, rfl⟩
    · intro x y
      exact (datum_phi_eq D Fr.xs Fr.δ0 Fr.n0off x y).symm
    · show R.cwOf (qFirst ((Fr.xstar (N0Of Fr P.r0 r) : ℝ) : ℂ) (physL Fr P r) P.tailDir) = _
      rw [hq]
  choose J hJ using key
  exact ⟨J, fun r hr => (hJ r hr).1, fun r hr => (hJ r hr).2.1, fun r hr => (hJ r hr).2.2.1,
    fun r hr => (hJ r hr).2.2.2⟩

end RefMatch
end CatalanCore.Uniform.Decay.Jet

/-! ### The rays of a polygon with non-positive leans -/

namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore

/-- Points of the upper path at positive parameter have positive imaginary part. -/
theorem pathPt_im_pos (d : ℂ) (hd : 0 < d.im) :
    ∀ (l : List ℂ) (a : ℂ), 0 ≤ a.im → (∀ z ∈ l, 0 < z.im) → ∀ u : ℝ, 0 < u →
      0 < (pathPt d a l u).im
  | [], a, ha, _, u, hu => by
    simp only [pathPt, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    nlinarith
  | b :: l, a, ha, hl, u, hu => by
    by_cases h1 : u ≤ 1
    · simp only [pathPt, if_pos h1, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.sub_im]
      have hb := hl b (by simp)
      nlinarith
    · simp only [pathPt, if_neg h1]
      exact pathPt_im_pos d hd l b (hl b (by simp)).le (fun z hz => hl z (by simp [hz])) (u - 1)
        (by linarith)

/-- Points of the upper path stay to the left of `c` when the vertices and the tail do. -/
theorem pathPt_re_le (d : ℂ) (hd : d.re ≤ 0) (c : ℝ) :
    ∀ (l : List ℂ) (a : ℂ), a.re ≤ c → (∀ z ∈ l, z.re ≤ c) → ∀ u : ℝ, 0 ≤ u →
      (pathPt d a l u).re ≤ c
  | [], a, ha, _, u, hu => by
    simp only [pathPt, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    nlinarith
  | b :: l, a, ha, hl, u, hu => by
    by_cases h1 : u ≤ 1
    · simp only [pathPt, if_pos h1, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
      have hb := hl b (by simp)
      nlinarith
    · simp only [pathPt, if_neg h1]
      exact pathPt_re_le d hd c l b (hl b (by simp)) (fun z hz => hl z (by simp [hz])) (u - 1)
        (by linarith)

end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
namespace RefMatch
open CatalanCore CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.PolyChain
variable {D : Datum} {Fr : Frame} (R : RefMatch D Fr)

/-- **The lattice hypotheses on the rays, from a polygon with non-positive leans.**  The constants
`ρ, a, a0, g` and the reference conditions are uniform; the ray conditions (`rayim_up`, `rayim_low`, `rayR`
with `d₀ = δ0`) are proved from the geometry of the polygon and the contour gap of the reference. -/
theorem jetSetup_of_polygon {P : RatPolygon} (hP : P.OK) (hCr : Fr.ContourOK)
    (hneg : ∀ p ∈ P.verts, p.1 + P.r0 ≤ 0) {r : ℕ} (hr : Rmin Fr P ≤ (r : ℝ))
    {ρ a a0 g : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (ha1 : a ≤ 1) (ha0 : 0 < a0) (hg : 0 < g)
    (hw : ∀ q, Fr.w q ≠ 0)
    (sepR : ∀ (m m' : ℕ) (q q' : Fin Fr.d), (m, q) ≠ (m', q') →
      g ≤ |((m : ℝ) + (Fr.μ q : ℝ)) - ((m' : ℝ) + (Fr.μ q' : ℝ))|)
    (helper_dist : ∀ j : {i : Fin D.n // D.b i ≠ 0},
      |(Fr.μ (R.role.symm (Sum.inr j)) : ℝ) - (D.s j.1 : ℝ)| ≤ 1 / 2)
    (a_rho : ∀ i, a + ρ ≤ (D.s i : ℝ)) (rho_gap : 2 * ρ ≤ g)
    (a0_mu : ∀ q, a0 ≤ (Fr.μ q : ℝ)) (a0_one : a0 ≤ 1) :
    R.JetSetup (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir ρ a a0 g (Fr.δ0 : ℝ) := by
  have hr1 : (1 : ℝ) ≤ r := (le_max_left _ _).trans hr
  have hrpos : (0 : ℝ) < r := by linarith
  set N0 := N0Of Fr P.r0 r with hN0
  have hd : 0 < P.tailDir.im := RatPolygon.tailDir_im_pos hP
  have hverts : ∀ z ∈ physL Fr P r, 0 < z.im := by
    have := RatPolygon.physPts_upper hP (Fr.xstar N0) hrpos
    rw [hN0, physPts_eq_scaled] at this
    exact this
  have hre : ∀ z ∈ physL Fr P r, z.re ≤ Fr.xstar N0 := by
    have h0 : ∀ z ∈ P.physPts (Fr.xstar N0) r, z.re ≤ Fr.xstar N0 := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := RatPolygon.mem_physPts hz
      simp only [RatPolygon.off, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      have h1 : ((p.1 + P.r0 : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hneg p hp
      nlinarith
    rw [hN0, physPts_eq_scaled] at h0
    exact h0
  have hup : ∀ u : ℝ, 0 < u → 0 < (pathPt P.tailDir ((Fr.xstar N0 : ℝ) : ℂ) (physL Fr P r) u).im :=
    fun u hu => pathPt_im_pos P.tailDir hd (physL Fr P r) _ (by simp) hverts u hu
  have hrel : ∀ u : ℝ, 0 ≤ u →
      (pathPt P.tailDir ((Fr.xstar N0 : ℝ) : ℂ) (physL Fr P r) u).re ≤ Fr.xstar N0 :=
    fun u hu => pathPt_re_le P.tailDir (by rw [RatPolygon.tailDir_re]; norm_num) (Fr.xstar N0)
      (physL Fr P r) _ (by simp) hre u hu
  have hlowim : ∀ u : ℝ, 0 < u →
      (pathPt (starRingEnd ℂ P.tailDir) ((Fr.xstar N0 : ℝ) : ℂ) (conjL (physL Fr P r)) u).im ≠ 0 := by
    intro u hu
    rw [conjL_conj_path (Fr := Fr), Complex.conj_im]
    have := hup u hu
    linarith
  have hlowre : ∀ u : ℝ, 0 ≤ u →
      (pathPt (starRingEnd ℂ P.tailDir) ((Fr.xstar N0 : ℝ) : ℂ) (conjL (physL Fr P r)) u).re
        ≤ Fr.xstar N0 := by
    intro u hu
    rw [conjL_conj_path (Fr := Fr), Complex.conj_re]
    exact hrel u hu
  -- the atoms are at least `δ0` to the right of `x*`
  have hatom : ∀ p : ↥(Fr.atomIdx N0), Fr.xstar N0 + (Fr.δ0 : ℝ) ≤ -((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)) := by
    intro p
    have hp := p.2
    unfold Frame.atomIdx at hp
    rw [Finset.mem_filter] at hp
    have hle : (p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ) ≤ (N0 : ℝ) + (Fr.xs : ℝ) := not_lt.1 hp.2
    have hgap := hCr.gap.2 p.1.2 ((p.1.1 : ℤ) - N0)
    have h1 : (Fr.δ0 : ℝ) ≤ |(((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)) - ((N0 : ℝ) + (Fr.xs : ℝ)))| := by
      have : (Fr.δ0 : ℝ) ≤ |((((p.1.1 : ℤ) - N0 : ℤ) : ℚ) + Fr.μ p.1.2 - Fr.xs : ℚ)| := by
        exact_mod_cast hgap
      have e : ((((p.1.1 : ℤ) - N0 : ℤ) : ℚ) + Fr.μ p.1.2 - Fr.xs : ℚ) =
          (((p.1.1 : ℚ) + Fr.μ p.1.2) - ((N0 : ℚ) + Fr.xs)) := by push_cast; ring
      rw [e] at this
      exact_mod_cast this
    rw [abs_of_nonpos (by linarith)] at h1
    unfold Frame.xstar
    linarith
  have hδ : (0 : ℝ) < Fr.δ0 := by exact_mod_cast hCr.gap.1
  refine ⟨hρ, ha, ha1, ha0, hg, ?_, hw, sepR, helper_dist, a_rho, rho_gap, a0_mu, a0_one, ?_, ?_, ?_⟩
  · exact_mod_cast hCr.gap.1
  · intro u; exact (hup u.1 u.2).ne'
  · intro u; exact hlowim u.1 u.2
  · intro z z' h1 h2
    rcases z with p | u | u
    · rcases z' with p' | u' | u'
      · exact absurd (by rw [pos0_atom]; simp) h2
      · -- ray above an atom
        have hre' := hrel u'.1 (le_of_lt u'.2)
        have hb := hatom p
        rw [pos0_atom]
        have : (Fr.δ0 : ℝ) ≤ |(polyPt Fr N0 (physL Fr P r) P.tailDir (Sum.inr (Sum.inl u'))).re -
            (-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)))| := by
          simp only [polyPt, Sum.elim_inr, Sum.elim_inl]
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        refine this.trans ?_
        have := Complex.abs_re_le_norm (polyPt Fr N0 (physL Fr P r) P.tailDir (Sum.inr (Sum.inl u')) -
          (((-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ))) : ℝ) : ℂ))
        simpa using this
      · have hre' := hlowre u'.1 (le_of_lt u'.2)
        have hb := hatom p
        rw [pos0_atom]
        have : (Fr.δ0 : ℝ) ≤ |(polyPt Fr N0 (physL Fr P r) P.tailDir (Sum.inr (Sum.inr u'))).re -
            (-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)))| := by
          simp only [polyPt, Sum.elim_inr]
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        refine this.trans ?_
        have := Complex.abs_re_le_norm (polyPt Fr N0 (physL Fr P r) P.tailDir (Sum.inr (Sum.inr u')) -
          (((-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ))) : ℝ) : ℂ))
        simpa using this
    · exact absurd h1 (by simp only [polyPt, Sum.elim_inr, Sum.elim_inl]; exact (hup u.1 u.2).ne')
    · exact absurd h1 (by simp only [polyPt, Sum.elim_inr]; exact hlowim u.1 u.2)

end RefMatch
end CatalanCore.Uniform.Decay.Jet

namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Cert

/-- **S15: decay of the Löwner family of a support datum from a polygon certificate.**

`HasScaledDecay (seqFamily D.f D.e D.xi G) scale D c` for the exponents `D, c` of a certificate `Ct`
(`Support.Certificate`, a `PolyCellRulesB` record with a passing `checkPB`), given a reference frame `Fr` matched
to the datum (`RefMatch`, S04) and the lattice constants of the reference: the atoms of the reference are `g`
apart, the helper shifts within `1/2` of the shifts they stand for, `a + ρ ≤ s_i`, `2ρ ≤ g`, `a0 ≤ μ`, together
with the contour data of the reference and of the datum's jet frame, and a polygon whose vertices lean left
(`hneg`, a finite rational check of the receipt).  Nothing else about the datum or the weights is assumed. -/
theorem support_decay (Dat : Datum) (G : BlockGeom) {Fr : Frame} (R : RefMatch Dat Fr)
    (hC : Fr.ContourOK) (hCd : (datumJet Dat Fr.xs Fr.δ0 Fr.n0off).toFrame.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (Ct : Support.Certificate G.nodePot)
    (hneg : ∀ p ∈ Ct.polygon.verts, p.1 + Ct.polygon.r0 ≤ 0)
    (hMq : Ct.spline.Mq = G.totalMass)
    (hd : Ct.spline.dim = Fr.d) (hInu : (Ct.spline.Inu : ℝ) ≤ G.nodeEnergy)
    (hVc : ∀ s, G.nodePot ((starRingEnd ℂ) s) = G.nodePot s)
    (hUc : ContinuousOn (fun x : ℝ => G.nodePot (x : ℂ)) (Set.Icc (-(Ct.polygon.r0 : ℝ)) 0))
    (hsupp : ∀ r a : ℕ, a ∈ (G.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (Ct.spline.ε : ℝ)) (depth : ℕ)
    {ρ a a0 g : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (ha1 : a ≤ 1) (ha0 : 0 < a0) (hg : 0 < g)
    (hw : ∀ q, Fr.w q ≠ 0)
    (sepR : ∀ (m m' : ℕ) (q q' : Fin Fr.d), (m, q) ≠ (m', q') →
      g ≤ |((m : ℝ) + (Fr.μ q : ℝ)) - ((m' : ℝ) + (Fr.μ q' : ℝ))|)
    (helper_dist : ∀ j : {i : Fin Dat.n // Dat.b i ≠ 0},
      |(Fr.μ (R.role.symm (Sum.inr j)) : ℝ) - (Dat.s j.1 : ℝ)| ≤ 1 / 2)
    (a_rho : ∀ i, a + ρ ≤ (Dat.s i : ℝ)) (rho_gap : 2 * ρ ≤ g)
    (a0_mu : ∀ q, a0 ≤ (Fr.μ q : ℝ)) (a0_one : a0 ≤ 1) :
    HasScaledDecay (seqFamily Dat.f Dat.e Dat.xi G.geometry depth) (SeqFamily.scale G.geometry)
      Ct.Dr Ct.cr := by
  obtain ⟨B, hP, _, C, hCW, hCm, hCg, hCS, hCI, hCc⟩ := SplineData.checkP_sound Ct.checkP
  have hJall := RefMatch.jetFamily R (P := Ct.polygon) hP hC hCd
    (fun r hr => RefMatch.jetSetup_of_polygon R hP hC hneg hr hρ ha ha1 ha0 hg hw sepR helper_dist
      a_rho rho_gap a0_mu a0_one)
  have h := hasScaledDecay_of_check_jet G hC hAR Ct.rules.toRules Ct.spline Ct.polygon Ct.checkP hMq hd
    hInu hVc hUc hsupp hBd0 hBc hBr hBq hm0 hm0μ he0 heε depth Dat.f Dat.e Dat.xi _ _ _ hJall
  rw [Ct.hD, Ct.hc'] at h
  exact h

end CatalanCore.Uniform.Decay.Jet

#print axioms CatalanCore.Uniform.Decay.Jet.support_decay
#print axioms CatalanCore.Uniform.Decay.Jet.RefMatch.jetSetup_of_polygon


/-! # Arbitrary finite pole-order source and decay interface (Q04)
The permanent generic analytic components are imported above. This final
assembly proves the actual reference-space Gram entries and uniform JetRep
family without an additional analytic hypothesis. All scales, natural nodes,
finite jet orders, rational Gram splits and zero-weight padding remain generic.
-/
namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore CatalanCore.Uniform.Support
open CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.PolyChain
open CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.Cert
open Finset MeasureTheory Set Filter Complex
open CatalanLambda.Decay (sumM integrable_sumM_iff integral_sumM)

/-! Uniform comparison with the unchanged reference majorant. -/

theorem poleE_conj (D : PoleDatum) (z : ℂ) :
    poleE D ((starRingEnd ℂ) z) = (starRingEnd ℂ) (poleE D z) := by
  unfold poleE
  rw [map_neg, Complex.conj_tsum]
  congr 1
  apply tsum_congr
  intro n
  simp only [map_sum, map_div₀, map_pow, map_add, map_intCast, map_ratCast]

noncomputable def poleRayK (D : PoleDatum) (Fr : Frame) (q : ℝ) : ℝ :=
  poleK D (kappaP (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off) q)

noncomputable def poleCw {D : PoleDatum} {Fr : Frame}
    (S : PoleGramSplit D) (R : PoleRefMatch D S Fr) (q : ℝ) : ℝ :=
  1 + ∑ i : Fin Fr.d, ‖(S.weight (R.role i) : ℂ)‖ + poleRayK D Fr q / (2 * Real.pi)

theorem poleRayK_nonneg (D : PoleDatum) (Fr : Frame)
    (hC : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK) (q : ℝ) :
    0 ≤ poleRayK D Fr q := poleK_nonneg D (kappaP_pos hC q)

theorem one_le_poleCw {D : PoleDatum} {Fr : Frame} (S : PoleGramSplit D)
    (R : PoleRefMatch D S Fr) (hC : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK) (q : ℝ) :
    1 ≤ poleCw S R q := by
  have h1 : 0 ≤ ∑ i : Fin Fr.d, ‖(S.weight (R.role i) : ℂ)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 := div_nonneg (poleRayK_nonneg D Fr hC q) (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  unfold poleCw
  linarith

theorem norm_poleE_path (D : PoleDatum) (Fr : Frame)
    (hC : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK) (N0 : ℕ)
    {pts : List ℂ} {d : ℂ} (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im)
    {u : ℝ} (hu : 0 < u) :
    ‖poleE D (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)‖ ≤
      poleRayK D Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) *
        Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) := by
  have him := pathPt_im_pos d hd pts ((Fr.xstar N0 : ℝ) : ℂ) (by simp)
    (fun z hz => by linarith [hlow z hz]) u hu
  rw [poleE_eq_closed D him.ne']
  exact norm_poleClosed_le D (kappaP_pos hC _)
    (fun i => path_sin_lower hC N0 hlow hd hu.le i)

noncomputable def poleUpWeight (D : PoleDatum) (Fr : Frame) (N0 : ℕ)
    (pts : List ℂ) (d : ℂ) (u : ℝ) : ℂ :=
  -((2 * Real.pi * I)⁻¹ * poleE D (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u) *
    pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u)

noncomputable def poleLowWeight (D : PoleDatum) (Fr : Frame) (N0 : ℕ)
    (pts : List ℂ) (d : ℂ) (u : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    poleE D (pathPt ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u) *
      pathDer ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u

theorem norm_poleUpWeight_le (D : PoleDatum) (Fr : Frame)
    (hC : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK) (N0 : ℕ)
    {pts : List ℂ} {d : ℂ} (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im)
    {u : ℝ} (hu : 0 < u) :
    ‖poleUpWeight D Fr N0 pts d u‖ ≤
      poleRayK D Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) *
        Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) *
          ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖ := by
  have hE := norm_poleE_path D Fr hC N0 hlow hd hu
  have h2 : ‖(2 * Real.pi * I : ℂ)⁻¹‖ = 1 / (2 * Real.pi) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    simp
  unfold poleUpWeight
  rw [norm_neg, norm_mul, norm_mul, h2]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity))
    (norm_nonneg _)).trans_eq (by ring)

theorem norm_poleLowWeight (D : PoleDatum) (Fr : Frame) (N0 : ℕ)
    (pts : List ℂ) (d : ℂ) (u : ℝ) :
    ‖poleLowWeight D Fr N0 pts d u‖ = ‖poleUpWeight D Fr N0 pts d u‖ := by
  unfold poleLowWeight poleUpWeight
  rw [conjL_conj_path (Fr := Fr), conjL_conj_der (Fr := Fr), poleE_conj]
  simp only [norm_mul, norm_neg, Complex.norm_conj]

theorem poleW_weight {D : PoleDatum} {Fr : Frame} (S : PoleGramSplit D)
    (R : PoleRefMatch D S Fr) (hC : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK)
    {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C : ℝ}
    (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im)
    (hw : ∀ q, Fr.w q ≠ 0) {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (z : Fr.XT N0) :
    ‖poleW S R N0 pts d z‖ ≤ poleCw S R (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) *
      (vP Fr N0 pts d C e z * qP Fr N0 pts d C e z) := by
  have hcw := one_le_poleCw S R hC (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
  have hA := amp_pos C
  have hA1 := one_le_amp C
  have hK := poleRayK_nonneg D Fr hC (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
  have hsum0 : 0 ≤ ∑ i : Fin Fr.d, ‖(S.weight (R.role i) : ℂ)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hK2 : poleRayK D Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) ≤
      poleCw S R (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * amp C := by
    have hh : poleRayK D Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi) ≤
        poleCw S R (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) := by unfold poleCw; linarith
    calc
      _ ≤ poleCw S R (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) := hh
      _ = poleCw S R (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hA1 (by linarith)
  rcases z with p | r | r
  · simp only [poleW, Sum.elim_inl, vP, qP, mul_one]
    have h1 : (1 : ℝ) ≤ |(Fr.w p.1.2 : ℝ)| := by
      have hh : (1 : ℤ) ≤ |Fr.w p.1.2| := Int.one_le_abs (hw p.1.2)
      exact_mod_cast hh
    have h2 : ‖(S.weight (R.role p.1.2) : ℂ)‖ ≤ ∑ i : Fin Fr.d, ‖(S.weight (R.role i) : ℂ)‖ :=
      Finset.single_le_sum (f := fun i : Fin Fr.d => ‖(S.weight (R.role i) : ℂ)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p.1.2)
    have h3 : (∑ i : Fin Fr.d, ‖(S.weight (R.role i) : ℂ)‖) + 1 ≤
        poleCw S R (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) := by
      unfold poleCw
      have hh := div_nonneg hK (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      linarith
    nlinarith [abs_nonneg (Fr.w p.1.2 : ℝ), norm_nonneg (S.weight (R.role p.1.2) : ℂ)]
  · have hb := norm_poleUpWeight_le D Fr hC N0 hlow hd r.2
    change ‖poleUpWeight D Fr N0 pts d r.1‖ ≤ _
    simp only [vP, qP, vPath, gam, gamD, Sum.elim_inr, Sum.elim_inl]
    rw [RefMatch.vq_ray_eq (amp C) _ _ e hA]
    refine hb.trans ?_
    have ht : 0 ≤ Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖ := by positivity
    calc
      _ = (poleRayK D Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi)) *
          (Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
            ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖) := by ring
      _ ≤ (poleCw S R (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * amp C) *
          (Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
            ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖) := mul_le_mul_of_nonneg_right hK2 ht
      _ = _ := by ring
  · have hb := norm_poleUpWeight_le D Fr hC N0 hlow hd r.2
    change ‖poleLowWeight D Fr N0 pts d r.1‖ ≤ _
    rw [norm_poleLowWeight]
    simp only [vP, qP, vPath, gam, gamD, Sum.elim_inr, Sum.elim_inl]
    rw [RefMatch.vq_ray_eq (amp C) _ _ e hA]
    refine hb.trans ?_
    have ht : 0 ≤ Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
        ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖ := by positivity
    calc
      _ = (poleRayK D Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi)) *
          (Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
            ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖) := by ring
      _ ≤ (poleCw S R (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) * amp C) *
          (Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1).im|)) *
            ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1‖) := mul_le_mul_of_nonneg_right hK2 ht
      _ = _ := by ring

/-! The actual polygon-space entry and the conditional-side padded head matching. -/

noncomputable def poleHeadRow {D : PoleDatum} (S : PoleGramSplit D)
    (q : S.Role) (m t : ℕ) : ℂ :=
  ∑ j : Fin (S.J + 1), (S.coeff q j : ℂ) *
    iteratedDeriv j.val (fun z : ℂ => (z - (t : ℂ))⁻¹) (-(m : ℂ) - (D.s q.1 : ℂ))

noncomputable def poleHeadEntry {D : PoleDatum} (S : PoleGramSplit D)
    (q : S.Role) (m a b : ℕ) : ℂ :=
  (S.weight q : ℂ) * poleHeadRow S q m a * poleHeadRow S q m b

theorem poleRows_inl {D : PoleDatum} {Fr : Frame} (S : PoleGramSplit D)
    (R : PoleRefMatch D S Fr) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (t : ℕ)
    (p : ↥(Fr.atomIdx N0)) :
    poleRows S R N0 pts d t (Sum.inl p) = poleHeadRow S (R.role p.1.2) p.1.1 t := by
  simp [poleRows, jetRowFinite, poleHead, poleCenter, poleCoefficients, poleHeadRow]

theorem poleRows_up {D : PoleDatum} {Fr : Frame} (S : PoleGramSplit D)
    (R : PoleRefMatch D S Fr) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (t : ℕ) (r : Decay.RayP) :
    poleRows S R N0 pts d t (Sum.inr (Sum.inl r)) =
      (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1 - (t : ℂ))⁻¹ := by
  simp [poleRows, jetRowFinite, poleHead, polyPt]

theorem poleRows_low {D : PoleDatum} {Fr : Frame} (S : PoleGramSplit D)
    (R : PoleRefMatch D S Fr) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (t : ℕ) (r : Decay.RayP) :
    poleRows S R N0 pts d t (Sum.inr (Sum.inr r)) =
      (pathPt ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r.1 - (t : ℂ))⁻¹ := by
  simp [poleRows, jetRowFinite, poleHead, polyPt]

theorem pole_atom_sum {D : PoleDatum} {Fr : Frame} (S : PoleGramSplit D)
    (R : PoleRefMatch D S Fr) (N0 a b : ℕ) :
    (∑ p ∈ Fr.atomIdx N0, poleHeadEntry S (R.role p.2) p.1 a b) =
      (poleHeadSum D Fr.xs N0 a b : ℂ) := by
  classical
  unfold Frame.atomIdx poleHeadSum
  rw [Finset.sum_filter, Finset.sum_product, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have he : (∑ q : Fin Fr.d,
      if ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ q : ℝ))
        then poleHeadEntry S (R.role q) m a b else 0) =
      ∑ q : S.Role,
        if ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm q) : ℝ))
          then poleHeadEntry S q m a b else 0 := by
    simpa only [Equiv.apply_symm_apply] using
      (Equiv.sum_comp R.role.symm (fun q =>
        if ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ q : ℝ))
          then poleHeadEntry S (R.role q) m a b else 0)).symm
  rw [he, Fintype.sum_sigma]
  unfold poleHeadTerm
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hmask (k : Fin (S.count i)) :
      (if ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ (R.role.symm ⟨i, k⟩) : ℝ))
        then poleHeadEntry S ⟨i, k⟩ m a b else 0) =
      (if (N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (D.s i : ℝ)
        then 0 else poleHeadEntry S ⟨i, k⟩ m a b) := by
    by_cases hweight : S.weight ⟨i, k⟩ = 0
    · simp [poleHeadEntry, hweight]
    · have hs := R.side N0 m (R.role.symm ⟨i, k⟩) (by simpa using hweight)
      simp only [Equiv.apply_symm_apply] at hs
      simp only [hs]
      split_ifs <;> rfl
  simp_rw [hmask]
  by_cases ht : (N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (D.s i : ℝ)
  · simp [ht]
  · simp only [ht, if_false]
    push_cast
    have hsplit := pole_head_split D S i m a b
    push_cast at hsplit
    simpa only [poleHeadEntry, poleHeadRow] using hsplit

theorem pole_up_entry_eq (D : PoleDatum) (Fr : Frame) (N0 a b : ℕ)
    {pts : List ℂ} {d : ℂ} (hP : PolyOK pts d) {u : ℝ} (hu : 0 < u) :
    poleUpWeight D Fr N0 pts d u *
      (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u - (a : ℂ))⁻¹ *
      (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u - (b : ℂ))⁻¹ =
        -(2 * Real.pi * I)⁻¹ *
          (poleSrc D a b (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u) *
            pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u) := by
  have hi := pathPt_im_pos d hP.tail pts ((Fr.xstar N0 : ℝ) : ℂ) (by simp) hP.upper u hu
  unfold poleUpWeight
  rw [poleE_eq_closed D hi.ne']
  unfold poleSrc
  ring

theorem pole_low_entry_eq (D : PoleDatum) (Fr : Frame) (N0 a b : ℕ)
    {pts : List ℂ} {d : ℂ} (hP : PolyOK pts d) {u : ℝ} (hu : 0 < u) :
    poleLowWeight D Fr N0 pts d u *
      (pathPt ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u - (a : ℂ))⁻¹ *
      (pathPt ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u - (b : ℂ))⁻¹ =
        (2 * Real.pi * I)⁻¹ *
          (poleSrc D a b (pathPt ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u) *
            pathDer ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u) := by
  have hi := pathPt_im_pos d hP.tail pts ((Fr.xstar N0 : ℝ) : ℂ) (by simp) hP.upper u hu
  have hl : (pathPt ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u).im ≠ 0 := by
    rw [conjL_conj_path (Fr := Fr), Complex.conj_im]
    linarith
  unfold poleLowWeight
  rw [poleE_eq_closed D hl]
  unfold poleSrc
  ring

theorem pole_integrable_entry {D : PoleDatum} {Fr : Frame} (S : PoleGramSplit D)
    (R : PoleRefMatch D S Fr) (hC : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK)
    (N0 a b : ℕ) {pts : List ℂ} {d : ℂ} (hP : PolyOK pts d) :
    Integrable (fun z => poleW S R N0 pts d z * poleRows S R N0 pts d a z *
      poleRows S R N0 pts d b z) (Fr.muT N0) := by
  unfold Frame.muT
  rw [integrable_sumM_iff, integrable_sumM_iff]
  refine ⟨Integrable.of_finite, ?_, ?_⟩
  · have hu := (poleSrc_path D Fr.xs Fr.δ0 Fr.n0off hC N0 a b
      (by simp : |(1 : ℝ)| = 1) hP.upper' (by simpa using hP.tail)).1
    have hi := hu.const_mul (-(2 * Real.pi * I)⁻¹)
    refine Integrable.congr ((Decay.integrable_comap_Ioi (fun r => poleUpWeight D Fr N0 pts d r *
      (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r - a)⁻¹ *
      (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r - b)⁻¹)).mpr
        (IntegrableOn.congr_fun hi (fun r hr => (pole_up_entry_eq D Fr N0 a b hP hr).symm)
          measurableSet_Ioi)) (Filter.Eventually.of_forall fun z => ?_)
    simp only [poleW, Sum.elim_inr, Sum.elim_inl, poleRows_up, poleUpWeight]
  · have hl := (poleSrc_path D Fr.xs Fr.δ0 Fr.n0off hC N0 a b (pts := conjL pts) (d := (starRingEnd ℂ) d)
      (by simp : |(-1 : ℝ)| = 1) hP.lower (by simpa using hP.tail)).1
    have hi := hl.const_mul ((2 * Real.pi * I)⁻¹)
    refine Integrable.congr ((Decay.integrable_comap_Ioi (fun r => poleLowWeight D Fr N0 pts d r *
      (pathPt ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r - a)⁻¹ *
      (pathPt ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r - b)⁻¹)).mpr
        (IntegrableOn.congr_fun hi (fun r hr => (pole_low_entry_eq D Fr N0 a b hP hr).symm)
          measurableSet_Ioi)) (Filter.Eventually.of_forall fun z => ?_)
    simp only [poleW, Sum.elim_inr, poleRows_low, poleLowWeight]

theorem pole_entry {D : PoleDatum} {Fr : Frame} (S : PoleGramSplit D)
    (R : PoleRefMatch D S Fr) (hC : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK)
    (N0 a b : ℕ) {pts : List ℂ} {d : ℂ} (hP : PolyOK pts d) :
    (∫ z, poleW S R N0 pts d z * poleRows S R N0 pts d a z *
      poleRows S R N0 pts d b z ∂(Fr.muT N0)) =
        (((lw D.f D.e a b : ℝ) + if a = b then D.xi else 0 : ℝ) : ℂ) := by
  have hint := pole_integrable_entry S R hC N0 a b hP
  unfold Frame.muT at hint ⊢
  rw [integral_sumM _ _ _ hint]
  have hint2 := ((integrable_sumM_iff _ _ _).mp hint).2
  rw [integral_sumM _ _ _ hint2, integral_count]
  have hA : (∑ p : ↥(Fr.atomIdx N0),
      poleW S R N0 pts d (Sum.inl p) * poleRows S R N0 pts d a (Sum.inl p) *
        poleRows S R N0 pts d b (Sum.inl p)) = (poleHeadSum D Fr.xs N0 a b : ℂ) := by
    rw [← pole_atom_sum S R N0 a b]
    rw [← Finset.sum_coe_sort (Fr.atomIdx N0) (fun p => poleHeadEntry S (R.role p.2) p.1 a b)]
    apply Finset.sum_congr rfl
    intro p _
    simp only [poleW, Sum.elim_inl, poleRows_inl, poleHeadEntry]
  let γ := pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts
  let γ' := pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts
  let η := pathPt ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts)
  let η' := pathDer ((starRingEnd ℂ) d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts)
  have hU : (∫ z : Decay.RayP,
      poleW S R N0 pts d (Sum.inr (Sum.inl z)) *
        poleRows S R N0 pts d a (Sum.inr (Sum.inl z)) *
        poleRows S R N0 pts d b (Sum.inr (Sum.inl z))
      ∂(Measure.comap Subtype.val (volume : Measure ℝ))) =
        ∫ u in Ioi (0 : ℝ), poleUpWeight D Fr N0 pts d u * (γ u - a)⁻¹ * (γ u - b)⁻¹ := by
    have h := integral_subtype_comap (μ := (volume : Measure ℝ))
      (measurableSet_Ioi (a := (0 : ℝ)))
      (fun u => poleUpWeight D Fr N0 pts d u * (γ u - a)⁻¹ * (γ u - b)⁻¹)
    simpa only [poleW, poleRows_up, Sum.elim_inr, Sum.elim_inl, poleUpWeight] using h
  have hL : (∫ z : Decay.RayP,
      poleW S R N0 pts d (Sum.inr (Sum.inr z)) *
        poleRows S R N0 pts d a (Sum.inr (Sum.inr z)) *
        poleRows S R N0 pts d b (Sum.inr (Sum.inr z))
      ∂(Measure.comap Subtype.val (volume : Measure ℝ))) =
        ∫ u in Ioi (0 : ℝ), poleLowWeight D Fr N0 pts d u * (η u - a)⁻¹ * (η u - b)⁻¹ := by
    have h := integral_subtype_comap (μ := (volume : Measure ℝ))
      (measurableSet_Ioi (a := (0 : ℝ)))
      (fun u => poleLowWeight D Fr N0 pts d u * (η u - a)⁻¹ * (η u - b)⁻¹)
    simpa only [poleW, poleRows_low, Sum.elim_inr, poleLowWeight] using h
  have hx : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).xstar N0 = Fr.xstar N0 := rfl
  have hu := poleSrc_path D Fr.xs Fr.δ0 Fr.n0off hC N0 a b
    (by simp : |(1 : ℝ)| = 1) hP.upper' (by simpa using hP.tail)
  have hl := poleSrc_path D Fr.xs Fr.δ0 Fr.n0off hC N0 a b (pts := conjL pts) (d := (starRingEnd ℂ) d)
    (by simp : |(-1 : ℝ)| = 1) hP.lower (by simpa using hP.tail)
  rw [hx] at hu hl
  have eU : (∫ u in Ioi (0 : ℝ), poleUpWeight D Fr N0 pts d u * (γ u - a)⁻¹ * (γ u - b)⁻¹) =
      -(2 * Real.pi * I)⁻¹ * polyI (poleSrc D a b) ((Fr.xstar N0 : ℝ) : ℂ) pts d := by
    rw [← hu.2, ← integral_const_mul]
    apply integral_congr_ae
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    exact pole_up_entry_eq D Fr N0 a b hP hu
  have eL : (∫ u in Ioi (0 : ℝ), poleLowWeight D Fr N0 pts d u * (η u - a)⁻¹ * (η u - b)⁻¹) =
      (2 * Real.pi * I)⁻¹ * polyI (poleSrc D a b) ((Fr.xstar N0 : ℝ) : ℂ)
        (conjL pts) ((starRingEnd ℂ) d) := by
    rw [← hl.2, ← integral_const_mul]
    apply integral_congr_ae
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    exact pole_low_entry_eq D Fr N0 a b hP hu
  rw [hA, hU, hL, eU, eL]
  have hG := pole_gram_formula D Fr.xs Fr.δ0 Fr.n0off N0 a b hC hP.upper hP.tail
  rw [hx] at hG
  calc
    _ = (poleHeadSum D Fr.xs N0 a b : ℂ) + (2 * Real.pi * I)⁻¹ *
        (polyI (poleSrc D a b) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) ((starRingEnd ℂ) d) -
          polyI (poleSrc D a b) ((Fr.xstar N0 : ℝ) : ℂ) pts d) := by ring
    _ = _ := hG.symm

/-! Analytic obligations are separated from the unchanged JetRep/decay engine.
The public pole_jetFamily is only closed after the unconditional constructor of
this internal analytic record has been proved; the record is not an added public hypothesis.
-/
structure PoleAnalyticData (D : PoleDatum) (S : PoleGramSplit D) (Fr : Frame)
    (R : PoleRefMatch D S Fr) (P : RatPolygon) where
  cw : ℝ
  hcw : 1 ≤ cw
  weight : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) → (∀ q, Fr.w q ≠ 0) →
    ∀ e : ℝ, 0 < e → e < 1 → ∀ z,
      ‖poleW S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir z‖ ≤
        cw * (vP Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (CP Fr (P.qRat : ℝ)) e z *
          qP Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (CP Fr (P.qRat : ℝ)) e z)
  integrable_entry : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) → ∀ a b : ℕ,
    Integrable (fun z => poleW S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir z *
      poleRows S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir a z *
      poleRows S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir b z) (Fr.muT (N0Of Fr P.r0 r))
  gram_entry : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) → ∀ a b : ℕ,
    (∫ z, poleW S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir z *
      poleRows S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir a z *
      poleRows S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir b z ∂(Fr.muT (N0Of Fr P.r0 r))) =
        (((lw D.f D.e a b : ℝ) + if a = b then D.xi else 0 : ℝ) : ℂ)

theorem pole_andreief_of_analytic {D : PoleDatum} {S : PoleGramSplit D} {Fr : Frame}
    {R : PoleRefMatch D S Fr} {P : RatPolygon} (B : PoleAnalyticData D S Fr R P)
    (r : ℕ) (hr : Rmin Fr P ≤ (r : ℝ)) (k : ℕ) (s t : Fin k → ℕ) :
    ‖(Matrix.of fun i j : Fin k =>
      (((lw D.f D.e (s i) (t j) : ℝ) + if s i = t j then D.xi else 0 : ℝ) : ℂ)).det‖ ≤
      (1 / (k.factorial : ℝ)) * ∫ z : Fin k → Fr.XT (N0Of Fr P.r0 r),
        (∏ l, ‖poleW S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (z l)‖) *
          (‖(Matrix.of fun i l : Fin k => poleRows S R (N0Of Fr P.r0 r)
            (physL Fr P r) P.tailDir (s i) (z l)).det‖ *
           ‖(Matrix.of fun j l : Fin k => poleRows S R (N0Of Fr P.r0 r)
            (physL Fr P r) P.tailDir (t j) (z l)).det‖)
          ∂(Measure.pi fun _ => Fr.muT (N0Of Fr P.r0 r)) := by
  have hb := CatalanLambda.Decay.norm_det_le_andreief (Fr.muT (N0Of Fr P.r0 r))
    (poleW S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir)
    (fun (i : Fin k) z => poleRows S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (s i) z)
    (fun (j : Fin k) z => poleRows S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (t j) z)
    (fun i j => B.integrable_entry r hr (s i) (t j))
  have hM : (Matrix.of fun i j : Fin k => ∫ z,
      poleW S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir z *
        poleRows S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (s i) z *
        poleRows S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (t j) z
        ∂(Fr.muT (N0Of Fr P.r0 r))) =
      Matrix.of fun i j : Fin k =>
        (((lw D.f D.e (s i) (t j) : ℝ) + if s i = t j then D.xi else 0 : ℝ) : ℂ) := by
    apply Matrix.ext
    intro i j
    exact B.gram_entry r hr (s i) (t j)
  rw [hM] at hb
  refine hb.trans (le_of_eq ?_)
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

theorem pole_jetFamily_of_analytic (D : PoleDatum) (S : PoleGramSplit D)
    (Fr : Frame) (R : PoleRefMatch D S Fr) {P : RatPolygon}
    (B : PoleAnalyticData D S Fr R P)
    (H C0 g d0 a : ℝ) (hH : 0 ≤ H) (hC0 : 0 ≤ C0)
    (hg : 0 < g) (hd0 : 0 < d0) (ha : 0 < a)
    (hsetup : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) →
      PoleJetSetup D S Fr R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir H C0 g d0 a) :
    ∃ cw c1 c2 : ℝ, 1 ≤ cw ∧ 0 ≤ c1 ∧ 0 ≤ c2 ∧
      ∃ J : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) →
        JetRep Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (CP Fr (P.qRat : ℝ)),
        (∀ r hr x y, (J r hr).Φ x y = (lw D.f D.e x y : ℝ) + if x = y then D.xi else 0) ∧
        (∀ r hr, (J r hr).cw = cw) ∧
        (∀ r hr, (J r hr).c1 = c1) ∧ (∀ r hr, (J r hr).c2 = c2) := by
  obtain ⟨c1, c2, hc1, hc2, hj⟩ := finite_jet_cauchy_bound S.J H C0 g d0 a hH hC0 hg hd0 ha
  refine ⟨B.cw, c1, c2, B.hcw, hc1, hc2, ?_⟩
  let J : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) →
      JetRep Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir (CP Fr (P.qRat : ℝ)) := fun r hr =>
    { W := poleW S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir
      rows := poleRows S R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir
      Φ := fun x y => (lw D.f D.e x y : ℝ) + if x = y then D.xi else 0
      cw := B.cw
      hcw := B.hcw
      c1 := c1
      c2 := c2
      hc1 := hc1
      hc2 := hc2
      weight := B.weight r hr (hsetup r hr).weight_ne
      andreief := fun k s t _ _ => pole_andreief_of_analytic B r hr k s t
      jet := by
        let hs := (hsetup r hr).jet_hypotheses
        exact hj (poleHead Fr (N0Of Fr P.r0 r))
          (poleCenter R (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir)
          (polyPt Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir)
          (poleCoefficients S R (N0Of Fr P.r0 r)) hs.center_real_neg hs.reference_real
          hs.displacement hs.coeff_bound hs.contour_center hs.head_sep hs.contour_gap
          hs.reference_node_ne hs.collision }
  exact ⟨J, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-! Unconditional constructor: all analytic fields are proved above, not hypotheses. -/

theorem pole_physical_setup (Fr : Frame) (P : RatPolygon) (hP : P.OK)
    (r : ℕ) (hr : Rmin Fr P ≤ (r : ℝ)) :
    (∀ z ∈ physL Fr P r, 1 / 8 ≤ z.im) ∧ PolyOK (physL Fr P r) P.tailDir ∧
      qFirst ((Fr.xstar (N0Of Fr P.r0 r) : ℝ) : ℂ) (physL Fr P r) P.tailDir = (P.qRat : ℝ) := by
  have hr1 : (1 : ℝ) ≤ r := (le_max_left _ _).trans hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hinv : (P.invIm : ℝ) ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hr
  have hhigh := high_of_ge hP hinv
  have hone := RatPolygon.physPts_high (Fr.xstar (N0Of Fr P.r0 r)) r hhigh
  rw [physPts_eq_scaled] at hone
  have hlow : ∀ z ∈ physL Fr P r, 1 / 8 ≤ z.im := fun z hz => by linarith [hone z hz]
  have hPoly : PolyOK (physL Fr P r) P.tailDir := by
    have hh := RatPolygon.polyOK hP (Fr.xstar (N0Of Fr P.r0 r)) hrpos
    rw [physPts_eq_scaled] at hh
    exact hh
  have hq : qFirst ((Fr.xstar (N0Of Fr P.r0 r) : ℝ) : ℂ) (physL Fr P r) P.tailDir = (P.qRat : ℝ) := by
    have hh := RatPolygon.qFirst_phys hP (Fr.xstar (N0Of Fr P.r0 r)) hrpos
    rw [physPts_eq_scaled] at hh
    exact hh
  exact ⟨hlow, hPoly, hq⟩

noncomputable def poleAnalyticData (D : PoleDatum) (S : PoleGramSplit D)
    (Fr : Frame) (R : PoleRefMatch D S Fr) (P : RatPolygon)
    (hP : P.OK) (hCr : Fr.ContourOK)
    (hCd : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK) :
    PoleAnalyticData D S Fr R P where
  cw := poleCw S R (P.qRat : ℝ)
  hcw := one_le_poleCw S R hCd _
  weight := by
    intro r hr hw e he0 he1 z
    obtain ⟨hlow, hPoly, hq⟩ := pole_physical_setup Fr P hP r hr
    have hh := poleW_weight (C := CP Fr (P.qRat : ℝ)) S R hCd hlow (RatPolygon.tailDir_im_pos hP) hw he0 he1 z
    rw [hq] at hh
    exact hh
  integrable_entry := by
    intro r hr a b
    obtain ⟨hlow, hPoly, hq⟩ := pole_physical_setup Fr P hP r hr
    exact pole_integrable_entry S R hCd _ a b hPoly
  gram_entry := by
    intro r hr a b
    obtain ⟨hlow, hPoly, hq⟩ := pole_physical_setup Fr P hP r hr
    exact pole_entry S R hCd _ a b hPoly

/-! The exact frozen public family theorem, from the unconditional analytic constructor. -/
theorem pole_jetFamily (D : PoleDatum) (S : PoleGramSplit D)
    (Fr : Frame) (R : PoleRefMatch D S Fr)
    {P : RatPolygon} (hP : P.OK) (hCr : Fr.ContourOK)
    (hCd : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK)
    (H C0 g d0 a : ℝ) (hH : 0 ≤ H) (hC0 : 0 ≤ C0)
    (hg : 0 < g) (hd0 : 0 < d0) (ha : 0 < a)
    (hsetup : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) →
      PoleJetSetup D S Fr R (N0Of Fr P.r0 r)
        (physL Fr P r) P.tailDir H C0 g d0 a) :
    ∃ cw c1 c2 : ℝ, 1 ≤ cw ∧ 0 ≤ c1 ∧ 0 ≤ c2 ∧
      ∃ J : ∀ r : ℕ, Rmin Fr P ≤ (r : ℝ) →
        JetRep Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir
          (CP Fr (P.qRat : ℝ)),
        (∀ r hr x y, (J r hr).Φ x y =
          (lw D.f D.e x y : ℝ) + (if x=y then D.xi else 0)) ∧
        (∀ r hr, (J r hr).cw = cw) ∧
        (∀ r hr, (J r hr).c1 = c1) ∧
        (∀ r hr, (J r hr).c2 = c2) := by
  exact pole_jetFamily_of_analytic D S Fr R (poleAnalyticData D S Fr R P hP hCr hCd)
    H C0 g d0 a hH hC0 hg hd0 ha hsetup

/-! Exact frozen Q04 final decay adapter; unconditional pole_jetFamily remains a prior obligation. -/
theorem pole_support_decay
    (D : PoleDatum) (S : PoleGramSplit D)
    (G : BlockGeom) {Fr : Frame} (R : PoleRefMatch D S Fr)
    (hC : Fr.ContourOK)
    (hCd : (D.clearanceFrame Fr.xs Fr.δ0 Fr.n0off).ContourOK)
    (hAR : ∀ i : Fin Fr.d,
      ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (Ct : Support.Certificate G.nodePot)
    (hneg : ∀ p ∈ Ct.polygon.verts, p.1 + Ct.polygon.r0 ≤ 0)
    (hMq : Ct.spline.Mq = G.totalMass)
    (hd : Ct.spline.dim = Fr.d)
    (hInu : (Ct.spline.Inu : ℝ) ≤ G.nodeEnergy)
    (hVc : ∀ z, G.nodePot ((starRingEnd ℂ) z) = G.nodePot z)
    (hUc : ContinuousOn (fun x : ℝ => G.nodePot (x : ℂ))
      (Set.Icc (-(Ct.polygon.r0 : ℝ)) 0))
    (hsupp : ∀ r n : ℕ, n ∈ (G.geometry r).C → (n : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd)
    (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd)
    (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (Ct.spline.ε : ℝ))
    (depth : ℕ)
    (H C0 g d0 a : ℝ)
    (hH : 0 ≤ H) (hC0 : 0 ≤ C0)
    (hg : 0 < g) (hd0 : 0 < d0) (ha : 0 < a)
    (hsetup : ∀ r : ℕ, Rmin Fr Ct.polygon ≤ (r : ℝ) →
      PoleJetSetup D S Fr R
        (N0Of Fr Ct.polygon.r0 r)
        (physL Fr Ct.polygon r) Ct.polygon.tailDir H C0 g d0 a) :
    HasScaledDecay (seqFamily D.f D.e D.xi G.geometry depth)
      (SeqFamily.scale G.geometry) Ct.Dr Ct.cr := by
  obtain ⟨B, hP, _, C, hCW, hCm, hCg, hCS, hCI, hCc⟩ := SplineData.checkP_sound Ct.checkP
  obtain ⟨cw, c1, c2, hcw, hc1, hc2, hJall⟩ :=
    pole_jetFamily D S Fr R hP hC hCd H C0 g d0 a hH hC0 hg hd0 ha hsetup
  have h := hasScaledDecay_of_check_jet G hC hAR Ct.rules.toRules Ct.spline Ct.polygon Ct.checkP
    hMq hd hInu hVc hUc hsupp hBd0 hBc hBr hBq hm0 hm0μ he0 heε depth
    D.f D.e D.xi cw c1 c2 hJall
  rw [Ct.hD, Ct.hc'] at h
  exact h


#print axioms poleW_weight
#print axioms pole_atom_sum
#print axioms pole_integrable_entry
#print axioms pole_entry
#print axioms pole_andreief_of_analytic
#print axioms poleAnalyticData
#print axioms pole_jetFamily
#print axioms pole_support_decay
end CatalanCore.Uniform.Decay.Jet
