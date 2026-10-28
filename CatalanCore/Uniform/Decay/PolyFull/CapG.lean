import CatalanCore.Uniform.Decay.PolyFull.CapNodes
set_option Elab.async false

/-!
# The lower bound `G ≤ ∫_{-r0}^0 g` of the cap oracle (lane D, package D10)

`g(x) = M U0(x) - Vnu(x)` on the cap (the term `(1-ε)π|Im|` vanishes).  With the cap segment
`capSegOf r0`:
* `∫_{-r0}^0 U0 = r0 Σ_j ∫₀¹ segU_j(cap(s)) ds`, and each term is bounded below through the pair
  energy of the cap with the segment of negated density (`cap_pair_ge`);
* `∫_{-r0}^0 Vnu = ½ r0 Σ_P ∫₀¹ pot_P(cap(s)) ds` over the row and column pieces, each term bounded
  above through the collinear pair energy of the cap with the piece segment (`cap_piece_le`).
`capGokOf` is the Boolean test; `capGokOf_sound` is the field `G_sound` of `CapOracle`.
-/

namespace CatalanCore.Uniform.Decay.PolyFull

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.PairEnergy CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform

theorem int_cap (r0 : ℚ) (hr : 0 < r0) (F : ℝ → ℝ) :
    ∫ x in (-(r0 : ℝ))..0, F x = (r0 : ℝ) * ∫ s in (0 : ℝ)..1, F (capX r0 s) := by
  have hr' : (r0 : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1) F hr' (-(r0 : ℝ))
  have e1 : (r0 : ℝ) * 0 + -(r0 : ℝ) = -(r0 : ℝ) := by ring
  have e2 : (r0 : ℝ) * 1 + -(r0 : ℝ) = 0 := by ring
  rw [e1, e2] at h
  unfold capX
  rw [h, smul_eq_mul]
  field_simp

theorem int_list_sum {α : Type} (l : List α) (F : α → ℝ → ℝ) (hF : ∀ a, Continuous (F a))
    (a b : ℝ) :
    ∫ x in a..b, (l.map fun p => F p x).sum = (l.map fun p => ∫ x in a..b, F p x).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [intervalIntegral.integral_add ((hF p).intervalIntegrable _ _), ih]
    exact (continuous_list_sum l (fun q _ => hF q)).intervalIntegrable _ _

/-- Boolean test for the lower bound of `∫ g` on the cap. -/
def capGokOf (RP CP : List (ℚ × ℚ × ℚ)) (D : SplineData) (G : ℚ) : Bool :=
  match listUb (fun j : Fin D.n => pairBound (capSegOf D.r0) (negSeg (D.seg j))) (List.finRange D.n),
      listUb (fun p => pairBound (capSegOf D.r0) (pieceSeg p)) (RP ++ CP) with
  | some a, some b => decide (G ≤ D.Mq * D.r0 * (-a) - D.r0 * b / 2)
  | _, _ => false

theorem capGokOf_sound (G₀ : BlockGeom) (RP CP : List (ℚ × ℚ × ℚ))
    (hrow : G₀.rowPieces = RP.map ratPiece) (hcol : G₀.colPieces = CP.map ratPiece)
    (D : SplineData) (hb : D.basicOk = true) (G : ℚ) (h : capGokOf RP CP D G = true) :
    (G : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0,
      gNu D.Mq G₀.nodePot (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  have B := SplineData.basicOk_sound hb
  have hr : 0 < D.r0 := B.r0_pos
  have hMq : (0 : ℝ) < D.Mq := by exact_mod_cast B.hM
  unfold capGokOf at h
  split at h
  swap; · simp at h
  rename_i a b ha hbb
  simp only [decide_eq_true_eq] at h
  -- continuity facts
  have hcz : Continuous (fun x : ℝ => (⟨x, 0⟩ : ℂ)) := Complex.continuous_ofReal
  have hUc : Continuous (fun x : ℝ => U0 D.A D.B D.f (⟨x, 0⟩ : ℂ)) := (U0_continuous B).comp hcz
  have hVc : Continuous (fun x : ℝ => G₀.nodePot (⟨x, 0⟩ : ℂ)) := nodePot_real_continuous G₀
  -- U0 part
  have hsegc : ∀ j : Fin D.n, Continuous (fun x : ℝ => segU D j (⟨x, 0⟩ : ℂ)) :=
    fun j => (segU_continuous B j).comp hcz
  have hU : ∫ x in (-(D.r0 : ℝ))..0, U0 D.A D.B D.f (⟨x, 0⟩ : ℂ) ≥ (D.r0 : ℝ) * (-(a : ℝ)) := by
    have e : ∀ x : ℝ, U0 D.A D.B D.f (⟨x, 0⟩ : ℂ) = ∑ j, segU D j (⟨x, 0⟩ : ℂ) :=
      fun x => U0_eq_sum _
    simp_rw [e]
    rw [intervalIntegral.integral_finset_sum (fun j _ => (hsegc j).intervalIntegrable _ _)]
    have e2 : ∀ j : Fin D.n, ∫ x in (-(D.r0 : ℝ))..0, segU D j (⟨x, 0⟩ : ℂ) =
        (D.r0 : ℝ) * ∫ s in (0 : ℝ)..1, Wseg (D.seg j) ((capX D.r0 s : ℝ) : ℂ) := by
      intro j
      rw [int_cap D.r0 hr (fun x => segU D j (⟨x, 0⟩ : ℂ))]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      exact segU_eq_Wseg D j _
    simp_rw [e2]
    rw [← Finset.mul_sum]
    have hsum := listUb_sound (f := fun j : Fin D.n => pairBound (capSegOf D.r0) (negSeg (D.seg j)))
      (F := fun j => -∫ s in (0 : ℝ)..1, Wseg (D.seg j) ((capX D.r0 s : ℝ) : ℂ))
      (fun j u hj => by
        have := cap_pair_ge hj
        linarith) (List.finRange D.n) ha
    rw [← Fin.sum_univ_def] at hsum
    rw [Finset.sum_neg_distrib] at hsum
    have hr' : (0 : ℝ) < D.r0 := by exact_mod_cast hr
    nlinarith
  -- Vnu part
  have hV : ∫ x in (-(D.r0 : ℝ))..0, G₀.nodePot (⟨x, 0⟩ : ℂ) ≤ (D.r0 : ℝ) * (b : ℝ) / 2 := by
    have e : ∀ x : ℝ, G₀.nodePot (⟨x, 0⟩ : ℂ) =
        (1 / 2 : ℝ) * (((RP ++ CP).map fun p => (ratPiece p).pot x).sum) := by
      intro x
      unfold BlockGeom.nodePot
      rw [ppotC_real, ppotC_real, hrow, hcol]
      simp only [ppot, List.map_append, List.sum_append, List.map_map, Function.comp_def]
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul,
      int_list_sum (RP ++ CP) (fun p x => (ratPiece p).pot x) (fun p => pot_continuous _)]
    have e3 : ∀ p : ℚ × ℚ × ℚ, ∫ x in (-(D.r0 : ℝ))..0, (ratPiece p).pot x =
        (D.r0 : ℝ) * ∫ s in (0 : ℝ)..1, (ratPiece p).pot (capX D.r0 s) :=
      fun p => int_cap D.r0 hr (fun x => (ratPiece p).pot x)
    simp_rw [e3]
    have hsum := listUb_sound (f := fun p => pairBound (capSegOf D.r0) (pieceSeg p))
      (F := fun p => ∫ s in (0 : ℝ)..1, (ratPiece p).pot (capX D.r0 s))
      (fun p u hp => cap_piece_le hp) (RP ++ CP) hbb
    have hmul : ((RP ++ CP).map fun p => (D.r0 : ℝ) * ∫ s in (0 : ℝ)..1, (ratPiece p).pot (capX D.r0 s)).sum
        = (D.r0 : ℝ) * ((RP ++ CP).map fun p => ∫ s in (0 : ℝ)..1, (ratPiece p).pot (capX D.r0 s)).sum := by
      rw [List.sum_map_mul_left]
    rw [hmul]
    have hr' : (0 : ℝ) < D.r0 := by exact_mod_cast hr
    nlinarith
  -- assemble
  have hg : ∀ x : ℝ, gNu D.Mq G₀.nodePot (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ =
      (D.Mq : ℝ) * U0 D.A D.B D.f (⟨x, 0⟩ : ℂ) - G₀.nodePot (⟨x, 0⟩ : ℂ) := by
    intro x; simp [gNu]
  simp_rw [hg]
  have i1 : IntervalIntegrable (fun x : ℝ => (D.Mq : ℝ) * U0 D.A D.B D.f (⟨x, 0⟩ : ℂ)) volume
      (-(D.r0 : ℝ)) 0 := (continuous_const.mul hUc).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i1 (hVc.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  have hG : (G : ℝ) ≤ (D.Mq : ℝ) * (D.r0 : ℝ) * (-(a : ℝ)) - (D.r0 : ℝ) * (b : ℝ) / 2 := by
    exact_mod_cast h
  nlinarith

end CatalanCore.Uniform.Decay.PolyFull
