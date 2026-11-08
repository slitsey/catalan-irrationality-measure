module

public import CatalanCore.Uniform.Bank.Plane2.Bound
public import CatalanCore.Uniform.Decay.Jet.RelaxedMatch

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# The plane 2 theorem on the whole projective line (lane H, wave P209; ledger P209, S15 instance)

`Bound.plane2_point_of_content` is the plane 2 theorem for `a b ≠ 0`.  The two points `a = 0` (`π²`) and `b = 0`
(`ζ(3)`) are data with fewer roles than the three atoms of the `d = 3` reference frame `p2ref` of the cover:
`π²` is the simple-pole datum `S = {1, 1/2}` (two roles), `ζ(3)` the one-term double-pole datum (two roles).  They
are matched by adding a ghost shift of weight zero (`DatumX`, `Jet.RelaxedMatch`): `piX` (ghost `3/4`) and
`plane2X 1 0` (ghost `1/2`).  The Löwner sequences, and hence the families, do not see the ghost (`piX_f`, …).

`plane2_point_ab_of_content` is the theorem for every rational `(a, b) ≠ (0, 0)` with the three contents (`Plane2Content`,
`Plane2ContentZeta`, `Plane2ContentPi`, all at the same `Λ ≤ 869210883039/250000000000`) as the only open input.
-/

namespace CatalanCore.Uniform.Bank.Plane2
open CatalanCore.Measure
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Polygon
  CatalanCore.Uniform.Decay.Jet.Relaxed

/-! ### The padded data -/

/-- The plane 2 datum with possibly vanishing weights (`v = 0` or `u = 0` allowed). -/
@[reducible] def plane2X (v u : ℤ) : DatumX where
  n := 2
  hn := by norm_num
  s := ![1, 1 / 2]
  a := ![u, -u]
  b := ![v, 0]
  hs := by intro i; fin_cases i <;> norm_num
  hinj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  hbal := by simp

/-- `π²`: the shifts `1, 1/2` with weights `1, -1` and the ghost shift `3/4`. -/
@[reducible] def piX : DatumX where
  n := 3
  hn := by norm_num
  s := ![1, 1 / 2, 3 / 4]
  a := ![1, -1, 0]
  b := fun _ => 0
  hs := by intro i; fin_cases i <;> norm_num
  hinj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all <;> norm_num at h
  hbal := by simp [Fin.sum_univ_three]

/-- The simple-pole datum of `π²`: `S = {1, 1/2}`, `a = (1, -1)`. -/
@[reducible] def piDatum : Datum where
  n := 2
  hn := by norm_num
  s := ![1, 1 / 2]
  a := ![1, -1]
  b := ![0, 0]
  hs := by intro i; fin_cases i <;> norm_num
  hinj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  hab := by intro i; fin_cases i <;> simp
  hbal := by simp

theorem piX_f : piX.f = piDatum.f := by
  funext t
  unfold DatumX.f Datum.f
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold DatumX.delta Datum.delta
  simp [Fin.sum_univ_three, Fin.sum_univ_two]

theorem piX_e : piX.e = piDatum.e := by
  funext t
  unfold DatumX.e Datum.e
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold DatumX.delta1 Datum.delta1
  simp [Fin.sum_univ_three, Fin.sum_univ_two]

theorem piX_xi : piX.xi = piDatum.xi := by
  unfold DatumX.xi Datum.xi
  simp [Fin.sum_univ_three, Fin.sum_univ_two]

theorem piDatum_xi : piDatum.xi = -(Real.pi ^ 2) / 3 := by
  unfold Datum.xi
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_one, Int.cast_neg,
    Int.cast_zero, mul_zero, zero_mul, sub_zero]
  have e2 : CatalanCore.hurwitzTail2 ((1 : ℚ) / 2) = Real.pi ^ 2 / 2 := by
    exact_mod_cast Bank.Plane1.hurwitz_half_pi
  have e1 : CatalanCore.hurwitzTail2 1 = Real.pi ^ 2 / 6 := Bank.Plane1.hurwitz_one_pi
  simp only [Rat.cast_one, e1, e2]
  push_cast
  ring

theorem zetaX_f : (plane2X 1 0).f = zeta3Datum.f := by
  funext t
  unfold DatumX.f Datum.f
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold DatumX.delta Datum.delta
  simp [Fin.sum_univ_two, zeta3Datum]

theorem zetaX_e : (plane2X 1 0).e = zeta3Datum.e := by
  funext t
  unfold DatumX.e Datum.e
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold DatumX.delta1 Datum.delta1
  simp [Fin.sum_univ_two, zeta3Datum]

theorem zetaX_xi : (plane2X 1 0).xi = zeta3Datum.xi := by
  unfold DatumX.xi Datum.xi
  simp [Fin.sum_univ_two, zeta3Datum]

/-! ### The matches -/

theorem p2X_b0 (v u : ℤ) (hv : v ≠ 0) : (plane2X v u).b 0 ≠ 0 := by
  simpa [plane2X] using hv

/-- Roles for `plane2X v u`, `v ≠ 0`: atom `1/2` is the shift `1/2` (a ghost if `u = 0`), `1` the double shift, `3/4` its
helper. -/
def p2RoleX (v u : ℤ) (hv : v ≠ 0) :
    Fin p2ref.d ≃ Fin (plane2X v u).n ⊕ {i : Fin (plane2X v u).n // (plane2X v u).b i ≠ 0} where
  toFun := fun q => if q.val = 0 then Sum.inl 1 else if q.val = 1 then Sum.inr ⟨0, p2X_b0 v u hv⟩ else Sum.inl 0
  invFun := fun x => match x with
    | Sum.inl i => if i.val = 0 then 2 else 0
    | Sum.inr _ => 1
  left_inv := by
    intro q; fin_cases q <;> simp
  right_inv := by
    intro x
    rcases x with i | ⟨j, hj⟩
    · fin_cases i <;> simp
    · fin_cases j
      · simp
      · exact absurd (by simp [plane2X]) hj

/-- **The match of `p2ref` with `plane2X v u`, `v ≠ 0`** (`u = 0`: the ghost shift `1/2`). -/
noncomputable def p2RefX (v u : ℤ) (hv : v ≠ 0) : RefMatch (plane2X v u) p2ref where
  role := p2RoleX v u hv
  idx_mu := by
    intro i
    fin_cases i <;> rfl
  side := by
    intro N0 m j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · have h1 : (p2ref.μ ((p2RoleX v u hv).symm (Sum.inr ⟨0, hj⟩)) : ℝ) = 3 / 4 := by
        show ((p2ref.μ 1 : ℚ) : ℝ) = 3 / 4
        simp [p2ref]
      have h2 : ((plane2X v u).s 0 : ℝ) = 1 := by simp [plane2X]
      have hxs : (p2ref.xs : ℝ) = 1 / 4 := by simp [p2ref]
      show ((N0 : ℝ) + (p2ref.xs : ℝ) < (m : ℝ) + (p2ref.μ ((p2RoleX v u hv).symm (Sum.inr ⟨0, hj⟩)) : ℝ)) ↔
        ((N0 : ℝ) + (p2ref.xs : ℝ) < (m : ℝ) + (((plane2X v u).s 0 : ℚ) : ℝ))
      rw [h1, h2, hxs]
      exact p2_half_iff N0 m
    · exact absurd (by simp [plane2X]) hj

/-- Roles for `piX`: three simple shifts, one atom each. -/
def piRole : Fin p2ref.d ≃ Fin piX.n ⊕ {i : Fin piX.n // piX.b i ≠ 0} where
  toFun := fun q => Sum.inl (![1, 2, 0] q)
  invFun := fun x => match x with
    | Sum.inl i => ![2, 0, 1] i
    | Sum.inr j => absurd rfl j.2
  left_inv := by
    intro q; fin_cases q <;> rfl
  right_inv := by
    intro x
    rcases x with i | ⟨j, hj⟩
    · fin_cases i <;> rfl
    · exact absurd rfl hj

/-- **The match of `p2ref` with `piX`.** -/
noncomputable def piRef : RefMatch piX p2ref where
  role := piRole
  idx_mu := by
    intro i
    fin_cases i <;> rfl
  side := by
    intro N0 m j
    exact absurd rfl j.2

/-! ### Decay of the families of the padded data -/

theorem p2X_contour (v u : ℤ) :
    (datumJet (plane2X v u) p2ref.xs p2ref.δ0 p2ref.n0off).toFrame.ContourOK := by
  apply Frame.contourOK_of_check
  have h : Frame.contourCheck (datumJet (plane2X v u) p2ref.xs p2ref.δ0 p2ref.n0off).toFrame =
      Frame.contourCheck (datumJet (plane2X 1 1) p2ref.xs p2ref.δ0 p2ref.n0off).toFrame := rfl
  rw [h]
  decide +kernel

theorem piX_contour :
    (datumJet piX p2ref.xs p2ref.δ0 p2ref.n0off).toFrame.ContourOK := by
  apply Frame.contourOK_of_check
  decide +kernel

/-- **S15 at the plane 2 cover for a padded datum**: the generic wrapper of `Relaxed.support_decay` with the constants of
the cover. -/
theorem decayX (D : DatumX) (R : RefMatch D p2ref)
    (hCd : (datumJet D p2ref.xs p2ref.δ0 p2ref.n0off).toFrame.ContourOK)
    (hhelp : ∀ j : {i : Fin D.n // D.b i ≠ 0},
      |(p2ref.μ (R.role.symm (Sum.inr j)) : ℝ) - (D.s j.1 : ℝ)| ≤ 1 / 2)
    (harho : ∀ i, (3 / 8 : ℝ) + 1 / 8 ≤ (D.s i : ℝ)) (depth : ℕ) :
    HasScaledDecay (P2G.seqFamily D.f D.e D.xi depth) (SeqFamily.scale P2G.geometry) p2Cert.Dr p2Cert.cr := by
  obtain ⟨hbc, hbr, hbq⟩ := altGeom_blocks_v (6 / 41) p2c_pos (by norm_num)
  have hεpos : (0 : ℝ) < (Cover.Dchi.ε : ℝ) := by exact_mod_cast p2_eps
  refine support_decay D P2G (Fr := p2ref) R
    (Frame.contourOK_of_check p2ref_contour) hCd p2ref_hAR p2Cert
    (by show ∀ p ∈ Cover.Pply.verts, p.1 + Cover.Pply.r0 ≤ 0; decide +kernel) ?_ ?_ ?_
    (nodePot_conj P2G) ((nodePot_real_continuous P2G).continuousOn) (altGeom_supp (6 / 41) p2c_pos)
    (Bd := 2) (by norm_num) hbc hbr hbq
    (m0 := 1 / 2) (by norm_num) p2ref_mu_ge (e := (Cover.Dchi.ε : ℝ) / 2) (by linarith) ?_ depth
    (ρ := 1 / 8) (a := 3 / 8) (a0 := 1 / 2) (g := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) p2ref_w_ne ?_ hhelp harho (by norm_num) ?_ (by norm_num)
  · show Cover.Dchi.Mq = P2G.totalMass
    rw [p2_totalMass]; decide +kernel
  · show Cover.Dchi.dim = p2ref.d
    exact p2_dim
  · exact inu_le_nodeEnergy_of_check (altGeom_rowPieces (6 / 41) p2c_pos)
      (altGeom_colPieces (6 / 41) p2c_pos) p2_energy
  · show (Cover.Dchi.ε : ℝ) / 2 < (Cover.Dchi.ε : ℝ)
    linarith
  · intro m m' q q' hne
    exact p2ref_sep m m' q q' hne
  · intro q
    exact p2ref_mu_ge q

theorem plane2X_hhelp (v u : ℤ) (hv : v ≠ 0) :
    ∀ j : {i : Fin (plane2X v u).n // (plane2X v u).b i ≠ 0},
      |(p2ref.μ ((p2RefX v u hv).role.symm (Sum.inr j)) : ℝ) - ((plane2X v u).s j.1 : ℝ)| ≤ 1 / 2 := by
  intro j
  obtain ⟨j, hj⟩ := j
  fin_cases j
  · have h1 : (p2ref.μ ((p2RefX v u hv).role.symm (Sum.inr ⟨0, hj⟩)) : ℝ) = 3 / 4 := by
      show ((p2ref.μ 1 : ℚ) : ℝ) = 3 / 4
      simp [p2ref]
    have h2 : ((plane2X v u).s 0 : ℝ) = 1 := by simp [plane2X]
    show |(p2ref.μ ((p2RefX v u hv).role.symm (Sum.inr ⟨0, hj⟩)) : ℝ) -
      (((plane2X v u).s 0 : ℚ) : ℝ)| ≤ 1 / 2
    rw [h1, h2]; norm_num [abs_of_neg]
  · exact absurd (by simp [plane2X]) hj

/-- The decay of the family of `ζ(3)` (the one-term datum) on the plane 2 cover, by the ghost shift `1/2`. -/
theorem plane2_decay_zeta (depth : ℕ) :
    HasScaledDecay (P2G.seqFamily zeta3Datum.f zeta3Datum.e zeta3Datum.xi depth)
      (SeqFamily.scale P2G.geometry) p2Cert.Dr p2Cert.cr := by
  have h := decayX (plane2X 1 0) (p2RefX 1 0 one_ne_zero) (p2X_contour 1 0)
    (plane2X_hhelp 1 0 one_ne_zero) (by intro i; fin_cases i <;> norm_num [plane2X]) depth
  rw [zetaX_f, zetaX_e, zetaX_xi] at h
  exact h

/-- The decay of the family of `π²` (the simple-pole datum) on the plane 2 cover, by the ghost shift `3/4`. -/
theorem plane2_decay_pi (depth : ℕ) :
    HasScaledDecay (P2G.seqFamily piDatum.f piDatum.e piDatum.xi depth)
      (SeqFamily.scale P2G.geometry) p2Cert.Dr p2Cert.cr := by
  have h := decayX piX piRef piX_contour (fun j => absurd rfl j.2)
    (by intro i; fin_cases i <;> norm_num [piX]) depth
  rw [piX_f, piX_e, piX_xi] at h
  exact h

/-! ### The theorem on the projective line -/

/-- The content of the family of `ζ(3)` (one-term datum) on the plane 2 geometry. -/
def Plane2ContentZeta (Λ : ℝ) : Prop :=
  HasScaledContent ((P2G.seqFamily zeta3Datum.f zeta3Datum.e zeta3Datum.xi 1).restrictAdm
    (fun n => SeqFamily.scale P2G.geometry n % 2 = 0)) (SeqFamily.scale P2G.geometry) Λ

/-- The content of the family of `π²` (simple-pole datum) on the plane 2 geometry. -/
def Plane2ContentPi (Λ : ℝ) : Prop :=
  HasScaledContent ((P2G.seqFamily piDatum.f piDatum.e piDatum.xi 1).restrictAdm
    (fun n => SeqFamily.scale P2G.geometry n % 2 = 0)) (SeqFamily.scale P2G.geometry) Λ

/-- **The plane 2 theorem on the whole projective line, contents as the only open input.**  For every rational
`(a, b) ≠ (0, 0)`, `a ζ(3) + b π²` is irrational and has irrationality measure at most every `B ≥ ccert / (D - Λ)`, given the contents of the
three families (generic datum, `ζ(3)`, `π²`) at the same `Λ ≤ 869210883039/250000000000`. -/
theorem plane2_point_ab_of_content {Λ : ℚ} (hΛu : Λ ≤ p2LamMax) {B : ℚ} (hB : Cover.Dchi.ccert / (Cover.Dchi.Dt - Λ) ≤ B)
    (hG : Plane2Content (Λ : ℝ))
    (hZ : Plane2ContentZeta (Λ : ℝ)) (hP : Plane2ContentPi (Λ : ℝ)) (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    MeasureLBAt ((a : ℝ) * (riemannZeta 3).re + (b : ℝ) * Real.pi ^ 2) (B : ℝ) ∧
      Irrational ((a : ℝ) * (riemannZeta 3).re + (b : ℝ) * Real.pi ^ 2) := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by tauto
    refine plane2_family_point piDatum (by decide) (plane2_decay_pi 1) hΛu hB hP (lam := -1 / (3 * b)) ?_ ?_
    · simp [hb]
    · rw [piDatum_xi, ha]
      have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      push_cast
      field_simp
      ring
  · by_cases hb : b = 0
    · refine plane2_family_point zeta3Datum (by decide) (plane2_decay_zeta 1) hΛu hB hZ (lam := -2 / a) ?_ ?_
      · simp [ha]
      · rw [zeta3Datum_xi, hb]
        have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
        push_cast
        field_simp
        ring
    · exact plane2_point_of_content hΛu hB hG a b ha hb

end CatalanCore.Uniform.Bank.Plane2

#print axioms CatalanCore.Uniform.Bank.Plane2.plane2_decay_zeta
#print axioms CatalanCore.Uniform.Bank.Plane2.plane2_decay_pi
#print axioms CatalanCore.Uniform.Bank.Plane2.plane2_point_ab_of_content
