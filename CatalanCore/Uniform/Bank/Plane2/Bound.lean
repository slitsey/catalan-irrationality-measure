module

public import CatalanCore.Uniform.Bank.Plane2.Const
public import CatalanCore.Uniform.Bank.Plane2.Cover.Decay
public import CatalanCore.Uniform.Bank.Plane1.Frame
public import CatalanCore.Uniform.Decay.AltFold
public import CatalanCore.Uniform.Decay.Jet.Source
public import CatalanCore.Uniform.Support.Theorem
public import CatalanCore.Uniform.Support.NV

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# The plane 2 theorem (lane H, wave P209; ledger P209, P211, N6, S15 instance)

The plane `a ζ(3) + b π²`.  The datum `Datum.plane2 v u` (`S = {1, 1/2}`, `a = (u, -u)`, `b = (v, 0)`, `d = 3`)
has constant `ξ = -2 v ζ(3) - (u/3) π²` (`plane2_xi`, N6), its Löwner family `seqFamily` over the node geometry
`P2G = altGeom (6/41)` has the decay `(Dt, ccert)` of the generated plane 2 cover (`Cover.TabC`, `Cover.check_true`),
by `Jet.support_decay` with the `d = 3` reference frame `p2ref` (shifts `1/2, 3/4, 1`; the atom `3/4` is the helper of
the double shift `1`) and the certificate `p2Cert` (the rule record of the folded tables).

`plane2_point_of_content` is the plane 2 theorem for `a b ≠ 0` with the content as the only open input: the
content `Λ` of the family of every datum `plane2 v u` (`Plane2Content Λ`, supplied by wave P210) with
`Λ ≤ 869210883039/250000000000`.  The value `335.20` is the receipt value `335.182690829…`.
-/

namespace CatalanCore.Uniform.Bank.Plane2
open CatalanCore.Measure
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Decay.Jet CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Decay.AltDecay
  CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Polygon

/-! ### The constant (N6) -/

/-- **N6.**  The constant of the plane 2 datum: `ξ = -2 v ζ(3) - (u/3) π²`. -/
theorem plane2_xi (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) :
    (Datum.plane2 v u hv hu).xi = -2 * (v : ℝ) * (riemannZeta 3).re - ((u : ℝ) / 3) * Real.pi ^ 2 := by
  have h3 : hurwitzTail3 1 = (riemannZeta 3).re := by
    rw [riemannZeta_three_re]; unfold hurwitzTail3; simp
  unfold Datum.xi
  rw [Fin.sum_univ_two]
  simp only [Datum.plane2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Rat.cast_one,
    Rat.cast_div, Rat.cast_ofNat, Int.cast_neg, Int.cast_zero, mul_zero, zero_mul, sub_zero]
  have e2 : CatalanCore.hurwitzTail2 (1 / 2) = Real.pi ^ 2 / 2 := Bank.Plane1.hurwitz_half_pi
  have e1 : CatalanCore.hurwitzTail2 1 = Real.pi ^ 2 / 6 := Bank.Plane1.hurwitz_one_pi
  rw [h3]
  have e3 : CatalanCore.hurwitzTail2 ((1 : ℚ) / 2) = Real.pi ^ 2 / 2 := by exact_mod_cast e2
  simp only [e1, e3, e2]
  ring

/-! ### The geometry and the certificate -/

theorem p2c_pos : (0 : ℚ) < 6 / 41 := by norm_num

/-- The node geometry of the plane 2 cover: `altGeom (6/41)`. -/
noncomputable def P2G : BlockGeom := altGeom (6 / 41) p2c_pos

theorem p2_RP : Cover.RP = altPieces (6 / 41) := by decide +kernel
theorem p2_CP : Cover.CP = altPieces (6 / 41) := by decide +kernel

theorem p2_hrow : P2G.rowPieces = Cover.TabC.RP.map ratPiece := by
  rw [P2G, altGeom_rowPieces]
  show _ = Cover.RP.map ratPiece
  rw [p2_RP]

theorem p2_hcol : P2G.colPieces = Cover.TabC.CP.map ratPiece := by
  rw [P2G, altGeom_colPieces]
  show _ = Cover.CP.map ratPiece
  rw [p2_CP]

theorem p2_totalMass : P2G.totalMass = 44 / 41 := by
  rw [P2G, altGeom_totalMass]; norm_num

theorem p2_hMq : Cover.TabC.Mq = P2G.totalMass := by
  rw [p2_totalMass]; decide +kernel

theorem p2_cc : 0 < Cover.Dchi.ccert := by decide +kernel
theorem p2_dim : Cover.Dchi.dim = 3 := by decide +kernel
theorem p2_eps : 0 < Cover.Dchi.ε := by decide +kernel
theorem p2_energy : energyCheck 30 (altPieces (6 / 41)) (altPieces (6 / 41)) Cover.Dchi.Inu = true := by
  -- kcost: 0.26 s measured (energy check at N = 30, 2 pieces; type checking 262 ms)
  decide +kernel

/-- The decay certificate of the plane 2 cover over the node potential of `P2G`. -/
noncomputable def p2Cert : Support.Certificate P2G.nodePot where
  rules := rulesOfTablesF P2G Cover.TabC p2_hrow p2_hcol p2_hMq
  spline := Cover.Dchi
  polygon := Cover.Pply
  ok := checkPB_of_tablesF P2G Cover.TabC p2_hrow p2_hcol p2_hMq Cover.check_true
  D := Cover.Dchi.Dt
  c := Cover.Dchi.ccert
  hD := rfl
  hc' := rfl
  hc := p2_cc

/-! ### The reference frame and its match with the datum -/

/-- The `d = 3` reference frame of the plane 2 cover: shifts `1/2, 3/4, 1`, `x* = -N0 - 1/4`, gap `1/4`. -/
@[reducible] def p2ref : Frame where
  d := 3
  μ := ![1 / 2, 3 / 4, 1]
  w := ![1, 1, -2]
  norm := 1
  xs := 1 / 4
  δ0 := 1 / 4
  n0off := 0
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by
    intro i j hij h
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (norm_num at h)
  hw := by simp [Fin.sum_univ_three]
  hnorm := one_pos

theorem p2ref_contour : Frame.contourCheck p2ref = true := by decide +kernel

theorem p2ref_hAR : ∀ i : Fin p2ref.d, ((⌊p2ref.xs - p2ref.μ i⌋ : ℤ) : ℚ) + p2ref.μ i ≤ p2ref.n0off := by
  decide +kernel

theorem p2ref_w_ne (q : Fin p2ref.d) : p2ref.w q ≠ 0 := by
  fin_cases q <;> decide

theorem p2ref_mu_real (q : Fin p2ref.d) :
    ((p2ref.μ q : ℚ) : ℝ) = 1 / 2 ∨ ((p2ref.μ q : ℚ) : ℝ) = 3 / 4 ∨ ((p2ref.μ q : ℚ) : ℝ) = 1 := by
  fin_cases q <;> simp [p2ref] <;> norm_num

theorem p2ref_mu_inj (q q' : Fin p2ref.d) (h : p2ref.μ q = p2ref.μ q') : q = q' := by
  fin_cases q <;> fin_cases q' <;> first | rfl | (norm_num [p2ref] at h)

theorem p2ref_mu_ge (q : Fin p2ref.d) : (1 / 2 : ℝ) ≤ ((p2ref.μ q : ℚ) : ℝ) := by
  rcases p2ref_mu_real q with h | h | h <;> rw [h] <;> norm_num

theorem quarter_abs (k : ℤ) (d : ℝ) (hd : d = 1 / 4 ∨ d = -1 / 4 ∨ d = 1 / 2 ∨ d = -1 / 2) :
    1 / 4 ≤ |(k : ℝ) + d| := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    refine le_abs.2 (Or.inr ?_)
    rcases hd with rfl | rfl | rfl | rfl <;> linarith
  · rcases hd with rfl | rfl | rfl | rfl <;> simp <;> norm_num [abs_of_neg, abs_of_pos]
  · have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
    refine le_abs.2 (Or.inl ?_)
    rcases hd with rfl | rfl | rfl | rfl <;> linarith

theorem p2ref_sep (m m' : ℕ) (q q' : Fin p2ref.d) (hne : (m, q) ≠ (m', q')) :
    (1 / 4 : ℝ) ≤ |((m : ℝ) + (p2ref.μ q : ℝ)) - ((m' : ℝ) + (p2ref.μ q' : ℝ))| := by
  have e : ((m : ℝ) + (p2ref.μ q : ℝ)) - ((m' : ℝ) + (p2ref.μ q' : ℝ)) =
      (((m : ℤ) - (m' : ℤ) : ℤ) : ℝ) + (((p2ref.μ q : ℚ) : ℝ) - ((p2ref.μ q' : ℚ) : ℝ)) := by
    push_cast; ring
  rw [e]
  by_cases hq : q = q'
  · subst hq
    have hm : m ≠ m' := fun h => hne (by rw [h])
    have hk : ((m : ℤ) - (m' : ℤ)) ≠ 0 := by omega
    rw [sub_self, add_zero]
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have : (((m : ℤ) - m' : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : (m : ℤ) - m' ≤ -1)
      exact le_abs.2 (Or.inr (by linarith))
    · have : (1 : ℝ) ≤ (((m : ℤ) - m' : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ (m : ℤ) - m')
      exact le_abs.2 (Or.inl (by linarith))
  · refine quarter_abs _ _ ?_
    rcases p2ref_mu_real q with h1 | h1 | h1 <;> rcases p2ref_mu_real q' with h2 | h2 | h2 <;>
      first
        | (exfalso; apply hq; apply p2ref_mu_inj; exact_mod_cast h1.trans h2.symm)
        | (rw [h1, h2]; norm_num)

theorem p2_b0 (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) : (Datum.plane2 v u hv hu).b 0 ≠ 0 := by
  simpa [Datum.plane2] using hv

/-- The roles of the three atoms of `p2ref`: `1/2` is the shift `1/2`, `1` the double shift `1`, and `3/4` its helper. -/
def p2Role (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) :
    Fin p2ref.d ≃ Fin (Datum.plane2 v u hv hu).n ⊕ {i : Fin (Datum.plane2 v u hv hu).n // (Datum.plane2 v u hv hu).b i ≠ 0} where
  toFun := fun q => if q.val = 0 then Sum.inl 1 else if q.val = 1 then Sum.inr ⟨0, p2_b0 v u hv hu⟩ else Sum.inl 0
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
      · exact absurd (by simp [Datum.plane2]) hj

theorem p2_half_iff (N0 m : ℕ) :
    ((N0 : ℝ) + 1 / 4 < (m : ℝ) + 3 / 4) ↔ ((N0 : ℝ) + 1 / 4 < (m : ℝ) + 1) := by
  constructor
  · intro h
    have hle : N0 ≤ m := by
      by_contra hc; push_neg at hc
      have : (m : ℝ) + 1 ≤ N0 := by exact_mod_cast hc
      linarith
    have : (N0 : ℝ) ≤ m := by exact_mod_cast hle
    linarith
  · intro h
    have hle : N0 ≤ m := by
      by_contra hc; push_neg at hc
      have : (m : ℝ) + 1 ≤ N0 := by exact_mod_cast hc
      linarith
    have : (N0 : ℝ) ≤ m := by exact_mod_cast hle
    linarith

/-- **The match of `p2ref` with the plane 2 datum** (S04, F1, F2). -/
noncomputable def p2Ref (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) : RefMatch (Datum.plane2 v u hv hu) p2ref where
  role := p2Role v u hv hu
  idx_mu := by
    intro i
    fin_cases i <;> rfl
  side := by
    intro N0 m j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · have h1 : (p2ref.μ ((p2Role v u hv hu).symm (Sum.inr ⟨0, hj⟩)) : ℝ) = 3 / 4 := by
        show ((p2ref.μ 1 : ℚ) : ℝ) = 3 / 4
        simp [p2ref]
      have h2 : ((Datum.plane2 v u hv hu).s 0 : ℝ) = 1 := by simp [Datum.plane2]
      have hxs : (p2ref.xs : ℝ) = 1 / 4 := by simp [p2ref]
      show ((N0 : ℝ) + (p2ref.xs : ℝ) < (m : ℝ) + (p2ref.μ ((p2Role v u hv hu).symm (Sum.inr ⟨0, hj⟩)) : ℝ)) ↔
        ((N0 : ℝ) + (p2ref.xs : ℝ) < (m : ℝ) + (((Datum.plane2 v u hv hu).s 0 : ℚ) : ℝ))
      rw [h1, h2, hxs]
      exact p2_half_iff N0 m
    · exact absurd (by simp [Datum.plane2]) hj

/-- The contour condition of the jet frame of the plane 2 datum: it reads only the shifts, `x*` and the gap. -/
theorem p2_datum_contour (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) :
    (datumJet (Datum.plane2 v u hv hu) p2ref.xs p2ref.δ0 p2ref.n0off).toFrame.ContourOK := by
  apply Frame.contourOK_of_check
  have h : Frame.contourCheck (datumJet (Datum.plane2 v u hv hu) p2ref.xs p2ref.δ0 p2ref.n0off).toFrame =
      Frame.contourCheck (datumJet (Datum.plane2 1 1 one_ne_zero one_ne_zero) p2ref.xs p2ref.δ0
        p2ref.n0off).toFrame := rfl
  rw [h]
  decide +kernel

/-! ### The decay of the plane 2 family -/

/-- **S15 at the plane 2 cover.**  The Löwner family of the datum `plane2 v u` over `P2G` has the decay
`(Dt, ccert)` of the generated plane 2 cover, for every `v, u ≠ 0` and every selection depth. -/
theorem plane2_decay (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) (depth : ℕ) :
    HasScaledDecay (P2G.seqFamily (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e
      (Datum.plane2 v u hv hu).xi depth) (SeqFamily.scale P2G.geometry) p2Cert.Dr p2Cert.cr := by
  obtain ⟨hbc, hbr, hbq⟩ := altGeom_blocks_v (6 / 41) p2c_pos (by norm_num)
  have hεpos : (0 : ℝ) < (Cover.Dchi.ε : ℝ) := by exact_mod_cast p2_eps
  refine support_decay (Datum.plane2 v u hv hu) P2G (Fr := p2ref) (p2Ref v u hv hu)
    (Frame.contourOK_of_check p2ref_contour) (p2_datum_contour v u hv hu) p2ref_hAR p2Cert
    (by show ∀ p ∈ Cover.Pply.verts, p.1 + Cover.Pply.r0 ≤ 0; decide +kernel) ?_ ?_ ?_
    (nodePot_conj P2G) ((nodePot_real_continuous P2G).continuousOn) (altGeom_supp (6 / 41) p2c_pos)
    (Bd := 2) (by norm_num) hbc hbr hbq
    (m0 := 1 / 2) (by norm_num) p2ref_mu_ge (e := (Cover.Dchi.ε : ℝ) / 2) (by linarith) ?_ depth
    (ρ := 1 / 8) (a := 3 / 8) (a0 := 1 / 2) (g := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) p2ref_w_ne ?_ ?_ ?_ (by norm_num) ?_ (by norm_num)
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
  · intro j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · have h1 : (p2ref.μ ((p2Ref v u hv hu).role.symm (Sum.inr ⟨0, hj⟩)) : ℝ) = 3 / 4 := by
        show ((p2ref.μ 1 : ℚ) : ℝ) = 3 / 4
        simp [p2ref]
      have h2 : ((Datum.plane2 v u hv hu).s 0 : ℝ) = 1 := by simp [Datum.plane2]
      show |(p2ref.μ ((p2Ref v u hv hu).role.symm (Sum.inr ⟨0, hj⟩)) : ℝ) -
        (((Datum.plane2 v u hv hu).s 0 : ℚ) : ℝ)| ≤ 1 / 2
      rw [h1, h2]; norm_num [abs_of_neg]
    · exact absurd (by simp [Datum.plane2]) hj
  · intro i
    fin_cases i <;> norm_num [Datum.plane2]
  · intro q
    exact p2ref_mu_ge q

/-! ### The plane 2 theorem for `a b ≠ 0` -/

theorem P2G_common_mass : P2G.common.mass = 1 := by
  simp [P2G, altGeom, single_mass, commonB, PeriodicBlock.mass]

/-- The Löwner family of the plane 2 datum at the selection depth `1`. -/
noncomputable abbrev p2Fam (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) : PolyFamily :=
  P2G.seqFamily (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e (Datum.plane2 v u hv hu).xi 1

/-- **The content `Λ` of the plane 2 families** (supplied by wave P210): every datum `plane2 v u`, `v u ≠ 0`, at the
even scales of `P2G`. -/
def Plane2Content (Λ : ℝ) : Prop :=
  ∀ (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0),
    HasScaledContent ((p2Fam v u hv hu).restrictAdm (fun n => SeqFamily.scale P2G.geometry n % 2 = 0))
      (SeqFamily.scale P2G.geometry) Λ

/-- The largest content for which the receipt gives `335.20`. -/
def p2LamMax : ℚ := 869210883039 / 250000000000

theorem p2_eta : p2LamMax < Cover.Dchi.Dt := by
  -- kcost: rational comparison of two literals, < 1 s
  decide +kernel

theorem p2_ratio : Cover.Dchi.ccert / (Cover.Dchi.Dt - p2LamMax) ≤ 33520 / 100 := by
  -- kcost: exact rational arithmetic, < 1 s
  decide +kernel

theorem p2_ratio_real {Λ : ℚ} (hΛ : Λ ≤ p2LamMax) :
    ((Cover.Dchi.ccert : ℚ) : ℝ) / (((Cover.Dchi.Dt : ℚ) : ℝ) - (Λ : ℝ)) ≤ ((33520 / 100 : ℚ) : ℝ) := by
  have h1 : (0 : ℝ) < ((Cover.Dchi.Dt : ℚ) : ℝ) - ((p2LamMax : ℚ) : ℝ) := by
    have : ((p2LamMax : ℚ) : ℝ) < ((Cover.Dchi.Dt : ℚ) : ℝ) := by exact_mod_cast p2_eta
    linarith
  have hΛ' : (Λ : ℝ) ≤ ((p2LamMax : ℚ) : ℝ) := by exact_mod_cast hΛ
  have hc : (0 : ℝ) ≤ ((Cover.Dchi.ccert : ℚ) : ℝ) := by exact_mod_cast p2_cc.le
  calc ((Cover.Dchi.ccert : ℚ) : ℝ) / (((Cover.Dchi.Dt : ℚ) : ℝ) - (Λ : ℝ))
      ≤ ((Cover.Dchi.ccert : ℚ) : ℝ) / (((Cover.Dchi.Dt : ℚ) : ℝ) - ((p2LamMax : ℚ) : ℝ)) :=
        div_le_div_of_nonneg_left hc h1 (by linarith)
    _ = (((Cover.Dchi.ccert / (Cover.Dchi.Dt - p2LamMax) : ℚ)) : ℝ) := by push_cast; rfl
    _ ≤ ((33520 / 100 : ℚ) : ℝ) := by exact_mod_cast p2_ratio

/-- The ratio bound `335.20` for every content below `p2LamMax`, in `ℚ`. -/
theorem p2_ratio_le {Λ : ℚ} (hΛ : Λ ≤ p2LamMax) : Cover.Dchi.ccert / (Cover.Dchi.Dt - Λ) ≤ 33520 / 100 := by
  have h := p2_ratio_real hΛ
  have h' : ((Cover.Dchi.ccert / (Cover.Dchi.Dt - Λ) : ℚ) : ℝ) ≤ ((33520 / 100 : ℚ) : ℝ) := by
    push_cast at h ⊢; exact h
  exact_mod_cast h'

/-- **A datum on the plane 2 cover** (generic): a datum `D` of depth `d / 2 ≤ 1` whose Löwner family over `P2G` has the
decay of the cover and a content `Λ ≤ 869210883039/250000000000` has a constant `ξ` with `D.xi = lam ξ`, `lam ≠ 0`
of irrationality measure at most `B`, for every `B` above the exact ratio `ccert / (D - Λ)`. -/
theorem plane2_family_point (D : Datum) (hdepth : D.d / 2 ≤ 1)
    (hdecay : HasScaledDecay (P2G.seqFamily D.f D.e D.xi 1) (SeqFamily.scale P2G.geometry) p2Cert.Dr p2Cert.cr)
    {Λ : ℚ} (hΛu : Λ ≤ p2LamMax) {B : ℚ} (hB : Cover.Dchi.ccert / (Cover.Dchi.Dt - Λ) ≤ B)
    (hΛ : HasScaledContent ((P2G.seqFamily D.f D.e D.xi 1).restrictAdm
      (fun n => SeqFamily.scale P2G.geometry n % 2 = 0)) (SeqFamily.scale P2G.geometry) (Λ : ℝ))
    {ξ : ℝ} {lam : ℚ} (hlam : lam ≠ 0) (hconst : D.xi = (lam : ℝ) * ξ) :
    MeasureLBAt ξ (B : ℝ) ∧ Irrational ξ := by
  set P : (P2G.seqFamily D.f D.e D.xi 1).ι → Prop := fun n => SeqFamily.scale P2G.geometry n % 2 = 0 with hP
  set Famr := (P2G.seqFamily D.f D.e D.xi 1).restrictAdm P with hFamr
  have hΛ' : HasScaledContent (Famr.restrictAdm (fun n => SeqFamily.scale P2G.geometry n % 2 = 0))
      (SeqFamily.scale P2G.geometry) (Λ : ℝ) := by
    obtain ⟨den, hpos, hint, hlog⟩ := hΛ
    refine ⟨den, hpos, fun n hn p q hq => hint n hn.1 p q hq, fun ε hε => ?_⟩
    obtain ⟨R0, hR⟩ := hlog ε hε
    exact ⟨R0, fun n hn hr => hR n hn.1 hr⟩
  have hD : HasScaledDecay Famr (SeqFamily.scale P2G.geometry) p2Cert.Dr p2Cert.cr := by
    intro ε hε
    obtain ⟨R0, hR⟩ := hdecay ε hε
    exact ⟨R0, fun n hn hr t ht => hR n hn.1 hr t ht⟩
  have hη : (Λ : ℝ) < p2Cert.Dr := by
    have h1 : Λ < Cover.Dchi.Dt := lt_of_le_of_lt hΛu p2_eta
    show (Λ : ℝ) < ((Cover.Dchi.Dt : ℚ) : ℝ)
    exact_mod_cast h1
  have hc : 0 < p2Cert.cr := by exact_mod_cast p2Cert.hc
  have hdeg : ∀ n, Famr.Adm n →
      (Famr.deg n : ℝ) ≤ 1 * (SeqFamily.scale P2G.geometry n) + (P2G.common.n : ℝ) := by
    intro n hn
    have := P2G.seq_degree_bound D.f D.e D.xi 1 n
    rw [P2G_common_mass, Rat.cast_one, one_mul] at this
    rw [one_mul]
    exact this
  have heven : ∀ n, Famr.Adm n → SeqFamily.scale P2G.geometry n % 2 = 0 := fun n hn => hn.2
  have hnv : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, Famr.Adm n ∧ SeqFamily.scale P2G.geometry n = 2 * s ∧ Famr.evalQ n x ≠ 0 := by
    obtain ⟨R0, h⟩ := altGeom_seqFamily_nv0_even D (6 / 41) p2c_pos D.xi 1 hdepth
    refine ⟨R0, fun s hs x => ?_⟩
    obtain ⟨n, hn, hsc, hne⟩ := h s hs x
    have hsc' : SeqFamily.scale P2G.geometry n = 2 * s := hsc
    exact ⟨n, ⟨hn, by omega⟩, hsc', hne⟩
  have hconst' : Famr.const = (lam : ℝ) * ξ + ((0 : ℚ) : ℝ) := by
    show D.xi = _
    rw [hconst]; push_cast; ring
  have key := support_measureLB Famr (SeqFamily.scale P2G.geometry) hΛ' hD hη hc one_pos
    (Nat.cast_nonneg _) hdeg hnv (ξ := ξ) (a := lam) (b := 0) hlam hconst'
  refine ⟨key.1.mono ?_, key.2⟩
  have e1 : p2Cert.cr = ((Cover.Dchi.ccert : ℚ) : ℝ) := rfl
  have e2 : p2Cert.Dr = ((Cover.Dchi.Dt : ℚ) : ℝ) := rfl
  rw [one_mul, e1, e2]
  exact_mod_cast hB

/-- **The plane 2 theorem for `a b ≠ 0`, the content as the only open input.**  Given a content
`Λ ≤ 869210883039/250000000000` of the plane 2 families (`Plane2Content`), `a ζ(3) + b π²` is irrational and has
irrationality measure at most every `B ≥ ccert / (D - Λ)` (`335.20` at `p2LamMax`), for rational `a, b ≠ 0`.  The decay is `plane2_decay` (the generated cover),
the nonvanishing `altGeom_seqFamily_nv0_even`, the constant `plane2_xi`. -/
theorem plane2_point_of_content {Λ : ℚ} (hΛu : Λ ≤ p2LamMax) {B : ℚ} (hB : Cover.Dchi.ccert / (Cover.Dchi.Dt - Λ) ≤ B)
    (hΛ : Plane2Content (Λ : ℝ))
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    MeasureLBAt ((a : ℝ) * (riemannZeta 3).re + (b : ℝ) * Real.pi ^ 2) (B : ℝ) ∧
      Irrational ((a : ℝ) * (riemannZeta 3).re + (b : ℝ) * Real.pi ^ 2) := by
  have hden_a : (a.den : ℤ) ≠ 0 := by exact_mod_cast a.den_nz
  have hden_b : (b.den : ℤ) ≠ 0 := by exact_mod_cast b.den_nz
  have hv : (b.den : ℤ) * a.num ≠ 0 := mul_ne_zero hden_b (Rat.num_ne_zero.2 ha)
  have hu : 6 * (a.den : ℤ) * b.num ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hden_a) (Rat.num_ne_zero.2 hb)
  set v : ℤ := (b.den : ℤ) * a.num with hvdef
  set u : ℤ := 6 * (a.den : ℤ) * b.num with hudef
  set lam : ℚ := -2 * a.den * b.den with hlamdef
  have hlam : lam ≠ 0 := by
    rw [hlamdef]
    have h1 : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
    have h2 : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
    exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2
  have hconst : (Datum.plane2 v u hv hu).xi = (lam : ℝ) * ((a : ℝ) * (riemannZeta 3).re + (b : ℝ) * Real.pi ^ 2) := by
    rw [plane2_xi]
    have ha' : (a : ℝ) = (a.num : ℝ) / (a.den : ℝ) := by exact_mod_cast (Rat.num_div_den a).symm
    have hb' : (b : ℝ) = (b.num : ℝ) / (b.den : ℝ) := by exact_mod_cast (Rat.num_div_den b).symm
    have h1 : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_nz
    have h2 : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_nz
    rw [ha', hb', hvdef, hudef, hlamdef]
    push_cast
    field_simp
    ring
  exact plane2_family_point (Datum.plane2 v u hv hu) (by rw [Datum.plane2_d]) (plane2_decay v u hv hu 1) hΛu hB
    (hΛ v u hv hu) hlam hconst

end CatalanCore.Uniform.Bank.Plane2

#print axioms CatalanCore.Uniform.Bank.Plane2.plane2_xi
#print axioms CatalanCore.Uniform.Bank.Plane2.plane2_decay
#print axioms CatalanCore.Uniform.Bank.Plane2.plane2_family_point
#print axioms CatalanCore.Uniform.Bank.Plane2.plane2_point_of_content
