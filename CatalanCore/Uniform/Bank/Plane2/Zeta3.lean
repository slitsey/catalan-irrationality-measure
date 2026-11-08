module

public import CatalanCore.Uniform.Bank.Plane2.Const
public import CatalanCore.Uniform.Bank.HalvesContent.Bound
public import CatalanCore.Uniform.Decay.PolyWire3.RulesOfTables
public import CatalanCore.Uniform.Decay.Jet.Source

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# ζ(3) on the halves cover: the decay (lane H, wave Z; ledger Z01, Z02)

The one-term datum `zeta3Datum` (`Plane2.Const`) has the Löwner family `FH.seqFamily` over the node geometry
`FH = altGeom (3/10)` of the halves bank.  Its decay is `Jet.support_decay` with the reference frame `halves`
(`zeta3Ref`: the shift `1` of the datum is the atom of the shift `1`, the helper of its double pole is the atom
of the shift `1/2`) and the certificate of the built halves cover (`halvesCert`, the rule record of `TabC` from
`PolyWire3.RulesOfTables`): no new cell.  Lattice constants: `ρ = 1/4`, `a = 3/4`, `a0 = g = 1/2`.
-/

namespace CatalanCore.Uniform.Bank.Plane2
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Bank.Halves
  CatalanCore.Uniform.Bank.Halves.Cover CatalanCore.Uniform.Bank.HalvesContent.Bound
  CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Jet CatalanCore.Uniform.Decay.Polygon
  CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyFull

theorem halves_hrow : FH.rowPieces = TabC.RP.map CatalanCore.Uniform.Decay.PolyFull.ratPiece := by
  rw [tab_RP]; exact altGeom_rowPieces (3 / 10) three_tenths_pos

theorem halves_hcol : FH.colPieces = TabC.CP.map CatalanCore.Uniform.Decay.PolyFull.ratPiece := by
  rw [tab_CP]; exact altGeom_colPieces (3 / 10) three_tenths_pos

theorem halves_hMq : TabC.Mq = FH.totalMass := by
  rw [tab_Mq]; exact (altGeom_totalMass (3 / 10) three_tenths_pos).symm

/-- The decay certificate of the halves cover, as a `Support.Certificate` over the node potential of `FH`. -/
noncomputable def halvesCert : Support.Certificate FH.nodePot where
  rules := rulesOfTables3 FH TabC halves_hrow halves_hcol halves_hMq
  spline := Dchi
  polygon := Pply
  ok := checkPB_of_tables3 FH TabC halves_hrow halves_hcol halves_hMq check_true
  D := Dchi.Dt
  c := Dchi.ccert
  hD := rfl
  hc' := rfl
  hc := by rw [ccert_eq]; unfold cH; norm_num


/-- The roles of the two atoms of the halves frame: the shift `1` stands for the shift of the datum, the shift
`1/2` is the helper of its double pole. -/
def zeta3Role : Fin 2 ≃ Fin zeta3Datum.n ⊕ {i : Fin zeta3Datum.n // zeta3Datum.b i ≠ 0} where
  toFun := fun q => if q = 0 then Sum.inr ⟨0, by simp [zeta3Datum]⟩ else Sum.inl 0
  invFun := fun x => match x with
    | Sum.inl _ => 1
    | Sum.inr _ => 0
  left_inv := by
    intro q; fin_cases q <;> simp
  right_inv := by
    intro x
    rcases x with i | j
    · have : i = 0 := Subsingleton.elim _ _
      subst this; simp
    · have : j = ⟨0, by simp [zeta3Datum]⟩ := Subsingleton.elim _ _
      subst this; simp

theorem halves_d : halves.d = 2 := rfl

noncomputable def zeta3Ref_role : Fin halves.d ≃ Fin zeta3Datum.n ⊕ {i : Fin zeta3Datum.n // zeta3Datum.b i ≠ 0} :=
  (finCongr halves_d).trans zeta3Role

noncomputable def zeta3Ref : RefMatch zeta3Datum halves where
  role := zeta3Ref_role
  idx_mu := by
    intro i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    change halves.μ ⟨1, by decide⟩ = (1 : ℚ)
    rfl
  side := by
    intro N0 m j
    have h1 : (halves.μ ((zeta3Ref_role).symm (Sum.inr j)) : ℝ) = 1 / 2 := by
      have : j = ⟨0, by simp [zeta3Datum]⟩ := Subsingleton.elim _ _
      subst this
      change ((halves.μ ⟨0, by decide⟩ : ℚ) : ℝ) = 1 / 2
      have : halves.μ ⟨0, by decide⟩ = (1 / 2 : ℚ) := rfl
      rw [this]; norm_num
    have h2 : ((zeta3Datum.s j.1 : ℚ) : ℝ) = 1 := by
      have : j.1 = 0 := Subsingleton.elim _ _
      rw [this]; simp [zeta3Datum]
    have hxs : ((halves.xs : ℚ) : ℝ) = 1 / 4 := by
      have : halves.xs = (1 / 4 : ℚ) := rfl
      rw [this]; norm_num
    rw [h1, h2, hxs]
    constructor
    · intro h
      have hle : N0 ≤ m := by
        by_contra hc
        push_neg at hc
        have : (m : ℝ) + 1 ≤ N0 := by exact_mod_cast hc
        linarith
      have : (N0 : ℝ) ≤ m := by exact_mod_cast hle
      linarith
    · intro h
      have hle : N0 ≤ m := by
        by_contra hc
        push_neg at hc
        have : (m : ℝ) + 1 ≤ N0 := by exact_mod_cast hc
        linarith
      have : (N0 : ℝ) ≤ m := by exact_mod_cast hle
      linarith


theorem halves_mu (q : Fin halves.d) :
    (halves.μ q = 1 / 2 ∧ q.val = 0) ∨ (halves.μ q = 1 ∧ q.val = 1) := by
  rcases q with ⟨q, hq⟩
  have hq2 : q < 2 := hq
  interval_cases q
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩

theorem half_int_abs (k : ℤ) (σ : ℝ) (hσ : σ = 1 / 2 ∨ σ = -1 / 2) : 1 / 2 ≤ |(k : ℝ) + σ| := by
  rcases le_or_gt 0 k with hk | hk
  · have : (0 : ℝ) ≤ k := by exact_mod_cast hk
    rcases hσ with h | h
    · exact le_abs.2 (Or.inl (by rw [h]; linarith))
    · -- k - 1/2 with k ≥ 0 : k = 0 gives -1/2, else ≥ 1/2
      rcases eq_or_lt_of_le hk with h0 | h0
      · subst h0; rw [h]; norm_num [abs_of_neg]
      · have : (1 : ℝ) ≤ k := by exact_mod_cast h0
        exact le_abs.2 (Or.inl (by rw [h]; linarith))
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    rcases hσ with h | h
    · exact le_abs.2 (Or.inr (by rw [h]; linarith))
    · exact le_abs.2 (Or.inr (by rw [h]; linarith))

theorem zeta3_decay (depth : ℕ) :
    HasScaledDecay (FH.seqFamily zeta3Datum.f zeta3Datum.e zeta3Datum.xi depth)
      (SeqFamily.scale FH.geometry) (halvesCert.Dr) (halvesCert.cr) := by
  obtain ⟨hbc, hbr, hbq⟩ := FH_blocks_v
  have hεpos : (0 : ℝ) < (Dchi.ε : ℝ) := by exact_mod_cast eps_pos
  have hrole : ∀ j : {i : Fin zeta3Datum.n // zeta3Datum.b i ≠ 0},
      (halves.μ (zeta3Ref.role.symm (Sum.inr j)) : ℚ) = 1 / 2 := by
    intro j
    have : j = ⟨0, by simp [zeta3Datum]⟩ := Subsingleton.elim _ _
    subst this
    rfl
  refine support_decay zeta3Datum FH (Fr := halves) zeta3Ref
    (Frame.contourOK_of_check (by decide +kernel)) (Frame.contourOK_of_check (by decide +kernel))
    (by decide +kernel) halvesCert (by decide +kernel) ?_ ?_ ?_ (nodePot_conj FH)
    ((nodePot_real_continuous FH).continuousOn) FH_supp (Bd := 2) (by norm_num) hbc hbr hbq
    (m0 := 1 / 2) (by norm_num) m0_le (e := (Dchi.ε : ℝ) / 2) ?_ ?_ depth
    (ρ := 1 / 4) (a := 3 / 4) (a0 := 1 / 2) (g := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show Dchi.Mq = FH.totalMass
    rw [FH_totalMass]; decide +kernel
  · show Dchi.dim = halves.d
    rw [dim_eq]; rfl
  · exact inu_le_nodeEnergy_of_check (altGeom_rowPieces (3 / 10) three_tenths_pos)
      (altGeom_colPieces (3 / 10) three_tenths_pos) energy_ok
  · linarith
  · show (Dchi.ε : ℝ) / 2 < (Dchi.ε : ℝ)
    linarith
  · exact halves_w_ne
  · intro m m' q q' hne
    have hq := halves_mu q
    have hq' := halves_mu q'
    have hk : ((m : ℤ) - m' : ℤ) = (m : ℤ) - m' := rfl
    have e1 : ((m : ℝ) + ((halves.μ q : ℚ) : ℝ) - ((m' : ℝ) + ((halves.μ q' : ℚ) : ℝ))) =
        (((m : ℤ) - (m' : ℤ) : ℤ) : ℝ) + (((halves.μ q : ℚ) : ℝ) - ((halves.μ q' : ℚ) : ℝ)) := by
      push_cast; ring
    rw [e1]
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hq' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · -- same atom family: then m ≠ m'
      have hmm : m ≠ m' := by
        intro h; apply hne
        have : q = q' := Fin.ext (by omega)
        rw [h, this]
      rw [h1, h3]
      have : ((m : ℤ) - m' : ℤ) ≠ 0 := by omega
      push_cast
      rcases lt_or_gt_of_ne this with hlt | hgt
      · have : ((m : ℝ) - m') ≤ -1 := by exact_mod_cast (by omega : (m : ℤ) - m' ≤ -1)
        refine le_abs.2 (Or.inr ?_); push_cast; linarith
      · have : (1 : ℝ) ≤ (m : ℝ) - m' := by exact_mod_cast (by omega : (1 : ℤ) ≤ (m : ℤ) - m')
        refine le_abs.2 (Or.inl ?_); push_cast; linarith
    · rw [h1, h3]; push_cast
      have := half_int_abs ((m : ℤ) - m') (-1 / 2) (Or.inr rfl)
      push_cast at this ⊢; convert this using 2; ring
    · rw [h1, h3]; push_cast
      have := half_int_abs ((m : ℤ) - m') (1 / 2) (Or.inl rfl)
      push_cast at this ⊢; convert this using 2; ring
    · have hmm : m ≠ m' := by
        intro h; apply hne
        have : q = q' := Fin.ext (by omega)
        rw [h, this]
      rw [h1, h3]
      have : ((m : ℤ) - m' : ℤ) ≠ 0 := by omega
      push_cast
      rcases lt_or_gt_of_ne this with hlt | hgt
      · have : ((m : ℝ) - m') ≤ -1 := by exact_mod_cast (by omega : (m : ℤ) - m' ≤ -1)
        refine le_abs.2 (Or.inr ?_); push_cast; linarith
      · have : (1 : ℝ) ≤ (m : ℝ) - m' := by exact_mod_cast (by omega : (1 : ℤ) ≤ (m : ℤ) - m')
        refine le_abs.2 (Or.inl ?_); push_cast; linarith
  · intro j
    have h1 : (halves.μ (zeta3Ref.role.symm (Sum.inr j)) : ℚ) = 1 / 2 := hrole j
    have h2 : (zeta3Datum.s j.1 : ℚ) = 1 := by
      have : j.1 = 0 := Subsingleton.elim _ _
      rw [this]; rfl
    rw [h1, h2]; norm_num [abs_of_neg]
  · intro i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    norm_num [zeta3Datum]
  · norm_num
  · exact m0_le
  · norm_num

end CatalanCore.Uniform.Bank.Plane2

#print axioms CatalanCore.Uniform.Bank.Plane2.halvesCert
#print axioms CatalanCore.Uniform.Bank.Plane2.zeta3Ref
#print axioms CatalanCore.Uniform.Bank.Plane2.zeta3_decay
