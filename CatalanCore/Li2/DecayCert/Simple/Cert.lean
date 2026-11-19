module
public import CatalanCore.Li2.DecayCert.Simple.Link
public import CatalanCore.Li2.DecayCert.Lattice.Energy
public import CatalanCore.Li2.DecayCert.Lattice.Tail
/-! The SIMPLE lattice certificate. `SimpleSetup` is the certificate of one lattice datum (source and its
check, W side with caps, Right cells, tail, energy); `SimplePairCert` adds one `ρ` (atom side with caps and
the final scalar). `latticeSimple_D_ge` concludes the dual lower bound in the form of `latticeCert_D_ge`. -/
@[expose] public section
open MeasureTheory Set Polynomial
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay CatalanCore.Li2.DecayCert.LatticeSimple
  CatalanCore.Zeta5.Potential CatalanCore.Li2.DecayCert.LatticeGate
noncomputable section

/-- The SIMPLE certificate of one lattice datum, shared by all its `ρ`. -/
structure SimpleSetup where
  density : DensityWitness
  energy : LatticeEnergyWitness
  Iup : ℚ
  cutoff : ℚ
  terms : ℕ
  source : SourceF
  logs : List LogEntry
  aux : SimpleAux
  wside : Side
  wcaps : List ℚ
  wIds : List ℕ
  TW : ℚ
  rcells : List RCell
  TR : ℚ

/-- The old setup record carrying the fields the tail and energy checks read. -/
def SimpleSetup.toLS (c : SimpleSetup) : LatticeSetup :=
  ⟨c.density,c.energy,c.source.theta,c.Iup,c.cutoff,[],[],c.terms⟩

/-- One gap cap from the closed-form primitive. -/
def gapCapOK (s : SourceF) (logs : List LogEntry) (ids : List ℕ) (qI : List FBox) (p q cap : ℚ) : Bool :=
  match primBoxF s (fun a => lookupLogF logs a ids) qI p,primBoxF s (fun a => lookupLogF logs a ids) qI q with
  | some bp,some bq => decide ((bq.2:ℚ)/(S:ℚ)-(bp.1:ℚ)/(S:ℚ)+(s.globalW:ℚ)/(S:ℚ)*(q-p) ≤ cap)
  | _,_ => false

def atomGapCapOK (s : SourceF) (logs : List LogEntry) (ids : List ℕ) (qAI : List FBox) (p q cap : ℚ) : Bool :=
  match atomPrimBoxF s (fun a => lookupLogF logs a ids) qAI p,atomPrimBoxF s (fun a => lookupLogF logs a ids) qAI q with
  | some bp,some bq => decide ((bq.2:ℚ)/(S:ℚ)-(bp.1:ℚ)/(S:ℚ)+(s.globalA:ℚ)/(S:ℚ)*(q-p) ≤ cap)
  | _,_ => false

def capsCheck (ok : ℚ → ℚ → ℚ → Bool) (w : Side) (caps : List ℚ) : Bool :=
  (List.range w.pat.gaps).all (fun i => !w.pat.positive i || ok (w.pat.node i) (w.pat.node (i+1)) (caps.getD i 0))

def simpleSetupCheck (z : ℚ) (d : LatticeInput) (c : SimpleSetup) : Bool :=
  decide (0 < |z| ∧ |z| < 1 ∧ 1 ≤ c.cutoff ∧ d.Y ≤ c.cutoff) &&
  latticeShapeCheck d && datumCheck d.data c.density &&
  simpleSourceCheck z d c.source c.logs c.aux &&
  c.wside.check (WCell.ok c.source c.logs) 0 c.source.Y &&
  capsCheck (gapCapOK c.source c.logs c.wIds c.aux.qI) c.wside c.wcaps &&
  decide (c.wside.pat.plusCap (fun i => c.wcaps.getD i 0)+c.wside.pat.rootCap c.wside.ep c.wside.em ≤ c.TW) &&
  chainCheck c.source.Y c.cutoff (c.rcells.map RCell.iv) && c.rcells.all (RCell.ok c.source c.logs) &&
  decide ((c.rcells.map RCell.cap).sum ≤ c.TR) &&
  scalarUpperCheck (latticeTailExpr z d c.toLS) c.source.theta &&
  scalarUpperCheck (seAdd (seRat (3/(c.cutoff+1))) (.log c.terms |z|)) 0 &&
  (match latticeEnergyExpr d c.energy with | some e => scalarUpperCheck e c.Iup | none => false)

/-- The SIMPLE certificate of one `(datum, ρ)` pair: the atom side and the final scalar. -/
structure SimplePairCert where
  rho : ℚ
  lower : ℚ
  aside : Side
  acaps : List ℚ
  aIds : List ℕ
  TA : ℚ

def SimpleSetup.sourceAt (c : SimpleSetup) (ρ : ℚ) : SourceF := {c.source with rho := ρ}

def simplePairCheck (c : SimpleSetup) (p : SimplePairCert) : Bool :=
  decide (0 < p.rho) &&
  p.aside.check (ACell.ok (c.sourceAt p.rho) c.logs) 1 4 &&
  capsCheck (atomGapCapOK (c.sourceAt p.rho) c.logs p.aIds c.aux.qAI) p.aside p.acaps &&
  decide (p.aside.pat.plusCap (fun i => p.acaps.getD i 0)+p.aside.pat.rootCap p.aside.ep p.aside.em ≤ p.TA) &&
  scalarLowerCheck p.lower (seSum [seScale (-12) (.log c.terms 2),
    seRat (-4-c.Iup-2*c.source.theta-2*(c.TW+c.TR)-p.TA)])

theorem forall2_boxOfQ (l : List ℚ) : List.Forall₂ Contains (l.map boxOfQ) (l.map (fun q : ℚ => (q:ℝ))) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih => exact List.Forall₂.cons (boxOfQ_sound a) ih

/-- The Joukowski tail coefficients `c_{k+1}/(k+1)` in Horner order with the zero constant. -/
theorem hfk_of_exact (d : LatticeInput) (t : ℝ) :
    hornerR t (((fkQ d).map (fun q : ℚ => (q:ℝ))).reverse++[0])=
      ∑ k ∈ Finset.range (d.first.coeff.length-1),(d.first.c (k+1):ℝ)*t^(k+1)/((k+1:ℕ):ℝ) := by
  have h := hornerR_reverse (0::fkQ d) t
  simp only [List.map_cons,List.reverse_cons,Rat.cast_zero] at h
  rw [h,qListPoly_map_eval,List.length_cons,Finset.sum_range_succ']
  have hl : (fkQ d).length=d.first.coeff.length-1 := by simp [fkQ]
  rw [hl]
  simp only [coeffQ,List.getElem?_cons_zero,Option.getD_some,Rat.cast_zero,zero_mul,add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < d.first.coeff.length-1 := Finset.mem_range.mp hk
  simp only [List.getElem?_cons_succ,fkQ,List.getElem?_map,List.getElem?_range hk',Option.map_some,Option.getD_some]
  push_cast; ring

/-- A passed cap check bounds each positive gap's integral. -/
theorem capsCheck_sound (ok : ℚ → ℚ → ℚ → Bool) (w : Side) (caps : List ℚ) (f : ℝ → ℝ)
    (hc : capsCheck ok w caps=true)
    (hok : ∀ i, i < w.pat.gaps → ok (w.pat.node i) (w.pat.node (i+1)) (caps.getD i 0)=true →
      (∫ x in (w.pat.node i:ℝ)..(w.pat.node (i+1):ℝ), f x) ≤ ((caps.getD i 0:ℚ):ℝ)) :
    ∀ i, i < w.pat.gaps → w.pat.positive i=true →
      (∫ x in (w.pat.node i:ℝ)..(w.pat.node (i+1):ℝ), f x) ≤ ((caps.getD i 0:ℚ):ℝ) := by
  intro i hi hpos
  have h := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  rw [hpos,Bool.not_true,Bool.false_or] at h
  exact hok i hi h

theorem pattern_nodes (w : Side) (a b : ℚ) (hp : w.pat.check a b=true) (i : ℕ) (hi : i < w.pat.gaps) :
    a ≤ w.pat.node i ∧ w.pat.node i ≤ w.pat.node (i+1) ∧ w.pat.node (i+1) ≤ b := by
  have h := w.pat.check_parts a b hp
  obtain ⟨⟨hg,h0,hn⟩,hinc,-,-⟩ := h
  refine ⟨?_,(hinc i (i+1) (by omega) (by omega)).le,?_⟩
  · rcases Nat.eq_zero_or_pos i with h|h
    · subst h; rw [h0]
    · rw [← h0]; exact (hinc 0 i h hi.le).le
  · rcases (Nat.lt_or_ge (i+1) w.pat.gaps) with h|h
    · rw [← hn]; exact (hinc (i+1) w.pat.gaps h le_rfl).le
    · have : i+1=w.pat.gaps := by omega
      rw [this,hn]

/-- **The SIMPLE lattice certificate.** A passed setup check and pair check give the dual lower bound at
`(z, ρ)` in the form the decay table consumes (`latticeCert_D_ge`). -/
theorem latticeSimple_D_ge (z : ℚ) (d : LatticeInput) (c : SimpleSetup) (p : SimplePairCert)
    (hc : simpleSetupCheck z d c=true) (hp : simplePairCheck c p=true) :
    (p.lower:ℝ) ≤ -(12*Real.log 2+4)-I d.data.dual.σ-2*(c.source.theta:ℝ)-
      2*(∫ x in Ici (0:ℝ),pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(c.source.theta:ℝ)))-
        atomPenalty (z:ℝ) (p.rho:ℝ) d.data.dual.σ (c.source.theta:ℝ) := by
  simp only [simpleSetupCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,hsh⟩,hd⟩,hsrc⟩,hws⟩,hwc⟩,hTW⟩,hrch⟩,hrok⟩,hTR⟩,ht1⟩,ht2⟩,hen⟩ := hc
  have h1' := of_decide_eq_true h1
  simp only [simplePairCheck,Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨hρ,has⟩,hac⟩,hTA⟩,hsc⟩ := hp
  have hall := simpleSourceCheck_parts z d c.source c.logs c.aux hsrc
  have hP := hall.1
  have hYs : c.source.Y=d.Y := hP.2.1
  have hσ := lattice_sources d
  have hpos1 := (datum_source_data d.data c.density hd d.first (lattice_first_mem d)).2.2
  have hpos2 := (datum_source_data d.data c.density hd d.second (lattice_second_mem d)).2.2
  haveI := positive_source_finite d.first hpos1
  haveI := positive_source_finite d.second hpos2
  -- energy
  have hI : I d.data.dual.σ ≤ (c.Iup:ℝ) := by
    cases he : latticeEnergyExpr d c.energy with
    | none => rw [he] at hen; simp at hen
    | some e =>
      rw [he] at hen
      exact (latticeEnergyExpr_upper d c.density hd hsh c.energy e he).trans (scalarUpperCheck_sound _ _ hen)
  -- the W side on [0, Y]
  have lkW := simpleWLink z d c.density hd hsh c.source c.logs c.aux hsrc
  have hfW : ContinuousOn (fun x : ℝ => W (z:ℝ) (d.first.measure+d.second.measure) (x:ℂ)-(c.source.theta:ℝ))
      (Icc ((0:ℚ):ℝ) (c.source.Y:ℝ)) := by
    rw [← hσ]; exact ((continuous_W_real _ _).sub continuous_const).continuousOn
  have hqIF : List.Forall₂ Contains c.aux.qI
      (((qListIntegral (ownXList d)).map (fun q : ℚ => (q:ℝ))).reverse) := by
    rw [hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,← List.map_reverse]
    exact forall2_boxOfQ _
  have hcapW := capsCheck_sound _ c.wside c.wcaps
    (fun x => W (z:ℝ) (d.first.measure+d.second.measure) (x:ℂ)-(c.source.theta:ℝ)) hwc
    (by
      intro i hi hok
      obtain ⟨hn0,hn1,hn2⟩ := pattern_nodes c.wside 0 c.source.Y ((c.wside.check_parts _ 0 c.source.Y hws).1) i hi
      unfold gapCapOK at hok
      split at hok
      · rename_i bp bq hbp hbq
        have hg := gapIntegral_le c.source c.logs (simpleR z d c.source c.aux) (z:ℝ) (c.source.theta:ℝ) (d.Y:ℝ)
          d.first.measure d.second.measure (simpleMoments z d c.density hd hsh c.source c.logs c.aux hsrc)
          c.source.MU.length lkW c.wIds c.aux.qI _ hqIF
          (fun x => hqI_of_exact d c.density hd hsh c.source.y0 c.aux.H hP.2.2.2.2.1 hP.2.2.2.2.2.1
            hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1 x)
          hP.2.2.2.2.2.2.2.2.2.1 _ _ hn0 hn1 hn2 bp bq hbp hbq
        have hq := of_decide_eq_true hok
        have hq2 : (((bq.2:ℚ)/(S:ℚ)-(bp.1:ℚ)/(S:ℚ)+(c.source.globalW:ℚ)/(S:ℚ)*
            (c.wside.pat.node (i+1)-c.wside.pat.node i):ℚ):ℝ) ≤ ((c.wcaps.getD i 0:ℚ):ℝ) := by
          exact_mod_cast hq
        rw [dec_eq_ratCast,dec_eq_ratCast,dec_eq_ratCast] at hg
        push_cast at hq2 hg
        linarith
      · simp at hok)
  have hW := WSide.penalty c.source c.logs (simpleR z d c.source c.aux) (z:ℝ) (c.source.theta:ℝ) (d.Y:ℝ)
    d.first.measure d.second.measure (simpleMoments z d c.density hd hsh c.source c.logs c.aux hsrc)
    c.source.MU.length lkW c.wside hws hfW (fun i => c.wcaps.getD i 0) hcapW c.TW hTW
  rw [hYs] at hW
  -- the Right side on [Y, C]
  have hcont : Continuous (fun x : ℝ => pos (W (z:ℝ) (d.first.measure+d.second.measure) (x:ℂ)-(c.source.theta:ℝ))) := by
    rw [← hσ]; exact ((continuous_W_real _ _).sub continuous_const).max continuous_const
  have hR := RSide.penalty c.source c.logs (simpleR z d c.source c.aux) (z:ℝ) (c.source.theta:ℝ) (d.Y:ℝ)
    d.first.measure d.second.measure (simpleMoments z d c.density hd hsh c.source c.logs c.aux hsrc)
    c.source.MU.length lkW rfl (fun t => hfk_of_exact d t) c.cutoff c.rcells hrch
    (fun x hx => List.all_eq_true.mp hrok x hx) hcont
  rw [hYs] at hR
  have hTR2 : ((((c.rcells.map RCell.cap).sum:ℚ)):ℝ) ≤ (c.TR:ℝ) := by exact_mod_cast of_decide_eq_true hTR
  -- the tail beyond C
  have htail := latticeTail_checked z d c.toLS hd h1'.2.2.1 ht1 ht2
  -- the atom side on [1, 4]
  have hsrc2 : simpleSourceCheck z d (c.sourceAt p.rho) c.logs c.aux=true := hsrc
  have lkA := simpleALink z d c.density hd hsh (c.sourceAt p.rho) c.logs c.aux hsrc2
  have hfA : ContinuousOn (fun x : ℝ => A (z:ℝ) (p.rho:ℝ) (d.first.measure+d.second.measure) x-(c.source.theta:ℝ))
      (Icc ((1:ℚ):ℝ) ((4:ℚ):ℝ)) := by
    rw [← hσ]; exact ((continuous_A_real _ _ _).sub continuous_const).continuousOn
  have hqAIF : List.Forall₂ Contains c.aux.qAI
      (((qListIntegral (atomXList d c.source.y0 c.aux.sm c.aux.KA)).map (fun q : ℚ => (q:ℝ))).reverse) := by
    rw [hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,← List.map_reverse]
    exact forall2_boxOfQ _
  have hcapA := capsCheck_sound _ p.aside p.acaps
    (fun x => A (z:ℝ) (p.rho:ℝ) (d.first.measure+d.second.measure) x-(c.source.theta:ℝ)) hac
    (by
      intro i hi hok
      obtain ⟨hn0,hn1,hn2⟩ := pattern_nodes p.aside 1 4 ((p.aside.check_parts _ 1 4 has).1) i hi
      unfold atomGapCapOK at hok
      split at hok
      · rename_i bp bq hbp hbq
        have hg := atomGapIntegral_le (c.sourceAt p.rho) c.logs (simpleR z d (c.sourceAt p.rho) c.aux) (z:ℝ)
          (p.rho:ℝ) (c.source.theta:ℝ) (d.Y:ℝ) d.first.measure d.second.measure ((c.sourceAt p.rho).y0:ℝ)
          (rrQ (c.sourceAt p.rho):ℝ) c.aux.KA (f2R d) lkA d.data.dual hσ p.aIds
          ((qListPoly (atomXList d c.source.y0 c.aux.sm c.aux.KA)).map (algebraMap ℚ ℝ))
          (fun x => (hornerR_reverse _ x).symm) c.aux.qAI _ hqAIF
          (fun x => by
            have h := hornerR_reverse (qListIntegral (atomXList d c.source.y0 c.aux.sm c.aux.KA)) x
            unfold hornerR at h
            rw [h,qListIntegral_map])
          _ _ hn0 hn1 hn2 bp bq hbp hbq
        have hq := of_decide_eq_true hok
        have hq2 : (((bq.2:ℚ)/(S:ℚ)-(bp.1:ℚ)/(S:ℚ)+((c.sourceAt p.rho).globalA:ℚ)/(S:ℚ)*
            (p.aside.pat.node (i+1)-p.aside.pat.node i):ℚ):ℝ) ≤ ((p.acaps.getD i 0:ℚ):ℝ) := by
          exact_mod_cast hq
        rw [dec_eq_ratCast,dec_eq_ratCast,dec_eq_ratCast] at hg
        push_cast at hq2 hg
        linarith
      · simp at hok)
  have hA := ASide.penalty (c.sourceAt p.rho) c.logs (simpleR z d (c.sourceAt p.rho) c.aux) (z:ℝ) (p.rho:ℝ)
    (c.source.theta:ℝ) (d.Y:ℝ) d.first.measure d.second.measure _ _ c.aux.KA (f2R d) lkA p.aside has hfA
    (fun i => p.acaps.getD i 0) hcapA p.TA hTA
  -- assemble
  rw [hσ] at hI ⊢
  rw [hσ] at htail
  exact simple_dual_ge (z:ℝ) (p.rho:ℝ) (c.source.theta:ℝ) (d.first.measure+d.second.measure) d.Y c.cutoff
    (by exact_mod_cast (latticeShapeCheck_parts d hsh).1.le) h1'.2.2.2 c.Iup c.TW c.TR p.TA p.lower
    c.source.theta rfl c.terms hI hcont hW (hR.trans hTR2) htail hA hsc

end
end CatalanCore.Li2.DecayCert.Simple
