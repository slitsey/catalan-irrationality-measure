module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Compiled
public import CatalanArchive.Li2.DecayCert.Lattice.Gates.Far
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Stieltjes
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Transport
public import CatalanCore.Li2.DecayCert.Lattice.Shape
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Set Polynomial MeasureTheory
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeGate
open CatalanCore.Li2.Decay BernsteinGrid

def addCompiled (a b : CompiledModel) : CompiledModel :=
  ⟨combineCoeffs a.coeff b.coeff,seAdd a.error b.error⟩
def scaleCompiled (c : ℚ) (a : CompiledModel) : CompiledModel :=
  ⟨a.coeff.map (seScale c),seScale |c| a.error⟩

theorem addCompiled_sound (a b : CompiledModel) (f g : ℝ→ℝ)
    (ha : ModelsOn f (a.coeff.map ScalarExpr.value) (-1) 1 a.error.value)
    (hb : ModelsOn g (b.coeff.map ScalarExpr.value) (-1) 1 b.error.value) :
    ModelsOn (fun t=>f t+g t) ((addCompiled a b).coeff.map ScalarExpr.value)
      (-1) 1 (addCompiled a b).error.value := by
  simpa only [addCompiled,seAdd_value] using ha.add_scalar hb

theorem scaleCompiled_sound (c : ℚ) (a : CompiledModel) (f : ℝ→ℝ)
    (ha : ModelsOn f (a.coeff.map ScalarExpr.value) (-1) 1 a.error.value) :
    ModelsOn (fun t=>(c:ℝ)*f t) ((scaleCompiled c a).coeff.map ScalarExpr.value)
      (-1) 1 (scaleCompiled c a).error.value := by
  simpa only [scaleCompiled,seScale_value,Rat.cast_abs] using ha.scale_scalar c

theorem modelsOn_congr_domain {f g : ℝ→ℝ} {co : List ℝ} {a b E : ℝ}
    (hf : ModelsOn f co a b E) (he : ∀t∈Icc a b,f t=g t) : ModelsOn g co a b E := by
  refine ⟨hf.1,hf.2.1,?_⟩
  intro t ht
  rw [← he t ht]
  exact hf.2.2 t ht

def WBase (terms : ℕ) (z : ℚ) (d : LatticeInput) (p r : ℚ) : CellExpr :=
  .add (fieldExpr terms z (p,0) (r,0)) (.scale 2 (.segment d.first (p,0) (r,0)))

def atomBase (terms : ℕ) (z : ℚ) (d : LatticeInput) (p r : ℚ) : CellExpr :=
  .add (atomExpr terms z [] p r) (.scale 2 (.segment d.second (-p,0) (-r,0)))

noncomputable def WMacroModel (terms : ℕ) (z : ℚ) (d : LatticeInput)
    (p r y0 H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness) : Option CompiledModel := do
  let b ← compileModel (-1) 1 (WBase terms z d p r) base
  pure (addCompiled b (scaleCompiled (-2)
    (affineCompiled (farModel terms (d.second.c 0) mu y0 H p r K J) 0 r)))

noncomputable def WMacroParentCheck (terms : ℕ) (z : ℚ) (d : LatticeInput)
    (p r y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ)) : Bool :=
  decide (0≤p-|r|) && farModelCheck d.second mu y0 L Y H p r K &&
    (match WMacroModel terms z d p r y0 H mu K J base with
     | none=>false | some m=>bernParentCheck S m w boxes)

theorem WBase_positive (terms : ℕ) (z : ℚ) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true) (p r : ℚ) :
    PositiveSources (WBase terms z d p r) := by
  have hp := (datum_source_data d.data dw hd d.first (lattice_first_mem d)).2.2
  simpa [WBase,fieldExpr,exprSum,PositiveSources] using hp

theorem WBase_value (terms : ℕ) (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true) (p r : ℚ) (t : ℝ)
    (hpoint : 0≤(p:ℝ)+(r:ℝ)*t) :
    (WBase terms z d p r).value t-2*U d.second.measure (((p:ℝ)+(r:ℝ)*t:ℝ):ℂ)=
      W (z:ℝ) d.data.dual.σ (((p:ℝ)+(r:ℝ)*t:ℝ):ℂ) := by
  have he := WExpr_value terms z hz d.data dw hd (p,0) (r,0) t
    (by simpa [cqReal] using hpoint) (by simp [cqReal])
  rw [d.source_eq] at he
  simpa [WBase,WExpr,exprSum,CellExpr.value,cqReal,U,ScalarExpr.value,add_assoc] using he

theorem WMacroModel_sound (terms : ℕ) (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (p r y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (hpoint : 0≤p-|r|) (hfar : farModelCheck d.second mu y0 L Y H p r K=true)
    (m : CompiledModel) (hm : WMacroModel terms z d p r y0 H mu K J base=some m) :
    ModelsOn (fun t=>W (z:ℝ) d.data.dual.σ (((p:ℝ)+(r:ℝ)*t:ℝ):ℂ))
      (m.coeff.map ScalarExpr.value) (-1) 1 m.error.value := by
  unfold WMacroModel at hm
  cases hb : compileModel (-1) 1 (WBase terms z d p r) base with
  | none => simp [hb] at hm
  | some b =>
    simp [hb] at hm
    subst m
    have hbase := compileModel_sound (-1) 1 _ base b (by norm_num)
      (WBase_positive terms z d dw hd p r) hb
    simp only [Rat.cast_neg,Rat.cast_one] at hbase
    have hp := (datum_source_data d.data dw hd d.second (lattice_second_mem d)).2.2
    have hsource := farModelCheck_sound terms d.second mu y0 L Y H p r K J hp hfar
    have hparts : realSupportCheck d.second L Y=true ∧ ordinaryMomentCheck d.second y0 K mu=true ∧
        (0≤H ∧ 0≤r ∧ H<p-y0-r ∧ |L-y0|≤H ∧ |Y-y0|≤H) := by
      simpa only [farModelCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hfar
    have haff : affineDomainCheck 0 r r=true := by
      simp [affineDomainCheck,abs_of_nonneg hparts.2.2.2.1]
    have hnorm := affineCompiled_sound _ 0 r r _ hsource haff
    simp only [Rat.cast_zero,zero_add] at hnorm
    have hsum := addCompiled_sound b _ _ _ hbase (scaleCompiled_sound (-2) _ _ hnorm)
    apply modelsOn_congr_domain hsum
    intro t ht
    have hmul : |(r:ℝ)*t|≤|(r:ℝ)| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ht)
    have hnon : 0≤(p:ℝ)+(r:ℝ)*t := by
      have h : (0:ℝ)≤(p:ℝ)-|(r:ℝ)| := by exact_mod_cast hpoint
      linarith [neg_abs_le ((r:ℝ)*t)]
    simpa only [Rat.cast_neg,Rat.cast_ofNat,neg_mul,← sub_eq_add_neg] using
      WBase_value terms z hz d dw hd p r t hnon

theorem WMacroParentCheck_sound (terms : ℕ) (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (p r y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ))
    (hc : WMacroParentCheck terms z d p r y0 L Y H mu K J base S w boxes=true) :
    ModelsOn (fun t=>W (z:ℝ) d.data.dual.σ (((p:ℝ)+(r:ℝ)*t:ℝ):ℂ))
      ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) (-1) 1 w.remainder ∧
    TableEncloses S boxes (canonicalControls (qListPoly (gridCoeffs S w)) (-1) 1 (w.coeff.length-1)) := by
  have hh : (0≤p-|r|) ∧ farModelCheck d.second mu y0 L Y H p r K=true ∧
      (match WMacroModel terms z d p r y0 H mu K J base with
       | none=>false | some m=>bernParentCheck S m w boxes)=true := by
    simpa only [WMacroParentCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc
  cases hm : WMacroModel terms z d p r y0 H mu K J base with
  | none => simp [hm] at hh
  | some m =>
    have hcheck : bernParentCheck S m w boxes=true := by simpa only [hm] using hh.2.2
    exact ⟨(bernParentCheck_sound S m w boxes _
      (WMacroModel_sound terms z hz d dw hd p r y0 L Y H mu K J base hh.1 hh.2.1 m hm) hcheck).1,
      bernParentCheck_table S m w boxes hcheck⟩
#print axioms WBase_value
#print axioms WMacroModel_sound
#print axioms WMacroParentCheck_sound

def stieltjesCenter (d : QSegment) (phi : ℚ) : ℚ :=
  d.mid.1-d.half.1*((phi+phi⁻¹)/2)

noncomputable def atomMacroModel (terms : ℕ) (z : ℚ) (d : LatticeInput)
    (p r phi R : ℚ) (sm : List ℚ) (K : ℕ) (base : ModelWitness) : Option CompiledModel := do
  let b ← compileModel (-1) 1 (atomBase terms z d p r) base
  pure (addCompiled b (scaleCompiled (-2)
    (affineCompiled (stieltjesModel terms d.first phi sm R K)
      (-p-stieltjesCenter d.first phi) (-r))))

noncomputable def atomMacroParentCheck (terms : ℕ) (z : ℚ) (d : LatticeInput)
    (p r phi Y R : ℚ) (sm : List ℚ) (K : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ)) : Bool :=
  decide (1≤p-|r| ∧ p+|r|≤4) && stieltjesModelCheck d.first phi sm Y R K &&
    affineDomainCheck (-p-stieltjesCenter d.first phi) (-r) R &&
    (match atomMacroModel terms z d p r phi R sm K base with
     | none=>false | some m=>bernParentCheck S m w boxes)

theorem atomBase_positive (terms : ℕ) (z : ℚ) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true) (p r : ℚ) :
    PositiveSources (atomBase terms z d p r) := by
  have hp := (datum_source_data d.data dw hd d.second (lattice_second_mem d)).2.2
  simpa [atomBase,atomExpr,exprSum,PositiveSources] using hp

theorem atomBase_value (terms : ℕ) (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true) (p r : ℚ) (t : ℝ)
    (hpoint : (p:ℝ)+(r:ℝ)*t∈Icc 1 4) :
    (atomBase terms z d p r).value t-2*U d.first.measure (-(((p:ℝ)+(r:ℝ)*t:ℝ):ℂ))=
      omega (z:ℝ) ((p:ℝ)+(r:ℝ)*t)-
        2*U d.data.dual.σ (-(((p:ℝ)+(r:ℝ)*t:ℝ):ℂ)) := by
  have he := atomExpr_value terms z hz d.data dw hd p r t hpoint
  rw [d.source_eq] at he
  have heq : cqReal (-p,0)+cqReal (-r,0)*(t:ℂ)=-(((p:ℝ)+(r:ℝ)*t:ℝ):ℂ) := by
    simp [cqReal]
    push_cast
    ring
  simp only [atomBase,atomExpr,exprSum,CellExpr.value,List.map_cons,List.map_nil,
    List.foldl_cons,List.foldl_nil,ScalarExpr.value,Rat.cast_zero,Rat.cast_ofNat,zero_add,heq,U] at he ⊢
  push_cast at he ⊢
  linarith only [he]

theorem atomMacroModel_sound (terms : ℕ) (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (p r phi Y R : ℚ) (sm : List ℚ) (K : ℕ) (base : ModelWitness)
    (hpoint : 1≤p-|r| ∧ p+|r|≤4)
    (hsource : stieltjesModelCheck d.first phi sm Y R K=true)
    (haff : affineDomainCheck (-p-stieltjesCenter d.first phi) (-r) R=true)
    (m : CompiledModel) (hm : atomMacroModel terms z d p r phi R sm K base=some m) :
    ModelsOn (fun t=>omega (z:ℝ) ((p:ℝ)+(r:ℝ)*t)-
      2*U d.data.dual.σ (-(((p:ℝ)+(r:ℝ)*t:ℝ):ℂ)))
      (m.coeff.map ScalarExpr.value) (-1) 1 m.error.value := by
  unfold atomMacroModel at hm
  cases hb : compileModel (-1) 1 (atomBase terms z d p r) base with
  | none => simp [hb] at hm
  | some b =>
    simp [hb] at hm
    subst m
    have hbase := compileModel_sound (-1) 1 _ base b (by norm_num)
      (atomBase_positive terms z d dw hd p r) hb
    simp only [Rat.cast_neg,Rat.cast_one] at hbase
    have hp := (datum_source_data d.data dw hd d.first (lattice_first_mem d)).2.2
    have hs := stieltjesModelCheck_sound terms d.first phi sm Y R K hp hsource
    have hnorm := affineCompiled_sound _ (-p-stieltjesCenter d.first phi) (-r) R _ hs haff
    have hsum := addCompiled_sound b _ _ _ hbase (scaleCompiled_sound (-2) _ _ hnorm)
    apply modelsOn_congr_domain hsum
    intro t ht
    have hmul : |(r:ℝ)*t|≤|(r:ℝ)| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ht)
    have hlo : (1:ℝ)≤(p:ℝ)-|(r:ℝ)| := by exact_mod_cast hpoint.1
    have hhi : (p:ℝ)+|(r:ℝ)|≤4 := by exact_mod_cast hpoint.2
    have hdom : (p:ℝ)+(r:ℝ)*t∈Icc 1 4 := by
      constructor <;>linarith [neg_abs_le ((r:ℝ)*t),le_abs_self ((r:ℝ)*t)]
    have he : (((stieltjesCenter d.first phi:ℚ):ℝ)+
        (((-p-stieltjesCenter d.first phi:ℚ):ℝ)+((-r:ℚ):ℝ)*t):ℝ)=
        -((p:ℝ)+(r:ℝ)*t) := by push_cast;ring
    dsimp only [stieltjesCenter] at he ⊢
    rw [he]
    simpa only [Rat.cast_neg,Rat.cast_ofNat,neg_mul,← sub_eq_add_neg,Complex.ofReal_neg] using
      atomBase_value terms z hz d dw hd p r t hdom

theorem atomMacroParentCheck_sound (terms : ℕ) (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (p r phi Y R : ℚ) (sm : List ℚ) (K : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ))
    (hc : atomMacroParentCheck terms z d p r phi Y R sm K base S w boxes=true) :
    ModelsOn (fun t=>omega (z:ℝ) ((p:ℝ)+(r:ℝ)*t)-
      2*U d.data.dual.σ (-(((p:ℝ)+(r:ℝ)*t:ℝ):ℂ)))
      ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) (-1) 1 w.remainder ∧
    TableEncloses S boxes (canonicalControls (qListPoly (gridCoeffs S w)) (-1) 1 (w.coeff.length-1)) := by
  have hh : (1≤p-|r| ∧ p+|r|≤4) ∧ stieltjesModelCheck d.first phi sm Y R K=true ∧
      affineDomainCheck (-p-stieltjesCenter d.first phi) (-r) R=true ∧
      (match atomMacroModel terms z d p r phi R sm K base with
       | none=>false | some m=>bernParentCheck S m w boxes)=true := by
    simpa only [atomMacroParentCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc
  cases hm : atomMacroModel terms z d p r phi R sm K base with
  | none => simp [hm] at hh
  | some m =>
    have hcheck : bernParentCheck S m w boxes=true := by simpa only [hm] using hh.2.2.2
    exact ⟨(bernParentCheck_sound S m w boxes _
      (atomMacroModel_sound terms z hz d dw hd p r phi Y R sm K base hh.1 hh.2.1 hh.2.2.1 m hm) hcheck).1,
      bernParentCheck_table S m w boxes hcheck⟩
#print axioms atomMacroParentCheck_sound

end CatalanCore.Li2.DecayCert.LatticeGate
