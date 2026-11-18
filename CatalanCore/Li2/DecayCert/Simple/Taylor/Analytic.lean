module
public import CatalanCore.Li2.DecayCert.Compile.Regular
public import CatalanCore.Li2.DecayCert.RealCells.Elementary
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Set
namespace CatalanCore.Li2.DecayCert.Simple
noncomputable section

def xlogError (a r : ℚ) (J : ℕ) : ℚ :=
  a*(r/a)^(J+1)/((J+1:ℚ)*J*(1-r/a))

def xlogModel (a r : ℚ) (J terms : ℕ) : CompiledModel :=
  ⟨(List.range (J+1)).map (xlogScalarCoeff a 1 terms),seRat (xlogError a r J)⟩

theorem xlogModel_compile (a r : ℚ) (J terms : ℕ) (hJ : 2≤J) (hr : 0≤r) (ha : r<a) :
    regularCompile (.xlog a 1) (-r) r ⟨J,terms,0,0,0,0⟩=some (xlogModel a r J terms) := by
  have ha0 : 0<a := hr.trans_lt ha
  have hrr : -r≤r := by linarith
  simp [regularCompile,hJ,ha0,hrr,ha,abs_of_nonneg hr,xlogModel,xlogError,xlogScalarCoeff]

theorem xlogModel_sound (a r : ℚ) (J terms : ℕ) (hJ : 2≤J) (hr : 0≤r) (ha : r<a) :
    Models (fun u : ℝ=>xlog ((a:ℝ)+u))
      ((xlogModel a r J terms).coeff.map ScalarExpr.value) (r:ℝ) (xlogError a r J:ℝ) := by
  have hm := regularCompile_xlog_sound a 1 (-r) r ⟨J,terms,0,0,0,0⟩ _
    (xlogModel_compile a r J terms hJ hr ha)
  have he : (xlogModel a r J terms).error.value=(xlogError a r J:ℝ) := by rfl
  rw [he] at hm
  refine ⟨by exact_mod_cast hr,hm.2.1,?_⟩
  intro u hu
  have hu' : u∈Icc ((-r:ℚ):ℝ) (r:ℝ) := by
    constructor
    · rw [Rat.cast_neg]
      exact (abs_le.mp hu).1
    · exact (abs_le.mp hu).2
  simpa only [CellExpr.value,Rat.cast_one,one_mul,xlog] using hm.2.2 u hu'

theorem xlogModel_coeff (a r : ℚ) (J terms : ℕ) (j : ℕ) (hj : j<J+1) :
    (seGet (xlogModel a r J terms).coeff j).value=
      if j=0 then (a:ℝ)*Real.log (a:ℝ)
      else if j=1 then Real.log (a:ℝ)+1
      else (((-1:ℚ)^j/((j:ℚ)*(j-1)*a^(j-1)):ℚ):ℝ) := by
  have he : seGet (xlogModel a r J terms).coeff j=xlogScalarCoeff a 1 terms j := by
    simp [xlogModel,seGet,hj]
  rw [he]
  by_cases h0 : j=0
  · subst j
    simp [xlogScalarCoeff,seScale_value,ScalarExpr.value]
  by_cases h1 : j=1
  · subst j
    simp [xlogScalarCoeff,h0,seScale_value,seAdd_value,seRat_value,ScalarExpr.value]
  simp [xlogScalarCoeff,h0,h1,seRat_value]

theorem negative_xlog_hull (alpha h u : ℝ) (halpha : 0≤alpha) (hh : 0<h)
    (hsmall : h≤Real.exp (-1)) (hu : u∈Icc 0 h) :
    -alpha*xlog u∈Icc 0 (-alpha*xlog h) := by
  have hx := xlogx_hull h u hh hsmall hu
  exact ⟨mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr halpha) hx.2,
    mul_le_mul_of_nonpos_left hx.1 (neg_nonpos.mpr halpha)⟩

theorem endpoint_hull_model (alpha h : ℝ) (halpha : 0≤alpha) (hh : 0<h)
    (hsmall : h≤Real.exp (-1)) :
    ModelsOn (fun u=>-alpha*xlog u) [-alpha*xlog h/2] 0 h (-alpha*xlog h/2) := by
  have hcap := negative_xlog_hull alpha h h halpha hh hsmall ⟨hh.le,le_rfl⟩
  refine ⟨hh.le,by linarith [hcap.1],?_⟩
  intro u hu
  have hx := negative_xlog_hull alpha h u halpha hh hsmall hu
  have he : evalModel [-alpha*xlog h/2] u=-alpha*xlog h/2 := by simp [evalModel]
  rw [he]
  exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
#print axioms xlogModel_sound
#print axioms xlogModel_coeff
#print axioms endpoint_hull_model
end
end CatalanCore.Li2.DecayCert.Simple
