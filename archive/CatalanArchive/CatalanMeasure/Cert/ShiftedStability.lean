module
public import CatalanMeasure.Cert.ShiftedCoverColumn
public import CatalanMeasure.LogFieldStability
public import Mathlib.Analysis.Normed.Group.Bounded
@[expose] public section
namespace CatalanMeasure.Cert
open OAI.InternalCatalan Set Filter Real
open scoped Topology
noncomputable section

theorem shiftedRowField_endpoint_bound {R : RowWeights} {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P=true) (hV : tailsInDisk V=true) (hAlpha : 0 ≤ R.alpha) :
    ∃ K : ℝ,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      shiftedRowField R Pc Vc P V x ≤ (R.beta:ℝ)*Real.log (1-x)+K :=by
  obtain ⟨K,hK⟩ :=isCompact_Icc.exists_bound_of_continuousOn
    (shiftedRowRegular_continuousOn (R :=R) (Pc :=Pc) (Vc :=Vc) hP hV)
  refine ⟨K,?_⟩
  intro x hx
  have hxi : x ∈ Icc (-1:ℝ) 1 :=by
    rcases hx with hx|hx
    · exact ⟨hx.1,by linarith only [hx.2]⟩
    · exact ⟨by linarith only [hx.1],hx.2.le⟩
  have hlog : Real.log |x| ≤ 0 :=Real.log_nonpos (abs_nonneg _) (abs_le.mpr hxi)
  have hterm : (R.alpha:ℝ)*Real.log |x| ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hAlpha) hlog
  have hreg : shiftedRowRegular R Pc Vc P V x ≤ K :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hK x hxi)
  rw [shiftedRowField_split]
  linarith only [hterm,hreg]

/-- A concrete row-field certificate survives all finite diagonal corrections,
    uniformly up to the logarithmic endpoint. -/
theorem shiftedRowField_corrected_eventually {R : RowWeights} {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P=true) (hV : tailsInDisk V=true) (hAlpha : 0 ≤ R.alpha)
    (hBeta : 0<R.beta) {M a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : ∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,shiftedRowField R Pc Vc P V x ≤ M)
    (t : ℕ → ℝ) (ht0 : ∀ N,0 ≤ t N) (ht : Tendsto t atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      shiftedRowField R Pc Vc P V x+t N*(a*Real.log (1+x^2)-b*Real.log (1-x)) ≤ M+ε :=by
  obtain ⟨K,hK⟩ :=shiftedRowField_endpoint_bound hP hV hAlpha
  apply CatalanMeasure.log_field_correction_eventually (by exact_mod_cast hBeta) ha hb
    ?_ hM hK t ht0 ht hε
  intro x hx
  rcases hx with hx|hx
  · exact ⟨hx.1,by linarith only [hx.2]⟩
  · exact ⟨by linarith only [hx.1],hx.2⟩

theorem shiftedColumnField_endpoint_bound {C : ColumnWeights} {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V=true) (hb : 0 ≤ C.b) :
    ∃ K : ℝ,∀ x ∈ Ioo (0:ℝ) 1,
      shiftedColumnField C Vc V x ≤ (C.q:ℝ)*Real.log (1-x)+K :=by
  obtain ⟨K,hK⟩ :=isCompact_Icc.exists_bound_of_continuousOn
    (shiftedColumnRegular_continuousOn (C :=C) (Vc :=Vc) hV)
  refine ⟨K,?_⟩
  intro x hx
  have hlog : Real.log x ≤ 0 :=Real.log_nonpos hx.1.le hx.2.le
  have hterm : (C.b:ℝ)*Real.log x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hb) hlog
  have hreg : shiftedColumnRegular C Vc V x ≤ K :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hK x ⟨hx.1.le,hx.2.le⟩)
  rw [shiftedColumnField_split]
  linarith only [hterm,hreg]

theorem shiftedColumnField_corrected_eventually {C : ColumnWeights} {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V=true) (hb : 0 ≤ C.b) (hq : 0<C.q) {M : ℝ}
    (hM : ∀ x ∈ Ioo (0:ℝ) 1,shiftedColumnField C Vc V x ≤ M)
    (t : ℕ → ℝ) (ht0 : ∀ N,0 ≤ t N) (ht : Tendsto t atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ioo (0:ℝ) 1,
      shiftedColumnField C Vc V x-t N*Real.log (1-x) ≤ M+ε :=by
  obtain ⟨K,hK⟩ :=shiftedColumnField_endpoint_bound hV hb
  have hh :=CatalanMeasure.log_field_correction_eventually
    (by exact_mod_cast hq : (0:ℝ)<C.q) (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) ≤ 1)
    (fun x hx =>⟨by linarith only [hx.1],hx.2⟩) hM hK t ht0 ht hε
  simpa only [zero_mul,one_mul,zero_sub,zero_add,mul_neg,sub_eq_add_neg] using hh

end
end CatalanMeasure.Cert
