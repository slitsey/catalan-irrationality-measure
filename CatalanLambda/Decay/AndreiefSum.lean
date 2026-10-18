module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Sum measures on `α ⊕ β`
-/

open MeasureTheory

namespace CatalanLambda.Decay

section
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma meInl (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : MeasurableEmbedding (Sum.inl : α → α ⊕ β) :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩

lemma meInr (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : MeasurableEmbedding (Sum.inr : β → α ⊕ β) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩

/-- The sum of two measures on `α ⊕ β`. -/
noncomputable def sumM (μ : Measure α) (ν : Measure β) : Measure (α ⊕ β) :=
  μ.map Sum.inl + ν.map Sum.inr

instance (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] :
    SigmaFinite (sumM μ ν) := by
  unfold sumM
  have : SigmaFinite (μ.map Sum.inl) := (meInl α β).sigmaFinite_map
  have : SigmaFinite (ν.map Sum.inr) := (meInr α β).sigmaFinite_map
  infer_instance

lemma integrable_sumM_iff (μ : Measure α) (ν : Measure β) (F : α ⊕ β → ℂ) :
    Integrable F (sumM μ ν) ↔
      Integrable (fun a => F (Sum.inl a)) μ ∧ Integrable (fun b => F (Sum.inr b)) ν := by
  unfold sumM
  rw [integrable_add_measure, (meInl α β).integrable_map_iff,
    (meInr α β).integrable_map_iff]
  rfl

lemma integral_sumM (μ : Measure α) (ν : Measure β) (F : α ⊕ β → ℂ)
    (h : Integrable F (sumM μ ν)) :
    ∫ x, F x ∂(sumM μ ν) = ∫ a, F (Sum.inl a) ∂μ + ∫ b, F (Sum.inr b) ∂ν := by
  unfold sumM at h ⊢
  rw [integrable_add_measure] at h
  rw [integral_add_measure h.1 h.2, (meInl α β).integral_map,
    (meInr α β).integral_map]

end
end CatalanLambda.Decay
