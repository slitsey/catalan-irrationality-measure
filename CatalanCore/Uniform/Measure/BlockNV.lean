module
public import CatalanCore.Uniform.Measure.Block
public import CatalanCore.Uniform.Frame.NVAdapter
@[expose] public section

namespace CatalanCore.Uniform.BlockGeom

/-- Content and all-minor analytic decay now suffice: characteristic-zero
selection is proved for the same complete fixed-depth family. -/
theorem measure_of_content_and_minors (G : BlockGeom) (Fr : Frame) (L depth : ℕ)
    (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hC : ∀ i, (G.common.block i).d ∣ L)
    (hX : ∀ i, (G.row.block i).d ∣ L)
    (hY : ∀ i, (G.column.block i).d ∣ L)
    (hdepth : G.selectionDepth Fr L ≤ depth)
    {Λ D c : ℝ}
    (hΛ : HasCoefficientContent (G.family Fr depth) G.scale Λ)
    (hminor : NodeFamily.HasAllMinorDecay G.geometry Fr D c)
    (hη : Λ < D) (hc : 0 < c) :
    (G.family Fr depth).MeasureLB ((G.common.mass : ℝ) * c / (D - Λ)) :=
  G.measure_of_providers Fr depth hΛ hminor
    (G.hasNV0 Fr L depth hL hd hw hC hX hY hdepth) hη hc

theorem irrational_of_content_and_minors (G : BlockGeom) (Fr : Frame) (L depth : ℕ)
    (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hC : ∀ i, (G.common.block i).d ∣ L)
    (hX : ∀ i, (G.row.block i).d ∣ L)
    (hY : ∀ i, (G.column.block i).d ∣ L)
    (hdepth : G.selectionDepth Fr L ≤ depth)
    {Λ D c : ℝ}
    (hΛ : HasCoefficientContent (G.family Fr depth) G.scale Λ)
    (hminor : NodeFamily.HasAllMinorDecay G.geometry Fr D c)
    (hη : Λ < D) (hc : 0 < c) : Irrational Fr.const :=
  G.irrational_of_providers Fr depth hΛ hminor
    (G.hasNV0 Fr L depth hL hd hw hC hX hY hdepth) hη hc

#print axioms measure_of_content_and_minors
#print axioms irrational_of_content_and_minors
end CatalanCore.Uniform.BlockGeom
