module
public import CatalanMeasure.GenD.Uniform.W.Prof.Count
@[expose] public section
set_option Elab.async false

/-!
# Discharging `Ident.cover` from a row-combination identity

`Ident.cover` asks that every seen covector `ψ(J,a) ∘ emb` vanishes on `ker (B_g|V_p)`.  It
follows from a rational identity: the coordinates of `ψ(J,a)` are a combination of the stored
chart rows (mod `p`).  This is the shape of the chart-identification obligation; the lemma
below is the only place the linear algebra of it is used.
-/

namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- A covector whose coordinates are a combination of the chart rows vanishes on the chart kernel. -/
theorem vanish_of_comb (pk : Packet) (ch : Chart) (K : ℕ)
    (ψ : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p) (μ : Fin ch.rows.length → ZMod p)
    (h : ∀ k : Fin K, ψ (Pi.single k 1) = ∑ r, μ r * chartMat ch p K r k)
    (y : Fin pk.d → ZMod p) (hy : chartMap pk ch p K y = 0) : ψ (emb pk p K y) = 0 := by
  set z := emb pk p K y with hz
  have hz0 : chartLin ch p K z = 0 := hy
  have hψ : ψ z = ∑ k, z k * ψ (Pi.single k 1) := by
    conv_lhs => rw [show z = ∑ k, z k • (Pi.single k 1 : Fin K → ZMod p) from by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, map_smul]
  rw [hψ]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  have hr := congrFun hz0 r
  simp only [chartLin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] at hr
  calc ∑ k, z k * (μ r * chartMat ch p K r k) = μ r * ∑ k, chartMat ch p K r k * z k := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ = 0 := by rw [hr, mul_zero]

end
end CatalanMeasure.GenD.Uniform.W.Prof
