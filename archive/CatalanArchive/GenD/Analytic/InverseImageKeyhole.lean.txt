module

public import CatalanMeasure.GenD.Analytic.NodalKeyhole
public import CatalanMeasure.GenD.Signed.Davis.InverseImageWeights

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial Finset Set OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

/-- Sharp branch-certified inverse-image hW producer for a subunit keyhole.
Circle/segment Phi bounds are the only numerical analytic inputs. -/
theorem inverseImage_hW_of_phi (P : Parameters) (hg : P.g0 ≤ P.n0)
    (hdpos : 0 < P.n0 - P.g0) (hn0 : 0 < P.n0) (hPQ : 0 < P.h0 + P.q0)
    {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hdeg : p.natDegree = m) (hm : 0 < m)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ω : ℝ → ℝ)
    (hcirc : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = r →
      nodalPhi P (nodalGreen p m) κ z ≤ (P.n0 : ℝ) * ω κ)
    (hseg : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 →
      nodalPhi P (nodalGreen p m) κ (x : ℂ) ≤ (P.n0 : ℝ) * ω κ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ k : ℕ, k < P.n N → ∀ i : Fin ((P.n0 - P.g0) * N),
        |(rowCommonFactor P N).eval (inverseQuadratureNodes P cert hm N i)| *
          |restrictedWeight P N k (inverseQuadratureNodes P cert hm N) i| ≤
          C0 * (N : ℝ) ^ (2 * m + 1) *
            Real.exp ((P.n N : ℝ) * ω ((k : ℝ) / P.n N)) := by
  obtain ⟨d, hd, hder⟩ := cert.exists_derivative_lower hdeg hm
  obtain ⟨A, hA, hcardinal⟩ := uniform_retained_cardinal_green_bound p hm
    (P.n0 - P.g0) (m - 1) m hd (by norm_num : (0 : ℝ) ≤ 1)
  apply nodal_hW_of_cardinal_and_phi P hg hn0 (inverseQuadratureNodes P cert hm)
    (nodalGreen p m) hr0 hr1 hA.le (2 * m) ω _ hcirc hseg
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hN
  let J := (P.n0 - P.g0) * N
  let K := inverseImageDegree J m
  let S := K * m - J
  let τ := paddedInverseNodes cert hm J
  let H := inverseImagePolynomial p K
  let c := H.leadingCoeff
  have hJ : 0 < J := Nat.mul_pos hdpos hN
  have hK : 0 < K := inverseImageDegree_pos hJ hm
  have hS : S ≤ m - 1 := by
    have ht := inverseImageSurplus_lt J hm
    dsimp only [S, K]
    omega
  have hτ : Function.Injective τ := paddedInverseNodes_injective cert hm J
  have hmem : ∀ i, τ i ∈ Ioo (-1 : ℝ) 1 :=
    fun i => (paddedInverseNodes_support cert hm J i).1
  have hH : H = C c * ∏ i : Fin (J + S), (X - C (τ i)) := by
    have horig := inverseImagePolynomial_factorization cert hdeg hm hK
    have hprod := Fintype.prod_equiv (finCongr (inverseImageCount_split J hm))
      (fun i : Fin (J + S) => X - C (τ i))
      (fun i : Fin (K * m) => X - C (inverseImageNodes cert K i)) (fun i => rfl)
    change H = C c * _ at horig
    rw [← hprod] at horig
    exact horig
  have hfullDer : ∀ i, d ≤ |H.derivative.eval (τ i)| :=
    fun i => inverseImagePolynomial_derivative_uniform cert hd hder hK _
  have hceil : m * K ≤ J + m := by
    have hb := (inverseImageDegree_bounds J hm).2
    dsimp only [K]
    rw [Nat.mul_comm m]
    omega
  refine ⟨inverseQuadratureNodes_injective P cert hm N, ?_, ?_⟩
  · have he : P.h N + P.q N = (P.h0 + P.q0) * N := by
      simp only [Parameters.h, Parameters.q]
      ring
    rw [he]
    exact Nat.mul_pos hPQ hN
  · intro i z hz
    have ht := hcardinal N K S τ c hN hS hτ hmem hceil hH hfullDer z hz i
    have hm1 : m - 1 + 1 = m := by omega
    simpa only [hm1, inverseQuadratureNodes, τ, J] using ht

theorem inverseImage_binom_hweights_of_phi (P : Parameters) (hg : P.g0 ≤ P.n0)
    (hdpos : 0 < P.n0 - P.g0) (hn0 : 0 < P.n0) (hPQ : 0 < P.h0 + P.q0)
    {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hdeg : p.natDegree = m) (hm : 0 < m)
    {r Ψ w : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ω : ℝ → ℝ)
    (hcirc : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = r →
      nodalPhi P (nodalGreen p m) κ z ≤ (P.n0 : ℝ) * ω κ)
    (hseg : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 →
      nodalPhi P (nodalGreen p m) κ (x : ℂ) ≤ (P.n0 : ℝ) * ω κ)
    (hΨ : ∀ κ ∈ Icc (0 : ℝ) 1, ω κ + binomRate κ ≤ Ψ)
    (hw : (P.n0 : ℝ) * Ψ < w) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ p m : ℕ, p + m = P.n N →
      ∀ k : ℕ, k < P.n N → ∀ i : Fin ((P.n0 - P.g0) * N),
        |(rowCommonFactor P N).eval (inverseQuadratureNodes P cert hm N i)| *
          |restrictedWeight P N k (inverseQuadratureNodes P cert hm N) i| *
          (CatalanMeasure.binomBeta p m k : ℝ) ≤ 108000 * (N : ℝ) * Real.exp (w * N) := by
  obtain ⟨C0, hC0, hW⟩ := inverseImage_hW_of_phi P hg hdpos hn0 hPQ cert hdeg hm hr0 hr1 ω hcirc hseg
  exact binom_hweights_of_column_bound P (inverseQuadratureNodes P cert hm)
    (2 * m + 1) ω hC0 hW hΨ hw

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.inverseImage_hW_of_phi

#print axioms CatalanMeasure.GenD.Analytic.inverseImage_binom_hweights_of_phi
