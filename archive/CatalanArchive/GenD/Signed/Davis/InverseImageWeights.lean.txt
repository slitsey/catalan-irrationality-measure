module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/InverseImageWeights.lean
Original SHA256: 8747471adcc4e5f64c0b9e6d73332e20a58345a97b14471e19c6e8eb3f3216b5
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.GeneralNodalWeights
public import CatalanMeasure.GenD.Signed.Davis.NodalRootDeletion
public import CatalanMeasure.GenD.Signed.Davis.InverseImageCircle

@[expose] public section

/-!
# Inverse-image quadrature weight contract

This file assembles the inverse branches, the ceiling degree, deletion of a
bounded number of roots, and the coefficient-functional estimate. Its output
is precisely the `GapWeightBounds` contract consumed by the existing weighted
atom determinant argument. The word `Gap` in that existing contract imposes
no symmetry requirement.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Finset Set OAI.InternalCatalan CatalanMeasure.Parametric

noncomputable section

theorem inverseImageCount_split (J : ℕ) {m : ℕ} (hm : 0 < m) :
    J + (inverseImageDegree J m * m - J) = inverseImageDegree J m * m := by
  have hlow := (inverseImageDegree_bounds J hm).1
  omega

def paddedInverseNodes {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hm : 0 < m) (J : ℕ) :
    Fin (J + (inverseImageDegree J m * m - J)) → ℝ :=
  fun i => inverseImageNodes cert (inverseImageDegree J m)
    (Fin.cast (inverseImageCount_split J hm) i)

theorem paddedInverseNodes_injective {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hm : 0 < m) (J : ℕ) :
    Function.Injective (paddedInverseNodes cert hm J) :=
  (inverseImageNodes_injective cert _).comp (finCongr (inverseImageCount_split J hm)).injective

theorem paddedInverseNodes_support {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hm : 0 < m) (J : ℕ)
    (i : Fin (J + (inverseImageDegree J m * m - J))) :
    paddedInverseNodes cert hm J i ∈ Ioo (-1 : ℝ) 1 ∧
      paddedInverseNodes cert hm J i ≠ 0 ∧ G (paddedInverseNodes cert hm J i) :=
  inverseImageNodes_support cert _ _

def inverseQuadratureNodes (P : Parameters) {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hm : 0 < m) (N : ℕ) :
    Fin ((P.n0 - P.g0) * N) → ℝ :=
  retainedNodes (paddedInverseNodes cert hm ((P.n0 - P.g0) * N))

theorem inverseQuadratureNodes_injective (P : Parameters)
    {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hm : 0 < m) (N : ℕ) :
    Function.Injective (inverseQuadratureNodes P cert hm N) :=
  retainedNodes_injective (paddedInverseNodes_injective cert hm _)

theorem inverseQuadratureNodes_support (P : Parameters)
    {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hm : 0 < m) (N : ℕ)
    (i : Fin ((P.n0 - P.g0) * N)) :
    inverseQuadratureNodes P cert hm N i ∈ Ioo (-1 : ℝ) 1 ∧
      inverseQuadratureNodes P cert hm N i ≠ 0 ∧
      G (inverseQuadratureNodes P cert hm N i) :=
  paddedInverseNodes_support cert hm _ _

/-- The complete generic inverse-image quadrature theorem. All numerical
content is isolated in the branch certificate, the polynomial degree, and
the two fixed-circle hypotheses. -/
theorem inverseImage_weight_bounds (P : Parameters) (hg : P.g0 ≤ P.n0)
    (hdpos : 0 < P.n0 - P.g0)
    {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hdeg : p.natDegree = m) (hm : 0 < m)
    {radius C wc w : ℝ} (hr1 : 1 < radius) (hr2 : radius ≤ 2) (hw : wc < w)
    (hC : ∀ z : ℂ, ‖z‖ = radius →
      2 * ‖(p.map (algebraMap ℝ ℂ)).eval z‖ + 1 ≤ C)
    (hcert : ∀ z : ℂ, ‖z‖ = radius →
      (2 * ‖(p.map (algebraMap ℝ ℂ)).eval z‖ + 1) ^ (P.n0 - P.g0) *
        ‖(1 : ℂ) - z‖ ^ ((P.h0 + P.q0) * m) ≤ Real.exp ((m : ℝ) * wc)) :
    GapWeightBounds P (inverseQuadratureNodes P cert hm) w := by
  obtain ⟨d, hd, hder⟩ := cert.exists_derivative_lower hdeg hm
  apply general_nodal_weight_bounds P hg (inverseQuadratureNodes P cert hm)
    (d := d / 2 ^ (m - 1)) (B := C / (radius - 1) ^ (m - 1))
    (wc := wc) hr1 (by positivity) hw
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
    have hSlt := inverseImageSurplus_lt J hm
    dsimp only [S, K]
    omega
  have hτ : Function.Injective τ := paddedInverseNodes_injective cert hm J
  have hmem : ∀ i, τ i ∈ Ioo (-1 : ℝ) 1 :=
    fun i => (paddedInverseNodes_support cert hm J i).1
  have hzero : ∀ i, τ i ≠ 0 :=
    fun i => (paddedInverseNodes_support cert hm J i).2.1
  have hH : H = Polynomial.C c * ∏ i : Fin (J + S), (X - Polynomial.C (τ i)) := by
    have horig := inverseImagePolynomial_factorization cert hdeg hm hK
    have hprod := Fintype.prod_equiv (finCongr (inverseImageCount_split J hm))
      (fun i : Fin (J + S) => X - Polynomial.C (τ i))
      (fun i : Fin (K * m) => X - Polynomial.C (inverseImageNodes cert K i))
      (fun i => rfl)
    change H = Polynomial.C c * _ at horig
    rw [← hprod] at horig
    exact horig
  have hfullDer : ∀ i, d ≤ |(derivative H).eval (τ i)| :=
    fun i => inverseImagePolynomial_derivative_uniform cert hd hder hK _
  have hfullCirc : ∀ z : ℂ, ‖z‖ = radius →
      ‖(H.map (algebraMap ℝ ℂ)).eval z‖ *
        ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) ≤ C * Real.exp (wc * N) := by
    intro z hz
    have hceil : K * m ≤ (P.n0 - P.g0) * N + m := by
      have hb := (inverseImageDegree_bounds J hm).2
      dsimp only [K, J] at hb ⊢
      omega
    have hfilter : P.h N + P.q N = (P.h0 + P.q0) * N := by
      simp only [Parameters.h, Parameters.q]
      ring
    rw [hfilter]
    exact inverseImagePolynomial_circle_le hm hceil hC hcert z hz
  refine ⟨inverseQuadratureNodes_injective P cert hm N,
    (fun i => (inverseQuadratureNodes_support P cert hm N i).1),
    (fun i => (inverseQuadratureNodes_support P cert hm N i).2.1),
    retainedNodal τ c, c, rfl, ?_, ?_⟩
  · intro i
    exact retainedNodal_derivative_ge hmem hS hH hfullDer i
  · intro z hz
    have hh := retainedNodal_circle_le hmem hS hH hr1 hr2 hfullCirc z hz
    calc
      _ ≤ C * Real.exp (wc * N) / (radius - 1) ^ (m - 1) := hh
      _ = C / (radius - 1) ^ (m - 1) * Real.exp (wc * N) := by ring

end
end Analytic
end CatalanMeasure.GenD

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.GenD.Analytic.inverseImageCount_split
#print axioms CatalanMeasure.GenD.Analytic.paddedInverseNodes
#print axioms CatalanMeasure.GenD.Analytic.paddedInverseNodes_injective
#print axioms CatalanMeasure.GenD.Analytic.paddedInverseNodes_support
#print axioms CatalanMeasure.GenD.Analytic.inverseQuadratureNodes
#print axioms CatalanMeasure.GenD.Analytic.inverseQuadratureNodes_injective
#print axioms CatalanMeasure.GenD.Analytic.inverseQuadratureNodes_support
#print axioms CatalanMeasure.GenD.Analytic.inverseImage_weight_bounds
