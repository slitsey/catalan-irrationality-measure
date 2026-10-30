module
public import CatalanMeasure.GenD.Uniform.Prefix.RawResponseWindow
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset OAI.InternalCatalan
noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

def integerPhi (K J : ℕ) (S : ℤ) (a b : ℤ[X]) : ℚ :=
  (∑ v∈range (K+1),((intrinsicCoeff a (S+1-v):ℤ):ℚ)*momentRatSigned ((v:ℤ)-1) J)-
    (3/2:ℚ)*(∑ v∈range K,((intrinsicCoeff b (S-v):ℤ):ℚ)*zetaRat v J)

def integerPsi (K ah J : ℕ) (S : ℤ) (a b : ℤ[X]) : ℚ :=
  integerPhi K J S (a*(X-1)^ah) (b*(X-1)^ah)

theorem intrinsicCoeff_map_integer (a : ℤ[X]) (S : ℤ) :
    intrinsicCoeff (a.map (Int.castRingHom Fp)) S=((intrinsicCoeff a S:ℤ):Fp) := by
  by_cases hs : 0≤S <;> simp [intrinsicCoeff,hs,coeff_map]

/-- A concrete rational Phi reduces to the actual source covector, provided
EVERY displayed individual moment denominator is a unit first. -/
theorem integerPhi_residue (K J : ℕ) (S : ℤ) (a b : ℤ[X])
    (hpD : ¬p∣sourceMomentException J K) :
    ((integerPhi K J S a b).den:Fp)≠0 ∧
    palindromicRatResidue p (integerPhi K J S a b)=
      digitPhi K S (sourceM J) (sourceZ J)
        (a.map (Int.castRingHom Fp)) (b.map (Int.castRingHom Fp)) (3/2) := by
  have hu := sourceMoment_units J K hpD
  have hM := palindromicRatResidue_int_sum (p:=p) (range (K+1))
    (fun v => intrinsicCoeff a (S+1-v)) (fun v => momentRatSigned ((v:ℤ)-1) J) (by
      intro v hv
      apply hu
      exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hv)))
  have hZ := palindromicRatResidue_int_sum (p:=p) (range K)
    (fun v => intrinsicCoeff b (S-v)) (fun v => zetaRat v J) (by
      intro v hv
      apply hu
      exact mem_union_right _ (mem_image_of_mem _ hv))
  have h32 : (((3/2:ℚ).den:ℕ):Fp)≠0 := by
    apply hu
    exact mem_union_left _ (mem_union_left _ (mem_singleton_self _))
  have hprod := rational_residue_mul h32 hZ.1
  have hsub := rational_residue_sub hM.1 hprod.1
  refine ⟨hsub.1,?_⟩
  unfold integerPhi
  rw [palindromicRatResidue_sub hM.1 hprod.1,
    palindromicRatResidue_mul h32 hZ.1,hM.2,hZ.2]
  have he : palindromicRatResidue p (3/2:ℚ)=(3/2:Fp) := by
    norm_num [palindromicRatResidue]
  rw [he]
  simp only [digitPhi,sourceM,sourceZ,intrinsicCoeff_map_integer]

/-- Rational, bounded-index Psi covectors with an explicit finite exception
product; this is an actual characteristic-transfer theorem. -/
theorem integerPsi_residue (K ah J : ℕ) (S : ℤ) (a b : ℤ[X])
    (hpD : ¬p∣sourceMomentException J K) :
    ((integerPsi K ah J S a b).den:Fp)≠0 ∧
    palindromicRatResidue p (integerPsi K ah J S a b)=
      sourcePsi K ah J S (a.map (Int.castRingHom Fp)) (b.map (Int.castRingHom Fp)) := by
  have hr := integerPhi_residue K J S (a*(X-1)^ah) (b*(X-1)^ah) hpD
  rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_X,
    Polynomial.map_one,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_X,Polynomial.map_one] at hr
  exact hr
#print axioms integerPhi_residue
#print axioms integerPsi_residue
end
end CatalanMeasure.GenD.Uniform.Prefix

