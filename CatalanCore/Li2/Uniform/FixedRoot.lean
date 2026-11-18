module
public import CatalanCore.Li2.Uniform.FixedTable
public import CatalanCore.Li2.Root
@[expose] public section
set_option Elab.async false
open Filter
namespace CatalanCore.Li2

/-- Fixed structural table specialization. Raw checker records remain explicit. -/
theorem li2_measure_fixed_of_certs
    (a b : ℤ) (hb : 0<b) (hab : IsCoprime a b) (ha : a≠0) (h2 : 2*|a|≤b)
    (ρ D mu : ℝ) (hρ : 0<ρ)
    (hD : IsDlowCandidate (Int.sign a) (Real.log ((b:ℝ)/|(a:ℝ)|)) ρ D)
    (heta : 0<D+cRate a b) (hmu : ρ*max (2/(D+cRate a b)) (39/98)<mu)
    (decayCerts : DecayCert.DecayCertificates Uniform.nodeTable) (nvCerts : NVMod.AllConstantsChecked 12) :
    ∀ᶠ q : ℕ in atTop,∀ p : ℤ,(q:ℝ)^(-mu)<
      |(∑' k : ℕ,((a:ℝ)/b)^(k+1)/((k:ℝ)+1)^2)-(p:ℝ)/q| := by
  exact li2_measure_general_of_certs Uniform.nodeTable a b hb hab ha h2 ρ D mu hρ (public_candidate hD)
    heta hmu decayCerts nvCerts
#print axioms li2_measure_fixed_of_certs
end CatalanCore.Li2
