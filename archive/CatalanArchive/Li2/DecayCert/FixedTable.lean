module
public import CatalanCore.Li2.Uniform.FixedTable
public import CatalanCore.Li2.Root
public import CatalanArchive.Li2.DecayCert.FixedTable.Assembly
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert

theorem decay_certs_to_scaled (a b : ℤ) (hb : 0<b) (hab : IsCoprime a b)
    (ha : a≠0) (h2 : 2*|a|≤b) (ρ D : ℝ) (hρ : 0<ρ)
    (hD : CatalanCore.Li2.IsDlowCandidate (Int.sign a) (Real.log ((b:ℝ)/|(a:ℝ)|)) ρ D)
    (cert : DecayCertificates CatalanCore.Li2.Uniform.nodeTable) :
    CatalanCore.Uniform.HasScaledDecay (CatalanCore.Li2.li2Family ((a:ℚ)/b)) CatalanCore.Li2.scale D ρ := by
  exact CatalanCore.Li2.decay_certs_to_scaled CatalanCore.Li2.Uniform.nodeTable a b hb hab ha h2 ρ D hρ
    (CatalanCore.Li2.public_candidate hD) cert
#print axioms decay_certs_to_scaled
end CatalanCore.Li2.DecayCert
