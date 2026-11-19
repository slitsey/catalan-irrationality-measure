module
public import CatalanCore.Li2.DecayCert.TableFinal
public import CatalanCore.Li2.NVMod.Data.AllConstants12
/-! The irrationality measure of Li₂(a/b): the decay table and the nonvanishing certificates, both checked. -/
@[expose] public section
namespace CatalanCore.Li2
open CatalanCore.Li2.Uniform

/-- **Irrationality measure of Li₂(a/b).** For coprime `a, b` with `0 < 2|a| ≤ b`, every decay candidate
`D` of the node table at `(sign a, log(b/|a|), ρ)` with `η = D + c(a,b) > 0` gives the measure
`μ > ρ·max(2/η, 39/98)`: for all large `q` and all `p`, `q^(-μ) < |Li₂(a/b) − p/q|`. -/
theorem li2_measure_general (a b : ℤ) (hb : 0<b) (hab : IsCoprime a b) (ha : a≠0) (h2 : 2*|a|≤b)
    (ρ D μ : ℝ) (hρ : 0<ρ)
    (hD : Candidate nodeTable (Int.sign a) (Real.log ((b:ℝ)/|(a:ℝ)|)) ρ D)
    (hη : 0<D+cRate a b) (hμ : ρ*max (2/(D+cRate a b)) (39/98)<μ) :
    ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,(q:ℝ)^(-μ)<
      |(∑' k : ℕ,((a:ℝ)/b)^(k+1)/((k:ℝ)+1)^2)-(p:ℝ)/q| :=
  DecayCert.TableFinal.li2_measure_of_table a b hb hab ha h2 ρ D μ hρ hD hη hμ NVMod.Data.AllConstants12.checked

#print axioms li2_measure_general
end CatalanCore.Li2
