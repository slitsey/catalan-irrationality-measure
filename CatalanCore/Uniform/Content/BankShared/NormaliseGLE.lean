module

public import CatalanCore.Uniform.Content.BankShared.Normalise
public import CatalanCore.Arith.Hybrid.Tropical

@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content.BankShared
open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid

/-- A unit normalization preserves the exact prime clearing exponent. -/
theorem gle_normalised_poly (p : ℕ) [Fact p.Prime] (e h : ℕ) (f : ℚ[X]) (N : ℚ)
    (hN : N ∈ LocRing p) (hi : N⁻¹ ∈ LocRing p) (hf : GLE p e f) :
    GLE p e (C ((N⁻¹) ^ h) * f.comp (C N * X)) := by
  intro i
  rw [Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
  have hm := (LocRing p).mul_mem ((LocRing p).pow_mem hi h)
    ((LocRing p).mul_mem (hf i) ((LocRing p).pow_mem hN i))
  convert hm using 1 <;> ring

/-- The shared polynomial identity transports GLE on every actual node-family member. -/
theorem normalisation_gle (Fr Fr0 : Frame) (G : NodeFamily) (i : G.Index)
    (p : ℕ) [Fact p.Prime] (e : ℕ) (N : ℚ) (hN0 : N ≠ 0)
    (hMn : ∀ a b, Fr.Mn a b = N⁻¹ * Fr0.Mn a b)
    (hN : N ∈ LocRing p) (hi : N⁻¹ ∈ LocRing p)
    (hf : GLE p e (G.polynomial Fr0 i)) : GLE p e (G.polynomial Fr i) := by
  rw [normalisation_poly Fr Fr0 G i hN0 hMn]
  exact gle_normalised_poly p e _ _ N hN hi hf

#print axioms gle_normalised_poly
#print axioms normalisation_gle
end CatalanCore.Uniform.Content.BankShared
