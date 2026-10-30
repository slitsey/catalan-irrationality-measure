import CatalanCore.Uniform.Bank.Lambda.Frame
import CatalanCore.Uniform.Bank.Lambda.Crude
import CatalanCore.Uniform.Content.BankShared.LeastPrice
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Content.BankShared

/-- A single clearing exponent for every template; crude clearing proves existence. -/
noncomputable def lambdaPrice (sgn : Bool) (depth : ℕ)
    (i : (FL.family (lambdaFrame sgn) depth).ι) (p : ℕ) : ℕ :=
  if hr : i.1 % 2 = 0 then
    if hp : p.Prime then
      @leastGLE p ⟨hp⟩ ((FL.family (lambdaFrame sgn) depth).Q i)
        ⟨Ecrude (cFr (lambdaFrame sgn)) i.1 p,
          @altGeom_gle_Ecrude (1 / 5) one_fifth_pos (by norm_num) (lambdaFrame sgn)
            depth i hr p ⟨hp⟩⟩
    else 0
  else 0

theorem lambdaPrice_gle (sgn : Bool) (depth : ℕ)
    (i : (FL.family (lambdaFrame sgn) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] :
    GLE p (lambdaPrice sgn depth i p) ((FL.family (lambdaFrame sgn) depth).Q i) := by
  unfold lambdaPrice
  rw [dif_pos hr, dif_pos (Fact.out : p.Prime)]
  exact leastGLE_valid _ _ _

theorem lambdaPrice_le (sgn : Bool) (depth : ℕ)
    (i : (FL.family (lambdaFrame sgn) depth).ι) (hr : i.1 % 2 = 0)
    (p e : ℕ) [Fact p.Prime]
    (he : GLE p e ((FL.family (lambdaFrame sgn) depth).Q i)) :
    lambdaPrice sgn depth i p ≤ e := by
  unfold lambdaPrice
  rw [dif_pos hr, dif_pos (Fact.out : p.Prime)]
  exact leastGLE_le _ _ _ e he

theorem lambdaPrice_crude (sgn : Bool) (depth : ℕ)
    (i : (FL.family (lambdaFrame sgn) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] :
    lambdaPrice sgn depth i p ≤ Ecrude (cFr (lambdaFrame sgn)) i.1 p :=
  lambdaPrice_le sgn depth i hr p _
    (altGeom_gle_Ecrude (1 / 5) one_fifth_pos (by norm_num) (lambdaFrame sgn) depth i hr p)

/-- Every concrete rank/LP/M3/tropical supplier bounds this same price. -/
theorem lambdaPrice_le_supplier (sgn : Bool) (depth : ℕ)
    (i : (FL.family (lambdaFrame sgn) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] (U : ℚ)
    (h : ∃ n : ℕ, GLE p n ((FL.family (lambdaFrame sgn) depth).Q i) ∧ (n : ℚ) ≤ U) :
    (lambdaPrice sgn depth i p : ℚ) ≤ U := by
  obtain ⟨n, hn, hb⟩ := h
  exact (show (lambdaPrice sgn depth i p : ℚ) ≤ n by
    exact_mod_cast lambdaPrice_le sgn depth i hr p n hn).trans hb

noncomputable def lambdaCut (sgn : Bool) (depth : ℕ)
    (i : (FL.family (lambdaFrame sgn) depth).ι) : ℕ :=
  max (coefficientCut ((FL.family (lambdaFrame sgn) depth).Q i)) (6 * i.1 + 1)

theorem lambdaPrice_zero_ge (sgn : Bool) (depth : ℕ)
    (i : (FL.family (lambdaFrame sgn) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] (hp : lambdaCut sgn depth i ≤ p) :
    lambdaPrice sgn depth i p = 0 := by
  have hc : coefficientCut ((FL.family (lambdaFrame sgn) depth).Q i) ≤ p :=
    (le_max_left _ _).trans hp
  have he := lambdaPrice_le sgn depth i hr p 0 (gle_zero_of_coefficientCut p _ hc)
  omega

/-- A certified base for the existing parameterized ClearMin layer list. -/
noncomputable def lambdaCertifiedPrice (sgn : Bool) (depth : ℕ) :
    CertifiedPrice (FamE (lambdaFrame sgn) depth) where
  price := lambdaPrice sgn depth
  gle i hi p := lambdaPrice_gle sgn depth i hi.2 p

#print axioms lambdaPrice_gle
#print axioms lambdaPrice_crude
#print axioms lambdaPrice_le_supplier
end CatalanCore.Uniform.Bank.Lambda