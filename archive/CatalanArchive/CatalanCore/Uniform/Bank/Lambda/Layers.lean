import CatalanCore.Uniform.Bank.Lambda.ContentAt
import CatalanCore.Uniform.Content.ClearMin
set_option Elab.async false

/-! A parameterized list of certified per-prime prices. The unconditional fallback
is retained; appending a layer (including future UF) changes only the minimum.
Fixed exceptional primes use their full crude exponent, never zero. -/
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.BankShared

structure CertifiedPrice (Fam : PolyFamily) where
  price : Fam.ι → ℕ → ℕ
  gle : ∀ i, Fam.Adm i → ∀ (p : ℕ) [Fact p.Prime], GLE p (price i p) (Fam.Q i)

namespace CertifiedPrice
variable {Fam : PolyFamily}

def minPrice (base : CertifiedPrice Fam) : List (CertifiedPrice Fam) → Fam.ι → ℕ → ℕ
  | [], i, p => base.price i p
  | L :: ls, i, p => min (L.price i p) (minPrice base ls i p)

theorem minPrice_gle (base : CertifiedPrice Fam) (ls : List (CertifiedPrice Fam))
    (i : Fam.ι) (hi : Fam.Adm i) (p : ℕ) [Fact p.Prime] :
    GLE p (minPrice base ls i p) (Fam.Q i) := by
  induction ls with
  | nil => exact base.gle i hi p
  | cons L ls ih => exact CatalanCore.Uniform.Content.gle_min (L.gle i hi p) ih

theorem minPrice_le_base (base : CertifiedPrice Fam) (ls : List (CertifiedPrice Fam))
    (i : Fam.ι) (p : ℕ) : minPrice base ls i p ≤ base.price i p := by
  induction ls with
  | nil => exact le_rfl
  | cons L ls ih => exact (min_le_right _ _).trans ih

theorem minPrice_le_member (base : CertifiedPrice Fam) (ls : List (CertifiedPrice Fam))
    (L : CertifiedPrice Fam) (hL : L ∈ ls) (i : Fam.ι) (p : ℕ) :
    minPrice base ls i p ≤ L.price i p := by
  induction ls with
  | nil => simp at hL
  | cons K ls ih =>
    simp only [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hL)

theorem minPrice_append (base : CertifiedPrice Fam) (xs ys : List (CertifiedPrice Fam))
    (i : Fam.ι) (p : ℕ) :
    minPrice base (xs ++ ys) i p = min (minPrice base xs i p) (minPrice base ys i p) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, minPrice]
    exact (min_eq_right (minPrice_le_base base ys i p)).symm
  | cons L xs ih =>
    simp only [List.cons_append, minPrice, ih, min_assoc]

def withExceptions (M cE : ℕ) (sc : Fam.ι → ℕ) (base : CertifiedPrice Fam)
    (ls : List (CertifiedPrice Fam)) (i : Fam.ι) (p : ℕ) : ℕ :=
  if p ∣ M then Ecrude cE (sc i) p else minPrice base ls i p

theorem withExceptions_gle (M cE : ℕ) (sc : Fam.ι → ℕ) (base : CertifiedPrice Fam)
    (ls : List (CertifiedPrice Fam))
    (hcrude : ∀ i, Fam.Adm i → ∀ (p : ℕ) [Fact p.Prime], p ∣ M →
      GLE p (Ecrude cE (sc i) p) (Fam.Q i))
    (i : Fam.ι) (hi : Fam.Adm i) (p : ℕ) [Fact p.Prime] :
    GLE p (withExceptions M cE sc base ls i p) (Fam.Q i) := by
  unfold withExceptions
  split_ifs with h
  · exact hcrude i hi p h
  · exact minPrice_gle base ls i hi p

theorem withExceptions_eq_crude (M cE : ℕ) (sc : Fam.ι → ℕ)
    (base : CertifiedPrice Fam) (ls : List (CertifiedPrice Fam)) (i : Fam.ι)
    (p : ℕ) (hp : p ∣ M) :
    withExceptions M cE sc base ls i p = Ecrude cE (sc i) p := by
  simp only [withExceptions, if_pos hp]

end CertifiedPrice
#print axioms CertifiedPrice.minPrice_gle
#print axioms CertifiedPrice.minPrice_append
#print axioms CertifiedPrice.withExceptions_gle
end CatalanCore.Uniform.Bank.Lambda
