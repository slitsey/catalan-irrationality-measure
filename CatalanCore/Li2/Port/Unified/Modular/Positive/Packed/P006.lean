/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Positive/Packed/P006.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P004
public import CatalanCore.Li2.Port.Unified.Modular.Base.PrimeJets

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial CatalanCore.Li2.Port.Li2
namespace CatalanCore.Li2.Port.Unified.Proofs.Hermite
noncomputable section

def generalIndexedJetLocalOrder (n p : ℕ)
    (i : Fin (generalJetSize n p)) (a : Fin p) : ℕ :=
  if a = (generalJetEquiv n p i).1 then (generalJetEquiv n p i).2.val
  else CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.multiplicity n p a

theorem generalIndexedJet_disc_factor (n p : ℕ)
    (i : Fin (generalJetSize n p)) (a : Fin p) :
    ∃ A : ℤ[X], (generalIndexedJetPoly n p i).comp
      (CatalanCore.Li2.Port.Li2.primeDiscSubstitution p a) =
        C ((p : ℤ) ^ (generalIndexedJetLocalOrder n p i a)) *
          X ^ (generalIndexedJetLocalOrder n p i a) * A := by
  by_cases he : a = (generalJetEquiv n p i).1
  · subst a
    obtain ⟨A, hA⟩ := CatalanCore.Li2.Port.Li2.classBasisPoly_own_expansion
      (CatalanCore.Li2.Port.Li2.primeCenter p)
      (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.multiplicity n p)
      (generalJetEquiv n p i).1 (generalJetEquiv n p i).2.val (p : ℤ)
    refine ⟨C ((CatalanCore.Li2.Port.Li2.classProduct (CatalanCore.Li2.Port.Li2.primeCenter p)
      (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.multiplicity n p)
      (generalJetEquiv n p i).1).eval (CatalanCore.Li2.Port.Li2.primeCenter p (generalJetEquiv n p i).1)) +
      C (p : ℤ) * A, ?_⟩
    simpa only [generalIndexedJetPoly, generalJetPoly,
      generalIndexedJetLocalOrder, if_pos rfl, ite_true, CatalanCore.Li2.Port.Li2.primeDiscSubstitution] using! hA
  · obtain ⟨A, hA⟩ := CatalanCore.Li2.Port.Li2.classBasisPoly_other_expansion
      (CatalanCore.Li2.Port.Li2.primeCenter p)
      (CatalanCore.Li2.Port.Unified.Proofs.Hermite.CountsCore.multiplicity n p)
      (generalJetEquiv n p i).1 a (generalJetEquiv n p i).2.val (p : ℤ) he
    refine ⟨A, ?_⟩
    simpa only [generalIndexedJetPoly, generalJetPoly,
      generalIndexedJetLocalOrder, if_neg he, CatalanCore.Li2.Port.Li2.primeDiscSubstitution] using hA

#print axioms generalIndexedJet_disc_factor

end
end CatalanCore.Li2.Port.Unified.Proofs.Hermite

end


end
