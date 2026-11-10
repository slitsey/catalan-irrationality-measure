module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Orbit
public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodTranslation
public import CatalanCore.Uniform.Content.BankShared.Check.Prefix
public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck

@[expose] public section
set_option Elab.async false

/-! Generic catalogue tags keep checked seed data separate from transport proofs.
Finite selections retain their original suppliers; all translated suppliers are explicit. -/
namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Content.UFSimple

inductive CatalogueOrbitLaw (C : List KBranch) where
  | constant (indices : List (Fin C.length))
  | d1x
  | pre (ν j0 j1 : ℕ)
  | wrap (ν : ℕ) (hν : 1≤ν)

def CatalogueOrbitLaw.palette {C : List KBranch} (idx : ℕ) : CatalogueOrbitLaw C → List KBranch
  | .constant indices => indices.map (fun i => C[i.val]'i.isLt)
  | .d1x => [kbD1xB]
  | .pre ν j0 j1 => [(brPre ν j0 j1).liftK idx]
  | .wrap ν _ => [(WrapPrefixCheck.brPrefix ν).liftK idx]

def CatalogueOrbitLaw.shiftB {C : List KBranch} (b : ℕ) : CatalogueOrbitLaw C → ℕ
  | .constant _ => 0
  | _ => b

def CatalogueOrbitLaw.shiftA {C : List KBranch} (a : ℕ) : CatalogueOrbitLaw C → ℕ
  | .constant _ => 0
  | _ => a

def CatalogueOrbitLaw.shiftK {C : List KBranch} (b a : ℕ) : CatalogueOrbitLaw C → ℕ
  | .constant _ => 0
  | _ => 2*b+2*a

def CatalogueOrbitLaw.Allowed {C : List KBranch} (V : List KBranch → Prop) (idx : ℕ) :
    CatalogueOrbitLaw C → Prop
  | .constant _ => V C
  | .d1x => V [kbD1xB]
  | .pre _ j0 j1 => ∀ ν', V [(brPre ν' j0 j1).liftK idx]
  | .wrap _ _ => ∀ ν', 1≤ν' → V [(WrapPrefixCheck.brPrefix ν').liftK idx]

structure CatalogueSeed (C : List KBranch) where
  law : CatalogueOrbitLaw C
  base : QPiece × Cert
  N : ℕ
  times : List ℕ

def CatalogueSeed.toSeed {C : List KBranch} (b a Ω : ℕ) (S : CatalogueSeed C) : OrbitSeed where
  base := S.base
  b := S.law.shiftB b
  a := S.law.shiftA a
  Kc := S.law.shiftK b a
  Ω := Ω
  N := S.N
  times := S.times

def CatalogueSeed.pieces {C : List KBranch} (b a Ω cF : ℕ) (S : CatalogueSeed C) :
    List (QPiece × Cert) := (S.toSeed b a Ω).pieces cF

def catalogueHead {C : List KBranch} (b a Ω cF : ℕ) (seeds : List (CatalogueSeed C)) :
    List (QPiece × Cert) :=
  (seeds.flatMap (CatalogueSeed.pieces b a Ω cF)).mergeSort (fun x y => decide (x.1.s≤y.1.s))

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.catalogueHead
