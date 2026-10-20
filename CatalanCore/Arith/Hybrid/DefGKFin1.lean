module

public import CatalanCore.Arith.Hybrid.DefGKVec1

@[expose] public section

/-!
# GK, class 1: the defect rows and columns `L = C - αA`, `L' = B - Aβ` (`hL`, `hL'` of `tcore_vec`)
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid.GK1

open CatalanCore.Arith.Hybrid

section Fin1

variable {o p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

/-- Row partners (zone rows `r + 2i`). -/
noncomputable abbrev alphaM (Fr : Frame) (p r m : ℕ) : Matrix (Fin m) (Fin r) ℚ[X] :=
  GKGen.alphaMG (avec p r) m

/-- Column partners (zone columns `r + 2j + 1`). -/
noncomputable abbrev betaM (Fr : Frame) (p r m : ℕ) : Matrix (Fin r) (Fin m) ℚ[X] :=
  GKGen.betaMG (avec p r) m

lemma avec_int (h13 : 13 ≤ p) (hp : p ≠ 1009) (u : ℕ) (c : Fin r) : Int1 p (C (avec p r u c)) :=
  int1_C_of_good (good_avec h13 hp u c)

theorem hL_bound (hL : LamData Fr o) (S : GKS1 o p r m k) (i : Fin m) (c : Fin r) :
    gn p (((Matrix.of (fullEntry Fr r m)).toBlocks₂₁ - alphaM Fr p r m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) i c) ≤ p :=
  GKGen.hL_boundG (avec p r) (fun u c => avec_int S.p13 S.h1009 u c)
    (fun u hu1 hu2 c => lbnd hL S hu1 hu2 c) i c

theorem hL'_bound (hL : LamData Fr o) (S : GKS1 o p r m k) (c : Fin r) (j : Fin m) :
    gn p (((Matrix.of (fullEntry Fr r m)).toBlocks₁₂ - (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ *
        betaM Fr p r m) c j) ≤ p :=
  GKGen.hL'_boundG (avec p r) (fun u c => avec_int S.p13 S.h1009 u c)
    (fun u hu1 hu2 c => lbnd hL S hu1 hu2 c) c j

end Fin1

end CatalanCore.Arith.Hybrid.GK1
