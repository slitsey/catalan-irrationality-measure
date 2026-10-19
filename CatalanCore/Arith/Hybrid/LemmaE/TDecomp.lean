module

public import CatalanCore.Arith.Hybrid.LemmaE.BlockScale

@[expose] public section

/-!
# The partner decomposition of the scaled Schur complement (DN §3c)

For partner maps `cz, cy : κ → ι` (the partner of the row node `z` is the clean node `cz z`, that
of the column node `y` is `cy y`) and `A N = N A = g • 1`:

  `g D - C N B = g (D - Sr B - C Sc + Sr A Sc) - L N L'`,

where `L = C - Sr A`, `L' = B - A Sc` are the *defect* blocks (`ℓ_z`, `ℓ'_y`) and the first
bracket is the second difference `Δ²R`.  Pure algebra over a commutative ring.
-/

open Polynomial Matrix

namespace CatalanCore.Arith.Hybrid.LemmaE

section

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- Row selection `Sr z c = [c = cz z]`. -/
def selR (cz : κ → ι) : Matrix κ ι R := Matrix.of fun z c => if c = cz z then 1 else 0

/-- Column selection `Sc c y = [c = cy y]`. -/
def selC (cy : κ → ι) : Matrix ι κ R := Matrix.of fun c y => if c = cy y then 1 else 0

lemma selR_mul (cz : κ → ι) (M : Matrix ι κ R) (z : κ) (y : κ) :
    ((selR cz : Matrix κ ι R) * M) z y = M (cz z) y := by
  simp [selR, Matrix.mul_apply]

lemma mul_selC (cy : κ → ι) (M : Matrix κ ι R) (z : κ) (y : κ) :
    (M * (selC cy : Matrix ι κ R)) z y = M z (cy y) := by
  simp [selC, Matrix.mul_apply]

lemma selR_mul' (cz : κ → ι) (M : Matrix ι ι R) (z : κ) (c : ι) :
    ((selR cz : Matrix κ ι R) * M) z c = M (cz z) c := by
  simp [selR, Matrix.mul_apply]

/-- The defect row block. -/
def defL (A : Matrix ι ι R) (C : Matrix κ ι R) (cz : κ → ι) : Matrix κ ι R :=
  C - (selR cz : Matrix κ ι R) * A

/-- The defect column block. -/
def defR (A : Matrix ι ι R) (B : Matrix ι κ R) (cy : κ → ι) : Matrix ι κ R :=
  B - A * (selC cy : Matrix ι κ R)

theorem T_decomp (A N : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R) (D : Matrix κ κ R)
    (g : R) (hAN : A * N = g • 1) (hNA : N * A = g • 1) (cz cy : κ → ι) :
    g • D - C * N * B =
      g • (D - (selR cz : Matrix κ ι R) * B - C * (selC cy : Matrix ι κ R) +
          (selR cz : Matrix κ ι R) * A * (selC cy : Matrix ι κ R))
        - defL A C cz * N * defR A B cy := by
  unfold defL defR
  set Sr : Matrix κ ι R := selR cz
  set Sc : Matrix ι κ R := selC cy
  have e1 : C * N * (A * Sc) = g • (C * Sc) := by
    rw [Matrix.mul_assoc C N, ← Matrix.mul_assoc N A, hNA]; simp
  have e2 : Sr * A * N * B = g • (Sr * B) := by
    rw [Matrix.mul_assoc Sr A N, hAN]; simp
  have e3 : Sr * A * N * (A * Sc) = g • (Sr * A * Sc) := by
    rw [Matrix.mul_assoc (Sr * A) N, ← Matrix.mul_assoc N A, hNA]; simp
  simp only [Matrix.sub_mul, Matrix.mul_sub, e1, e2, e3, smul_sub, smul_add]
  abel

end

end CatalanCore.Arith.Hybrid.LemmaE
