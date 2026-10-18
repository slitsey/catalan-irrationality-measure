module

public import CatalanCore.ThmA.Intertwine
public import CatalanCore.Linalg.Krylov

/-!
# Definitions for Theorem A at `θ = 0`

* `Nmat F K s = C_s C_sᵀ` (the `K × K` Gram-type matrix `N_s = ∑_{y=1}^{s} c_y c_yᵀ`),
* `wvec F K s = c_{s+1}`,
* `uK F K s = u(K, s) = det [w, N_s w, …, N_s^{K-1} w]`.
-/

@[expose] public section

namespace CatalanCore.ThmA

/-- `N_s = C_s C_sᵀ`. -/
def Nmat (F : Type*) [Field F] (K s : ℕ) : Matrix (Fin K) (Fin K) F :=
  Cmat F K s * (Cmat F K s).transpose

/-- `w = c_{s+1}`, `c_y = (1/(a+y))_{a<K}`. -/
def wvec (F : Type*) [Field F] (K s : ℕ) : Fin K → F :=
  fun a => 1 / (((a : ℕ) : F) + (s : F) + 1)

/-- `u(K, s)`, the Krylov determinant of Theorem A. -/
def uK (F : Type*) [Field F] (K s : ℕ) : F := kdet (Nmat F K s) (wvec F K s)

end CatalanCore.ThmA
