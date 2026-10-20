module

public import CatalanCore.NV.ReductionGeometry

@[expose] public section

/-! # Generic node-level residue data

The data contract is independent of any particular frame instance or harmonic
reduction proof.  Nodes in a geometry may use any finite common set below T.
-/
open Finset Matrix CatalanCore CatalanCore.Rect
namespace CatalanCore.NV

/-- Frame/prime-class data for the three-level reduction.  Nodes `< T` only occur in geometries. -/
structure ModData3 (Fr : Frame) (ℓ K T : ℕ) [Fact ℓ.Prime] where
  t : ZMod ℓ
  d : ZMod ℓ
  κ : ZMod ℓ
  h : ZMod ℓ
  τ₀ : ZMod ℓ
  A : Matrix (Fin K) (Fin K) (ZMod ℓ)
  ht : t ≠ 0
  hd : d ≠ 0
  hκ : κ ≠ 0
  hτ : τ₀ ≠ 0
  htk : t * t = -d * κ
  low : ∀ (a a' : Fin K) {e : ℚ} {eb : ZMod ℓ}, Good ℓ e eb →
    Good ℓ (Dq ℓ K a * Dq ℓ K a' * (e + Fr.Mn a a')) (eb + A a a')
  lh : ∀ p q : ℕ, p < K → K ≤ q → q < T →
    Good ℓ (Dq ℓ K p * Dq ℓ K q * (0 + Fr.Mn p q)) (-(t * (1 / ((p : ZMod ℓ) - q))))
  hl : ∀ p q : ℕ, K ≤ p → p < T → q < K →
    Good ℓ (Dq ℓ K p * Dq ℓ K q * (0 + Fr.Mn p q)) (-(t * (1 / ((q : ZMod ℓ) - p))))
  hhOff : ∀ p q : ℕ, K ≤ p → p < T → K ≤ q → q < T → p ≠ q →
    Good ℓ (Dq ℓ K p * Dq ℓ K q * (0 + Fr.Mn p q)) 0
  hhDiag : ∀ p : ℕ, K ≤ p → p < T → ∀ {e : ℚ} {eb : ZMod ℓ}, Good ℓ e eb →
    Good ℓ (Dq ℓ K p * Dq ℓ K p * (e + Fr.Mn p p)) (-d)
  harm : ∀ a a' : Fin K, A a a' = κ * ((if a = a' then h else 0) +
      ∑ n ∈ Ico K T, (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n))) +
    τ₀ * ∑ n ∈ Ico T ℓ, (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n))

end CatalanCore.NV
