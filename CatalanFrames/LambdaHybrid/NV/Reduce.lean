module

public import CatalanFrames.LambdaHybrid.NV.Schur
public import CatalanCore.Rect.Geometry
public import CatalanCore.NV.ReductionGeometry

/-!
# Generic mod-`ℓ` reduction of `Full(x)` for a hybrid geometry (DO Prop 1.3, frame-generic)

Everything here is parametrised by a `Frame` `Fr`, a prime `ℓ` and a threshold `K` (the first
`ℓ`-singular node index: `4K - 1 = ℓ` for λ).  The frame/prime-class specific input is packaged
in `ModData Fr ℓ K`: the node-level `ℓ`-integrality of the `Dq`-scaled entries with their
reductions, the low block `A`, and the harmonic identity `A = κ (W_all W_allᵀ + h)` (DO Lemma 1.2
at `h = ℓ`).  The λ values are supplied by `NV/LamData.lean`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

export CatalanCore.NV (Dq)

/-- Frame/prime-class data for the mod-`ℓ` reduction. `t`: cross coefficient, `d`: high diagonal,
`κ`: harmonic scale, `h`: harmonic constant. -/
structure ModData (Fr : Frame) (ℓ K : ℕ) [Fact ℓ.Prime] where
  t : ZMod ℓ
  d : ZMod ℓ
  κ : ZMod ℓ
  h : ZMod ℓ
  A : Matrix (Fin K) (Fin K) (ZMod ℓ)
  ht : t ≠ 0
  hd : d ≠ 0
  hκ : κ ≠ 0
  htk : t * t = -d * κ
  low : ∀ (a a' : Fin K) {e : ℚ} {eb : ZMod ℓ}, Good ℓ e eb →
    Good ℓ (Dq ℓ K a * Dq ℓ K a' * (e + Fr.Mn a a')) (eb + A a a')
  lh : ∀ p q : ℕ, p < K → K ≤ q → q < ℓ →
    Good ℓ (Dq ℓ K p * Dq ℓ K q * (0 + Fr.Mn p q)) (-(t * (1 / ((p : ZMod ℓ) - q))))
  hl : ∀ p q : ℕ, K ≤ p → p < ℓ → q < K →
    Good ℓ (Dq ℓ K p * Dq ℓ K q * (0 + Fr.Mn p q)) (-(t * (1 / ((q : ZMod ℓ) - p))))
  hhOff : ∀ p q : ℕ, K ≤ p → p < ℓ → K ≤ q → q < ℓ → p ≠ q →
    Good ℓ (Dq ℓ K p * Dq ℓ K q * (0 + Fr.Mn p q)) 0
  hhDiag : ∀ p : ℕ, K ≤ p → p < ℓ → ∀ {e : ℚ} {eb : ZMod ℓ}, Good ℓ e eb →
    Good ℓ (Dq ℓ K p * Dq ℓ K p * (e + Fr.Mn p p)) (-d)
  harm : ∀ a a' : Fin K, A a a' = κ * ((if a = a' then h else 0) +
    ∑ n ∈ Ico K ℓ, (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))

export CatalanCore.NV
  (HiC Wnode WC WX WY Gcols eLow eIdx full_ll full_lr full_rl full_rr xs_mem ys_mem)


section YGood

variable {ℓ K : ℕ} [Fact ℓ.Prime]

/-- row node / column node of the `FullN` index. -/
noncomputable def rn (G : Geometry) : G.C ⊕ Fin G.k → ℕ := Sum.elim (fun a : G.C => (a : ℕ)) G.xs
noncomputable def cn (G : Geometry) : G.C ⊕ Fin G.k → ℕ := Sum.elim (fun a : G.C => (a : ℕ)) G.ys

/-- the negated, `D`-scaled hybrid matrix. -/
noncomputable def Ncell (Fr : Frame) (ℓ K : ℕ) (G : Geometry) (x : ℚ) :
    Matrix (G.C ⊕ Fin G.k) (G.C ⊕ Fin G.k) ℚ :=
  Matrix.of fun i j => -(Dq ℓ K (rn G i) * Dq ℓ K (cn G j) * G.Full Fr x i j)



end YGood

end CatalanFrames.LambdaHybrid.NV
