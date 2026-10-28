module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MData
@[expose] public section
set_option Elab.async false

/-!
# Theorem M: the instance `mixedInst` and the banked `theoremMLB'`

`mixedInst` is a `MixedMData P N p (mCount P N p)` built from the real atoms; the only
hypotheses are the window conditions `MWin P N p` and `p ∉ {2, 3}`.
`theorem_M_inst` / `theoremMInstLB` are `theorem_M_bound` / `theoremMLB` with these discharged.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The `C`-type conditions `α`: digit `a = 2` covectors of blocks `J = 0, 1`. -/
def mAlpha (p H : ℕ) [Fact p.Prime] : (Fin 3 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p) :=
  LinearMap.pi fun J : Fin 2 => psiLin p 3 0 H (J : ℕ) 2

/-- The mixed-class `C` part `β`: digit `a = 3` covectors of blocks `J = 1, 2`. -/
def mBeta (p H : ℕ) [Fact p.Prime] : (Fin 3 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p) :=
  LinearMap.pi fun J : Fin 2 => psiLin p 3 0 H ((J : ℕ) + 1) 3

/-- The chosen injection `F_p^{mCount} → ker holeMap`. -/
def phiOf (P : Parameters) (N p : ℕ) [Fact p.Prime] :
    (Fin (mCount P N p) → ZMod p) →ₗ[ZMod p] (Fin (R0 P N p) → ZMod p) :=
  Classical.choose (exists_phi (P := P) (N := N) (p := p))

theorem phiOf_inj : Function.Injective (phiOf P N p) :=
  (Classical.choose_spec (exists_phi (P := P) (N := N) (p := p))).1

theorem phiOf_hole (y : Fin (mCount P N p) → ZMod p) : holeMap P N p (phiOf P N p y) = 0 :=
  (Classical.choose_spec (exists_phi (P := P) (N := N) (p := p))).2 y

/-- First component of the profiles. -/
def fstV {m : ℕ} (V : Submodule (ZMod p) ((Fin 3 → ZMod p) × (Fin 2 → ZMod p))) :
    (Fin m → V) →ₗ[ZMod p] (Fin m → (Fin 3 → ZMod p)) :=
  LinearMap.pi fun a => ((LinearMap.fst (ZMod p) (Fin 3 → ZMod p) (Fin 2 → ZMod p)).comp
    V.subtype).comp (LinearMap.proj a)

/-- Second component of the profiles. -/
def sndV {m : ℕ} (V : Submodule (ZMod p) ((Fin 3 → ZMod p) × (Fin 2 → ZMod p))) :
    (Fin m → V) →ₗ[ZMod p] (Fin m → (Fin 2 → ZMod p)) :=
  LinearMap.pi fun a => ((LinearMap.snd (ZMod p) (Fin 3 → ZMod p) (Fin 2 → ZMod p)).comp
    V.subtype).comp (LinearMap.proj a)

theorem sum_range_ext {M mn : ℕ} (hmn : mn ≤ M) (f : ℕ → ZMod p) :
    ∑ e ∈ Finset.range mn, f e = ∑ e ∈ Finset.range M, if e < mn then f e else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

section Inst
variable (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hH : P.H N < p ^ 2)
  (hW : MWin P N p)

theorem mn_h0 (hP : Admissible P) (hN : 0 < N) : 0 < P.h N :=
  Nat.mul_pos hP.2.2.2.1 hN

/-- The atom map of Theorem M. -/
def mIota (hp2 : p ≠ 2) (h0 : 0 < P.h N) (hW : MWin P N p)
    (V : Submodule (ZMod p) ((Fin 3 → ZMod p) × (Fin 2 → ZMod p))) :
    (Fin (mCount P N p) → V) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  (cTheta P N p hp2 3 0 (R0 P N p) 0).comp ((tens (phiOf P N p)).comp (fstV V)) +
    (hTheta P N p hp2 h0 hW.hh (min_le_right (P.H N - 3 * p) (P.h N)) 2 (R0 P N p) 0).comp
      ((tens (phiOf P N p)).comp (sndV V))

theorem ker_comps (H : ℕ) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {v : (Fin 3 → ZMod p) × (Fin 2 → ZMod p)}
    (hv : v ∈ LinearMap.ker (mixedMap (mAlpha p H) (mBeta p H) (gammaH p H))) :
    mAlpha p H v.1 = 0 ∧ mBeta p H v.1 + gammaH p H v.2 = 0 := by
  have h := LinearMap.mem_ker.mp hv
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end Inst

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
