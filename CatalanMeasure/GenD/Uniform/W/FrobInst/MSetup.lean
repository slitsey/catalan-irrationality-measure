module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MClass
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MResp
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MRows
public import CatalanMeasure.GenD.Uniform.W.FrobInst.Gamma4
public import CatalanMeasure.GenD.Uniform.W.FrobInst.CType
public import CatalanMeasure.GenD.Uniform.W.Frob.MixedM
@[expose] public section
set_option Elab.async false

/-!
# Theorem M: design setup

* `R0 = min (g, n-g-2p-1)` : the number of free monomial coordinates `S = Σ s_r y^r`, `P = (y-1)^h S`;
* `MWin` : the window conditions (floor(H/p) = 3, `q`-free, `b ≥ H - 3p`, `L ≤ 3p`, `h ≤ (p-1)/2+1`,
  `R0 ≤ (p-1)/2`, `2p + 1 + g ≤ n`);
* `holeMap` : the `H - 3p - h` hole conditions `P[e] = 0`, `e ∈ [h, eta)`;
* `exists_phi` : an injective linear map `F_p^{mCount} → ker holeMap` (the `dim Poly_adm ≥ mCount`);
* `prof_eq_zero_of_rows` : row-level independence of the `C` coordinates from the `H+` ones.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The number of free monomial coordinates of `S`. -/
abbrev R0 (P : Parameters) (N p : ℕ) : ℕ := min (P.g N) (P.n N - P.g N - 2 * p - 1)

/-- Window conditions of Theorem M. -/
structure MWin (P : Parameters) (N p : ℕ) : Prop where
  h3 : 3 * p ≤ P.H N
  h4 : P.H N < 4 * p
  hb : P.H N ≤ P.b N + 3 * p
  hL : P.L N ≤ 3 * p
  hh : P.h N ≤ (p - 1) / 2 + 1
  hR : R0 P N p ≤ (p - 1) / 2
  hn : 2 * p + 1 + P.g N ≤ P.n N

/-- Slot coefficient `[X^e] 2 (X-1)^h X^r`. -/
def cMat (P : Parameters) (N p e r : ℕ) : ZMod p :=
  2 * ((X - 1) ^ P.h N * X ^ r : (ZMod p)[X]).coeff e

/-- The hole conditions `P[e] = 0`, `e ∈ [h, eta)`, as a linear map on the coordinates of `S`. -/
def holeMap (P : Parameters) (N p : ℕ) [Fact p.Prime] :
    (Fin (R0 P N p) → ZMod p) →ₗ[ZMod p] (Fin (P.H N - 3 * p - P.h N) → ZMod p) :=
  LinearMap.pi fun i => ∑ r : Fin (R0 P N p),
    cMat P N p (P.h N + i) r • (LinearMap.proj r : (Fin (R0 P N p) → ZMod p) →ₗ[ZMod p] ZMod p)

theorem holeMap_apply (s : Fin (R0 P N p) → ZMod p) (i : Fin (P.H N - 3 * p - P.h N)) :
    holeMap P N p s i = ∑ r : Fin (R0 P N p), cMat P N p (P.h N + i) r * s r := by
  simp [holeMap]

/-- `dim Poly_adm ≥ mCount`: an injective linear map from `F_p^{mCount}` into the hole kernel. -/
theorem exists_phi : ∃ φ : (Fin (mCount P N p) → ZMod p) →ₗ[ZMod p] (Fin (R0 P N p) → ZMod p),
    Function.Injective φ ∧ ∀ y, holeMap P N p (φ y) = 0 := by
  classical
  have hW : mCount P N p ≤ finrank (ZMod p) (LinearMap.ker (holeMap P N p)) := by
    have h1 := (holeMap P N p).finrank_range_add_finrank_ker
    have h2 : finrank (ZMod p) (LinearMap.range (holeMap P N p)) ≤ P.H N - 3 * p - P.h N := by
      have := Submodule.finrank_le (LinearMap.range (holeMap P N p))
      simpa [Module.finrank_fin_fun] using this
    rw [Module.finrank_fin_fun] at h1
    have hR0 : R0 P N p = min (P.g N) (P.n N - P.g N - 2 * p - 1) := rfl
    have h1' := h1.trans hR0
    unfold mCount
    omega
  set W := LinearMap.ker (holeMap P N p) with hWdef
  set B := Module.finBasis (ZMod p) W with hB
  set d := finrank (ZMod p) W with hd
  let ext : (Fin (mCount P N p) → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p) :=
    LinearMap.pi fun i => if h : (i : ℕ) < mCount P N p then LinearMap.proj ⟨i, h⟩ else 0
  have hext : ∀ (y : Fin (mCount P N p) → ZMod p) (k : Fin (mCount P N p)),
      ext y ⟨k, by have := k.isLt; omega⟩ = y k := by
    intro y k
    simp [ext]
  refine ⟨W.subtype ∘ₗ B.equivFun.symm.toLinearMap ∘ₗ ext, ?_, ?_⟩
  · intro y y' hy
    have h1 : B.equivFun.symm (ext y) = B.equivFun.symm (ext y') := Subtype.ext hy
    have h2 : ext y = ext y' := B.equivFun.symm.injective h1
    funext k
    rw [← hext y k, ← hext y' k, h2]
  · intro y
    exact LinearMap.mem_ker.mp (B.equivFun.symm (ext y)).2

theorem exists_row (m : ℤ) (h1 : -(P.g N : ℤ) ≤ m) (h2 : m < (P.n N : ℤ) - P.g N) :
    ∃ r : Fin (P.n N), (r : ℤ) - P.g N = m := by
  have hr : (m + P.g N).toNat < P.n N := by omega
  exact ⟨⟨(m + P.g N).toNat, hr⟩, by simp only; omega⟩

theorem MWin.hp_pos (hp3 : 3 ≤ p) : 0 < p := by omega

theorem MWin.cGood (hW : MWin P N p) : FrobGood P N p 3 0 (R0 P N p) 0 := by
  intro k hk
  have hRg : R0 P N p ≤ P.g N := min_le_left _ _
  have hRn : R0 P N p ≤ P.n N - P.g N - 2 * p - 1 := min_le_right _ _
  have hn := hW.hn
  have hRn' : R0 P N p + 2 * p + 1 + P.g N ≤ P.n N := by omega
  generalize R0 P N p = R at *
  have hp1 : (0 : ℤ) < p := by
    have := (Fact.out : p.Prime).pos; exact_mod_cast this
  have hk2 : ((k : ℕ) : ℤ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
  have hk0 : (0 : ℤ) ≤ (k : ℕ) := by positivity
  have hRg' : (R : ℤ) ≤ P.g N := by exact_mod_cast hRg
  have hRn'' : (R : ℤ) + 2 * p + 1 + P.g N ≤ P.n N := by exact_mod_cast hRn'
  constructor
  · push_cast
    nlinarith
  · push_cast
    nlinarith

theorem MWin.hGood (hW : MWin P N p) (hp2 : p ≠ 2) (j : Fin ((p - 1) / 2 + 1)) (k : Fin 2) :
    HGood P N p 0 (j : ℕ) k := by
  have hodd := native_half_identity hp2
  have hj := j.isLt
  have hk := k.isLt
  have hp1 : (0 : ℤ) < p := by
    have := (Fact.out : p.Prime).pos; exact_mod_cast this
  have hk1 : ((k : ℕ) : ℤ) ≤ 1 := by exact_mod_cast (by omega : (k : ℕ) ≤ 1)
  have hk0 : (0 : ℤ) ≤ (k : ℕ) := by positivity
  have hn := hW.hn
  unfold HGood InRange
  push_cast
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
