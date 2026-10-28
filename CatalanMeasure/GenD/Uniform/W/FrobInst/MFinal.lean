module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MKill
@[expose] public section
set_option Elab.async false

/-!
# Theorem M with every instance hypothesis discharged

* `mixedInst`      : a genuine `MixedMData P N p (mCount P N p)` for any design in the window `MWin`
                     and `p ∉ {2, 3}`;
* `theorem_M_inst` : `mCount P N p ≤ nullity P N p` (adds `p ≠ 1291` for the rank of `gammaQ`);
* `theoremMInstLB` : the banked `NullityLB`, with only `MWin`, `p ∉ {3, 1291}` left.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem mIota_injective (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hW : MWin P N p)
    (V : Submodule (ZMod p) ((Fin 3 → ZMod p) × (Fin 2 → ZMod p)))
    (hfst : Function.Injective ((LinearMap.fst (ZMod p) (Fin 3 → ZMod p) (Fin 2 → ZMod p)).comp
      V.subtype)) : Function.Injective (mIota hp2 (mn_h0 hP hN) hW V) := by
  refine injective_of_zero _ fun x hx => ?_
  have hrows : ∀ r, tRows P N p 3 (0 + R0 P N p) 0
      (prof hp2 3 0 (R0 P N p) (tens (phiOf P N p) (fstV V x))) r +
      hRows P N p 2 ((p - 1) / 2 + 1) 0
        (hprof hp2 (mn_h0 hP hN) hW.hh (min_le_right (P.H N - 3 * p) (P.h N)) 2 (R0 P N p)
          (tens (phiOf P N p) (sndV V x))) r = 0 := by
    intro r
    have := congrFun hx r
    simpa [mIota, cTheta, hTheta] using this
  have h1 := prof_eq_zero_of_rows hp2 hW _ _ hrows
  have h2 : tens (phiOf P N p) (fstV V x) = 0 :=
    prof_injective hp2 3 0 (R0 P N p) (by rw [h1, map_zero])
  have h3 : fstV V x = 0 := tens_injective _ phiOf_inj _ h2
  funext a
  apply hfst
  have := congrFun h3 a
  simpa [fstV] using this

/-- **Theorem M instance.** -/
def mixedInst (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hH : P.H N < p ^ 2) (hW : MWin P N p) : MixedMData P N p (mCount P N p) where
  α := mAlpha p (P.H N)
  β := mBeta p (P.H N)
  Γ := gammaH p (P.H N)
  hΓ := gammaH_eq_residue hp2 hp3 (by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have := hW.h3
    omega)
  ι := fun V => mIota hp2 (mn_h0 hP hN) hW V
  inj := fun V _ hfst => mIota_injective hP hN hp2 hW V hfst
  killed := fun V hV x => by
    refine ⟨0, ?_, fun j h1 h2 => ?_⟩
    · have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
      simpa using hq
    · rw [Polynomial.eval_zero]
      exact uResp_mIota_eq_zero hP hN hp2 hp3 hH hW V hV x h1 h2

/-- **Theorem M, discharged.** -/
theorem theorem_M_inst (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp1291 : p ≠ 1291) (hH : P.H N < p ^ 2) (hW : MWin P N p) :
    mCount P N p ≤ nullity P N p :=
  theorem_M_bound hp2 hp3 hp1291 hH (mixedInst hP hN hp2 hp3 hH hW)

/-- The banked `NullityLB` of Theorem M: only the window conditions and `p ∉ {3, 1291}` remain. -/
def theoremMInstLB (P : Parameters) (hP : Admissible P) (App : ℕ → ℕ → Prop)
    (hApp : ∀ N p : ℕ, 0 < N → p.Prime → p ≠ 2 → P.H N < p ^ 2 → App N p →
      p ≠ 3 ∧ p ≠ 1291 ∧ MWin P N p) : NullityLB P :=
  theoremMLB P App fun N p hN hp hp2 hH hA => by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨h3, h1291, hW⟩ := hApp N p hN hp hp2 hH hA
    exact ⟨h3, h1291, ⟨mixedInst hP hN hp2 h3 hH hW⟩⟩

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
