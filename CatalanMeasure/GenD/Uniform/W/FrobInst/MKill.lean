module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MInst
@[expose] public section
set_option Elab.async false

/-!
# Theorem M: the killing step

`uResp_mIota_eq_zero` : for `V ≤ ker (mixedMap α β Γ)`, every atom `mIota V x` has zero raw
response on all visible columns `j ∈ [b, L)`.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem uResp_mIota_eq_zero (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hH : P.H N < p ^ 2) (hW : MWin P N p)
    (V : Submodule (ZMod p) ((Fin 3 → ZMod p) × (Fin 2 → ZMod p)))
    (hV : V ≤ LinearMap.ker (mixedMap (mAlpha p (P.H N)) (mBeta p (P.H N)) (gammaH p (P.H N))))
    (x : Fin (mCount P N p) → V) {j : ℕ} (hj1 : P.b N ≤ j) (hj2 : j < P.L N) :
    uResp P N p j (mIota hp2 (mn_h0 hP hN) hW V x) = 0 := by
  have hodd := native_half_identity hp2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h0 := mn_h0 hP hN
  have hmn : min (P.H N - 3 * p) (P.h N) ≤ P.h N := min_le_right _ _
  have hhp : P.h N ≤ p := by have := hW.hh; omega
  have hHL : P.H N = P.L N + P.g N + P.h N := by simp [Parameters.H, Parameters.C]
  have hjH : j < P.H N := by omega
  have hRg : R0 P N p ≤ P.g N := min_le_left _ _
  have hhR : P.h N + R0 P N p ≤ p := by have := hW.hh; have := hW.hR; omega
  set φ := phiOf P N p with hφ
  set zC := tens φ (fstV V x) with hzC
  set zH := tens φ (sndV V x) with hzH
  have hc := uResp_tRows (P := P) (N := N) hP hN hp2 hH 0 (prof hp2 3 0 (R0 P N p) zC)
    (fun d k hg => absurd (frobGood_good hW.cGood d k) hg) hjH
  have hh' := uResp_hTheta (P := P) (N := N) hP hN hp2 hH h0 hW.hh hmn hhp 0
    (fun j k => hW.hGood hp2 j k) zH hjH
  have hker : ∀ a, mAlpha p (P.H N) (x a : (Fin 3 → ZMod p) × (Fin 2 → ZMod p)).1 = 0 ∧
      mBeta p (P.H N) (x a : (Fin 3 → ZMod p) × (Fin 2 → ZMod p)).1 +
        gammaH p (P.H N) (x a : (Fin 3 → ZMod p) × (Fin 2 → ZMod p)).2 = 0 :=
    fun a => ker_comps (P.H N) hp2 hp3 (hV (x a).2)
  have hadd : uResp P N p j (mIota hp2 (mn_h0 hP hN) hW V x) =
      uResp P N p j (cTheta P N p hp2 3 0 (R0 P N p) 0 zC) +
        uResp P N p j (hTheta P N p hp2 h0 hW.hh hmn 2 (R0 P N p) 0 zH) := by
    simp only [mIota, LinearMap.add_apply, LinearMap.comp_apply, map_add]
    rfl
  rw [hadd]
  show uResp P N p j (tRows P N p 3 (0 + R0 P N p) 0 (prof hp2 3 0 (R0 P N p) zC)) + _ = 0
  rw [hc, hh', sum_range_ext (M := P.h N + (0 + R0 P N p))
    (mn := min (P.H N - 3 * p) (P.h N)) (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun e he => ?_
  have he' : e < P.h N + R0 P N p := by
    have := Finset.mem_range.mp he; omega
  by_cases hd : (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e
  · have heq : (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e =
        (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) * p := (Int.ediv_mul_cancel hd).symm
    have hcl := class_split (p := p) (H := P.H N) (b := P.b N) (L := P.L N) (g := P.g N)
      (h := P.h N) (R0 := R0 P N p) (j := j) (e := e) _ hp0 hW.h3 hW.h4 hW.hb hW.hL hHL hRg hhR
      hj1 hj2 he' heq
    simp only [if_pos hd]
    rcases hcl with ⟨ha3, hJ, hlt⟩ | ⟨ha2, hJ, hge⟩
    · rw [ha3]
      by_cases hem : e < min (P.H N - 3 * p) (P.h N)
      · rw [if_pos hem, wvec_prof_cMat, wH_cMat, lin_comb φ (psiLin p 3 0 (P.H N) (j / p) 3)
          (fstV V x) e, lin_comb φ (psiLinH p 2 0 (P.H N) (j / p) 3) (sndV V x) e,
          ← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun a _ => ?_
        rw [← mul_add]
        have hk := hker a
        have hz : psiLin p 3 0 (P.H N) (j / p) 3 (fstV V x a) +
            psiLinH p 2 0 (P.H N) (j / p) 3 (sndV V x a) = 0 := by
          show psiLin p 3 0 (P.H N) (j / p) 3 ((x a : (Fin 3 → ZMod p) × (Fin 2 → ZMod p)).1) +
            psiLinH p 2 0 (P.H N) (j / p) 3 ((x a : (Fin 3 → ZMod p) × (Fin 2 → ZMod p)).2) = 0
          rcases hJ with hJ | hJ
          · rw [hJ]
            have := congrFun hk.2 0
            simpa [mBeta, gammaH] using this
          · rw [hJ]
            have := congrFun hk.2 1
            simpa [mBeta, gammaH] using this
        rw [hz, mul_zero]
      · rw [if_neg hem, add_zero, wvec_prof_cMat, lin_comb φ (psiLin p 3 0 (P.H N) (j / p) 3)
          (fstV V x) e]
        refine Finset.sum_eq_zero fun a _ => ?_
        have hq : qco P N p φ a e = 0 := by
          have hlt' : e - P.h N < P.H N - 3 * p - P.h N := by omega
          have h1 := holeMap_apply (P := P) (N := N) (p := p) (φ (Pi.single a 1))
            ⟨e - P.h N, hlt'⟩
          have h2 := phiOf_hole (P := P) (N := N) (p := p) (Pi.single a 1)
          rw [h2] at h1
          have h3 : P.h N + (e - P.h N) = e := by omega
          simp only [h3, Pi.zero_apply] at h1
          rw [qco]
          exact h1.symm
        rw [hq, zero_mul]
    · rw [ha2]
      have hem : ¬ e < min (P.H N - 3 * p) (P.h N) := by
        have := min_le_left (P.H N - 3 * p) (P.h N); omega
      rw [if_neg hem, add_zero, wvec_prof_cMat, lin_comb φ (psiLin p 3 0 (P.H N) (j / p) 2)
        (fstV V x) e]
      refine Finset.sum_eq_zero fun a _ => ?_
      have hk := hker a
      have hz : psiLin p 3 0 (P.H N) (j / p) 2 (fstV V x a) = 0 := by
        show psiLin p 3 0 (P.H N) (j / p) 2 ((x a : (Fin 3 → ZMod p) × (Fin 2 → ZMod p)).1) = 0
        rcases hJ with hJ | hJ
        · rw [hJ]
          have := congrFun hk.1 0
          simpa [mAlpha] using this
        · rw [hJ]
          have := congrFun hk.1 1
          simpa [mAlpha] using this
      rw [hz, mul_zero]
  · simp only [if_neg hd, ite_self, add_zero]

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
