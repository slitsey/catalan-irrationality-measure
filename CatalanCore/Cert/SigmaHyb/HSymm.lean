module

public import CatalanCore.Cert.SigmaHyb.ConjL
public import CatalanLambda.Cert.Symm

@[expose] public section

/-!
# Symmetry (`g_conj`) and total mass (`hm`) of the hybrid data
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def conjOKL (k : ℕ) : Bool :=
  decide (conjIdxL.getD k 0 < 180) &&
    decide ((ptAtL lamS (conjIdxL.getD k 0)).1 = (ptAtL lamS k).1) &&
    decide ((ptAtL lamS (conjIdxL.getD k 0)).2.1 = -(ptAtL lamS k).2.1) &&
    decide ((ptAtL lamS (conjIdxL.getD k 0)).2.2 = (ptAtL lamS k).2.2) &&
    decide (conjIdxL.getD (conjIdxL.getD k 0) 0 = k)

theorem conjL_check : (List.range 180).all conjOKL = true := by decide +kernel

lemma conjL_prop (k : Fin 180) :
    conjIdxL.getD k 0 < 180 ∧ (ptAtL lamS (conjIdxL.getD k 0)).1 = (ptAtL lamS k).1 ∧
    (ptAtL lamS (conjIdxL.getD k 0)).2.1 = -(ptAtL lamS k).2.1 ∧
    (ptAtL lamS (conjIdxL.getD k 0)).2.2 = (ptAtL lamS k).2.2 ∧
    conjIdxL.getD (conjIdxL.getD k 0) 0 = k := by
  have h := List.all_eq_true.mp conjL_check k (List.mem_range.mpr k.2)
  simp only [conjOKL, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

def sgmL (k : Fin 180) : Fin 180 := ⟨(conjIdxL.getD k 0) % 180, Nat.mod_lt _ (by norm_num)⟩

lemma sgmL_val (k : Fin 180) : (sgmL k : ℕ) = conjIdxL.getD k 0 :=
  Nat.mod_eq_of_lt (conjL_prop k).1

lemma sgmL_inv : Function.Involutive sgmL := fun k => by
  apply Fin.ext
  rw [sgmL_val, sgmL_val]
  exact (conjL_prop k).2.2.2.2

lemma cL_sgm (k : Fin 180) : cL (sgmL k) = (starRingEnd ℂ) (cL k) := by
  obtain ⟨_, h1, h2, _, _⟩ := conjL_prop k
  unfold cL cOfL
  rw [sgmL_val, h1, h2]
  apply Complex.ext <;> simp [neg_div]

lemma mL_sgm (k : Fin 180) : mL (sgmL k) = mL k := by
  obtain ⟨_, _, _, h3, _⟩ := conjL_prop k
  unfold mL mOfL
  rw [sgmL_val, h3]

theorem UsigL_conj (s : ℂ) :
    CatalanLambda.Decay.Usig (1 / 1024 : ℝ) cL mL ((starRingEnd ℂ) s)
      = CatalanLambda.Decay.Usig (1 / 1024 : ℝ) cL mL s := by
  unfold CatalanLambda.Decay.Usig
  have h : ∀ k, mL k * CatalanLambda.Decay.krho (1 / 1024 : ℝ) ((starRingEnd ℂ) s) (cL k)
      = mL (sgmL k) * CatalanLambda.Decay.krho (1 / 1024 : ℝ) s (cL (sgmL k)) := by
    intro k
    rw [mL_sgm, cL_sgm]
    unfold CatalanLambda.Decay.krho
    rw [norm_conj_sub]
  simp_rw [h]
  exact Equiv.sum_comp (Function.Involutive.toPerm sgmL sgmL_inv)
    (fun j => mL j * CatalanLambda.Decay.krho (1 / 1024 : ℝ) s (cL j))

theorem Uex_conj (L : ℝ) (s : ℂ) :
    CatalanCore.Decay.Uex L ((starRingEnd ℂ) s) = CatalanCore.Decay.Uex L s := by
  unfold CatalanCore.Decay.Uex
  congr 1
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  unfold CatalanLambda.Decay.elog
  have : (starRingEnd ℂ) s - (u : ℂ) = (starRingEnd ℂ) (s - (u : ℂ)) := by simp
  simp only [this, Complex.norm_conj]

theorem mL_sum : ∑ k, mL k = 1 / 8 := by
  have h := sum_gen lamS 180 lamS_len (fun p => (p.2.2 : ℝ) / 2 ^ 32)
  have e : ∑ k : Fin 180, mL k = ∑ k : Fin 180, (fun p : Pt => (p.2.2 : ℝ) / 2 ^ 32) (ptAtL lamS k) := rfl
  rw [e, h, msum_list, lamS_mass]
  push_cast
  norm_num

theorem wtH_sum : ∑ k, wtH k = 1 := by
  unfold wtH mH
  rw [← Finset.sum_div, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [mS_sum, mL_sum]
  norm_num

theorem wtH_nonneg (k : Fin (300 + 180)) : 0 ≤ wtH k := by
  unfold wtH mH
  refine div_nonneg ?_ (by norm_num)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left]; unfold mS; positivity
  · rw [Fin.append_right]; unfold mL mOfL; positivity

theorem g_conj_hyb (s : ℂ) :
    CatalanCore.Cert.gAlpha (1 / 1024 : ℝ) (1 / 1000 : ℝ) cH wtH (1 / 8 : ℝ)
        (CatalanCore.Decay.Unu (1 / 8 : ℝ)) ((starRingEnd ℂ) s)
      = CatalanCore.Cert.gAlpha (1 / 1024 : ℝ) (1 / 1000 : ℝ) cH wtH (1 / 8 : ℝ)
        (CatalanCore.Decay.Unu (1 / 8 : ℝ)) s := by
  unfold CatalanCore.Cert.gAlpha
  have e : (fun k : Fin (300 + 180) => (Fin.append mS mL k) / (1 + (1 / 8 : ℝ))) = wtH := rfl
  have h1 := CatalanCore.Decay.hyb_g_decomp (1 / 1024 : ℝ) (1 / 1000 : ℝ) (1 / 8 : ℝ) (by norm_num)
    cS mS cL mL s
  have h2 := CatalanCore.Decay.hyb_g_decomp (1 / 1024 : ℝ) (1 / 1000 : ℝ) (1 / 8 : ℝ) (by norm_num)
    cS mS cL mL ((starRingEnd ℂ) s)
  rw [e] at h1 h2
  rw [h1, h2]
  have c1 := g_conj_cert s
  unfold CatalanLambda.Decay.gfun at c1
  rw [UsigL_conj, Uex_conj]
  linarith

end CatalanCore.Cert.SigmaHyb
