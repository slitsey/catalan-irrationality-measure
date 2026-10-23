module

public import CatalanCore.Cert.SigmaHybS.ConjData

@[expose] public section

/-!
# Symmetry (`g_conj`), total mass (`hm`) and nonnegativity of the hybrid data
-/

open Real

namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000

def conjOK (k : ℕ) : Bool :=
  decide (conjIdx.getD k 0 < 1650) &&
    decide ((ptAt (conjIdx.getD k 0)).1 = (ptAt k).1) &&
    decide ((ptAt (conjIdx.getD k 0)).2.1 = -(ptAt k).2.1) &&
    decide ((ptAt (conjIdx.getD k 0)).2.2 = (ptAt k).2.2) &&
    decide (conjIdx.getD (conjIdx.getD k 0) 0 = k)

theorem conj_check : (List.range 1650).all conjOK = true := by decide +kernel

lemma conj_prop (k : Fin 1650) :
    conjIdx.getD k 0 < 1650 ∧ (ptAt (conjIdx.getD k 0)).1 = (ptAt k).1 ∧
    (ptAt (conjIdx.getD k 0)).2.1 = -(ptAt k).2.1 ∧ (ptAt (conjIdx.getD k 0)).2.2 = (ptAt k).2.2 ∧
    conjIdx.getD (conjIdx.getD k 0) 0 = k := by
  have h := List.all_eq_true.mp conj_check k (List.mem_range.mpr k.2)
  simp only [conjOK, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

def sgm (k : Fin 1650) : Fin 1650 := ⟨(conjIdx.getD k 0) % 1650, Nat.mod_lt _ (by norm_num)⟩

lemma sgm_val (k : Fin 1650) : (sgm k : ℕ) = conjIdx.getD k 0 :=
  Nat.mod_eq_of_lt (conj_prop k).1

lemma sgm_inv : Function.Involutive sgm := fun k => by
  apply Fin.ext
  rw [sgm_val, sgm_val]
  exact (conj_prop k).2.2.2.2

lemma cH_sgm (k : Fin 1650) : cH (sgm k) = (starRingEnd ℂ) (cH k) := by
  obtain ⟨_, h1, h2, _, _⟩ := conj_prop k
  unfold cH
  rw [sgm_val, h1, h2]
  apply Complex.ext <;> simp [neg_div]

lemma mH_sgm (k : Fin 1650) : mH (sgm k) = mH k := by
  obtain ⟨_, _, _, h3, _⟩ := conj_prop k
  unfold mH
  rw [sgm_val, h3]

lemma norm_conj_sub (s c : ℂ) : ‖(starRingEnd ℂ) s - c‖ = ‖s - (starRingEnd ℂ) c‖ := by
  rw [← Complex.norm_conj (s - (starRingEnd ℂ) c)]
  simp [map_sub]

theorem Usig_conj (s : ℂ) :
    CatalanLambda.Decay.Usig (1 / 4096 : ℝ) cH mH ((starRingEnd ℂ) s)
      = CatalanLambda.Decay.Usig (1 / 4096 : ℝ) cH mH s := by
  unfold CatalanLambda.Decay.Usig
  have h : ∀ k, mH k * CatalanLambda.Decay.krho (1 / 4096 : ℝ) ((starRingEnd ℂ) s) (cH k)
      = mH (sgm k) * CatalanLambda.Decay.krho (1 / 4096 : ℝ) s (cH (sgm k)) := by
    intro k
    rw [mH_sgm, cH_sgm]
    unfold CatalanLambda.Decay.krho
    rw [norm_conj_sub]
  simp_rw [h]
  exact Equiv.sum_comp (Function.Involutive.toPerm sgm sgm_inv)
    (fun j => mH j * CatalanLambda.Decay.krho (1 / 4096 : ℝ) s (cH j))

theorem Utau_conj (s : ℂ) : CatalanLambda.Decay.Utau ((starRingEnd ℂ) s) = CatalanLambda.Decay.Utau s := by
  unfold CatalanLambda.Decay.Utau
  congr 1
  funext t
  have : (starRingEnd ℂ) s - (t : ℂ) = (starRingEnd ℂ) (s - (t : ℂ)) := by simp
  rw [this, Complex.norm_conj]

theorem Uex_conj (L : ℝ) (s : ℂ) :
    CatalanCore.Decay.Uex L ((starRingEnd ℂ) s) = CatalanCore.Decay.Uex L s := by
  unfold CatalanCore.Decay.Uex
  congr 1
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  unfold CatalanLambda.Decay.elog
  have : (starRingEnd ℂ) s - (u : ℂ) = (starRingEnd ℂ) (s - (u : ℂ)) := by simp
  simp only [this, Complex.norm_conj]

theorem g_conj_hyb (s : ℂ) : gHyb ((starRingEnd ℂ) s) = gHyb s := by
  rw [gHyb_eq, gHyb_eq]
  unfold CatalanCore.Decay.Unu
  rw [Usig_conj, Utau_conj, Uex_conj]
  simp

lemma msum_list (l : List Pt) :
    (l.map (fun p => (p.2.2 : ℝ) / 2 ^ 32)).sum = (((l.map (fun p => p.2.2)).sum : ℕ) : ℝ) / 2 ^ 32 := by
  induction l with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

theorem mass_check : (sigH.map (fun p => p.2.2)).sum = 9 * 2 ^ 29 := by decide +kernel

theorem mH_sum : ∑ k, mH k = 9 / 8 := by
  have h := sum_sigma (fun p => (p.2.2 : ℝ) / 2 ^ 32)
  have e : ∑ k : Fin 1650, mH k = ∑ k : Fin 1650, (fun p : Pt => (p.2.2 : ℝ) / 2 ^ 32) (ptAt k) := rfl
  rw [e, h, msum_list, mass_check]
  push_cast
  norm_num

theorem wtH_sum : ∑ k, wtH k = 1 := by
  unfold wtH
  rw [← Finset.sum_div, mH_sum]
  norm_num

theorem wtH_nonneg (k : Fin 1650) : 0 ≤ wtH k := by
  unfold wtH mH
  positivity

end CatalanCore.Cert.SigmaHybS
