module

public import CatalanCore.Cert.SigmaP6.ConjData

@[expose] public section

/-!
# Symmetry of the sigma data (`g_conj`) and total mass (`hm`)
-/

open Real

namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

set_option maxRecDepth 100000

def conjOK (k : ℕ) : Bool :=
  decide (conjIdx.getD k 0 < 699) &&
    decide ((ptAt (conjIdx.getD k 0)).1 = (ptAt k).1) &&
    decide ((ptAt (conjIdx.getD k 0)).2.1 = -(ptAt k).2.1) &&
    decide ((ptAt (conjIdx.getD k 0)).2.2 = (ptAt k).2.2) &&
    decide (conjIdx.getD (conjIdx.getD k 0) 0 = k)

theorem conj_check : (List.range 699).all conjOK = true := by decide +kernel

lemma conj_prop (k : Fin 699) :
    conjIdx.getD k 0 < 699 ∧ (ptAt (conjIdx.getD k 0)).1 = (ptAt k).1 ∧
    (ptAt (conjIdx.getD k 0)).2.1 = -(ptAt k).2.1 ∧ (ptAt (conjIdx.getD k 0)).2.2 = (ptAt k).2.2 ∧
    conjIdx.getD (conjIdx.getD k 0) 0 = k := by
  have h := List.all_eq_true.mp conj_check k (List.mem_range.mpr k.2)
  simp only [conjOK, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

def sgm (k : Fin 699) : Fin 699 := ⟨(conjIdx.getD k 0) % 699, Nat.mod_lt _ (by norm_num)⟩

lemma sgm_val (k : Fin 699) : (sgm k : ℕ) = conjIdx.getD k 0 :=
  Nat.mod_eq_of_lt (conj_prop k).1

lemma sgm_inv : Function.Involutive sgm := fun k => by
  apply Fin.ext
  rw [sgm_val, sgm_val]
  exact (conj_prop k).2.2.2.2

lemma cS_sgm (k : Fin 699) : cS (sgm k) = (starRingEnd ℂ) (cS k) := by
  obtain ⟨_, h1, h2, _, _⟩ := conj_prop k
  unfold cS
  rw [sgm_val, h1, h2]
  apply Complex.ext <;> simp [neg_div]

lemma mS_sgm (k : Fin 699) : mS (sgm k) = mS k := by
  obtain ⟨_, _, _, h3, _⟩ := conj_prop k
  unfold mS
  rw [sgm_val, h3]

lemma norm_conj_sub (s c : ℂ) : ‖(starRingEnd ℂ) s - c‖ = ‖s - (starRingEnd ℂ) c‖ := by
  rw [← Complex.norm_conj (s - (starRingEnd ℂ) c)]
  simp [map_sub]

theorem Usig_conj (s : ℂ) :
    CatalanLambda.Decay.Usig (1 / 2048 : ℝ) cS mS ((starRingEnd ℂ) s) = CatalanLambda.Decay.Usig (1 / 2048 : ℝ) cS mS s := by
  unfold CatalanLambda.Decay.Usig
  have h : ∀ k, mS k * CatalanLambda.Decay.krho (1 / 2048 : ℝ) ((starRingEnd ℂ) s) (cS k)
      = mS (sgm k) * CatalanLambda.Decay.krho (1 / 2048 : ℝ) s (cS (sgm k)) := by
    intro k
    rw [mS_sgm, cS_sgm]
    unfold CatalanLambda.Decay.krho
    rw [norm_conj_sub]
  simp_rw [h]
  exact Equiv.sum_comp (Function.Involutive.toPerm sgm sgm_inv)
    (fun j => mS j * CatalanLambda.Decay.krho (1 / 2048 : ℝ) s (cS j))

theorem Utau_conj (s : ℂ) : CatalanLambda.Decay.Utau ((starRingEnd ℂ) s) = CatalanLambda.Decay.Utau s := by
  unfold CatalanLambda.Decay.Utau
  congr 1
  funext t
  have : (starRingEnd ℂ) s - (t : ℂ) = (starRingEnd ℂ) (s - (t : ℂ)) := by simp
  rw [this, Complex.norm_conj]

theorem g_conj_cert (s : ℂ) :
    CatalanLambda.Decay.gfun (1 / 2048 : ℝ) (1 / 1000 : ℝ) cS mS ((starRingEnd ℂ) s)
      = CatalanLambda.Decay.gfun (1 / 2048 : ℝ) (1 / 1000 : ℝ) cS mS s := by
  unfold CatalanLambda.Decay.gfun
  rw [Usig_conj, Utau_conj]
  simp

lemma msum_list (l : List Pt) :
    (l.map (fun p => (p.2.2 : ℝ) / 2 ^ 32)).sum = (((l.map (fun p => p.2.2)).sum : ℕ) : ℝ) / 2 ^ 32 := by
  induction l with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

theorem mass_check : (sigD.map (fun p => p.2.2)).sum = 2 ^ 32 := by decide +kernel

theorem mS_sum : ∑ k, mS k = 1 := by
  have h := sum_sigma (fun p => (p.2.2 : ℝ) / 2 ^ 32)
  have e : ∑ k : Fin 699, mS k = ∑ k : Fin 699, (fun p : Pt => (p.2.2 : ℝ) / 2 ^ 32) (ptAt k) := rfl
  rw [e, h, msum_list, mass_check]
  push_cast
  norm_num

end CatalanCore.Cert.SigmaP6
