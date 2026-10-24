module

public import CatalanCore.Cert.SigmaHybS.ConjData

@[expose] public section

/-!
# Symmetry (`g_conj`), total mass (`hm`) and nonnegativity of the hybrid data
-/

open Real

namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

def conjOK (k : ℕ) : Bool :=
  decide (conjIdx.getD k 0 < 1650) &&
    decide ((ptAt (conjIdx.getD k 0)).1 = (ptAt k).1) &&
    decide ((ptAt (conjIdx.getD k 0)).2.1 = -(ptAt k).2.1) &&
    decide ((ptAt (conjIdx.getD k 0)).2.2 = (ptAt k).2.2) &&
    decide (conjIdx.getD (conjIdx.getD k 0) 0 = k)

theorem all_chunks (f : ℕ → Bool) (n c : ℕ)
    (h : ∀ m < n, (List.range c).all (fun i => f (c * m + i)) = true) :
    (List.range (n * c)).all f = true := by
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at hk
    · exact h0
  have hm : k / c < n := (Nat.div_lt_iff_lt_mul hc).2 hk
  have := List.all_eq_true.mp (h (k / c) hm) (k % c) (List.mem_range.mpr (Nat.mod_lt _ hc))
  have e : c * (k / c) + k % c = k := Nat.div_add_mod k c
  rwa [e] at this

theorem conj_c0 : (List.range 50).all (fun i => conjOK (50 * 0 + i)) = true := by decide +kernel
theorem conj_c1 : (List.range 50).all (fun i => conjOK (50 * 1 + i)) = true := by decide +kernel
theorem conj_c2 : (List.range 50).all (fun i => conjOK (50 * 2 + i)) = true := by decide +kernel
theorem conj_c3 : (List.range 50).all (fun i => conjOK (50 * 3 + i)) = true := by decide +kernel
theorem conj_c4 : (List.range 50).all (fun i => conjOK (50 * 4 + i)) = true := by decide +kernel
theorem conj_c5 : (List.range 50).all (fun i => conjOK (50 * 5 + i)) = true := by decide +kernel
theorem conj_c6 : (List.range 50).all (fun i => conjOK (50 * 6 + i)) = true := by decide +kernel
theorem conj_c7 : (List.range 50).all (fun i => conjOK (50 * 7 + i)) = true := by decide +kernel
theorem conj_c8 : (List.range 50).all (fun i => conjOK (50 * 8 + i)) = true := by decide +kernel
theorem conj_c9 : (List.range 50).all (fun i => conjOK (50 * 9 + i)) = true := by decide +kernel
theorem conj_c10 : (List.range 50).all (fun i => conjOK (50 * 10 + i)) = true := by decide +kernel
theorem conj_c11 : (List.range 50).all (fun i => conjOK (50 * 11 + i)) = true := by decide +kernel
theorem conj_c12 : (List.range 50).all (fun i => conjOK (50 * 12 + i)) = true := by decide +kernel
theorem conj_c13 : (List.range 50).all (fun i => conjOK (50 * 13 + i)) = true := by decide +kernel
theorem conj_c14 : (List.range 50).all (fun i => conjOK (50 * 14 + i)) = true := by decide +kernel
theorem conj_c15 : (List.range 50).all (fun i => conjOK (50 * 15 + i)) = true := by decide +kernel
theorem conj_c16 : (List.range 50).all (fun i => conjOK (50 * 16 + i)) = true := by decide +kernel
theorem conj_c17 : (List.range 50).all (fun i => conjOK (50 * 17 + i)) = true := by decide +kernel
theorem conj_c18 : (List.range 50).all (fun i => conjOK (50 * 18 + i)) = true := by decide +kernel
theorem conj_c19 : (List.range 50).all (fun i => conjOK (50 * 19 + i)) = true := by decide +kernel
theorem conj_c20 : (List.range 50).all (fun i => conjOK (50 * 20 + i)) = true := by decide +kernel
theorem conj_c21 : (List.range 50).all (fun i => conjOK (50 * 21 + i)) = true := by decide +kernel
theorem conj_c22 : (List.range 50).all (fun i => conjOK (50 * 22 + i)) = true := by decide +kernel
theorem conj_c23 : (List.range 50).all (fun i => conjOK (50 * 23 + i)) = true := by decide +kernel
theorem conj_c24 : (List.range 50).all (fun i => conjOK (50 * 24 + i)) = true := by decide +kernel
theorem conj_c25 : (List.range 50).all (fun i => conjOK (50 * 25 + i)) = true := by decide +kernel
theorem conj_c26 : (List.range 50).all (fun i => conjOK (50 * 26 + i)) = true := by decide +kernel
theorem conj_c27 : (List.range 50).all (fun i => conjOK (50 * 27 + i)) = true := by decide +kernel
theorem conj_c28 : (List.range 50).all (fun i => conjOK (50 * 28 + i)) = true := by decide +kernel
theorem conj_c29 : (List.range 50).all (fun i => conjOK (50 * 29 + i)) = true := by decide +kernel
theorem conj_c30 : (List.range 50).all (fun i => conjOK (50 * 30 + i)) = true := by decide +kernel
theorem conj_c31 : (List.range 50).all (fun i => conjOK (50 * 31 + i)) = true := by decide +kernel
theorem conj_c32 : (List.range 50).all (fun i => conjOK (50 * 32 + i)) = true := by decide +kernel

theorem conj_check : (List.range 1650).all conjOK = true :=
  all_chunks conjOK 33 50 (by
    intro m hm
    interval_cases m
    exacts [conj_c0, conj_c1, conj_c2, conj_c3, conj_c4, conj_c5, conj_c6, conj_c7, conj_c8, conj_c9, conj_c10, conj_c11, conj_c12, conj_c13, conj_c14, conj_c15, conj_c16, conj_c17, conj_c18, conj_c19, conj_c20, conj_c21, conj_c22, conj_c23, conj_c24, conj_c25, conj_c26, conj_c27, conj_c28, conj_c29, conj_c30, conj_c31, conj_c32])

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
