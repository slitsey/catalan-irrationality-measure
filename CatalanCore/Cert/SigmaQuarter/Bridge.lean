module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaP6.Symm

@[expose] public section

/-! The finite quarter-border witness reuses the existing list checker and
the existing rectangular potential.  Only witness enumeration is new. -/

open Real

namespace CatalanCore.Cert.SigmaQuarter

open CatalanLambda.Cert
open CatalanCore.Cert.SigmaP6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ptAtQ (k : ℕ) : Pt := pts.getD k (0, 0, 0)

noncomputable def cQ (k : Fin pts.length) : ℂ :=
  ⟨((ptAtQ k).1 : ℝ) / 2 ^ 40, ((ptAtQ k).2.1 : ℝ) / 2 ^ 40⟩

noncomputable def mQ (k : Fin pts.length) : ℝ := ((ptAtQ k).2.2 : ℝ) / 2 ^ 32

theorem pts_len : pts.length = 600 := by decide +kernel

lemma pts_ofFn : pts = List.ofFn (fun k : Fin pts.length => ptAtQ k) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    rw [List.getElem_ofFn]
    unfold ptAtQ
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rfl

lemma sum_sigmaQ (f : Pt → ℝ) :
    ∑ k : Fin pts.length, f (ptAtQ k) = (pts.map f).sum := by
  conv_rhs => rw [pts_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

theorem Usig_bridge (x y : ℝ) :
    CatalanLambda.Decay.Usig (1 / 2048 : ℝ) cQ mQ ⟨x, y⟩ =
      CatalanCore.Cert.SigmaP6.Usig pts x y := by
  unfold CatalanLambda.Decay.Usig
  rw [Usig_eq_sum, ← sum_sigmaQ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold CatalanLambda.Decay.krho mQ cQ
  rw [norm_sq_mk]

theorem mass_check : (pts.map (fun p => p.2.2)).sum = 2 ^ 32 := by decide +kernel

theorem mQ_sum : ∑ k, mQ k = 1 := by
  have h := sum_sigmaQ (fun p => (p.2.2 : ℝ) / 2 ^ 32)
  change (∑ k : Fin pts.length, (ptAtQ k).2.2 / (2 : ℝ) ^ 32) = 1
  rw [h, msum_list, mass_check]
  norm_num

theorem mQ_nonneg (k : Fin pts.length) : 0 ≤ mQ k := by
  unfold mQ
  positivity

def radiusOK (k : ℕ) : Bool :=
  decide ((ptAtQ k).1 ^ 2 + (ptAtQ k).2.1 ^ 2 ≤ (256 : ℤ) * (2 ^ 40) ^ 2)

theorem radius_check : (List.range pts.length).all radiusOK = true := by decide +kernel

theorem cQ_norm (k : Fin pts.length) : ‖cQ k‖ ≤ 16 := by
  have h := List.all_eq_true.mp radius_check k (List.mem_range.mpr k.2)
  simp only [radiusOK, decide_eq_true_eq] at h
  have hR : ((ptAtQ k).1 : ℝ) ^ 2 + ((ptAtQ k).2.1 : ℝ) ^ 2 ≤
      (256 : ℝ) * (2 ^ 40) ^ 2 := by exact_mod_cast h
  have hs : ‖cQ k‖ ^ 2 ≤ (16 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    unfold cQ
    change (((ptAtQ k).1 : ℝ) / 2 ^ 40) * (((ptAtQ k).1 : ℝ) / 2 ^ 40) +
      (((ptAtQ k).2.1 : ℝ) / 2 ^ 40) * (((ptAtQ k).2.1 : ℝ) / 2 ^ 40) ≤ (16 : ℝ) ^ 2
    nlinarith [sq_nonneg (((ptAtQ k).1 : ℝ) / 2 ^ 40),
      sq_nonneg (((ptAtQ k).2.1 : ℝ) / 2 ^ 40)]
  nlinarith [norm_nonneg (cQ k)]

def conjIndexQ (k : ℕ) : ℕ :=
  if k < 500 then (if k % 2 = 0 then k + 1 else k - 1) else k

def conjOKQ (k : ℕ) : Bool :=
  decide (conjIndexQ k < pts.length) &&
    decide ((ptAtQ (conjIndexQ k)).1 = (ptAtQ k).1) &&
    decide ((ptAtQ (conjIndexQ k)).2.1 = -(ptAtQ k).2.1) &&
    decide ((ptAtQ (conjIndexQ k)).2.2 = (ptAtQ k).2.2) &&
    decide (conjIndexQ (conjIndexQ k) = k)

theorem conj_check : (List.range pts.length).all conjOKQ = true := by decide +kernel

lemma conj_propQ (k : Fin pts.length) :
    conjIndexQ k < pts.length ∧
    (ptAtQ (conjIndexQ k)).1 = (ptAtQ k).1 ∧
    (ptAtQ (conjIndexQ k)).2.1 = -(ptAtQ k).2.1 ∧
    (ptAtQ (conjIndexQ k)).2.2 = (ptAtQ k).2.2 ∧
    conjIndexQ (conjIndexQ k) = k := by
  have h := List.all_eq_true.mp conj_check k (List.mem_range.mpr k.2)
  simp only [conjOKQ, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

def sgmQ (k : Fin pts.length) : Fin pts.length := ⟨conjIndexQ k, (conj_propQ k).1⟩

lemma sgmQ_inv : Function.Involutive sgmQ := fun k => by
  apply Fin.ext
  exact (conj_propQ k).2.2.2.2

lemma cQ_sgm (k : Fin pts.length) : cQ (sgmQ k) = (starRingEnd ℂ) (cQ k) := by
  obtain ⟨_, h1, h2, _, _⟩ := conj_propQ k
  unfold cQ sgmQ
  simp only [h1, h2]
  apply Complex.ext <;> simp [neg_div]

lemma mQ_sgm (k : Fin pts.length) : mQ (sgmQ k) = mQ k := by
  obtain ⟨_, _, _, h3, _⟩ := conj_propQ k
  unfold mQ sgmQ
  simp only [h3]

theorem Usig_conj (s : ℂ) :
    CatalanLambda.Decay.Usig (1 / 2048 : ℝ) cQ mQ ((starRingEnd ℂ) s) =
      CatalanLambda.Decay.Usig (1 / 2048 : ℝ) cQ mQ s := by
  unfold CatalanLambda.Decay.Usig
  have h : ∀ k, mQ k * CatalanLambda.Decay.krho (1 / 2048 : ℝ) ((starRingEnd ℂ) s) (cQ k)
      = mQ (sgmQ k) * CatalanLambda.Decay.krho (1 / 2048 : ℝ) s (cQ (sgmQ k)) := by
    intro k
    rw [mQ_sgm, cQ_sgm]
    unfold CatalanLambda.Decay.krho
    rw [norm_conj_sub]
  simp_rw [h]
  exact Equiv.sum_comp (Function.Involutive.toPerm sgmQ sgmQ_inv)
    (fun j => mQ j * CatalanLambda.Decay.krho (1 / 2048 : ℝ) s (cQ j))

lemma div_threeHalf (x y : ℝ) :
    (⟨x, y⟩ : ℂ) / (3 / 2 : ℂ) = ⟨2 * x / 3, 2 * y / 3⟩ := by
  apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> ring

theorem gAlpha_bridge (x y : ℝ) (hx : x < 0) (hy : 0 ≤ y) :
    CatalanCore.Cert.gAlpha (1 / 2048 : ℝ) (1 / 1000 : ℝ) cQ mQ (1 / 4)
      (CatalanCore.Decay.Unu (1 / 4)) ⟨x, y⟩ = gQuarter pts x y := by
  unfold CatalanCore.Cert.gAlpha gQuarter
  rw [Unu_quarter, Usig_bridge, div_threeHalf,
    Utau_bridge x y hx, Utau_bridge (2 * x / 3) (2 * y / 3) (by linarith)]
  have habs : |(⟨x, y⟩ : ℂ).im| = y := abs_of_nonneg hy
  rw [habs]
  ring

theorem gAlpha_bridge_axis (x : ℝ) (hx : x ≤ 1) :
    CatalanCore.Cert.gAlpha (1 / 2048 : ℝ) (1 / 1000 : ℝ) cQ mQ (1 / 4)
      (CatalanCore.Decay.Unu (1 / 4)) ⟨x, 0⟩ = gQuarter pts x 0 := by
  unfold CatalanCore.Cert.gAlpha gQuarter
  rw [Unu_quarter, Usig_bridge, div_threeHalf]
  simp only [mul_zero, zero_div]
  rw [Utau_bridge_axis x hx, Utau_bridge_axis (2 * x / 3) (by linarith)]
  simp only [abs_zero, mul_zero, add_zero]
  ring

theorem Unu_conj (s : ℂ) :
    CatalanCore.Decay.Unu (1 / 4) ((starRingEnd ℂ) s) = CatalanCore.Decay.Unu (1 / 4) s := by
  rw [Unu_quarter, Unu_quarter, CatalanCore.Cert.SigmaP6.Utau_conj]
  have he : (starRingEnd ℂ) s / (3 / 2 : ℂ) = (starRingEnd ℂ) (s / (3 / 2 : ℂ)) := by
    rw [map_div₀]
    congr 1
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]
  rw [he, CatalanCore.Cert.SigmaP6.Utau_conj]

theorem g_conj_cert (s : ℂ) :
    CatalanCore.Cert.gAlpha (1 / 2048 : ℝ) (1 / 1000 : ℝ) cQ mQ (1 / 4)
        (CatalanCore.Decay.Unu (1 / 4)) ((starRingEnd ℂ) s) =
      CatalanCore.Cert.gAlpha (1 / 2048 : ℝ) (1 / 1000 : ℝ) cQ mQ (1 / 4)
        (CatalanCore.Decay.Unu (1 / 4)) s := by
  unfold CatalanCore.Cert.gAlpha
  rw [Usig_conj, Unu_conj]
  simp

end CatalanCore.Cert.SigmaQuarter
