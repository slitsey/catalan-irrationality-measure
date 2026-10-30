module

public import CatalanCore.Uniform.Decay.NearCells2.PieceExact
public import CatalanCore.Uniform.Decay.NearCells2.Eval2

@[expose] public section
set_option Elab.async false

/-!
# Soundness of the merged evaluation (lane D, package D6d)
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools

theorem ccoef_map_range (f : ℕ → CQ) (n j : ℕ) (hj : j < n) :
    ccoef ((List.range n).map f) j = f j := by
  simp [ccoef, List.getD_eq_getElem?_getD, List.getElem?_map, hj]

theorem pieceEval2_sound {n : ℕ} {P : WP} {zc dd : CQ} {h : ℚ} {c : List ℚ} {E : ℚ} {T : List Tm}
    (hev : pieceEval2 n P zc dd h = some (c, E, T)) (s : ℝ) (hs : |s| ≤ h) :
    |(∫ t in (0 : ℝ)..1, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * t ^ k) *
        Real.log ‖(zc.toC + (s : ℂ) * dd.toC) - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖)
      - ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m - (remSum n T (s : ℂ)).re| ≤ (E : ℝ) := by
  unfold pieceEval2 at hev
  split at hev
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨hn, hv⟩, hside⟩, hz0nsq⟩, h1z0nsq⟩, hr0⟩, hr1⟩, hh⟩ := hc
    split at hev
    · rename_i lv εv l0 e0l a0 e0a l1 e1l a1 e1a hlv hl0 ha0 hl1 ha1
      cases hev
      set z0 := z0of P.A P.B zc with hz0def
      set e := eof P.A P.B dd with hedef
      have hh0 : (0 : ℚ) ≤ h := hh
      have hnnsq : (CQ.neg z0).nsq ≠ 0 := by
        simpa [CQ.nsq, CQ.neg] using hz0nsq
      have hnn : ∀ q : CQ, 0 ≤ q.nsq * h ^ 2 := fun q =>
        mul_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (sq_nonneg _)
      have hM := piece_exact (coeffs P.a) (P.a.length - 1) n hn P.A P.B zc dd h
        (sqrtUp ((q0of z0 e).nsq * h ^ 2)) (sqrtUp ((q1of z0 e).nsq * h ^ 2)) hh0 hv hz0nsq h1z0nsq hside
        (sqrtUp_nonneg _) hr0 (le_sqrtUp_sq (hnn _)) (sqrtUp_nonneg _) hr1 (le_sqrtUp_sq (hnn _)) s hs
      have hL0 : ‖Complex.log (-z0.toC) - (CQ.mk l0 a0).toC‖ ≤ (e0l : ℝ) + e0a := by
        have := logC_close hnnsq hl0 ha0
        rwa [CQ.toC_neg] at this
      have hL1 : ‖Complex.log (1 - z0.toC) - (CQ.mk l1 a1).toC‖ ≤ (e1l : ℝ) + e1a := by
        have := logC_close h1z0nsq hl1 ha1
        rwa [CQ.toC_sub, CQ.toC_one] at this
      have hlv' : |(lv : ℝ) - Real.log ‖P.B.toC - P.A.toC‖| ≤ εv := by
        have := logHalf_sound hv hlv
        rwa [CQ.toC_sub] at this
      set f := pieceCoef n P z0 e ⟨l0, a0⟩ ⟨l1, a1⟩ lv with hf
      set ctil : ℕ → ℚ := fun m => (CQ.add (CQ.add (CQ.add (CQ.add
        (CQ.mul (PAc (coeffs P.a) (P.a.length - 1) z0 e m) ⟨l1, a1⟩)
        (CQ.mul (PBc (coeffs P.a) (P.a.length - 1) z0 e m) ⟨l0, a0⟩))
        (Rc (coeffs P.a) (P.a.length - 1) z0 e m))
        (jetc (PAc (coeffs P.a) (P.a.length - 1) z0 e) (q1of z0 e) m))
        (jetc (PBc (coeffs P.a) (P.a.length - 1) z0 e) (q0of z0 e) m)).re with hctil
      have hget : ∀ m ∈ range n, coeffs ((List.range n).map f) m = f m := by
        intro m hm
        have hm' := List.mem_range.1 hm
        simp [coeffs, List.getD_eq_getElem?_getD, List.getElem?_map, hm']
      have hfm : ∀ m, f m = ctil m + (if m = 0 then massQ (coeffs P.a) (P.a.length - 1) * lv else 0) := by
        intro m; rfl
      have hn0 : 0 < n := by omega
      have hsum : ∑ m ∈ range n, ((coeffs ((List.range n).map f) m : ℚ) : ℝ) * s ^ m
          = (massQ (coeffs P.a) (P.a.length - 1) : ℝ) * lv + ∑ m ∈ range n, (ctil m : ℝ) * s ^ m := by
        rw [Finset.sum_congr rfl (fun m hm => by rw [hget m hm])]
        have : ∀ m ∈ range n, (f m : ℝ) * s ^ m = (ctil m : ℝ) * s ^ m
            + (if m = 0 then (massQ (coeffs P.a) (P.a.length - 1) : ℝ) * lv * s ^ m else 0) := by
          intro m _
          rw [hfm m]
          split_ifs <;> push_cast <;> ring
        rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp [hn0]; ring
      rw [hsum]
      have hcm : ∀ m ∈ range n, |cmodel (coeffs P.a) (P.a.length - 1) z0 e
            (Complex.log (-z0.toC)) (Complex.log (1 - z0.toC)) m - (ctil m : ℝ)| ≤
          (nrmQ (PAc (coeffs P.a) (P.a.length - 1) z0 e m) : ℝ) * ((e1l : ℝ) + e1a)
            + (nrmQ (PBc (coeffs P.a) (P.a.length - 1) z0 e m) : ℝ) * ((e0l : ℝ) + e0a) := by
        intro m _
        exact cmodel_close (coeffs P.a) (P.a.length - 1) z0 e _ _ ⟨l0, a0⟩ ⟨l1, a1⟩ _ _ hL0 hL1 m
      set I := ∫ t in (0 : ℝ)..1, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * t ^ k) *
        Real.log ‖(zc.toC + (s : ℂ) * dd.toC) - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖ with hI
      set mass := (massQ (coeffs P.a) (P.a.length - 1) : ℝ) with hmass
      set Sm := ∑ m ∈ range n, cmodel (coeffs P.a) (P.a.length - 1) z0 e
        (Complex.log (-z0.toC)) (Complex.log (1 - z0.toC)) m * s ^ m with hSm
      have hdiffS : |Sm - ∑ m ∈ range n, (ctil m : ℝ) * s ^ m| ≤
          ∑ m ∈ range n, ((nrmQ (PAc (coeffs P.a) (P.a.length - 1) z0 e m) : ℝ) * ((e1l : ℝ) + e1a)
            + (nrmQ (PBc (coeffs P.a) (P.a.length - 1) z0 e m) : ℝ) * ((e0l : ℝ) + e0a)) * (h : ℝ) ^ m := by
        rw [hSm, ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        rw [← sub_mul, abs_mul, abs_pow]
        have hs' : |s| ^ m ≤ (h : ℝ) ^ m := pow_le_pow_left₀ (abs_nonneg _) hs m
        exact mul_le_mul (hcm m hm) hs' (by positivity) (by
          have := hcm m hm
          exact (abs_nonneg _).trans this)
      have h2 : |mass * (Real.log ‖P.B.toC - P.A.toC‖ - lv)| ≤ |mass| * εv := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hlv') (abs_nonneg _)
      have hE : (((lsum (fun m => (nrmQ (PAc (coeffs P.a) (P.a.length - 1) z0 e m) * (e1l + e1a)
             + nrmQ (PBc (coeffs P.a) (P.a.length - 1) z0 e m) * (e0l + e0a)) * h ^ m) n
          + |massQ (coeffs P.a) (P.a.length - 1)| * εv : ℚ)) : ℝ)
          = ∑ m ∈ range n, ((nrmQ (PAc (coeffs P.a) (P.a.length - 1) z0 e m) : ℝ) * ((e1l : ℝ) + e1a)
            + (nrmQ (PBc (coeffs P.a) (P.a.length - 1) z0 e m) : ℝ) * ((e0l : ℝ) + e0a)) * (h : ℝ) ^ m
          + |mass| * εv := by
        rw [Rat.cast_add, lsum_eq]
        push_cast
        rfl
      -- the remainder terms
      have hrem : (remSum n [⟨q1of z0 e, (List.range n).map (PAc (coeffs P.a) (P.a.length - 1) z0 e)⟩,
          ⟨q0of z0 e, (List.range n).map (PBc (coeffs P.a) (P.a.length - 1) z0 e)⟩] (s : ℂ))
          = remT n (fun j => (PAc (coeffs P.a) (P.a.length - 1) z0 e j).toC) (q1of z0 e).toC (s : ℂ)
            + remT n (fun j => (PBc (coeffs P.a) (P.a.length - 1) z0 e j).toC) (q0of z0 e).toC (s : ℂ) := by
        rw [remSum_cons, remSum_cons]
        simp only [remSum, List.map_nil, List.sum_nil, add_zero]
        unfold tmC
        simp only []
        have eA := remT_congr n (P := fun j => (ccoef ((List.range n).map
            (PAc (coeffs P.a) (P.a.length - 1) z0 e)) j).toC)
          (P' := fun j => (PAc (coeffs P.a) (P.a.length - 1) z0 e j).toC)
          (fun j hj => by rw [ccoef_map_range _ n j hj]) (q1of z0 e).toC (s : ℂ)
        have eB := remT_congr n (P := fun j => (ccoef ((List.range n).map
            (PBc (coeffs P.a) (P.a.length - 1) z0 e)) j).toC)
          (P' := fun j => (PBc (coeffs P.a) (P.a.length - 1) z0 e j).toC)
          (fun j hj => by rw [ccoef_map_range _ n j hj]) (q0of z0 e).toC (s : ℂ)
        rw [eA, eB]
      rw [hrem, hE]
      have key : I - (mass * lv + ∑ m ∈ range n, (ctil m : ℝ) * s ^ m)
            - (remT n (fun j => (PAc (coeffs P.a) (P.a.length - 1) z0 e j).toC) (q1of z0 e).toC (s : ℂ)
              + remT n (fun j => (PBc (coeffs P.a) (P.a.length - 1) z0 e j).toC) (q0of z0 e).toC (s : ℂ)).re
          = mass * (Real.log ‖P.B.toC - P.A.toC‖ - lv) + (Sm - ∑ m ∈ range n, (ctil m : ℝ) * s ^ m) := by
        linear_combination hM
      rw [key]
      refine (abs_add_le _ _).trans ?_
      linarith
    · cases hev
  · cases hev

end CatalanCore.Uniform.Decay.NearCells
