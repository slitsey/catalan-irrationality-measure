module

public import CatalanCore.Uniform.Decay.Breakpoint.Inc
public import CatalanCore.Uniform.Decay.NearCells.Agg

@[expose] public section
set_option Elab.async false

/-!
# Evaluating the incident model (lane D, package D14)

`incEval n P dd h = some (c, b, E)`: rational coefficient lists `c`, `b` of length `n` and an error `E`
with `|Φ_P(A + s dd) - (∑ c_m s^m + ln s ∑ b_m s^m)| ≤ E` for `0 ≤ s ≤ h`
(`incEval_sound`).  `incAgg` adds the weights `-w`; `incAgg_sound`.
-/

namespace CatalanCore.Uniform.Decay.Breakpoint

open Finset Complex CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

/-- Rational model coefficient (with the log enclosures `L0 ≈ Log(-e)`, `lv ≈ log‖B - A‖`). -/
def incCoef (a : ℕ → ℚ) (d : ℕ) (e L0 : CQ) (lv : ℚ) (m : ℕ) : ℚ :=
  (CQ.add (CQ.add (CQ.mul (PBc a d CQ.zero e m) L0) (Rc a d CQ.zero e m))
    (jetc (PAc a d CQ.zero e) e m)).re + (if m = 0 then massQ a d * lv else 0)

/-- Evaluate the model of one segment starting at the breakpoint. -/
def incEval (n : ℕ) (P : WP) (dd : CQ) (h : ℚ) : Option (List ℚ × List ℚ × ℚ) :=
  if decide (P.a.length - 1 + 2 ≤ n) && decide ((CQ.sub P.B P.A).nsq ≠ 0) &&
      decide ((eof P.A P.B dd).nsq ≠ 0) &&
      decide (sqrtUp ((eof P.A P.B dd).nsq * h ^ 2) < 1) && decide (0 ≤ h) then
    match logHalf (CQ.sub P.B P.A), logHalf (CQ.neg (eof P.A P.B dd)),
        argEnc (CQ.neg (eof P.A P.B dd)) with
    | some (lv, εv), some (l0, e0l), some (a0, e0a) =>
      some ((List.range n).map
          (incCoef (coeffs P.a) (P.a.length - 1) (eof P.A P.B dd) ⟨l0, a0⟩ lv),
        (List.range n).map
          (fun m => (PBc (coeffs P.a) (P.a.length - 1) CQ.zero (eof P.A P.B dd) m).re),
        jbQ (PAc (coeffs P.a) (P.a.length - 1) CQ.zero (eof P.A P.B dd)) n
            (sqrtUp ((eof P.A P.B dd).nsq * h ^ 2)) h
        + lsum (fun m => nrmQ (PBc (coeffs P.a) (P.a.length - 1) CQ.zero (eof P.A P.B dd) m)
            * (e0l + e0a) * h ^ m) n
        + |massQ (coeffs P.a) (P.a.length - 1)| * εv)
    | _, _, _ => none
  else none

theorem sum_coeffs_map (f : ℕ → ℚ) (n : ℕ) (s : ℝ) :
    ∑ m ∈ range n, ((coeffs ((List.range n).map f) m : ℚ) : ℝ) * s ^ m
      = ∑ m ∈ range n, ((f m : ℚ) : ℝ) * s ^ m := by
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m < n := Finset.mem_range.1 hm
  simp [coeffs, List.getD_eq_getElem?_getD, List.getElem?_map, hm']

theorem incEval_sound {n : ℕ} {P : WP} {dd : CQ} {h : ℚ} {c b : List ℚ} {E : ℚ}
    (hev : incEval n P dd h = some (c, b, E)) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ (h : ℝ)) :
    |PhiW P (P.A.toC + (s : ℂ) * dd.toC)
      - (∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m
        + Real.log s * ∑ m ∈ range n, ((coeffs b m : ℚ) : ℝ) * s ^ m)| ≤ (E : ℝ) := by
  unfold incEval at hev
  split at hev
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hn, hv⟩, he0⟩, hr⟩, hh⟩ := hc
    split at hev
    · rename_i lv εv l0 e0l a0 e0a hlv hl0 ha0
      cases hev
      set e := eof P.A P.B dd with hedef
      have hnn : 0 ≤ e.nsq * h ^ 2 :=
        mul_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (sq_nonneg _)
      have hM := incA_model (coeffs P.a) (P.a.length - 1) n hn P.A P.B dd h
        (sqrtUp (e.nsq * h ^ 2)) hh hv he0 (sqrtUp_nonneg _) hr (le_sqrtUp_sq hnn)
        (Complex.log (-e.toC)) rfl s hs0 hs
      have hnnsq : (CQ.neg e).nsq ≠ 0 := by simpa [CQ.nsq, CQ.neg] using he0
      have hL : ‖Complex.log (-e.toC) - (CQ.mk l0 a0).toC‖ ≤ (e0l : ℝ) + e0a := by
        have := logC_close hnnsq hl0 ha0
        rwa [CQ.toC_neg] at this
      have hlv' : |(lv : ℝ) - Real.log ‖P.B.toC - P.A.toC‖| ≤ εv := by
        have := logHalf_sound hv hlv
        rwa [CQ.toC_sub] at this
      set f := incCoef (coeffs P.a) (P.a.length - 1) e ⟨l0, a0⟩ lv with hf
      set ctil : ℕ → ℚ := fun m => (CQ.add (CQ.add (CQ.mul
        (PBc (coeffs P.a) (P.a.length - 1) CQ.zero e m) ⟨l0, a0⟩)
        (Rc (coeffs P.a) (P.a.length - 1) CQ.zero e m))
        (jetc (PAc (coeffs P.a) (P.a.length - 1) CQ.zero e) e m)).re with hctil
      have hn0 : 0 < n := by omega
      have hfm : ∀ m, f m = ctil m +
          (if m = 0 then massQ (coeffs P.a) (P.a.length - 1) * lv else 0) := by
        intro m; rfl
      have hsum : ∑ m ∈ range n, ((coeffs ((List.range n).map f) m : ℚ) : ℝ) * s ^ m
          = (massQ (coeffs P.a) (P.a.length - 1) : ℝ) * lv
            + ∑ m ∈ range n, (ctil m : ℝ) * s ^ m := by
        rw [sum_coeffs_map]
        have : ∀ m ∈ range n, (f m : ℝ) * s ^ m = (ctil m : ℝ) * s ^ m
            + (if m = 0 then (massQ (coeffs P.a) (P.a.length - 1) : ℝ) * lv * s ^ m else 0) := by
          intro m _
          rw [hfm m]
          split_ifs <;> push_cast <;> ring
        rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp [hn0]; ring
      have hcm : ∀ m ∈ range n, |cinc (coeffs P.a) (P.a.length - 1) e (Complex.log (-e.toC)) m
            - (ctil m : ℝ)|
          ≤ (nrmQ (PBc (coeffs P.a) (P.a.length - 1) CQ.zero e m) : ℝ) * ((e0l : ℝ) + e0a) := by
        intro m _
        have e1 : cinc (coeffs P.a) (P.a.length - 1) e (Complex.log (-e.toC)) m - (ctil m : ℝ)
            = ((PBc (coeffs P.a) (P.a.length - 1) CQ.zero e m).toC *
                (Complex.log (-e.toC) - (CQ.mk l0 a0).toC)).re := by
          rw [hctil]
          simp only []
          rw [← CQ.toC_re]
          unfold cinc
          simp only [CQ.toC_add, CQ.toC_mul]
          rw [← Complex.sub_re]
          congr 1; ring
        rw [e1]
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul]
        exact mul_le_mul (norm_le_nrmQ _) hL (norm_nonneg _) (by exact_mod_cast nrmQ_nonneg _)
      have hdiffS : |∑ m ∈ range n, cinc (coeffs P.a) (P.a.length - 1) e (Complex.log (-e.toC)) m * s ^ m
            - ∑ m ∈ range n, (ctil m : ℝ) * s ^ m| ≤
          ∑ m ∈ range n, ((nrmQ (PBc (coeffs P.a) (P.a.length - 1) CQ.zero e m) : ℝ) *
            ((e0l : ℝ) + e0a)) * (h : ℝ) ^ m := by
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        rw [← sub_mul, abs_mul, abs_pow]
        have hs' : |s| ^ m ≤ (h : ℝ) ^ m :=
          pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_of_nonneg hs0]; exact hs) m
        exact mul_le_mul (hcm m hm) hs' (by positivity) ((abs_nonneg _).trans (hcm m hm))
      have hb : ∑ m ∈ range n, ((coeffs ((List.range n).map
            (fun m => (PBc (coeffs P.a) (P.a.length - 1) CQ.zero e m).re)) m : ℚ) : ℝ) * s ^ m
          = ∑ m ∈ range n, ((PBc (coeffs P.a) (P.a.length - 1) CQ.zero e m).re : ℝ) * s ^ m :=
        sum_coeffs_map _ n s
      have hmass : |(massQ (coeffs P.a) (P.a.length - 1) : ℝ) * Real.log ‖P.B.toC - P.A.toC‖
          - (massQ (coeffs P.a) (P.a.length - 1) : ℝ) * lv|
          ≤ |(massQ (coeffs P.a) (P.a.length - 1) : ℝ)| * εv := by
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hlv') (abs_nonneg _)
      have hE : ((jbQ (PAc (coeffs P.a) (P.a.length - 1) CQ.zero e) n
            (sqrtUp (e.nsq * h ^ 2)) h
          + lsum (fun m => nrmQ (PBc (coeffs P.a) (P.a.length - 1) CQ.zero e m)
            * (e0l + e0a) * h ^ m) n
          + |massQ (coeffs P.a) (P.a.length - 1)| * εv : ℚ) : ℝ)
          = (jbQ (PAc (coeffs P.a) (P.a.length - 1) CQ.zero e) n
            (sqrtUp (e.nsq * h ^ 2)) h : ℝ)
          + ∑ m ∈ range n, ((nrmQ (PBc (coeffs P.a) (P.a.length - 1) CQ.zero e m) : ℝ) *
            ((e0l : ℝ) + e0a)) * (h : ℝ) ^ m
          + |(massQ (coeffs P.a) (P.a.length - 1) : ℝ)| * εv := by
        rw [Rat.cast_add, Rat.cast_add, lsum_eq]
        push_cast
        rfl
      rw [hE]
      show |(∫ t in (0 : ℝ)..1, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * t ^ k) *
          Real.log ‖(P.A.toC + (s : ℂ) * dd.toC) - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖) - _| ≤ _
      rw [hsum, hb]
      rw [abs_le] at hM hmass hdiffS ⊢
      constructor <;> linarith [hM.1, hM.2, hmass.1, hmass.2, hdiffS.1, hdiffS.2]
    · cases hev
  · cases hev

/-- Aggregate (weights `-w`) of incident segments. -/
def incAgg (n : ℕ) (dd : CQ) (h : ℚ) : List WP → Option (List ℚ × List ℚ × ℚ)
  | [] => some ([], [], 0)
  | P :: ps =>
    match incEval n P dd h, incAgg n dd h ps with
    | some (c, b, E), some (C, B, F) =>
      some (addL (scaleL (-P.w) c) C, addL (scaleL (-P.w) b) B, |P.w| * E + F)
    | _, _ => none

theorem incAgg_sound {n : ℕ} {dd : CQ} {h : ℚ} {pc : ℂ} (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ (h : ℝ)) :
    ∀ (ps : List WP), (∀ P ∈ ps, P.A.toC = pc) → ∀ {C B : List ℚ} {F : ℚ},
    incAgg n dd h ps = some (C, B, F) →
    |(-(ps.map (fun P => (P.w : ℝ) * PhiW P (pc + (s : ℂ) * dd.toC))).sum)
      - (∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m
        + Real.log s * ∑ m ∈ range n, ((coeffs B m : ℚ) : ℝ) * s ^ m)| ≤ (F : ℝ) := by
  intro ps
  induction ps with
  | nil =>
    intro _ C B F hC
    simp only [incAgg] at hC
    cases hC
    simp [coeffs]
  | cons P ps ih =>
    intro hA C B F hC
    simp only [incAgg] at hC
    split at hC
    · rename_i c b E C' B' F' hce hag
      cases hC
      have hPA : P.A.toC = pc := hA P (List.mem_cons_self ..)
      have h1 := incEval_sound hce s hs0 hs
      rw [hPA] at h1
      have h2 := ih (fun Q hQ => hA Q (List.mem_cons_of_mem _ hQ)) hag
      have hsplit : ∀ (X Y : List ℚ), ∑ m ∈ range n, ((coeffs (addL (scaleL (-P.w) X) Y) m : ℚ) : ℝ) * s ^ m
          = -(P.w : ℝ) * ∑ m ∈ range n, ((coeffs X m : ℚ) : ℝ) * s ^ m
            + ∑ m ∈ range n, ((coeffs Y m : ℚ) : ℝ) * s ^ m := by
        intro X Y
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [coeffs_addL, coeffs_scaleL]; push_cast; ring
      rw [hsplit c C', hsplit b B', List.map_cons, List.sum_cons]
      have hw : |(P.w : ℝ)| * |PhiW P (pc + (s : ℂ) * dd.toC)
          - (∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m
            + Real.log s * ∑ m ∈ range n, ((coeffs b m : ℚ) : ℝ) * s ^ m)|
          ≤ |(P.w : ℝ)| * E := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      rw [← abs_mul] at hw
      have e : -((P.w : ℝ) * PhiW P (pc + (s : ℂ) * dd.toC) +
            (List.map (fun P => (P.w : ℝ) * PhiW P (pc + (s : ℂ) * dd.toC)) ps).sum)
          - ((-(P.w : ℝ) * ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m
              + ∑ m ∈ range n, ((coeffs C' m : ℚ) : ℝ) * s ^ m)
            + Real.log s * (-(P.w : ℝ) * ∑ m ∈ range n, ((coeffs b m : ℚ) : ℝ) * s ^ m
              + ∑ m ∈ range n, ((coeffs B' m : ℚ) : ℝ) * s ^ m))
          = -((P.w : ℝ) * (PhiW P (pc + (s : ℂ) * dd.toC)
              - (∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m
                + Real.log s * ∑ m ∈ range n, ((coeffs b m : ℚ) : ℝ) * s ^ m)))
            + (-(List.map (fun P => (P.w : ℝ) * PhiW P (pc + (s : ℂ) * dd.toC)) ps).sum
              - (∑ m ∈ range n, ((coeffs C' m : ℚ) : ℝ) * s ^ m
                + Real.log s * ∑ m ∈ range n, ((coeffs B' m : ℚ) : ℝ) * s ^ m)) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      push_cast
      exact add_le_add hw h2
    · cases hC

end CatalanCore.Uniform.Decay.Breakpoint
