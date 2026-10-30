module

public import CatalanCore.Uniform.Decay.NearCells.Eval

@[expose] public section
set_option Elab.async false

/-!
# Evaluating the order-`n` model of one segment (lane D, package D6b)

`pieceEval n P zc dd h = some (c, E)` computes, in the kernel, rational model coefficients `c`
(length `n`) and an error `E`; `pieceEval_sound` proves
`|∫ density · log‖z - p(t)‖ - ∑_m c_m s^m| ≤ E` for `z = zc + s dd`, `|s| ≤ h`.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools

/-- Auxiliary: `(I+1)/(d 2^20)`. -/
def sqrtUpAux (y : ℚ) : ℚ :=
  ((Nat.sqrt (y.num.toNat * y.den) + 1 : ℕ) : ℚ) / ((y.den : ℚ) * 2 ^ 20)

/-- Rational upper bound of `√x`, `x ≥ 0`. -/
def sqrtUp (x : ℚ) : ℚ := sqrtUpAux (x * 4 ^ 20)

theorem sqrtUp_nonneg (x : ℚ) : 0 ≤ sqrtUp x := by
  unfold sqrtUp sqrtUpAux; positivity

theorem le_sqrtUp_sq {x : ℚ} (hx : 0 ≤ x) : x ≤ sqrtUp x ^ 2 := by
  unfold sqrtUp
  generalize hy : x * 4 ^ 20 = y
  have hy0 : 0 ≤ y := by rw [← hy]; positivity
  have hnum : (y.num.toNat : ℤ) = y.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hy0)
  have hd : (0 : ℚ) < y.den := by exact_mod_cast y.den_pos
  have hyq : y = (y.num : ℚ) / (y.den : ℚ) := (Rat.num_div_den y).symm
  have hlt := Nat.lt_succ_sqrt (y.num.toNat * y.den)
  have hlt' : ((y.num : ℚ)) * (y.den : ℚ) ≤
      ((Nat.sqrt (y.num.toNat * y.den) + 1 : ℕ) : ℚ) * ((Nat.sqrt (y.num.toNat * y.den) + 1 : ℕ) : ℚ) := by
    have : (y.num.toNat : ℚ) = (y.num : ℚ) := by exact_mod_cast hnum
    rw [← this]; exact_mod_cast hlt.le
  have hx' : x = y / 4 ^ 20 := by rw [← hy]; field_simp
  unfold sqrtUpAux
  generalize ((Nat.sqrt (y.num.toNat * y.den) + 1 : ℕ) : ℚ) = N at hlt' ⊢
  generalize (y.num : ℚ) = nn at hyq hlt'
  generalize (y.den : ℚ) = dd at hyq hlt' hd ⊢
  rw [hx', div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [hyq]
  have hy2 : dd ≠ 0 := hd.ne'
  have h4 : (4 : ℚ) ^ 20 = (2 ^ 20) ^ 2 := by norm_num
  rw [h4]
  field_simp
  nlinarith [hlt', hd]

/-- Evaluate one segment's model. -/
structure WP where
  w : ℚ
  a : List ℚ
  A : CQ
  B : CQ
  M : ℚ
  Lq : ℚ

def pieceCoef (n : ℕ) (P : WP) (z0 e : CQ) (L0 L1 : CQ) (lv : ℚ) (m : ℕ) : ℚ :=
  (CQ.add (CQ.add (CQ.add (CQ.add (CQ.mul (PAc (coeffs P.a) (P.a.length - 1) z0 e m) L1)
    (CQ.mul (PBc (coeffs P.a) (P.a.length - 1) z0 e m) L0))
    (Rc (coeffs P.a) (P.a.length - 1) z0 e m))
    (jetc (PAc (coeffs P.a) (P.a.length - 1) z0 e) (q1of z0 e) m))
    (jetc (PBc (coeffs P.a) (P.a.length - 1) z0 e) (q0of z0 e) m)).re
  + (if m = 0 then massQ (coeffs P.a) (P.a.length - 1) * lv else 0)


def pieceEval (n : ℕ) (P : WP) (zc dd : CQ) (h : ℚ) : Option (List ℚ × ℚ) :=
  if decide (P.a.length - 1 + 2 ≤ n) && decide ((CQ.sub P.B P.A).nsq ≠ 0) &&
      sideOk (z0of P.A P.B zc) (eof P.A P.B dd) h &&
      decide ((z0of P.A P.B zc).nsq ≠ 0) &&
      decide ((CQ.sub CQ.one (z0of P.A P.B zc)).nsq ≠ 0) &&
      decide (sqrtUp ((q0of (z0of P.A P.B zc) (eof P.A P.B dd)).nsq * h ^ 2) < 1) &&
      decide (sqrtUp ((q1of (z0of P.A P.B zc) (eof P.A P.B dd)).nsq * h ^ 2) < 1) &&
      decide (0 ≤ h) then
    match logHalf (CQ.sub P.B P.A), logHalf (CQ.neg (z0of P.A P.B zc)),
        argEnc (CQ.neg (z0of P.A P.B zc)), logHalf (CQ.sub CQ.one (z0of P.A P.B zc)),
        argEnc (CQ.sub CQ.one (z0of P.A P.B zc)) with
    | some (lv, εv), some (l0, e0l), some (a0, e0a), some (l1, e1l), some (a1, e1a) =>
      some ((List.range n).map (pieceCoef n P (z0of P.A P.B zc) (eof P.A P.B dd) ⟨l0, a0⟩ ⟨l1, a1⟩ lv),
        jbQ (PAc (coeffs P.a) (P.a.length - 1) (z0of P.A P.B zc) (eof P.A P.B dd)) n
            (sqrtUp ((q1of (z0of P.A P.B zc) (eof P.A P.B dd)).nsq * h ^ 2)) h
        + jbQ (PBc (coeffs P.a) (P.a.length - 1) (z0of P.A P.B zc) (eof P.A P.B dd)) n
            (sqrtUp ((q0of (z0of P.A P.B zc) (eof P.A P.B dd)).nsq * h ^ 2)) h
        + lsum (fun m =>
            (nrmQ (PAc (coeffs P.a) (P.a.length - 1) (z0of P.A P.B zc) (eof P.A P.B dd) m) * (e1l + e1a)
             + nrmQ (PBc (coeffs P.a) (P.a.length - 1) (z0of P.A P.B zc) (eof P.A P.B dd) m) * (e0l + e0a))
              * h ^ m) n
        + |massQ (coeffs P.a) (P.a.length - 1)| * εv)
    | _, _, _, _, _ => none
  else none


theorem nsq_ne_zero_of_im {w : CQ} (h : w.im ≠ 0) : w.nsq ≠ 0 := by
  intro h0
  unfold CQ.nsq at h0
  have hp : 0 < w.im * w.im := mul_self_pos.2 h
  nlinarith [mul_self_nonneg w.re]

theorem logC_close {w : CQ} (hw : w.nsq ≠ 0) {l εl a εa : ℚ} (hl : logHalf w = some (l, εl))
    (ha : argEnc w = some (a, εa)) :
    ‖Complex.log w.toC - (CQ.mk l a).toC‖ ≤ (εl : ℝ) + εa := by
  have h1 := logHalf_sound hw hl
  have h2 := argEnc_sound ha
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : (Complex.log w.toC - (CQ.mk l a).toC).re = Real.log ‖w.toC‖ - (l : ℝ) := by
    simp [Complex.log_re, CQ.toC]
  have e2 : (Complex.log w.toC - (CQ.mk l a).toC).im = Complex.arg w.toC - (a : ℝ) := by
    simp [Complex.log_im, CQ.toC]
  rw [e1, e2, abs_sub_comm, abs_sub_comm (Complex.arg _)]
  exact add_le_add h1 h2

theorem cmodel_close (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (L0 L1 : ℂ) (L0t L1t : CQ) (δ0 δ1 : ℝ)
    (h0 : ‖L0 - L0t.toC‖ ≤ δ0) (h1 : ‖L1 - L1t.toC‖ ≤ δ1) (m : ℕ) :
    |cmodel a d z0 e L0 L1 m
      - (((CQ.add (CQ.add (CQ.add (CQ.add (CQ.mul (PAc a d z0 e m) L1t) (CQ.mul (PBc a d z0 e m) L0t))
          (Rc a d z0 e m)) (jetc (PAc a d z0 e) (q1of z0 e) m))
          (jetc (PBc a d z0 e) (q0of z0 e) m)).re : ℚ) : ℝ)|
    ≤ (nrmQ (PAc a d z0 e m) : ℝ) * δ1 + (nrmQ (PBc a d z0 e m) : ℝ) * δ0 := by
  have e1 : cmodel a d z0 e L0 L1 m
      - (((CQ.add (CQ.add (CQ.add (CQ.add (CQ.mul (PAc a d z0 e m) L1t) (CQ.mul (PBc a d z0 e m) L0t))
          (Rc a d z0 e m)) (jetc (PAc a d z0 e) (q1of z0 e) m))
          (jetc (PBc a d z0 e) (q0of z0 e) m)).re : ℚ) : ℝ)
      = ((PAc a d z0 e m).toC * (L1 - L1t.toC) + (PBc a d z0 e m).toC * (L0 - L0t.toC)).re := by
    rw [← CQ.toC_re]
    unfold cmodel
    simp only [CQ.toC_add, CQ.toC_mul]
    rw [← Complex.sub_re]
    congr 1; ring
  rw [e1]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  exact add_le_add (mul_le_mul (norm_le_nrmQ _) h1 (norm_nonneg _) (by exact_mod_cast nrmQ_nonneg _))
    (mul_le_mul (norm_le_nrmQ _) h0 (norm_nonneg _) (by exact_mod_cast nrmQ_nonneg _))


theorem pieceEval_sound {n : ℕ} {P : WP} {zc dd : CQ} {h : ℚ} {c : List ℚ} {E : ℚ}
    (hev : pieceEval n P zc dd h = some (c, E)) (s : ℝ) (hs : |s| ≤ h) :
    |(∫ t in (0 : ℝ)..1, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * t ^ k) *
        Real.log ‖(zc.toC + (s : ℂ) * dd.toC) - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖)
      - ∑ m ∈ range n, ((coeffs c m : ℚ) : ℝ) * s ^ m| ≤ (E : ℝ) := by
  unfold pieceEval at hev
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
      have hM := piece_model (coeffs P.a) (P.a.length - 1) n hn P.A P.B zc dd h
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
      have hlogB : Real.log ‖P.B.toC - P.A.toC‖ = Real.log ‖P.B.toC - P.A.toC‖ := rfl
      -- decomposition
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
      have hE : ((jbQ (PAc (coeffs P.a) (P.a.length - 1) z0 e) n
            (sqrtUp ((q1of z0 e).nsq * h ^ 2)) h
          + jbQ (PBc (coeffs P.a) (P.a.length - 1) z0 e) n
            (sqrtUp ((q0of z0 e).nsq * h ^ 2)) h
          + lsum (fun m => (nrmQ (PAc (coeffs P.a) (P.a.length - 1) z0 e m) * (e1l + e1a)
             + nrmQ (PBc (coeffs P.a) (P.a.length - 1) z0 e m) * (e0l + e0a)) * h ^ m) n
          + |massQ (coeffs P.a) (P.a.length - 1)| * εv : ℚ) : ℝ)
          = (jbQ (PAc (coeffs P.a) (P.a.length - 1) z0 e) n
            (sqrtUp ((q1of z0 e).nsq * h ^ 2)) h : ℝ)
          + (jbQ (PBc (coeffs P.a) (P.a.length - 1) z0 e) n
            (sqrtUp ((q0of z0 e).nsq * h ^ 2)) h : ℝ)
          + ∑ m ∈ range n, ((nrmQ (PAc (coeffs P.a) (P.a.length - 1) z0 e m) : ℝ) * ((e1l : ℝ) + e1a)
            + (nrmQ (PBc (coeffs P.a) (P.a.length - 1) z0 e m) : ℝ) * ((e0l : ℝ) + e0a)) * (h : ℝ) ^ m
          + |mass| * εv := by
        rw [Rat.cast_add, Rat.cast_add, Rat.cast_add, lsum_eq]
        push_cast
        rfl
      rw [hE]
      rw [abs_le] at hM h2 hdiffS ⊢
      constructor <;> linarith [hM.1, hM.2, h2.1, h2.2, hdiffS.1, hdiffS.2]
    · cases hev
  · cases hev

end CatalanCore.Uniform.Decay.NearCells
