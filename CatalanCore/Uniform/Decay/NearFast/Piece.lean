import CatalanCore.Uniform.Decay.NearFast.Rep8
set_option Elab.async false

/-!
# The fast piece evaluator (lane D, package D12)

`pieceEval2F` has the shape of `NearCells.pieceEval2`, with the model coefficients computed by the
Gaussian-integer algorithm of `Alg.lean` and rounded to the grid `1/GG`; the error bound is the one of
`pieceEval2` plus `6/GG · ∑ h^m`.  `pieceEval2F_imp` is the one soundness theorem: a successful fast
evaluation implies the success of `pieceEval2` with the same remainder terms, coefficients within
`6/GG`, and the error bound enlarged by exactly the rounding allowance.
-/

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

def fCQ (g : GZ) (DP : ℤ) : CQ := ⟨(g.re : ℚ) / DP, (g.im : ℚ) / DP⟩

/-- Rounding allowance of one piece. -/
def rndAllow (n : ℕ) (h : ℚ) : ℚ := (6 : ℚ) / (GG : ℚ) * lsum (fun m => h ^ m) n

def pieceEval2F (n : ℕ) (P : WP) (zc dd : CQ) (h : ℚ) : Option (List ℚ × ℚ × List Tm) :=
  if decide (P.a.length - 1 + 2 ≤ n) && decide ((CQ.sub P.B P.A).nsq ≠ 0) &&
      sideOk3 (z0of P.A P.B zc) (eof P.A P.B dd) h &&
      decide ((z0of P.A P.B zc).nsq ≠ 0) &&
      decide ((CQ.sub CQ.one (z0of P.A P.B zc)).nsq ≠ 0) &&
      decide (sqrtUp ((q0of (z0of P.A P.B zc) (eof P.A P.B dd)).nsq * h ^ 2) < 1) &&
      decide (sqrtUp ((q1of (z0of P.A P.B zc) (eof P.A P.B dd)).nsq * h ^ 2) < 1) &&
      decide (0 ≤ h) then
    match logHalf (CQ.sub P.B P.A), logHalf (CQ.neg (z0of P.A P.B zc)),
        argEnc (CQ.neg (z0of P.A P.B zc)), logHalf (CQ.sub CQ.one (z0of P.A P.B zc)),
        argEnc (CQ.sub CQ.one (z0of P.A P.B zc)) with
    | some (lv, εv), some (l0, e0l), some (a0, e0a), some (l1, e1l), some (a1, e1a) =>
      let z0 := z0of P.A P.B zc
      let e := eof P.A P.B dd
      let DP : ℤ := (fDw (coeffs P.a) (P.a.length - 1) : ℤ) *
        iget (itab (fD z0 e : ℤ) (P.a.length - 1 + 2)) (P.a.length - 1 + 1)
      let PAl := (List.range n).map fun m => fCQ (gget (fPA n (coeffs P.a) (P.a.length - 1) z0 e) m) DP
      let PBl := (List.range n).map fun m => fCQ (gget (fPB n (coeffs P.a) (P.a.length - 1) z0 e) m) DP
      some ((fC n (coeffs P.a) (P.a.length - 1) z0 e ⟨l0, a0⟩ ⟨l1, a1⟩ lv).map
          (fun x : ℤ => (x : ℚ) / (GG : ℚ)),
        lsum (fun m => (nrmQ (ccoef PAl m) * (e1l + e1a) + nrmQ (ccoef PBl m) * (e0l + e0a)) * h ^ m) n
          + |massQ (coeffs P.a) (P.a.length - 1)| * εv + rndAllow n h,
        [⟨q1of z0 e, PAl⟩, ⟨q0of z0 e, PBl⟩])
    | _, _, _, _, _ => none
  else none

theorem CQ_ext' {a b : CQ} (h : a.toC = b.toC) : a = b := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [CQ.toC_re, CQ.toC_im] at h1 h2
  have e1 : a.re = b.re := Rat.cast_injective (α := ℝ) h1
  have e2 : a.im = b.im := Rat.cast_injective (α := ℝ) h2
  obtain ⟨ar, ai⟩ := a
  obtain ⟨br, bi⟩ := b
  simp only at e1 e2
  rw [e1, e2]

theorem fCQ_toC (g : GZ) (DP : ℤ) : (fCQ g DP).toC = g.toC / (DP : ℂ) := by
  apply Complex.ext
  · simp [fCQ, CQ.toC, GZ.toC, Complex.div_intCast_re]
  · simp [fCQ, CQ.toC, GZ.toC, Complex.div_intCast_im]

theorem fCQ_PA (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (m : ℕ) (hm : m < n) :
    fCQ (gget (fPA n a d z0 e) m) ((fDw a d : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) (d + 1))
      = PAc a d z0 e m := by
  apply CQ_ext'
  rw [fCQ_toC, ← PA_list_rep n a d z0 e m hm, ← DP_cast a d z0 e]
  have : (((fDw a d : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) (d + 1) : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (pos_DP a d z0 e).ne'
  field_simp

theorem fCQ_PB (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (m : ℕ) (hm : m < n) :
    fCQ (gget (fPB n a d z0 e) m) ((fDw a d : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) (d + 1))
      = PBc a d z0 e m := by
  apply CQ_ext'
  rw [fCQ_toC, ← PB_list_rep n a d z0 e m hm, ← DP_cast a d z0 e]
  have : (((fDw a d : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) (d + 1) : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (pos_DP a d z0 e).ne'
  field_simp

theorem getD_map_zero (l : List ℤ) (f : ℤ → ℚ) (hf : f 0 = 0) (i : ℕ) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  by_cases h : i < l.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  · have h' : ¬ i < (l.map f).length := by simpa using h
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h), hf]

theorem pieceEval2F_imp {n : ℕ} {P : WP} {zc dd : CQ} {h : ℚ} {cF : List ℚ} {EF : ℚ} {T : List Tm}
    (hev : pieceEval2F n P zc dd h = some (cF, EF, T)) :
    ∃ c E, pieceEval2 n P zc dd h = some (c, E, T) ∧
      (∀ m, m < n → |((coeffs cF m : ℚ) : ℝ) - ((coeffs c m : ℚ) : ℝ)| ≤ 6 / (GG : ℝ)) ∧
      EF = E + rndAllow n h := by
  unfold pieceEval2F at hev
  split at hev
  · rename_i hc
    have hc' := hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨hn, hv⟩, hside⟩, hz0nsq⟩, h1z0nsq⟩, hr0⟩, hr1⟩, hh⟩ := hc
    split at hev
    · rename_i lv εv l0 e0l a0 e0a l1 e1l a1 e1a hlv hl0 ha0 hl1 ha1
      cases hev
      generalize hz0def : z0of P.A P.B zc = z0 at *
      generalize hedef : eof P.A P.B dd = e at *
      have hlist : ∀ m, m < n →
          fCQ (gget (fPA n (coeffs P.a) (P.a.length - 1) z0 e) m)
            ((fDw (coeffs P.a) (P.a.length - 1) : ℤ) *
              iget (itab (fD z0 e : ℤ) (P.a.length - 1 + 2)) (P.a.length - 1 + 1))
          = PAc (coeffs P.a) (P.a.length - 1) z0 e m := fun m hm =>
        fCQ_PA n (coeffs P.a) (P.a.length - 1) z0 e m hm
      have hlistB : ∀ m, m < n →
          fCQ (gget (fPB n (coeffs P.a) (P.a.length - 1) z0 e) m)
            ((fDw (coeffs P.a) (P.a.length - 1) : ℤ) *
              iget (itab (fD z0 e : ℤ) (P.a.length - 1 + 2)) (P.a.length - 1 + 1))
          = PBc (coeffs P.a) (P.a.length - 1) z0 e m := fun m hm =>
        fCQ_PB n (coeffs P.a) (P.a.length - 1) z0 e m hm
      have hPAl : ((List.range n).map fun m =>
          fCQ (gget (fPA n (coeffs P.a) (P.a.length - 1) z0 e) m)
            ((fDw (coeffs P.a) (P.a.length - 1) : ℤ) *
              iget (itab (fD z0 e : ℤ) (P.a.length - 1 + 2)) (P.a.length - 1 + 1)))
          = (List.range n).map (PAc (coeffs P.a) (P.a.length - 1) z0 e) :=
        List.map_congr_left fun m hm => hlist m (List.mem_range.1 hm)
      have hPBl : ((List.range n).map fun m =>
          fCQ (gget (fPB n (coeffs P.a) (P.a.length - 1) z0 e) m)
            ((fDw (coeffs P.a) (P.a.length - 1) : ℤ) *
              iget (itab (fD z0 e : ℤ) (P.a.length - 1 + 2)) (P.a.length - 1 + 1)))
          = (List.range n).map (PBc (coeffs P.a) (P.a.length - 1) z0 e) :=
        List.map_congr_left fun m hm => hlistB m (List.mem_range.1 hm)
      refine ⟨(List.range n).map (pieceCoef n P z0 e ⟨l0, a0⟩ ⟨l1, a1⟩ lv),
        lsum (fun m =>
            (nrmQ (PAc (coeffs P.a) (P.a.length - 1) z0 e m) * (e1l + e1a)
             + nrmQ (PBc (coeffs P.a) (P.a.length - 1) z0 e m) * (e0l + e0a)) * h ^ m) n
        + |massQ (coeffs P.a) (P.a.length - 1)| * εv, ?_, ?_, ?_⟩
      · unfold pieceEval2
        rw [hz0def, hedef, if_pos hc']
        simp only [hlv, hl0, ha0, hl1, ha1]
        rw [hPAl, hPBl]
      · intro m hm
        have hcF : coeffs ((fC n (coeffs P.a) (P.a.length - 1) z0 e ⟨l0, a0⟩ ⟨l1, a1⟩ lv).map
            (fun x : ℤ => (x : ℚ) / (GG : ℚ))) m
            = (((fC n (coeffs P.a) (P.a.length - 1) z0 e ⟨l0, a0⟩ ⟨l1, a1⟩ lv).getD m 0 : ℤ) : ℚ) / (GG : ℚ) := by
          unfold coeffs
          exact getD_map_zero _ (fun x : ℤ => (x : ℚ) / (GG : ℚ)) (by simp) m
        have hcc : coeffs ((List.range n).map (pieceCoef n P z0 e ⟨l0, a0⟩ ⟨l1, a1⟩ lv)) m
            = pieceCoef n P z0 e ⟨l0, a0⟩ ⟨l1, a1⟩ lv m := by
          simp [coeffs, List.getD_eq_getElem?_getD, List.getElem?_map, hm]
        rw [hcF, hcc]
        have := fC_close n P z0 e ⟨l0, a0⟩ ⟨l1, a1⟩ lv hn hz0nsq h1z0nsq m hm
        push_cast
        exact this
      · have e1 : lsum (fun m => (nrmQ (ccoef ((List.range n).map fun m =>
              fCQ (gget (fPA n (coeffs P.a) (P.a.length - 1) z0 e) m)
                ((fDw (coeffs P.a) (P.a.length - 1) : ℤ) *
                  iget (itab (fD z0 e : ℤ) (P.a.length - 1 + 2)) (P.a.length - 1 + 1))) m) * (e1l + e1a)
              + nrmQ (ccoef ((List.range n).map fun m =>
              fCQ (gget (fPB n (coeffs P.a) (P.a.length - 1) z0 e) m)
                ((fDw (coeffs P.a) (P.a.length - 1) : ℤ) *
                  iget (itab (fD z0 e : ℤ) (P.a.length - 1 + 2)) (P.a.length - 1 + 1))) m) * (e0l + e0a)) * h ^ m) n
            = lsum (fun m => (nrmQ (PAc (coeffs P.a) (P.a.length - 1) z0 e m) * (e1l + e1a)
             + nrmQ (PBc (coeffs P.a) (P.a.length - 1) z0 e m) * (e0l + e0a)) * h ^ m) n := by
          rw [hPAl, hPBl, lsum_eq, lsum_eq]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [ccoef_map_range _ n m (Finset.mem_range.1 hm), ccoef_map_range _ n m (Finset.mem_range.1 hm)]
        rw [e1]
    · cases hev
  · cases hev

end CatalanCore.Uniform.Decay.NearFast
