import CatalanCore.Uniform.Decay.NearFast.Rep6
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

theorem fG_toC (w : CQ) : (fG w).toC = w.toC * ((fDL w : ℕ) : ℂ) := by
  apply Complex.ext
  · simp only [GZ.toC_re, fG, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero,
      sub_zero, CQ.toC_re]
    have := sc_cast w.re (fDL w) (Nat.dvd_lcm_left _ _)
    rw [← Rat.cast_natCast, ← Rat.cast_mul, ← this]; push_cast; rfl
  · simp only [GZ.toC_im, fG, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, mul_zero,
      zero_add, CQ.toC_im, CQ.toC_re]
    have := sc_cast w.im (fDL w) (Nat.dvd_lcm_right _ _)
    rw [← Rat.cast_natCast, ← Rat.cast_mul, ← this]; push_cast; rfl

theorem fDw_pos (a : ℕ → ℚ) : ∀ N, 0 < prodDen a N := by
  intro N
  induction N with
  | zero => simp [prodDen]
  | succ N ih => unfold prodDen; exact Nat.mul_pos ih (a N).den_pos

theorem prod_re (z1 z2 w1 w2 : ℂ) (c1 c2 : ℤ) (h1 : z1 * (c1 : ℂ) = w1) (h2 : z2 * (c2 : ℂ) = w2)
    (hc : c1 * c2 ≠ 0) : (z1 * z2).re = (w1 * w2).re / ((c1 * c2 : ℤ) : ℝ) := by
  apply re_of_mul _ _ _ _ hc
  rw [← h1, ← h2]; push_cast; ring

theorem fmassI_cast (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) :
    ((fmassI a d (itab (fD z0 e : ℤ) (d + 2)) : ℤ) : ℂ)
      = (massQ a d : ℂ) * ((fDw a d : ℂ) * (fD z0 e : ℂ) ^ (d + 1)) := by
  unfold fmassI
  rw [Int.cast_mul, cast_sumI, iget_itab _ _ _ (by omega)]
  have h : ∑ k ∈ range (d + 1), ((fwI a d k : ℤ) : ℂ) = ∑ k ∈ range (d + 1), (wq a k : ℂ) * (fDw a d : ℂ) :=
    Finset.sum_congr rfl fun k hk => fwI_castC a d k (by have := Finset.mem_range.1 hk; omega)
  rw [h, ← Finset.sum_mul]
  unfold massQ
  push_cast
  ring

theorem PB_list_rep (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (m : ℕ) (hm : m < n) :
    (PBc a d z0 e m).toC * ((fDw a d : ℂ) * (fD z0 e : ℂ) ^ (d + 1))
      = (gget (fPB n a d z0 e) m).toC := by
  unfold fPB
  dsimp only
  rw [gget_map_range _ n m hm]
  exact PBc_rep a d z0 e (fun i hi => iget_itab _ _ i hi) (fun i hi => gget_gtab _ _ i hi) m
    (gget_gtab _ _ m hm)

theorem PA_list_rep (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (m : ℕ) (hm : m < n) :
    (PAc a d z0 e m).toC * ((fDw a d : ℂ) * (fD z0 e : ℂ) ^ (d + 1))
      = (gget (fPA n a d z0 e) m).toC := by
  unfold fPA
  dsimp only
  rw [gget_map_range _ n m hm]
  have hPB := PB_list_rep n a d z0 e m hm
  have hmass := fmassI_cast a d z0 e
  simp only [PAc, CQ.toC_sub, CQ.toC_ofQ, GZ.toC_add, GZ.toC_sub, GZ.toC_zero, sub_mul]
  rw [hPB]
  split_ifs with hm0
  · have : (GZ.toC ⟨fmassI a d (itab (fD z0 e : ℤ) (d + 2)), 0⟩) = ((fmassI a d (itab (fD z0 e : ℤ) (d + 2)) : ℤ) : ℂ) := by
      apply Complex.ext <;> simp [GZ.toC]
    rw [this, hmass]; ring
  · have : (GZ.toC ⟨0, 0⟩) = 0 := by apply Complex.ext <;> simp [GZ.toC]
    rw [this]; simp

theorem R_list_rep (n : ℕ) (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (m : ℕ) (hm : m < n) :
    (Rc a d z0 e m).toC * ((fDw a d : ℂ) * (((d + 1).factorial : ℕ) : ℂ) * (fD z0 e : ℂ) ^ d)
      = -(gget (fRR n a d z0 e) m).toC := by
  unfold fRR
  dsimp only
  rw [gget_map_range _ n m hm]
  refine Rc_rep a d z0 e (fun i hi => iget_itab _ _ i hi) (fun i hi => gget_gtab _ _ i hi) ?_ m
    (gget_gtab _ _ m hm)
  intro j hj
  simp [iget, List.getD_eq_getElem?_getD, List.getElem?_map, hj]

end CatalanCore.Uniform.Decay.NearFast
