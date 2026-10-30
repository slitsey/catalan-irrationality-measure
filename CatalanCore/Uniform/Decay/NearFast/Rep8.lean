module

public import CatalanCore.Uniform.Decay.NearFast.Rep7

@[expose] public section
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

theorem DP_cast (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) :
    (((fDw a d : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) (d + 1) : ℤ) : ℂ)
      = (fDw a d : ℂ) * (fD z0 e : ℂ) ^ (d + 1) := by
  rw [iget_itab _ _ _ (by omega)]; push_cast; ring

theorem pos_DP (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) :
    0 < (fDw a d : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) (d + 1) := by
  rw [iget_itab _ _ _ (by omega)]
  have h1 : 0 < (fDw a d : ℤ) := by exact_mod_cast fDw_pos (wq a) (d + 1)
  have h2 : 0 < (fD z0 e : ℤ) := by exact_mod_cast fD_pos z0 e
  positivity

theorem pos_R (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) :
    0 < (fDw a d : ℤ) * ((d + 1).factorial : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) d := by
  rw [iget_itab _ _ _ (by omega)]
  have h1 : 0 < (fDw a d : ℤ) := by exact_mod_cast fDw_pos (wq a) (d + 1)
  have h2 : 0 < (fD z0 e : ℤ) := by exact_mod_cast fD_pos z0 e
  have h3 : 0 < ((d + 1).factorial : ℤ) := by exact_mod_cast Nat.factorial_pos _
  positivity

theorem pos_J (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (QD : ℤ) (hQD : 0 < QD) (n m : ℕ) (hm : m < n) :
    0 < ((fDw a d : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) (d + 1)) * ((n - 1).factorial : ℤ)
      * iget (itab QD n) m := by
  rw [iget_itab _ _ _ hm]
  have h1 := pos_DP a d z0 e
  have h3 : 0 < ((n - 1).factorial : ℤ) := by exact_mod_cast Nat.factorial_pos _
  positivity

theorem fC_close (n : ℕ) (P : WP) (z0 e L0 L1 : CQ) (lv : ℚ)
    (hn : P.a.length - 1 + 2 ≤ n) (h0 : z0.nsq ≠ 0) (h1 : (CQ.sub CQ.one z0).nsq ≠ 0)
    (m : ℕ) (hm : m < n) :
    |(((fC n (coeffs P.a) (P.a.length - 1) z0 e L0 L1 lv).getD m 0 : ℤ) : ℝ) / (GG : ℝ)
      - ((pieceCoef n P z0 e L0 L1 lv m : ℚ) : ℝ)| ≤ 6 / (GG : ℝ) := by
  rw [pieceCoef_cast]
  generalize coeffs P.a = a at *
  generalize P.a.length - 1 = d at *
  unfold fC
  dsimp only
  rw [getD_map_range _ _ _ hm]
  have hDPc := DP_cast a d z0 e
  have hPA : ∀ j, j < n → (PAc a d z0 e j).toC * (((fDw a d : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) (d + 1) : ℤ) : ℂ)
      = (gget (fPA n a d z0 e) j).toC := fun j hj => by rw [hDPc]; exact PA_list_rep n a d z0 e j hj
  have hPB : ∀ j, j < n → (PBc a d z0 e j).toC * (((fDw a d : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) (d + 1) : ℤ) : ℂ)
      = (gget (fPB n a d z0 e) j).toC := fun j hj => by rw [hDPc]; exact PB_list_rep n a d z0 e j hj
  have hQD1 := fQD1_pos z0 e h1
  have hQD0 := fQD0_pos z0 e h0
  refine fCm_close n a d lv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ _ _ _ _ _ _ (pos_DP a d z0 e) ?_ ?_
    (pos_R a d z0 e) (pos_J a d z0 e _ hQD1 n m hm) (pos_J a d z0 e _ hQD0 n m hm) ?_ ?_ ?_ ?_ ?_
  · exact_mod_cast Nat.lcm_pos L0.re.den_pos L0.im.den_pos
  · exact_mod_cast Nat.lcm_pos L1.re.den_pos L1.im.den_pos
  · -- hP1
    have := prod_re (PAc a d z0 e m).toC L1.toC (gget (fPA n a d z0 e) m).toC (fG L1).toC _
      ((fDL L1 : ℕ) : ℤ) (hPA m hm) (by rw [fG_toC]; push_cast; rfl)
      (mul_ne_zero (pos_DP a d z0 e).ne' (by exact_mod_cast (Nat.lcm_pos L1.re.den_pos L1.im.den_pos).ne'))
    rw [this, ← GZ.mul_re_cast]
  · have := prod_re (PBc a d z0 e m).toC L0.toC (gget (fPB n a d z0 e) m).toC (fG L0).toC _
      ((fDL L0 : ℕ) : ℤ) (hPB m hm) (by rw [fG_toC]; push_cast; rfl)
      (mul_ne_zero (pos_DP a d z0 e).ne' (by exact_mod_cast (Nat.lcm_pos L0.re.den_pos L0.im.den_pos).ne'))
    rw [this, ← GZ.mul_re_cast]
  · have hc := R_list_rep n a d z0 e m hm
    have := re_of_mul (Rc a d z0 e m).toC (-(gget (fRR n a d z0 e) m).toC)
      ((fDw a d : ℤ) * ((d + 1).factorial : ℤ) * iget (itab (fD z0 e : ℤ) (d + 2)) d)
      (by rw [iget_itab _ _ _ (by omega)]; push_cast; exact hc) (pos_R a d z0 e).ne'
    rw [this, Complex.neg_re, GZ.toC_re]
  · exact jetRe_rep n m (PAc a d z0 e) (q1of z0 e) (fPA n a d z0 e) (fQN1 z0 e) _ _ _ _ hm
      (fun j hj => hPA j (by omega)) (q1_rep z0 e h1) hQD1 (pos_DP a d z0 e)
      (fun j hj => iget_itab _ _ j hj) (fun i hi => gget_gtab _ _ i hi)
  · exact jetRe_rep n m (PBc a d z0 e) (q0of z0 e) (fPB n a d z0 e) (fQN0 z0 e) _ _ _ _ hm
      (fun j hj => hPB j (by omega)) (q0_rep z0 e h0) hQD0 (pos_DP a d z0 e)
      (fun j hj => iget_itab _ _ j hj) (fun i hi => gget_gtab _ _ i hi)

end CatalanCore.Uniform.Decay.NearFast
