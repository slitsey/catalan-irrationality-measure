import CatalanCore.Uniform.Decay.NearFast.Alg
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

namespace GZ

theorem toC_mul (a b : GZ) : (a.mul b).toC = a.toC * b.toC := by
  apply Complex.ext <;> simp [toC, mul]
theorem toC_add (a b : GZ) : (a.add b).toC = a.toC + b.toC := by
  apply Complex.ext <;> simp [toC, add]
theorem toC_sub (a b : GZ) : (a.sub b).toC = a.toC - b.toC := by
  apply Complex.ext <;> simp [toC, sub]
theorem toC_smul (c : ℤ) (a : GZ) : (a.smul c).toC = (c : ℂ) * a.toC := by
  apply Complex.ext <;> simp [toC, smul]
theorem toC_conj (a : GZ) : (a.conj).toC = (starRingEnd ℂ) a.toC := by
  apply Complex.ext <;> simp [toC, conj]
theorem toC_zero : zero.toC = 0 := by apply Complex.ext <;> simp [toC, zero]
theorem toC_one : one.toC = 1 := by apply Complex.ext <;> simp [toC, one]
theorem toC_re (a : GZ) : a.toC.re = (a.re : ℝ) := rfl
theorem toC_im (a : GZ) : a.toC.im = (a.im : ℝ) := rfl
theorem nsq_cast (a : GZ) : ((a.nsq : ℤ) : ℝ) = Complex.normSq a.toC := by
  simp [nsq, toC, Complex.normSq_apply]
theorem toC_mul_conj (a : GZ) : a.toC * (starRingEnd ℂ) a.toC = ((a.nsq : ℤ) : ℂ) := by
  rw [Complex.mul_conj, ← nsq_cast]; simp

theorem mul_re_cast (a b : GZ) : (((a.mul b).re : ℤ) : ℝ) = (a.toC * b.toC).re := by
  simp [toC, mul, Complex.mul_re]

end GZ

theorem toC_sumG (f : ℕ → GZ) (n : ℕ) : (sumG f n).toC = ∑ i ∈ range n, (f i).toC := by
  induction n with
  | zero => simp [sumG, GZ.toC_zero]
  | succ n ih => rw [sumG, GZ.toC_add, ih, Finset.sum_range_succ]

theorem cast_sumI (f : ℕ → ℤ) (n : ℕ) {K : Type*} [Ring K] :
    ((sumI f n : ℤ) : K) = ∑ i ∈ range n, ((f i : ℤ) : K) := by
  induction n with
  | zero => simp [sumI]
  | succ n ih => rw [sumI, Int.cast_add, ih, Finset.sum_range_succ]

theorem gget_ptabAux (z : GZ) : ∀ (N : ℕ) (cur : GZ) (i : ℕ), i < N →
    (gget (ptabAux z cur N) i).toC = cur.toC * z.toC ^ i := by
  intro N
  induction N with
  | zero => intro cur i h; omega
  | succ N ih =>
    intro cur i h
    cases i with
    | zero => simp [ptabAux, gget]
    | succ i =>
      have := ih (cur.mul z) i (by omega)
      simp only [ptabAux, gget, List.getD_cons_succ] at this ⊢
      rw [this, GZ.toC_mul]; ring

theorem gget_gtab (z : GZ) (N i : ℕ) (h : i < N) : (gget (gtab z N) i).toC = z.toC ^ i := by
  have := gget_ptabAux z N GZ.one i h
  rw [GZ.toC_one, one_mul] at this
  exact this

theorem iget_itabAux (D : ℤ) : ∀ (N : ℕ) (cur : ℤ) (i : ℕ), i < N →
    iget (itabAux D cur N) i = cur * D ^ i := by
  intro N
  induction N with
  | zero => intro cur i h; omega
  | succ N ih =>
    intro cur i h
    cases i with
    | zero => simp [itabAux, iget]
    | succ i =>
      have := ih (cur * D) i (by omega)
      simp only [itabAux, iget, List.getD_cons_succ] at this ⊢
      rw [this]; ring

theorem iget_itab (D : ℤ) (N i : ℕ) (h : i < N) : iget (itab D N) i = D ^ i := by
  have := iget_itabAux D N 1 i h
  rw [one_mul] at this
  exact this

theorem sc_cast (q : ℚ) (D : ℕ) (h : q.den ∣ D) : ((sc q D : ℤ) : ℚ) = q * D := by
  obtain ⟨k, hk⟩ := h
  have hpos : 0 < q.den := q.den_pos
  have hdiv : D / q.den = k := by rw [hk]; exact Nat.mul_div_cancel_left k hpos
  unfold sc
  rw [hdiv]
  push_cast
  rw [hk]
  push_cast
  rw [← mul_assoc, Rat.mul_den_eq_num]

theorem fD_pos (z0 e : CQ) : 0 < fD z0 e :=
  Nat.lcm_pos (Nat.lcm_pos z0.re.den_pos z0.im.den_pos) (Nat.lcm_pos e.re.den_pos e.im.den_pos)

theorem dvd_fD_z0re (z0 e : CQ) : z0.re.den ∣ fD z0 e :=
  (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _)
theorem dvd_fD_z0im (z0 e : CQ) : z0.im.den ∣ fD z0 e :=
  (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _)
theorem dvd_fD_ere (z0 e : CQ) : e.re.den ∣ fD z0 e :=
  (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)
theorem dvd_fD_eim (z0 e : CQ) : e.im.den ∣ fD z0 e :=
  (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)

theorem fZ_toC (z0 e : CQ) : (fZ z0 e).toC = z0.toC * (fD z0 e : ℂ) := by
  apply Complex.ext
  · simp only [GZ.toC_re, fZ, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero,
      sub_zero, CQ.toC_re]
    have := sc_cast z0.re (fD z0 e) (dvd_fD_z0re z0 e)
    rw [← Rat.cast_natCast, ← Rat.cast_mul, ← this]; push_cast; rfl
  · simp only [GZ.toC_im, fZ, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, mul_zero,
      zero_add, CQ.toC_im, CQ.toC_re]
    have := sc_cast z0.im (fD z0 e) (dvd_fD_z0im z0 e)
    rw [← Rat.cast_natCast, ← Rat.cast_mul, ← this]; push_cast; rfl

theorem fE_toC (z0 e : CQ) : (fE z0 e).toC = e.toC * (fD z0 e : ℂ) := by
  apply Complex.ext
  · simp only [GZ.toC_re, fE, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero,
      sub_zero, CQ.toC_re]
    have := sc_cast e.re (fD z0 e) (dvd_fD_ere z0 e)
    rw [← Rat.cast_natCast, ← Rat.cast_mul, ← this]; push_cast; rfl
  · simp only [GZ.toC_im, fE, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, mul_zero,
      zero_add, CQ.toC_im, CQ.toC_re]
    have := sc_cast e.im (fD z0 e) (dvd_fD_eim z0 e)
    rw [← Rat.cast_natCast, ← Rat.cast_mul, ← this]; push_cast; rfl

end CatalanCore.Uniform.Decay.NearFast
