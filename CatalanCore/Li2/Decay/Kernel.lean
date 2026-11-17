module
public import CatalanCore.Li2.Decay.Series
public import CatalanCore.Uniform.Decay.Jet.PoleSeries
public import CatalanCore.Li2.Uniform.Geometry
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators Polynomial
namespace CatalanCore.Li2.Decay
noncomputable def basicKernel (z : ℝ) (u : ℂ) : ℂ :=
  if z<0 then (Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*u)
  else (Real.pi:ℂ)*Complex.cos ((Real.pi:ℂ)*u)/Complex.sin ((Real.pi:ℂ)*u)+
    (if 0 ≤ u.im then (Real.pi:ℂ)*Complex.I else -(Real.pi:ℂ)*Complex.I)
noncomputable def basicKernelPrime (z : ℝ) (u : ℂ) : ℂ :=
  if z<0 then -(Real.pi:ℂ)^2*Complex.cos ((Real.pi:ℂ)*u)/Complex.sin ((Real.pi:ℂ)*u)^2
  else -(Real.pi:ℂ)^2/Complex.sin ((Real.pi:ℂ)*u)^2
noncomputable def kernel (z : ℝ) (u : ℂ) : ℂ :=
  -basicKernelPrime z u-(Real.log |z|:ℂ)*basicKernel z u
noncomputable def contourDensity (z : ℝ) (n : ℕ) (T : ℂ[X]) (u : ℂ) : ℂ :=
  ((2*Real.pi:ℂ)*Complex.I)⁻¹*u*weight n u*T.eval u*Complex.exp ((Real.log |z|:ℂ)*u)*kernel z u
noncomputable def rayDensity (z : ℝ) (n : ℕ) (u : ℂ) : ℂ :=
  (-Real.log |z|:ℂ)*u*weight n u*Complex.exp ((Real.log |z|:ℂ)*u)
theorem kernel_sin_guard (u : ℂ)
    (hu : (∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|) :
    (1/4:ℝ)*Real.exp (Real.pi*|u.im|) ≤ ‖Complex.sin ((Real.pi:ℂ)*u)‖ := by
  rcases hu with ⟨N,hN⟩ | him
  · have hh := CatalanCore.Decay.LemmaW.norm_sin_half (z := u) (k := (N:ℤ)) (by rw [hN]; push_cast; ring)
    have he := Real.exp_pos (Real.pi*|u.im|)
    linarith
  · have hi : (3:ℝ)/8 ≤ |((Real.pi:ℂ)*u).im| := by
      simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,zero_add,add_zero,
        abs_mul,abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have hh := CatalanCore.Decay.norm_sin_ge ((Real.pi:ℂ)*u) hi
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,zero_add,add_zero,
      abs_mul,abs_of_pos Real.pi_pos,div_eq_mul_inv,one_mul,mul_comm] using hh
theorem kernel_csc_guard (u : ℂ)
    (hs : (1/4:ℝ)*Real.exp (Real.pi*|u.im|) ≤ ‖Complex.sin ((Real.pi:ℂ)*u)‖) :
    ‖(Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*u)‖ ≤ 4*Real.pi*Real.exp (-(Real.pi*|u.im|)) := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    Real.pi/‖Complex.sin ((Real.pi:ℂ)*u)‖ ≤ Real.pi/((1/4:ℝ)*Real.exp (Real.pi*|u.im|)) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hs
    _ = _ := by rw [Real.exp_neg]; field_simp <;> ring
theorem kernel_shifted_cot_guard (u : ℂ)
    (hs : (1/4:ℝ)*Real.exp (Real.pi*|u.im|) ≤ ‖Complex.sin ((Real.pi:ℂ)*u)‖) :
    ‖Complex.cot ((Real.pi:ℂ)*u)+(if 0 ≤ u.im then Complex.I else -Complex.I)‖ ≤
      4*Real.exp (-(2*Real.pi*|u.im|)) := by
  have hne : Complex.sin ((Real.pi:ℂ)*u) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hs)
  have he : ‖Complex.cot ((Real.pi:ℂ)*u)+(if 0 ≤ u.im then Complex.I else -Complex.I)‖ =
      Real.exp (-(Real.pi*|u.im|))/‖Complex.sin ((Real.pi:ℂ)*u)‖ := by
    by_cases hi : 0 ≤ u.im
    · rw [if_pos hi,CatalanCore.Decay.norm_cot_add_I u hne,abs_of_nonneg hi]
    · rw [if_neg hi,← sub_eq_add_neg,CatalanCore.Decay.norm_cot_sub_I u hne,abs_of_neg (lt_of_not_ge hi)]
      congr 2
      ring
  rw [he]
  calc
    _ ≤ Real.exp (-(Real.pi*|u.im|))/((1/4:ℝ)*Real.exp (Real.pi*|u.im|)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hs
    _ = _ := by
      have hexp : Real.exp (-(2*Real.pi*|u.im|))=Real.exp (-(Real.pi*|u.im|))*Real.exp (-(Real.pi*|u.im|)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp,Real.exp_neg]
      field_simp
      <;> ring

theorem kernel_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, ValidZ z → ∀ u : ℂ,
    ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|) →
    ‖kernel z u‖ ≤ C*(1+|Real.log (|z|)|)*Real.exp (-kappaRate z*|u.im|) := by
  let C := 20*Real.pi^2+4*Real.pi
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro z hz u hu
  have hs := kernel_sin_guard u hu
  have hne : Complex.sin ((Real.pi:ℂ)*u) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hs)
  have hcsc := kernel_csc_guard u hs
  have hcot : ‖Complex.cot ((Real.pi:ℂ)*u)‖ ≤ 5 := by
    have hh := CatalanCore.Uniform.Decay.Jet.norm_cot_pi_le_of_sin_guard (by norm_num : (0:ℝ) < 1/4) hs
    norm_num at hh ⊢
    exact hh
  have htri : ‖kernel z u‖ ≤ ‖basicKernelPrime z u‖+|Real.log (|z|)| *‖basicKernel z u‖ := by
    unfold kernel
    exact (norm_sub_le _ _).trans (by simp only [norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs]; rfl)
  by_cases hneg : z<0
  · have hb : ‖basicKernel z u‖ ≤ 4*Real.pi*Real.exp (-(Real.pi*|u.im|)) := by
      simpa only [basicKernel,hneg,↓reduceIte] using hcsc
    have he : basicKernelPrime z u = -((Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*u))*
        ((Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*u)) := by
      rw [basicKernelPrime,if_pos hneg,Complex.cot_eq_cos_div_sin]
      field_simp
      <;> ring
    have hp : ‖basicKernelPrime z u‖ ≤ 20*Real.pi^2*Real.exp (-(Real.pi*|u.im|)) := by
      rw [he,norm_mul,norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      calc
        _ ≤ Real.pi*5*(4*Real.pi*Real.exp (-(Real.pi*|u.im|))) := by gcongr
        _ = _ := by ring
    have hzpos : ¬0<z := by linarith
    rw [kappaRate,if_neg hzpos]
    apply htri.trans
    apply (add_le_add hp (mul_le_mul_of_nonneg_left hb (abs_nonneg _))).trans
    dsimp only [C]
    simp only [neg_mul]
    have hh : 0 ≤ (4*Real.pi+20*Real.pi^2*|Real.log (|z|)|)*Real.exp (-(Real.pi*|u.im|)) := by positivity
    nlinarith
  · have hpos : 0<z := by have hh := hz.1; rw [abs_of_nonneg (le_of_not_gt hneg)] at hh; exact hh
    have hb : ‖basicKernel z u‖ ≤ 4*Real.pi*Real.exp (-(2*Real.pi*|u.im|)) := by
      have he : basicKernel z u = (Real.pi:ℂ)*(Complex.cot ((Real.pi:ℂ)*u)+
          (if 0 ≤ u.im then Complex.I else -Complex.I)) := by
        rw [basicKernel,if_neg hneg,Complex.cot_eq_cos_div_sin]
        split_ifs <;> ring
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      have hh := mul_le_mul_of_nonneg_left (kernel_shifted_cot_guard u hs) Real.pi_pos.le
      nlinarith
    have he : basicKernelPrime z u = -((Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*u))^2 := by
      rw [basicKernelPrime,if_neg hneg,div_pow]
      ring
    have hp : ‖basicKernelPrime z u‖ ≤ 16*Real.pi^2*Real.exp (-(2*Real.pi*|u.im|)) := by
      rw [he,norm_neg,norm_pow]
      have hh := pow_le_pow_left₀ (norm_nonneg _) hcsc 2
      have hexp : Real.exp (-(2*Real.pi*|u.im|))=Real.exp (-(Real.pi*|u.im|))^2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [hexp]
      nlinarith
    rw [kappaRate,if_pos hpos]
    apply htri.trans
    apply (add_le_add hp (mul_le_mul_of_nonneg_left hb (abs_nonneg _))).trans
    dsimp only [C]
    simp only [neg_mul]
    have hh : 0 ≤ (4*Real.pi^2+4*Real.pi+20*Real.pi^2*|Real.log (|z|)|)*Real.exp (-(2*Real.pi*|u.im|)) := by positivity
    nlinarith
theorem weight_envelope (z : ℝ) (n : ℕ) (hn : 0 < n) (u : ℂ)
    (hre : 0 ≤ u.re) (hu : 1/2 ≤ ‖u‖) :
    ‖u‖*‖weight n u‖*Real.exp (Real.log |z| *u.re-kappaRate z*|u.im|) ≤
      64*(n:ℝ)^4*(1+‖u/(n:ℂ)‖)^4*
        Real.exp ((n:ℝ)*(V z (u/(n:ℂ))-Real.log n)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnorm : ‖u/(n:ℂ)‖=‖u‖/(n:ℝ) := by
    rw [norm_div,Complex.norm_natCast]
  have hscale : (n:ℝ)*(V z (u/(n:ℂ))-Real.log n)=
      ((n:ℝ)*phi0 (u/(n:ℂ))-(n:ℝ)*Real.log n)+
        (Real.log |z| *u.re-kappaRate z*|u.im|) := by
    simp only [V,← Complex.ofReal_natCast,Complex.div_ofReal_re,Complex.div_ofReal_im,abs_div,
      abs_of_pos hnR]
    field_simp
    <;> ring
  have hw : ‖weight n u‖ ≤ 8*(‖u‖+(n:ℝ)+1)^3*
      Real.exp ((n:ℝ)*phi0 (u/(n:ℂ))-(n:ℝ)*Real.log n) := by
    by_cases hw0 : weight n u=0
    · rw [hw0,norm_zero]; positivity
    have hl := Real.exp_le_exp.mpr (weight_log_le n hn u hre hu)
    rw [Real.exp_log (norm_pos_iff.mpr hw0)] at hl
    have hlog : Real.exp (3*Real.log (‖u‖+(n:ℝ)+1))=(‖u‖+(n:ℝ)+1)^3 := by
      simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log (‖u‖+(n:ℝ)+1)) 3 |>.trans (by rw [Real.exp_log (by positivity)])
    have htwo : Real.exp (3*Real.log 2)=(8:ℝ) := by
      rw [show (3:ℝ)=(3:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      norm_num
    rw [Real.exp_add,Real.exp_add,hlog,htwo] at hl
    nlinarith
  have hr : ‖u‖ ≤ (n:ℝ)*(1+‖u/(n:ℂ)‖) := by rw [hnorm]; field_simp; nlinarith
  have hp : ‖u‖+(n:ℝ)+1 ≤ 2*(n:ℝ)*(1+‖u/(n:ℂ)‖) := by
    rw [hnorm]; field_simp; nlinarith [norm_nonneg u]
  calc
    _ ≤ ‖u‖*(8*(‖u‖+(n:ℝ)+1)^3*
      Real.exp ((n:ℝ)*phi0 (u/(n:ℂ))-(n:ℝ)*Real.log n))*
      Real.exp (Real.log |z| *u.re-kappaRate z*|u.im|) := by gcongr
    _ = 8*‖u‖*(‖u‖+(n:ℝ)+1)^3*
      Real.exp ((n:ℝ)*(V z (u/(n:ℂ))-Real.log n)) := by rw [hscale,Real.exp_add]; ring
    _ ≤ 8*((n:ℝ)*(1+‖u/(n:ℂ)‖))*(2*(n:ℝ)*(1+‖u/(n:ℂ)‖))^3*
      Real.exp ((n:ℝ)*(V z (u/(n:ℂ))-Real.log n)) := by gcongr
    _ = _ := by ring
theorem majorant_absorb (z : ℝ) (n : ℕ) (hn : 0 < n) (u : ℂ)
    (C K : ℝ) (hC : 0 ≤ C) (h4 : 4 ≤ C) (hK : K ≤ C) :
    K*(n:ℝ)^4*(1+‖u/(n:ℂ)‖)^4*
      Real.exp ((n:ℝ)*(V z (u/(n:ℂ))-Real.log n)) ≤ weightMajorant z n C u := by
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hp : (n:ℝ)^4 ≤ (n:ℝ)^C := by
    calc
      (n:ℝ)^(4:ℕ) = (n:ℝ)^((4:ℕ):ℝ) := (Real.rpow_natCast (n:ℝ) 4).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num only [Nat.cast_ofNat]; exact h4)
  have hq : (1+‖u/(n:ℂ)‖)^4 ≤ (1+‖u/(n:ℂ)‖)^C := by
    calc
      (1+‖u/(n:ℂ)‖)^(4:ℕ) = (1+‖u/(n:ℂ)‖)^((4:ℕ):ℝ) := (Real.rpow_natCast _ 4).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (u/(n:ℂ))]) (by norm_num only [Nat.cast_ofNat]; exact h4)
  unfold weightMajorant
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul (mul_le_mul hK hp (by positivity) hC) hq (by positivity)
  positivity

theorem contour_envelope (z : ℝ) (n : ℕ) (A : ℝ) (hA : 0 < A)
    (hk : ∀ u : ℂ, ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|) →
      ‖kernel z u‖ ≤ A*(1+|Real.log (|z|)|)*Real.exp (-kappaRate z*|u.im|))
    (u : ℂ) (hu : ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|)) :
    ‖contourDensity z n 1 u‖ ≤
      (‖((2*Real.pi:ℂ)*Complex.I)⁻¹‖*A*(1+|Real.log (|z|)|))*
        (‖u‖*‖weight n u‖*Real.exp (Real.log |z| *u.re-kappaRate z*|u.im|)) := by
  have hexp : ‖Complex.exp ((Real.log |z|:ℂ)*u)‖=Real.exp (Real.log |z| *u.re) := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp only [contourDensity,Polynomial.eval_one,mul_one,norm_mul,hexp]
  calc
    _ ≤ ‖((2*Real.pi:ℂ)*Complex.I)⁻¹‖*‖u‖*‖weight n u‖*
      Real.exp (Real.log |z| *u.re)*(A*(1+|Real.log (|z|)|)*Real.exp (-kappaRate z*|u.im|)) := by
      gcongr
      exact hk u hu
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add]; simp only [neg_mul]; ring
theorem ray_norm (z : ℝ) (n : ℕ) (x : ℝ) :
    ‖rayDensity z n x‖ = |Real.log (|z|)| *
      (‖(x:ℂ)‖*‖weight n x‖*Real.exp (Real.log |z| *(x:ℂ).re-kappaRate z*|(x:ℂ).im|)) := by
  simp only [rayDensity,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_neg,
    Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,abs_zero,mul_zero]
  ring
theorem lattice_norm (z : ℝ) (hz : ValidZ z) (n x : ℕ) :
    ‖latticeB z n x‖ = ‖(x:ℂ)‖*‖weight n x‖*
      Real.exp (Real.log |z| *(x:ℂ).re-kappaRate z*|(x:ℂ).im|) := by
  have hexp : Real.exp (Real.log |z| *(x:ℝ))=|z|^x := by
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log hz.1]
  simp only [latticeB,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    Complex.natCast_re,Complex.natCast_im,abs_zero,mul_zero,sub_zero,hexp]
  ring

theorem piece_weight_le (z : ℝ) (hz : ValidZ z) (F : Frame)
    (g : CatalanCore.Li2.Uniform.FrameGeometry F) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∀ u ∈ CatalanCore.Li2.Uniform.gammaN g n, ‖contourDensity z n 1 u‖ ≤ weightMajorant z n C u) ∧
      (0 < z → ∀ c : ℝ, CatalanCore.Li2.Uniform.frameCut g=some c → ∀ x : ℝ,
        (Nat.floor (c*n):ℝ)+1/2 ≤ x → ‖rayDensity z n x‖ ≤ weightMajorant z n C x) ∧
      (∀ x : ℕ, 1 ≤ x → ‖latticeB z n x‖ ≤ weightMajorant z n C x) := by
  obtain ⟨A,hA,hkernel⟩ := kernel_bound
  let B := ‖((2*Real.pi:ℂ)*Complex.I)⁻¹‖*A*(1+|Real.log (|z|)|)
  let C := 64*(B+|Real.log (|z|)|+1)+4
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hC4 : 4 ≤ C := by dsimp [C]; linarith [abs_nonneg (Real.log |z|)]
  refine ⟨C,hC,?_⟩
  filter_upwards [CatalanCore.Li2.Uniform.gammaN_kernel_domain F g,
    eventually_ge_atTop (1:ℕ)] with n hdom hn
  have hn0 : 0 < n := by omega
  have hbound : ∀ (K : ℝ), 0 ≤ K → 64*K ≤ C → ∀ u : ℂ,
      0 ≤ u.re → 1/2 ≤ ‖u‖ →
      K*(‖u‖*‖weight n u‖*Real.exp (Real.log |z| *u.re-kappaRate z*|u.im|)) ≤
        weightMajorant z n C u := by
    intro K hK hKC u hre hu
    have hh := mul_le_mul_of_nonneg_left (weight_envelope z n hn0 u hre hu) hK
    apply hh.trans
    convert majorant_absorb z n hn0 u C (64*K) hC.le hC4 hKC using 1 <;> ring
  refine ⟨?_,?_,?_⟩
  · intro u hu
    obtain ⟨hre,hnorm,hker⟩ := hdom u hu
    apply (contour_envelope z n A hA (hkernel z hz) u hker).trans
    exact hbound B hB (by dsimp [C]; linarith [abs_nonneg (Real.log |z|)]) u hre hnorm
  · intro hzpos c hc x hx
    have hxhalf : 1/2 ≤ x := by linarith [Nat.cast_nonneg (Nat.floor (c*n)) (α := ℝ)]
    rw [ray_norm]
    exact hbound _ (abs_nonneg _) (by dsimp [C]; linarith) x
      (by simpa only [Complex.ofReal_re] using (show 0 ≤ x by linarith))
      (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ x by linarith)] using hxhalf)
  · intro x hx
    rw [lattice_norm z hz n x]
    have hxR : 1 ≤ (x:ℝ) := by exact_mod_cast hx
    simpa only [one_mul] using hbound 1 (by norm_num) (by dsimp [C]; linarith [abs_nonneg (Real.log |z|)]) x
      (by simp only [Complex.natCast_re]; positivity)
      (by rw [Complex.norm_natCast]; linarith)

end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.kernel_bound

#print axioms CatalanCore.Li2.Decay.weight_envelope
#print axioms CatalanCore.Li2.Decay.majorant_absorb

#print axioms CatalanCore.Li2.Decay.piece_weight_le
