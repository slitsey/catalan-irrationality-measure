module

public import CatalanFrames.Thirds.Frame
public import CatalanCore.Rect.CharZeroNV.FrameAdapter

@[expose] public section

/-! # Characteristic-zero nonvanishing for the thirds frames

The increment of `ψ(z+1) - ψ(z+s)` is `(s-1)/((i+1)(i+s))`, so `D = c (X+1)(X+s)`,
`A` constant `c (s-1)/N`: a quadratic denominator with an isolated pole at `-1`
whenever `0 < s < 1`.  Everything is stated for all such `s`; the two thirds frames are
the instances `s = 1/3`, `s = 2/3`, `N = 9/2`.
-/

open Polynomial CatalanCore CatalanCore.Rect CatalanCore.Rect.CharZeroNV
  CatalanCore.Rect.CharZeroNV.FrameAdapter

namespace CatalanFrames.Thirds

variable (s N xs δ0 c : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) (hN : 0 < N) (hc : c ≠ 0)

/-- `D = c (X+1)(X+s)`. -/
noncomputable def incrementDen : ℚ[X] := C c * (X + 1) * (X + C s)

/-- `A = c (s-1) / N`, a constant. -/
noncomputable def incrementNum : ℚ[X] := C (c * (s - 1) / N)

include hs0 hs1 hc hN in
theorem thirds_increment :
    FrameIncrement (thirdsFrame s N xs δ0 n0off hs0 hs1 hN) (incrementDen s c)
      (incrementNum s N c) where
  pole := by
    refine ⟨by simp [incrementDen], ?_, ?_, ?_⟩
    · have : c * (s - 1) / N ≠ 0 :=
        div_ne_zero (mul_ne_zero hc (by linarith)) hN.ne'
      simpa [incrementNum] using this
    · intro n
      have hn : (n : ℚ) + 1 ≠ 0 := by positivity
      have hs : (n : ℚ) + s ≠ 0 := by positivity
      simpa [incrementDen] using mul_ne_zero (mul_ne_zero hc hn) hs
    · intro n
      have hn : -((n : ℚ) + 2) + 1 ≠ 0 := by
        have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        linarith
      have hs : -((n : ℚ) + 2) + s ≠ 0 := by
        have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        linarith
      simpa [incrementDen] using mul_ne_zero (mul_ne_zero hc hn) hs
  deg_D := by
    unfold incrementDen
    compute_degree!
  deg_A := by
    unfold incrementNum
    exact (natDegree_C _).le.trans (by norm_num)
  value i := by
    rw [Delta_eq]
    have h1 : (i : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (i : ℚ) + s ≠ 0 := by positivity
    simp only [incrementDen, incrementNum, eval_mul, eval_add, eval_X, eval_one, eval_C,
      Nat.cast_succ, thirdsFrame]
    simp only [show (i : ℚ) + 1 - 1 + s = i + s by ring]
    have hN' : N ≠ 0 := hN.ne'
    field_simp
    ring
  jet i := by
    rw [Delta_eq, Dsq_eq]
    have h1 : (i : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (i : ℚ) + s ≠ 0 := by positivity
    simp only [incrementDen, incrementNum, derivative_mul, derivative_add, derivative_X,
      derivative_one, derivative_C, eval_mul, eval_add, eval_X, eval_one, eval_C, eval_zero,
      Nat.cast_succ, thirdsFrame]
    simp only [show (i : ℚ) + 1 - 1 + s = i + s by ring]
    have hN' : N ≠ 0 := hN.ne'
    field_simp
    ring

include hs0 hs1 hc hN in
theorem exists_common_deletion_fullN_thirds (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ t : Finset (Fin r), t.card ≤ 1 ∧
      (FullN (thirdsFrame s N xs δ0 n0off hs0 hs1 hN) (fun i : {i // i ∉ t} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).det ≠ 0 :=
  exists_common_deletion_fullN (thirds_increment s N xs δ0 c n0off hs0 hs1 hN hc) U r m hr

include hs0 hs1 hN in
theorem thirds_hasNVPinC (Adm : ℕ → ℕ → Prop) (hAdm : ∀ r, 1 ≤ r → ∃ m, Adm r m)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    CatalanCore.HasNVPinC
      (commonMinorFam (thirdsFrame s N xs δ0 n0off hs0 hs1 hN) Adm 1) Cls Bad α β :=
  FrameAdapter.commonMinor_hasNVPinC (thirds_increment s N xs δ0 1 n0off hs0 hs1 hN one_ne_zero)
    Adm hAdm Cls Bad α β

end CatalanFrames.Thirds
