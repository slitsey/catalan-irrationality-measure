module

public import CatalanCore.Uniform.Content.UFMoments.TypeShift

@[expose] public section

/-!
# UF moments: `TypeData` of a shifted node of the scaled lift

`typeData_of_shift`: let `t = t₀ + Δ`, and let `e` map the own chain of `t` to that of `t₀` with
`c(e⁻¹ i) = c(i) + Δ`.  If every window `(a, a+Δ]` (`a` a chain node of `t₀`, or `a = t₀`) is free
of singular indices, the frame reduces periodically (`RegRed`), the core is injective and below the
border, and the border vectors are the Loewner rows of `t` and `t₀`, then `TypeData` holds with
`κ₁ = (F(t) - F(t₀))/norm`, provided its residue has the Cauchy form `hres`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A `p²`-difference of integral constants is `π²`-divisible in `GaussLoc p`. -/
theorem C_liftQ_sub_sq {x y w : ℚ} (hx : x ∈ S p) (hy : y ∈ S p) (hw : w ∈ S p)
    (h : x - y = (p : ℚ) ^ 2 * w) :
    algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p x)) =
      algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p y)) +
        piL p ^ 2 * algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p w)) := by
  have e : Hybrid.liftQ p x = Hybrid.liftQ p y + ((p : ℕ) : LocRing p) ^ 2 * Hybrid.liftQ p w := by
    apply Subtype.ext
    push_cast
    rw [Hybrid.liftQ_val hx, Hybrid.liftQ_val hy, Hybrid.liftQ_val hw]
    linarith
  rw [e, C_add, C_mul, C_pow, map_add, map_mul, map_pow]

/-- A `p`-difference of integral constants is `π`-divisible in `GaussLoc p`. -/
theorem C_liftQ_sub {x y w : ℚ} (hx : x ∈ S p) (hy : y ∈ S p) (hw : w ∈ S p)
    (h : x - y = (p : ℚ) * w) :
    algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p x)) -
      algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p y)) =
        piL p * algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p w)) := by
  have e : Hybrid.liftQ p x = Hybrid.liftQ p y + ((p : ℕ) : LocRing p) * Hybrid.liftQ p w := by
    apply Subtype.ext
    push_cast
    rw [Hybrid.liftQ_val hx, Hybrid.liftQ_val hy, Hybrid.liftQ_val hw]
    linarith
  rw [e, C_add, C_mul, map_add, map_mul]
  ring

/-- Loewner rows of two shifted node pairs agree modulo `π²`. -/
theorem loewner_entry_shift (D : PoleData Fr p N) (hR : RegRed D) (hN : N < p * p)
    (a b Δ : ℕ) (hab : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p))
    (ha : a + Δ < N) (hb : b + Δ < N) (hwa : NoSingWin D a Δ) (hwb : NoSingWin D b Δ) :
    ∃ x, algebraMap _ (GaussLoc p)
        (Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (a + Δ) (b + Δ)))) =
      algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn a b))) +
        piL p ^ 2 * x := by
  have hmem : Fr.Mn (a + Δ) (b + Δ) - Fr.Mn a b ∈ S p := by
    rcases lt_trichotomy a b with h | h | h
    · exact Mn_shift_off D hR hN a b Δ h hab ha hb hwa hwb
    · subst h; exact Mn_shift_diag D a Δ ha hwa
    · have := Mn_shift_off D hR hN b a Δ h hab.symm hb ha hwb hwa
      rw [frame_Mn_symm Fr (b + Δ), frame_Mn_symm Fr b] at this
      exact this
  have hs1 : (p : ℚ) ^ 2 * Fr.Mn (a + Δ) (b + Δ) ∈ S p := D.square_mem hN (by omega) (by omega)
  have hs2 : (p : ℚ) ^ 2 * Fr.Mn a b ∈ S p := D.square_mem hN (by omega) (by omega)
  exact ⟨_, C_liftQ_sub_sq hs1 hs2 hmem (by ring)⟩

/-- Four integral constants with a `p²`-combination. -/
theorem C_liftQ_four {x1 x2 x3 x4 w : ℚ} (h1 : x1 ∈ S p) (h2 : x2 ∈ S p) (h3 : x3 ∈ S p)
    (h4 : x4 ∈ S p) (hw : w ∈ S p) (h : x1 - x2 - (x3 - x4) = (p : ℚ) ^ 2 * w) :
    algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p x1)) =
      algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p x2)) +
        (algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p x3)) -
          algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p x4))) +
        piL p ^ 2 * algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p w)) := by
  have e : Hybrid.liftQ p x1 = Hybrid.liftQ p x2 + (Hybrid.liftQ p x3 - Hybrid.liftQ p x4) +
      ((p : ℕ) : LocRing p) ^ 2 * Hybrid.liftQ p w := by
    apply Subtype.ext
    push_cast
    rw [Hybrid.liftQ_val h1, Hybrid.liftQ_val h2, Hybrid.liftQ_val h3, Hybrid.liftQ_val h4,
      Hybrid.liftQ_val hw]
    linarith
  rw [e, C_add, C_add, C_sub, C_mul, C_pow, map_add, map_add, map_sub, map_mul, map_pow]

theorem PF1_eq_liftQ (a : ℕ) : PF1 p Fr a = Polynomial.C (Hybrid.liftQ p ((p : ℚ) * Fp Fr a)) := rfl

/-- **Prefix transport along a shift.** -/
theorem ellL_shift (D : PoleData Fr p N) (hR : RegRed D) (a t0 Δ : ℕ)
    (hat : ((a : ℕ) : ZMod p) = ((t0 : ℕ) : ZMod p))
    (ha : a + Δ < N) (ht : t0 + Δ < N) (hwa : NoSingWin D a Δ) (hwt : NoSingWin D t0 Δ) :
    ∃ x, ellL p Fr (a + Δ) = ellL p Fr a + (ellL p Fr (t0 + Δ) - ellL p Fr t0) +
      piL p ^ 2 * x := by
  obtain ⟨w, hw, hweq⟩ := shift_cong D hR a t0 Δ hat ha ht hwa hwt
  have m := fun n (hn : n < N) => p_Fp_mem (Fr := Fr) D hn
  have h := C_liftQ_four (m _ ha) (m a (by omega)) (m _ ht) (m t0 (by omega)) hw
    (show (p : ℚ) * Fp Fr (a + Δ) - p * Fp Fr a - (p * Fp Fr (t0 + Δ) - p * Fp Fr t0) =
      (p : ℚ) ^ 2 * w by rw [← mul_sub, ← mul_sub, ← mul_sub, hweq]; ring)
  refine ⟨algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p w)) *
    Ring.inverse (algebraMap _ (GaussLoc p) (nL p Fr)), ?_⟩
  unfold ellL
  rw [PF1_eq_liftQ, PF1_eq_liftQ, PF1_eq_liftQ, PF1_eq_liftQ, h]
  ring

/-- **The prefix shift is `π κ₁`.** -/
theorem ellL_kappa (D : PoleData Fr p N) (t0 Δ : ℕ) (ht : t0 + Δ < N)
    (hwt : NoSingWin D t0 Δ) :
    ellL p Fr (t0 + Δ) - ellL p Fr t0 = piL p *
      (algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p (Fp Fr (t0 + Δ) - Fp Fr t0))) *
        Ring.inverse (algebraMap _ (GaussLoc p) (nL p Fr))) := by
  have h := C_liftQ_sub (p_Fp_mem (Fr := Fr) D ht) (p_Fp_mem (Fr := Fr) D (by omega : t0 < N))
    (shift_mem D t0 Δ ht hwt) (by ring)
  have hsm : ∀ A B I : GaussLoc p, A * I - B * I = (A - B) * I := fun _ _ _ => by ring
  unfold ellL
  rw [PF1_eq_liftQ, PF1_eq_liftQ, hsm, h]
  ring

theorem res_kappa (D : PoleData Fr p N) (t0 Δ : ℕ) (ht : t0 + Δ < N)
    (hwt : NoSingWin D t0 Δ) :
    res p (algebraMap _ (GaussLoc p) (Polynomial.C (Hybrid.liftQ p (Fp Fr (t0 + Δ) - Fp Fr t0))) *
        Ring.inverse (algebraMap _ (GaussLoc p) (nL p Fr))) =
      rfH p (red p (Fp Fr (t0 + Δ) - Fp Fr t0)) * (rfH p (red p Fr.norm))⁻¹ := by
  rw [map_mul, res_inverse _ (isUnit_nL D), res_algebraMap, res_algebraMap, phiP_nL D, phiP_C,
    redQ_apply, Hybrid.liftQ_val (shift_mem D t0 Δ ht hwt), rfH_apply]
  rfl

end CatalanCore.Uniform.Content.UFMoments
