module

public import CatalanCore.Uniform.Content.UFMoments.FrameShift
public import CatalanCore.Uniform.Content.UFMoments.JBlockUF

@[expose] public section

/-!
# UF moments, frame layer: `TypeData` from a chain shift inside one arc

* `Mn_shift_off`, `Mn_shift_diag`: `Mn(a+Δ, b+Δ) - Mn(a, b) ∈ ℤ_(p)` for `a ≡ b (mod p)`
  (nonsingular windows, `RegRed`);
* `C_sub_sq`: a `p²`-difference of constants is `π²`-divisible in `GaussLoc p`;
* `ellL_shift`, `ellL_kappa`: the prefix transport and the shift `κ = π κ₁` with
  `res κ₁ = red(F(t) - F(t₀)) / red(norm)`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame}

theorem Mn_shift_off (D : PoleData Fr p N) (hR : RegRed D) (hN : N < p * p) (a b Δ : ℕ)
    (hlt : a < b) (hab : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p))
    (ha : a + Δ < N) (hb : b + Δ < N) (hwa : NoSingWin D a Δ) (hwb : NoSingWin D b Δ) :
    Fr.Mn (a + Δ) (b + Δ) - Fr.Mn a b ∈ S p := by
  obtain ⟨w, hw, hweq⟩ := shift_cong D hR b a Δ hab.symm hb ha hwb hwa
  obtain ⟨δ, hδ0, hδp, hδ⟩ := inv_digit_mem hlt (by omega) hab
  have hn : Fr.norm ≠ 0 := Fr.hnorm.ne'
  have h1 := norm_mul_Mn Fr a b
  have h2 := norm_mul_Mn Fr (a + Δ) (b + Δ)
  have hd : ((b + Δ : ℕ) : ℚ) - ((a + Δ : ℕ) : ℚ) = p * δ := by push_cast; linarith
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hδq : (δ : ℚ) ≠ 0 := by exact_mod_cast hδ0.ne'
  have key : Fr.Mn (a + Δ) (b + Δ) - Fr.Mn a b = w * (1 / Fr.norm) * (1 / (δ : ℚ)) := by
    rw [hd] at h2
    rw [hδ] at h1
    have e2 : Fr.Mn (a + Δ) (b + Δ) = (Fp Fr (b + Δ) - Fp Fr (a + Δ)) / (Fr.norm * (p * δ)) := by
      rw [← h2]; field_simp
    have e1 : Fr.Mn a b = (Fp Fr b - Fp Fr a) / (Fr.norm * (p * δ)) := by
      rw [← h1]; field_simp
    rw [e2, e1]
    field_simp
    linear_combination hweq
  rw [key]
  have hδS : 1 / (δ : ℚ) ∈ S p := by
    have g := (Good.natCast (ℓ := p) δ).inv (natCast_ne_zero' hδ0 hδp)
    simpa using g.mem
  have hnS : 1 / Fr.norm ∈ S p := by
    have g := (good_red D.norm_mem).inv D.norm_ne
    simpa using g.mem
  exact (S p).mul_mem ((S p).mul_mem hw hnS) hδS

theorem Mn_shift_diag (D : PoleData Fr p N) (a Δ : ℕ) (ha : a + Δ < N)
    (hwa : NoSingWin D a Δ) : Fr.Mn (a + Δ) (a + Δ) - Fr.Mn a a ∈ S p := by
  have hnS : 1 / Fr.norm ∈ S p := by
    have g := (good_red D.norm_mem).inv D.norm_ne
    simpa using g.mem
  have hsum : ∀ n, a + n < N → NoSingWin D a n →
      ∑ k ∈ Icc 1 (a + n), Fr.Dsq k - ∑ k ∈ Icc 1 a, Fr.Dsq k ∈ S p := by
    intro n
    induction n with
    | zero => intro _ _; simpa using (S p).zero_mem
    | succ m ih =>
      intro hm hw
      have ih' := ih (by omega) (fun k h1 h2 => hw k h1 (by omega))
      have hreg := D.regular_dsq (a + m + 1) (by omega) (by omega)
        (by have := hw (a + m + 1) (by omega) (by omega); exact_mod_cast this)
      rw [show a + (m + 1) = (a + m) + 1 by ring,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ a + m + 1)]
      have e : ∑ k ∈ Icc 1 (a + m), Fr.Dsq k + Fr.Dsq (a + m + 1) - ∑ k ∈ Icc 1 a, Fr.Dsq k =
          (∑ k ∈ Icc 1 (a + m), Fr.Dsq k - ∑ k ∈ Icc 1 a, Fr.Dsq k) + Fr.Dsq (a + m + 1) := by
        ring
      rw [e]
      exact (S p).add_mem ih' hreg
  unfold Frame.Mn
  rw [if_pos rfl, if_pos rfl]
  have e : -(1 / Fr.norm) * ∑ k ∈ Icc 1 (a + Δ), Fr.Dsq k - -(1 / Fr.norm) * ∑ k ∈ Icc 1 a, Fr.Dsq k =
      -(1 / Fr.norm) * (∑ k ∈ Icc 1 (a + Δ), Fr.Dsq k - ∑ k ∈ Icc 1 a, Fr.Dsq k) := by ring
  rw [e]
  exact (S p).mul_mem ((S p).neg_mem hnS) (hsum Δ ha hwa)

end CatalanCore.Uniform.Content.UFMoments
