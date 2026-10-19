module

public import CatalanFrames.Lambda.HybLemmaE
public import CatalanFrames.Lambda.DefB
public import CatalanCore.Arith.Hybrid.LemmaE.GleE4

@[expose] public section

/-!
# λ: Lemma E at a class-1 prime `p < r` (rank route)

`lam_hUU`: the scalar-Schur hypothesis `hUU` of `gleAt_E` for the actual λ matrix, from
`lam_UU_off`/`lam_UU_diag` (DQ Lemma 3.1).  `gleAt_E_lam`: with `j = 3`, `4k = 3p + 1`,
`GLE p (2 (2r - p - k) + 4m - m) (fullPoly)`.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanFrames.Lambda

section

variable {p : ℕ} [Fact p.Prime] {r m k : ℕ}

lemma hK4_of (S : ESetup p r m 3 k) : 4 * (k : ZMod p) = 1 := by
  have : ((4 * k : ℕ) : ZMod p) = ((3 * p + 1 : ℕ) : ZMod p) := by rw [S.hk]
  push_cast at this
  simpa [ZMod.natCast_self] using this

lemma TE_U_eq_red (S : ESetup p r m 3 k) {a b : ℕ} (ha1 : r - p ≤ a) (ha2 : a < k)
    (hb1 : r - p ≤ b) (hb2 : b < k) (hab : a < b) :
    TE p 3 r k a b = ((lamFrame.Mn a b : ℚ) : ZMod p) := by
  have hr := S.hpr
  have hkp := S.hkp
  have hw : wE p r k a + wE p r k b = 0 := by
    rw [wE_U ha1 ha2 (by omega), wE_U hb1 hb2 (by omega)]
  have hg := good_TEo lamData S hab (show b < r + 2 * m by omega)
  rw [hw, pow_zero, one_mul] at hg
  have e : TE p 3 r k a b = TEo p 3 k (wE p r k a + wE p r k b) a b := by
    unfold TE; rw [if_pos hab]
  rw [e, hw, ← hg.2]
  rfl

lemma TE_U_diag (S : ESetup p r m 3 k) {a : ℕ} (ha1 : r - p ≤ a) (ha2 : a < k) :
    TE p 3 r k a a = ((lamFrame.Mn a a : ℚ) : ZMod p) := by
  have hr := S.hpr
  have hkp := S.hkp
  have hw : wE p r k a + wE p r k a = 0 := by
    rw [wE_U ha1 ha2 (by omega)]
  have hg := good_TEd lamData S (A := a) (by omega)
  rw [hw, pow_zero, one_mul] at hg
  have e : TE p 3 r k a a = TEd p 3 k (wE p r k a + wE p r k a) a := by
    unfold TE; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
  rw [e, hw, ← hg.2]
  rfl

/-- **The scalar Schur complement hypothesis for λ** (DQ Lemma 3.1). -/
theorem lam_hUU (S : ESetup p r m 3 k) :
    ∀ a b : ℕ, r - p ≤ a → a < k → r - p ≤ b → b < k →
      TE p 3 r k a b = (16 : ZMod p)⁻¹ * ((if a = b then Gs p (fun x => (x⁻¹) ^ 2) (k - 1) else 0) +
        ∑ c ∈ Ico k p, ((c : ZMod p) - a)⁻¹ * ((c : ZMod p) - b)⁻¹) := by
  intro a b ha1 ha2 hb1 hb2
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p S.p5) (four_ne_zmod p S.p5)
  have hK4 := hK4_of S
  have hkp := S.hkp
  have hp5 := S.p5
  rcases lt_trichotomy a b with h | h | h
  · rw [TE_U_eq_red S ha1 ha2 hb1 hb2 h, if_neg (by omega), zero_add]
    have := lam_UU_off hp5 hK4 hkp h (by omega)
    have h2 : ((lamFrame.Mn a b : ℚ) : ZMod p) = (16 : ZMod p)⁻¹ * (16 * LemmaE.red p (lamFrame.Mn a b)) := by
      rw [← mul_assoc, inv_mul_cancel₀ h16, one_mul]; rfl
    rw [h2, this]
  · subst h
    rw [TE_U_diag S ha1 ha2, if_pos rfl]
    have := lam_UU_diag hp5 hK4 hkp (u := a) (by omega)
    have h2 : ((lamFrame.Mn a a : ℚ) : ZMod p) = (16 : ZMod p)⁻¹ * (16 * LemmaE.red p (lamFrame.Mn a a)) := by
      rw [← mul_assoc, inv_mul_cancel₀ h16, one_mul]; rfl
    rw [h2, this]
    congr 1
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun c _ => by rw [pow_two]
  · rw [TE_symm', TE_U_eq_red S hb1 hb2 ha1 ha2 h, if_neg (by omega), zero_add]
    have := lam_UU_off hp5 hK4 hkp h (by omega)
    have h2 : ((lamFrame.Mn b a : ℚ) : ZMod p) = (16 : ZMod p)⁻¹ * (16 * LemmaE.red p (lamFrame.Mn b a)) := by
      rw [← mul_assoc, inv_mul_cancel₀ h16, one_mul]; rfl
    rw [h2, this]
    congr 1
    exact Finset.sum_congr rfl fun c _ => by rw [mul_comm]

/-- **Lemma E for λ at a class-1 prime** (dual form). -/
theorem gleAt_E_lam (S : ESetup p r m 3 k) :
    GLE p (2 * ((r - p) + (r - k)) + 4 * m - m) (lamFrame.fullPoly r m) := by
  have hp5 := S.p5
  have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have h3' : ((3 : ℕ) : ZMod p) * ((3 : ℕ) : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h3
  have he : -(4 * ((3 : ℕ) : ZMod p)⁻¹) + 1 ≠ 0 := by
    intro h
    have h4 : (-(4 * ((3 : ℕ) : ZMod p)⁻¹) + 1) * ((3 : ℕ) : ZMod p) = 0 := by rw [h]; ring
    have h5 : (-(4 * ((3 : ℕ) : ZMod p)⁻¹) + 1) * ((3 : ℕ) : ZMod p) = -1 := by
      linear_combination (-4) * h3'
    rw [h5] at h4
    exact one_ne_zero (neg_eq_zero.1 h4)
  have := gleAt_E lamData S (Gs p (fun x => (x⁻¹) ^ 2) (k - 1)) h3 he (lam_hUU S)
  rw [wE_sum S.hrk (by have := S.hkp; have := S.hpr; omega)] at this
  exact this

end

end CatalanFrames.Lambda
