module

public import CatalanCore.Arith.Hybrid.DefC5Gle

@[expose] public section

/-!
# Theorem C5 as a `DefHypT` family
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Fam

variable {p : ℕ} {r m k : ℕ}

/-- The numeric side condition: the D2 potentials have total value `≥ m`. -/
lemma wC_sum_ge : m ≤ ∑ a : Fin r ⊕ Fin m, wC p r k (Frame.hybRow r m a) := by
  rw [Fintype.sum_sum_type]
  have : ∑ i : Fin m, wC p r k (Frame.hybRow r m (Sum.inr i)) ≥ ∑ i : Fin m, 1 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h : Frame.hybRow r m (Sum.inr i) = r + 2 * (i : ℕ) := rfl
    rw [h]; unfold wC; split_ifs <;> omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  omega

end Fam

open Classical in
/-- **Theorem C5 as a `DefHypT` family.**  `W` is the set of primes in the window
`p ≡ 3 (mod 4)`, `L_p = (5p+1)/4 - r ∈ [m, 2m)`, `r + 2m ≤ 2p` (where `CSetup` holds); `T p` is any
exponent bound dominating both `tropExp` and the dual value of the D2 potentials.  The deficit is
`δ p = L_p - m` on `W`, `0` elsewhere. -/
theorem defHypT_C5 {Fr : Frame} (I : HybInst Fr) {o : ℕ} (hL : LamData Fr o) (r m : ℕ) [I.DiagOK r m] (T : ℕ → ℕ)
    (W : ℕ → Prop) (hSet : ∀ p : ℕ, p.Prime → W p → ∃ k, CSetup o p r m k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → ∀ k, CSetup o p r m k →
      ∑ a, wC p r k (Frame.hybRow r m a) + ∑ b, wC p r k (Frame.hybCol r m b) ≤ T p) :
    DefHypT I r m T (fun p => if W p then p + (p + o) / 4 - r - m else 0) := by
  refine defHypT_of_local I r m T _ hT W (fun p hp => by simp [hp]) ?_
  intro p hp hb hWp
  obtain ⟨k, S⟩ := hSet p hp hWp
  haveI : Fact p.Prime := ⟨hp⟩
  have hd := hTd p hp hWp k S
  have h1 := wC_sum_ge (p := p) (r := r) (m := m) (k := k)
  have hg := gleAt_C5_lam S hL
  have hk : (p + o) / 4 = k := by have := S.hk; have := S.ho0; have := S.ho3; have := S.hp6; omega
  have hLhi := S.hLhi
  have hLlo := S.hLlo
  simp only [if_pos hWp, hk]
  refine ⟨by omega, fun [Fact p.Prime] => hg.mono (by omega)⟩

end CatalanCore.Arith.Hybrid
