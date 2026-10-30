module
public import CatalanMeasure.GenD.Uniform.W.Lucas.Kill
public import CatalanMeasure.GenD.Uniform.W.Lucas.Resp
@[expose] public section
set_option Elab.async false

/-!
# The Lucas family theorem (`q ≥ p`, J-affine cell)

`lucas_fam_le_nullity`: a finite-dimensional space `A` of tensor families `(σ, G)`,
`σ = ∑_d w_d U_d`, `(X-1)^h σ = (X^p - 1) G`, `G` supported below `hi ≤ p`, with `G[e] = P(e)` for a
polynomial `P` of degree `< q - p`, whose cell difference `ψ(a0-1) - ψ(a0)` at the positions of the
support is **J-affine**, `α + β J`, gives `dim A ≤ ν`.

The raw response of a member is `2 P(H-1-j) (α + β ⌊j/p⌋)`: slope `2β P(H-1-j)`, a polynomial in `j` of
degree `< q - p`, so the Lucas `Δ^q` kill (`gKill_of_lucas`) applies with filter cost `0`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `w ↦ w ⊗ z`. -/
def tensorL {K D : ℕ} (z : Fin K → ZMod p) :
    (Fin D → ZMod p) →ₗ[ZMod p] (Fin D → Fin K → ZMod p) where
  toFun w := tensorX w z
  map_add' a b := by funext d k; simp [tensorX, add_mul]
  map_smul' c a := by funext d k; simp [tensorX, mul_assoc]

theorem tensorL_injective {K D : ℕ} (z : Fin K → ZMod p) (hz : z ≠ 0) :
    Function.Injective (tensorL (D := D) z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  funext d
  have := congrFun (congrFun hw d) k
  simp only [tensorL, LinearMap.coe_mk, AddHom.coe_mk, tensorX, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_right hk

/-- The slope polynomial of the Lucas response: `j ↦ 2 β P(H - 1 - j)`. -/
def slopePoly (p : ℕ) [Fact p.Prime] (H : ℕ) (β : ZMod p) (Q : (ZMod p)[X]) : (ZMod p)[X] :=
  C (2 * β) * Q.comp (C ((H : ZMod p) - 1) - X)

theorem slopePoly_degree (H : ℕ) (β : ZMod p) (Q : (ZMod p)[X]) {n : ℕ}
    (hQ : Q.degree < (n : WithBot ℕ)) : (slopePoly p H β Q).degree < (n : WithBot ℕ) := by
  unfold slopePoly
  by_cases h0 : Q = 0
  · subst h0; simp
  have hnd : Q.natDegree < n := by
    rw [degree_eq_natDegree h0] at hQ
    exact_mod_cast hQ
  have h1 : (C ((H : ZMod p) - 1) - X : (ZMod p)[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_C, natDegree_X]
    omega
  have h2 : (Q.comp (C ((H : ZMod p) - 1) - X)).natDegree ≤ Q.natDegree := by
    refine (natDegree_comp_le).trans ?_
    calc Q.natDegree * (C ((H : ZMod p) - 1) - X).natDegree ≤ Q.natDegree * 1 :=
          Nat.mul_le_mul_left _ h1
      _ = Q.natDegree := mul_one _
  have h3 : (C (2 * β) * Q.comp (C ((H : ZMod p) - 1) - X)).natDegree ≤ Q.natDegree :=
    (natDegree_C_mul_le _ _).trans h2
  calc (C (2 * β) * Q.comp (C ((H : ZMod p) - 1) - X)).degree
      ≤ ((C (2 * β) * Q.comp (C ((H : ZMod p) - 1) - X)).natDegree : WithBot ℕ) :=
        degree_le_natDegree
    _ < n := by exact_mod_cast lt_of_le_of_lt h3 hnd

/-- **Family form of Theorem A (Lucas).** -/
theorem lucas_fam_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) (hpq : p ≤ P.q N) {K D : ℕ} (k0 : ℤ) (z : Fin K → ZMod p)
    (hz : z ≠ 0) (hDp : D ≤ (p - 1) / 2) (hgood : ∀ (d : Fin D) (k : Fin K), Good P N p k0 d k)
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (wm : A →ₗ[ZMod p] (Fin D → ZMod p)) (hwm : Function.Injective wm)
    (Gm Pm : A →ₗ[ZMod p] (ZMod p)[X]) (hi : ℕ)
    (hrel : ∀ a, (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D (wm a) = (X ^ p - 1) * Gm a)
    (hsupp : ∀ a e, (Gm a).coeff e ≠ 0 → e < hi) (hhi : hi ≤ p) (hD : p + hi ≤ P.h N + D)
    (hcoef : ∀ a e, e < p → (Gm a).coeff e = (Pm a).eval (e : ZMod p))
    (hPdeg : ∀ a, (Pm a).degree < ((P.q N - p : ℕ) : WithBot ℕ))
    (α β : ZMod p)
    (hcell : ∀ a j, P.b N ≤ j → j < P.L N →
      (Gm a).coeff (idxRes (P.H N) p (j % p)) ≠ 0 →
      psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p) - 1) z -
        psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p)) z =
        α + β * ((j / p : ℕ) : ZMod p)) :
    finrank (ZMod p) A ≤ nullity P N p := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  let ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
    (tRows P N p K D k0).comp ((tensorL z).comp wm)
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h1 : tensorL z (wm a) = 0 :=
      tRows_injective_on hp2 hDp k0 _ (fun d k hg => absurd (hgood d k) hg) ha
    have h2 : wm a = 0 := tensorL_injective z hz (by rw [h1, map_zero])
    exact hwm (by rw [h2, map_zero])
  refine le_nullity_of_lucas hp2 hH hpq ι hι (fun a => ?_)
  refine ⟨fun x => 2 * α * (Pm a).eval (((P.H N : ℕ) : ZMod p) - 1 - x),
    slopePoly p (P.H N) β (Pm a), slopePoly_degree _ _ _ (hPdeg a), ?_⟩
  intro j hj1 hj2
  have hjH : j < P.H N := lt_of_lt_of_le hj2 (by
    have : P.H N = P.L N + P.g N + P.h N := by simp [Parameters.H, Parameters.C]
    omega)
  have e1 : uResp P N p j (ι a) = 2 * (Gm a).coeff (idxRes (P.H N) p (j % p)) *
      (psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p) - 1) z -
        psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p)) z) :=
    uResp_tensor hP hN hp2 hH k0 z (wm a) (Gm a) hi (hrel a) (hsupp a) hhi hD
      (fun d k hg => absurd (hgood d k) hg) hjH
  have he0 := idxRes_lt hp0 (P.H N) (j % p)
  have hidx := idx_eq hp0 (P.H N) (j % p)
  have hcast : (((idxRes (P.H N) p (j % p) : ℕ)) : ZMod p) = ((P.H N : ℕ) : ZMod p) - 1 - j := by
    have := congrArg (fun t : ℤ => (t : ZMod p)) hidx
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_add, Int.cast_mul] at this
    rw [ZMod.natCast_mod] at this
    simpa using this.symm
  have hco : (Gm a).coeff (idxRes (P.H N) p (j % p)) =
      (Pm a).eval (((P.H N : ℕ) : ZMod p) - 1 - j) := by
    rw [hcoef a _ he0, hcast]
  rw [e1, hco]
  simp only [slopePoly, eval_mul, eval_C, eval_comp, eval_sub, eval_X]
  by_cases hc : (Pm a).eval (((P.H N : ℕ) : ZMod p) - 1 - j) = 0
  · rw [hc]; ring
  · have hne : (Gm a).coeff (idxRes (P.H N) p (j % p)) ≠ 0 := by rw [hco]; exact hc
    rw [hcell a j hj1 hj2 hne]
    ring

#print axioms lucas_fam_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.Lucas
