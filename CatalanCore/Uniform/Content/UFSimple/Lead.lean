module

public import CatalanCore.Uniform.Content.UFWedge.Kill
public import CatalanCore.Uniform.Content.UFFamily.Entries

@[expose] public section

/-!
# UF simplification (H18): the leading-coefficient wedge lemma

For a fiber block `M = X • 1 + K` with constant `K`, constant border vector `s`, constant prefix
vector `u` and constant border prefix `z` over a polynomial ring `R[X]`, the bordered determinant
`fibA M s u z` has degree at most `n = card` and `X^n`-coefficient `z` (the adjugate entries have
`X^n`-coefficient `0`).  Hence the cross wedge `B_J A_K - A_J B_K` of two such fibers has
`X^(n_J + n_K)`-coefficient `z_K - z_J`.

Consequently (`wedgeC_ne_of_V`, `wedgeR_ne_of_V`) a border node is killed against `t₀` as soon as
the two prefix residues `V = p F mod p` differ.  No evaluation point, integer realisation,
LU record or Bezout certificate is needed, and the fibers of the two nodes are arbitrary.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.UFFamily

namespace CatalanCore.Uniform.Content.UFSimple

section Poly

variable {R : Type*} [CommRing R] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m]

/-- The polynomial fiber block `X • 1 + K`. -/
noncomputable def xK (K : Matrix n n R) : Matrix n n R[X] :=
  (X : R[X]) • (1 : Matrix n n R).map C + K.map C

theorem xK_apply (K : Matrix n n R) (i j : n) :
    xK K i j = (if i = j then (X : R[X]) else 0) + C (K i j) := by
  unfold xK
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem natDegree_det_xK (K : Matrix n n R) : natDegree (xK K).det ≤ Fintype.card n :=
  natDegree_det_X_add_C_le _ _

theorem coeff_det_xK (K : Matrix n n R) : coeff (xK K).det (Fintype.card n) = 1 := by
  rw [xK, coeff_det_X_add_C_card, det_one]

theorem updateRow_xK (K : Matrix n n R) (i j : n) :
    (xK K).updateRow j (Pi.single i 1) =
      (X : R[X]) • ((1 : Matrix n n R).updateRow j 0).map C +
        (K.updateRow j (Pi.single i 1)).map C := by
  refine Matrix.ext fun a b => ?_
  by_cases ha : a = j
  · subst ha
    simp only [updateRow_self, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      Pi.zero_apply, map_zero, smul_zero, zero_add]
    by_cases hb : b = i
    · subst hb; simp
    · simp [hb]
  · simp only [xK, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, updateRow_ne ha]

theorem natDegree_adj_xK (K : Matrix n n R) (i j : n) :
    natDegree ((xK K).adjugate i j) ≤ Fintype.card n := by
  rw [adjugate_apply, updateRow_xK]
  exact natDegree_det_X_add_C_le _ _

theorem coeff_adj_xK (K : Matrix n n R) (i j : n) :
    coeff ((xK K).adjugate i j) (Fintype.card n) = 0 := by
  rw [adjugate_apply, updateRow_xK, coeff_det_X_add_C_card]
  exact det_eq_zero_of_row_eq_zero j (fun b => by simp)

/-- The sum `Σ_i s_i Σ_j adj_ij u_j` of a constant-bordered `xK` block. -/
theorem natDegree_adjSum (K : Matrix n n R) (s u : n → R) :
    natDegree (∑ i, C (s i) * ∑ j, (xK K).adjugate i j * C (u j)) ≤ Fintype.card n := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (natDegree_mul_C_le _ _).trans (natDegree_adj_xK K i j)

theorem coeff_adjSum (K : Matrix n n R) (s u : n → R) :
    coeff (∑ i, C (s i) * ∑ j, (xK K).adjugate i j * C (u j)) (Fintype.card n) = 0 := by
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_C_mul, finsetSum_coeff]
  rw [Finset.sum_eq_zero fun j _ => by rw [coeff_mul_C, coeff_adj_xK, zero_mul], mul_zero]

/-- **Degree and top coefficient of the bordered determinant.** -/
theorem natDegree_fibA_xK (K : Matrix n n R) (s u : n → R) (z : R) :
    natDegree (fibA (xK K) (fun i => C (s i)) (fun i => C (u i)) (C z)) ≤ Fintype.card n := by
  unfold fibA
  beta_reduce
  refine (natDegree_sub_le _ _).trans (max_le ?_ (natDegree_adjSum K s u))
  exact (natDegree_mul_C_le _ _).trans (natDegree_det_xK K)

theorem coeff_fibA_xK (K : Matrix n n R) (s u : n → R) (z : R) :
    coeff (fibA (xK K) (fun i => C (s i)) (fun i => C (u i)) (C z)) (Fintype.card n) = z := by
  unfold fibA
  beta_reduce
  rw [coeff_sub, coeff_mul_C, coeff_det_xK, coeff_adjSum, one_mul, sub_zero]

theorem fibB_xK (K : Matrix n n R) (s : n → R) :
    fibB (xK K) (fun i => C (s i)) =
      fibA (xK K) (fun i => C (s i)) (fun _ => C (1 : R)) (C 1) := by
  unfold fibB; rw [map_one]

/-- **Top coefficient of the cross wedge:** `z₁ - z₀`. -/
theorem coeff_fibCross_xK (K₀ : Matrix n n R) (s₀ u₀ : n → R) (z₀ : R)
    (K₁ : Matrix m m R) (s₁ u₁ : m → R) (z₁ : R) :
    coeff (fibCross (xK K₀) (fun i => C (s₀ i)) (fun i => C (u₀ i)) (C z₀)
      (xK K₁) (fun i => C (s₁ i)) (fun i => C (u₁ i)) (C z₁))
      (Fintype.card n + Fintype.card m) = z₁ - z₀ := by
  unfold fibCross
  rw [fibB_xK, fibB_xK, coeff_sub,
    coeff_mul_add_eq_of_natDegree_le (natDegree_fibA_xK K₀ s₀ _ _) (natDegree_fibA_xK K₁ s₁ u₁ z₁),
    coeff_mul_add_eq_of_natDegree_le (natDegree_fibA_xK K₀ s₀ u₀ z₀) (natDegree_fibA_xK K₁ s₁ _ _),
    coeff_fibA_xK, coeff_fibA_xK, coeff_fibA_xK, coeff_fibA_xK]
  ring

/-- **Leading-coefficient wedge lemma.** Distinct border prefixes give a nonzero cross wedge. -/
theorem fibCross_xK_ne (K₀ : Matrix n n R) (s₀ u₀ : n → R) (z₀ : R)
    (K₁ : Matrix m m R) (s₁ u₁ : m → R) (z₁ : R) (h : z₀ ≠ z₁) :
    fibCross (xK K₀) (fun i => C (s₀ i)) (fun i => C (u₀ i)) (C z₀)
      (xK K₁) (fun i => C (s₁ i)) (fun i => C (u₁ i)) (C z₁) ≠ 0 := by
  intro h0
  have := coeff_fibCross_xK K₀ s₀ u₀ z₀ K₁ s₁ u₁ z₁
  rw [h0, coeff_zero] at this
  exact h (sub_eq_zero.1 this.symm).symm

end Poly

section Fiber

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A core block of the form `C K + X • 1` (the shape of every `sLift` core block). -/
def CoreShape (Q : Matrix ι ι (LocRing p)[X]) (K : Matrix ι ι (LocRing p)) : Prop :=
  ∀ a b, Q a b = Polynomial.C (K a b) + (if a = b then (X : (LocRing p)[X]) else 0)

/-- The fiber of `psiP` of a `CoreShape` block is an `xK` block with constant data. -/
theorem fibOf_psiP_M (Q : Matrix ι ι (LocRing p)[X]) (K : Matrix ι ι (LocRing p))
    (hQ : CoreShape Q K) (c : ι → ℕ) (σ : ι → (LocRing p)[X]) (z : (LocRing p)[X]) (k : ZMod p) :
    (fibOf (psiP p) Fr c Q σ z k).M =
      xK (fun i j : {i // ((c i : ℕ) : ZMod p) = k} => redQ p (K i.1 j.1)) := by
  refine Matrix.ext fun i j => ?_
  change psiP p (Q i.1 j.1) = _
  rw [hQ]
  refine Eq.trans ?_ (xK_apply _ i j).symm
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
    simp only [psiP, map_add, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_X]
    ring
  · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    rw [if_neg hij', if_neg hij]
    simp only [psiP, add_zero, zero_add, Polynomial.coe_mapRingHom, Polynomial.map_C]

/-- **Cross wedge of two fibers over `𝔽_p[X]` from distinct border prefixes.** -/
theorem cross_psiP_ne (Q : Matrix ι ι (LocRing p)[X]) (K : Matrix ι ι (LocRing p))
    (hQ : CoreShape Q K) (c : ι → ℕ) (σ₀ σ : ι → LocRing p) (z₀ z : LocRing p) (k₀ k : ZMod p)
    (h : redQ p z₀ ≠ redQ p z) :
    (fibOf (psiP p) Fr c Q (fun a => Polynomial.C (σ₀ a)) (Polynomial.C z₀) k₀).cross
      (fibOf (psiP p) Fr c Q (fun a => Polynomial.C (σ a)) (Polynomial.C z) k) ≠ 0 := by
  have hM0 := fibOf_psiP_M (Fr := Fr) Q K hQ c (fun a => Polynomial.C (σ₀ a)) (Polynomial.C z₀) k₀
  have hM1 := fibOf_psiP_M (Fr := Fr) Q K hQ c (fun a => Polynomial.C (σ a)) (Polynomial.C z) k
  have key := fibCross_xK_ne
    (fun i j : {i // ((c i : ℕ) : ZMod p) = k₀} => redQ p (K i.1 j.1))
    (fun i => redQ p (σ₀ i.1)) (fun j => redQ p (Hybrid.liftQ p ((p : ℚ) * Fp Fr (c j.1))))
    (redQ p z₀)
    (fun i j : {i // ((c i : ℕ) : ZMod p) = k} => redQ p (K i.1 j.1))
    (fun i => redQ p (σ i.1)) (fun j => redQ p (Hybrid.liftQ p ((p : ℚ) * Fp Fr (c j.1))))
    (redQ p z) h
  unfold FibD.cross FibD.A FibD.B
  rw [hM0, hM1]
  unfold fibCross at key
  simpa [fibOf, psiP, PF1] using key

end Fiber

end CatalanCore.Uniform.Content.UFSimple
