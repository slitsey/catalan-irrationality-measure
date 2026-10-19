module

public import CatalanCore.Bordered.Z1.Lift
public import CatalanCore.Linalg.KrylovTri
public import CatalanCore.Linalg.TridiagCyclic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Z1.3: the chain formula for `u(X′, e_s)`
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Bordered.Z1

section Entries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `X′_{k,k+1}`. -/
def Xup (s m : ℕ) (θ : R) (k : ℕ) : R :=
  -(((k : R) + 1) * ((k : R) + 1 + θ) * ((k : R) + 1 + θ + ((s + m : ℕ) : R)) * ((s : R) - k - 1))
    * qc (pj s m k)
/-- `X′_{k,k}`. -/
def Xdiag (s m : ℕ) (θ : R) (k : ℕ) : R := Dq s m θ (-((k : R) + 1))
/-- `X′_{k+1,k}`. -/
def Xlow (s m : ℕ) (θ : R) (k : ℕ) : R :=
  -(((k : R) + 1) * ((k : R) + 1 + θ) * ((s : R) + 2 * m - k - 1)
        * (((s + m : ℕ) : R) + θ + k + 1)) * qc (1 / pj s m k)

lemma Xp_eq (s m : ℕ) (θ : R) : Xp s m θ = tri3 s (Xup s m θ) (Xdiag s m θ) (Xlow s m θ) := rfl

end Entries

lemma Xup_map {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (s m : ℕ) (θ : R) (k : ℕ) : f (Xup s m θ k) = Xup s m (f θ) k := by
  simp [Xup, qc_map]

lemma nested_prod {M : Type*} [CommMonoid M] (g : ℕ → M) (s : ℕ) :
    ∏ k ∈ range s, ∏ j ∈ range k, g j = ∏ j ∈ range s, g j ^ (s - 1 - j) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [prod_range_succ, ih, prod_range_succ (fun j => g j ^ (s + 1 - 1 - j)), ← prod_mul_distrib]
    have : s + 1 - 1 - s = 0 := by omega
    rw [this, pow_zero, mul_one]
    apply prod_congr rfl
    intro j hj
    have := mem_range.1 hj
    rw [← pow_succ]; congr 1; omega

section Field

variable {K : Type*} [Field K]

lemma tri3_mulVec_ev {n : ℕ} (sup d sub : ℕ → K) (p : ℕ) (hp : p < n) :
    tri3 n sup d sub *ᵥ ev n p =
      (if 0 < p then sup (p - 1) • ev n (p - 1) else 0) + d p • ev n p
        + (if p + 1 < n then sub p • ev n (p + 1) else 0) := by
  ext i
  have h1 : (tri3 n sup d sub *ᵥ ev n p) i = tri3 n sup d sub i ⟨p, hp⟩ := by
    simp only [Matrix.mulVec, dotProduct, ev]
    rw [Finset.sum_eq_single ⟨p, hp⟩]
    · simp
    · intro m _ hm
      have : (m : ℕ) ≠ p := fun h => hm (Fin.ext h)
      simp [this]
    · simp
  rw [h1, tri3_apply]
  have hi := i.2
  by_cases h0 : 0 < p <;> by_cases h2 : p + 1 < n <;>
  simp only [h0, h2, if_true, if_false, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, ev, smul_eq_mul,
    Fin.val_mk, add_zero, zero_add] <;>
  split_ifs <;> (try (exfalso; omega)) <;>
  first | ring1 | (have e : (i : ℕ) = p := by omega
                   rw [e]; ring1)
        | (have e : p - 1 = (i : ℕ) := by omega
           rw [e]; ring1)

lemma det_colMat_rev (s : ℕ) :
    (colMat (fun j => ev (F := K) s (s - 1 - j))).det = 1 ∨
      (colMat (fun j => ev (F := K) s (s - 1 - j))).det = -1 := by
  have h : colMat (fun j => ev (F := K) s (s - 1 - j)) =
      (Fin.revPerm : Equiv.Perm (Fin s)).permMatrix K := by
    ext i k
    simp only [colMat, ev, Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Fin.revPerm_apply, Option.mem_def, Option.some.injEq]
    have hi := i.2
    have hk := k.2
    by_cases h : (i : ℕ) = s - 1 - k
    · have : Fin.rev k = i := Fin.ext (by simp [Fin.val_rev]; omega)
      simp [h]; rw [← this, Fin.rev_rev]
    · have : Fin.rev k ≠ i := fun e => h (by rw [← e]; simp [Fin.val_rev]; omega)
      simp [h]; intro e; apply this; rw [← e, Fin.rev_rev]
  rw [h, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h | h <;>
    simp [h]

variable [Algebra ℚ K]

theorem kdet_Xp_chain (s m : ℕ) (θ : K) :
    kdet (Xp s m θ) (es K s) =
      (∏ k : Fin s, ∏ j ∈ range k, Xup s m θ (s - 1 - (j + 1))) *
        (colMat (fun j => ev (F := K) s (s - 1 - j))).det := by
  have hT : ∀ j, j + 1 < s → Xp s m θ *ᵥ ev s (s - 1 - j) =
      Xup s m θ (s - 1 - (j + 1)) • ev s (s - 1 - (j + 1)) + Xdiag s m θ (s - 1 - j) • ev s (s - 1 - j)
        + (if j = 0 then 0 else Xlow s m θ (s - 1 - j)) • ev s (s - 1 - (j - 1)) := by
    intro j hj
    have hp0 : 0 < s - 1 - j := by omega
    rw [Xp_eq, tri3_mulVec_ev _ _ _ (s - 1 - j) (by omega), if_pos hp0,
      show s - 1 - j - 1 = s - 1 - (j + 1) from by omega]
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_neg (by omega), if_pos rfl]; simp
    · rw [if_pos (by omega), if_neg hj0, show s - 1 - j + 1 = s - 1 - (j - 1) from by omega]
  have := kdet_eq_of_chain (Xp s m θ) (fun j => ev (F := K) s (s - 1 - j))
    (fun j => Xup s m θ (s - 1 - (j + 1))) (fun j => Xdiag s m θ (s - 1 - j))
    (fun j => if j = 0 then 0 else Xlow s m θ (s - 1 - j)) hT (by simp)
  have e : ev (F := K) s (s - 1 - 0) = es K s := by
    funext i; simp [es, ev]
  rw [e] at this
  exact this

end Field

/-- `u(X′, e_s)` over `ℚ[X]`: up to a sign, an explicit product. -/
theorem kdet_Xp_poly (s m : ℕ) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧
      kdet (Xp s m (X : ℚ[X])) (es ℚ[X] s) =
        C ε * ∏ j ∈ range s, (Xup s m (X : ℚ[X]) (s - 1 - (j + 1))) ^ (s - 1 - j) := by
  let f : ℚ[X] →ₐ[ℚ] RatFunc ℚ := IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)
  have hinj : Function.Injective f := RatFunc.algebraMap_injective ℚ
  have h1 := kdet_map (f : ℚ[X] →+* RatFunc ℚ) (Xp s m (X : ℚ[X])) (es ℚ[X] s)
  have h2 : (Xp s m (X : ℚ[X])).map (f : ℚ[X] →+* RatFunc ℚ) = Xp s m (f X) := Xp_map f s m X
  have h3 : ((f : ℚ[X] →+* RatFunc ℚ) ∘ es ℚ[X] s) = es (RatFunc ℚ) s := by
    funext i; simp [es]
  have hF := Fin.prod_univ_eq_prod_range
    (fun k : ℕ => ∏ j ∈ range k, Xup s m (f X) (s - 1 - (j + 1))) s
  rw [h2, h3, kdet_Xp_chain, hF, nested_prod] at h1
  rcases det_colMat_rev (K := RatFunc ℚ) s with hd | hd
  · refine ⟨1, Or.inl rfl, hinj ?_⟩
    refine h1.trans ?_
    rw [hd]
    simp [map_prod, map_pow, Xup_map]
  · refine ⟨-1, Or.inr rfl, hinj ?_⟩
    refine h1.trans ?_
    rw [hd]
    simp [map_prod, map_pow, Xup_map]

end CatalanCore.Bordered.Z1
