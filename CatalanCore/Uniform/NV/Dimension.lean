module
public import CatalanCore.Uniform.NV.PairSpace
@[expose] public section
open Polynomial Module
namespace CatalanCore.Uniform.NV
variable {K : Type*} [Field K]

/-- Rational rank one forces the same coordinate to dominate every pair. -/
theorem degree_dominated_of_cross_product (p0 q0 p q : K[X])
    (hp0 : p0 ≠ 0) (hdeg : q0.natDegree ≤ p0.natDegree)
    (hc : q*p0-q0*p = 0) : q.natDegree ≤ p.natDegree := by
  by_cases hq : q = 0
  · simp [hq]
  have he := sub_eq_zero.mp hc
  have hq0 : q0 ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at he
    exact mul_ne_zero hq hp0 he
  have hp : p ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at he
    exact mul_ne_zero hq hp0 he
  have hd := congrArg Polynomial.natDegree he
  rw [natDegree_mul hq hp0,natDegree_mul hq0 hp] at hd
  omega

/-- Vanishing highest s coefficients leaves a genuinely shorter polynomial. -/
theorem natDegree_le_of_top_coefficients (p : K[X]) (n s : ℕ) (hs : s < n)
    (hp : p.natDegree ≤ n-1)
    (hc : ∀ i : Fin s, p.coeff (n-s+i.val) = 0) : p.natDegree ≤ n-s-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  by_cases hkn : k < n
  · have hlo : n-s ≤ k := by omega
    have hi : k-(n-s) < s := by omega
    have he := hc ⟨k-(n-s),hi⟩
    change p.coeff (n-s+(k-(n-s))) = 0 at he
    convert he using 1 <;> congr 1 <;> omega
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

variable {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def topCoefficients (p : V →ₗ[K] K[X]) (n s : ℕ) : V →ₗ[K] (Fin s → K) where
  toFun v i := (p v).coeff (n-s+i.val)
  map_add' := by intros;ext i;simp
  map_smul' := by intros;ext i;simp

/-- A short-pair exclusion yields a dimension bound using only s coefficients. -/
theorem finrank_le_of_dominating_coordinate (p q : V →ₗ[K] K[X]) (n s : ℕ)
    (hs : s < n) (hdeg : ∀ v, (p v).natDegree ≤ n-1)
    (hdom : ∀ v, (q v).natDegree ≤ (p v).natDegree)
    (hshort : ∀ v, (p v).natDegree ≤ n-s-1 → (q v).natDegree ≤ n-s-1 → v = 0) :
    finrank K V ≤ s := by
  let T := topCoefficients p n s
  have hi : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hp := natDegree_le_of_top_coefficients (p v) n s hs (hdeg v)
      (fun i => congrFun hv i)
    exact hshort v hp ((hdom v).trans hp)
  simpa using T.finrank_le_finrank_of_injective hi

/-- This replaces primitive-pair factorization: the rank-one identity alone
selects a globally dominating polynomial coordinate. -/
theorem finrank_le_of_no_short_pairs (p q : V →ₗ[K] K[X]) (n s : ℕ)
    (hs : s < n) (hp : ∀ v, (p v).natDegree ≤ n-1)
    (hq : ∀ v, (q v).natDegree ≤ n-1)
    (hjoint : ∀ v, p v = 0 → q v = 0 → v = 0)
    (hcross : ∀ v w, q v*p w-q w*p v = 0)
    (hshort : ∀ v, (p v).natDegree ≤ n-s-1 → (q v).natDegree ≤ n-s-1 → v = 0) :
    finrank K V ≤ s := by
  by_cases hv : ∃ v : V, v ≠ 0
  · obtain ⟨v0,hv0⟩ := hv
    by_cases hdom : (q v0).natDegree ≤ (p v0).natDegree
    · by_cases hp0 : p v0 = 0
      · have hq0 : (q v0).natDegree = 0 := by simpa [hp0] using hdom
        have hcross0 := hcross
        -- If the chosen first coordinate vanishes, its nonzero second coordinate
        -- dominates, even when both natDegrees are zero.
        have hqn : q v0 ≠ 0 := by intro hz;exact hv0 (hjoint v0 hp0 hz)
        apply finrank_le_of_dominating_coordinate q p n s hs hq
        · intro v
          apply degree_dominated_of_cross_product (q v0) (p v0) (q v) (p v) hqn
          · simp [hp0]
          · linear_combination -(hcross v v0)
        · intro v hqv hpv
          exact hshort v hpv hqv
      · apply finrank_le_of_dominating_coordinate p q n s hs hp
        · intro v
          exact degree_dominated_of_cross_product (p v0) (q v0) (p v) (q v) hp0 hdom (hcross v v0)
        · exact hshort
    · have hqn : q v0 ≠ 0 := by intro hz;simp [hz] at hdom
      apply finrank_le_of_dominating_coordinate q p n s hs hq
      · intro v
        apply degree_dominated_of_cross_product (q v0) (p v0) (q v) (p v) hqn (by omega)
        linear_combination -(hcross v v0)
      · intro v hqv hpv
        exact hshort v hpv hqv
  · let T : V →ₗ[K] (Fin s → K) := 0
    have hi : Function.Injective T := by
      intro v w _
      have hv0 : v = 0 := by by_contra hn;exact hv ⟨v,hn⟩
      have hw0 : w = 0 := by by_contra hn;exact hv ⟨w,hn⟩
      exact hv0.trans hw0.symm
    simpa using T.finrank_le_finrank_of_injective hi

/-- A single bounded-degree polynomial coordinate has dimension at most n. -/
theorem finrank_le_of_bounded_coordinate (p : V →ₗ[K] K[X]) (n : ℕ)
    (hn : 1 ≤ n) (hp : ∀ v, (p v).natDegree ≤ n-1) (hinj : Function.Injective p) :
    finrank K V ≤ n := by
  let T := topCoefficients p n n
  have hi : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply hinj
    change p v = p 0
    rw [map_zero]
    apply Polynomial.ext
    intro k
    by_cases hk : k < n
    · have he := congrFun hv ⟨k,hk⟩
      simpa [T,topCoefficients] using he
    · simp only [coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt (by have := hp v;omega)
  simpa using T.finrank_le_finrank_of_injective hi
end CatalanCore.Uniform.NV


