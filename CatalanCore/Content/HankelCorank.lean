module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The generic-corank argument (Lemma K of `N9-LAI-CONTENT-EXACT`), generic part

* `rank_map_le`: the rank of a matrix over a field cannot rise under a specialisation
  (`R →+* L`) of a matrix over a domain, compared with its rank over any field `K ⊇ R`.
* `NB`: the matrix `∑_s w_s E_sᵀ H_s E_s` of a family of local Hankel forms plus a polynomial
  ("global") block.
* `rank_NB_generic`: if the local constants are indeterminates, then the corank of `NB` is at
  least `x₁` whenever the "sum" hypothesis holds.
-/

open Matrix Polynomial Finset

namespace CatalanCore.Content

section Minor

variable {L I : Type*} [Field L] [Fintype I] [DecidableEq I]

/-- Over a field, a matrix of rank `r` has a nonvanishing `r × r` minor. -/
lemma exists_minor (A : Matrix I I L) :
    ∃ f g : Fin A.rank → I, (A.submatrix f g).det ≠ 0 := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' L A.col
  haveI : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hspan]; exact (finrank_span_eq_card hli).symm
  let eκ : Fin A.rank ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let g : Fin A.rank → I := a ∘ eκ
  set B : Matrix I (Fin A.rank) L := A.submatrix id g with hB
  have hBli : LinearIndependent L B.col := by
    have := hli.comp eκ eκ.injective
    exact this
  have hrankB : B.rank = A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hBli, Fintype.card_fin]
  obtain ⟨κ', a', ha', hspan', hli'⟩ := exists_linearIndependent' L B.row
  haveI : Fintype κ' := Fintype.ofInjective a' ha'
  have hcard' : Fintype.card κ' = A.rank := by
    rw [← hrankB, Matrix.rank_eq_finrank_span_row, ← hspan']
    exact (finrank_span_eq_card hli').symm
  let eκ' : Fin A.rank ≃ κ' := (Fintype.equivFinOfCardEq hcard').symm
  let f : Fin A.rank → I := a' ∘ eκ'
  refine ⟨f, g, ?_⟩
  have hC : LinearIndependent L (B.submatrix f id).row := hli'.comp eκ' eκ'.injective
  have hU := Matrix.linearIndependent_rows_iff_isUnit.1 hC
  rw [Matrix.isUnit_iff_isUnit_det] at hU
  exact hU.ne_zero

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- **Semicontinuity of rank.**  Specialising a matrix over a domain does not raise its rank
above the rank over any field into which the domain embeds. -/
theorem rank_map_le (φ : R →+* L) (ψ : R →+* K) (hψ : Function.Injective ψ) (M : Matrix I I R) :
    (M.map φ).rank ≤ (M.map ψ).rank := by
  obtain ⟨f, g, hdet⟩ := exists_minor (M.map φ)
  have h1 : ((M.submatrix f g).map φ).det ≠ 0 := by
    simpa [Matrix.submatrix_map] using hdet
  have h2 : (M.submatrix f g).det ≠ 0 := by
    intro h0
    apply h1
    have e : ((M.submatrix f g).map φ).det = φ (M.submatrix f g).det := (RingHom.map_det φ _).symm
    rw [e, h0, map_zero]
  have h3 : ((M.submatrix f g).map ψ).det ≠ 0 := by
    have e : ((M.submatrix f g).map ψ).det = ψ (M.submatrix f g).det := (RingHom.map_det ψ _).symm
    rw [e]
    intro h0
    exact h2 (hψ (by rw [h0, map_zero]))
  have h4 := Matrix.rank_of_det_ne_zero h3
  rw [Fintype.card_fin] at h4
  have h5 := Matrix.rank_submatrix_le (M.map ψ) f g
  rw [Matrix.submatrix_map, h4] at h5
  exact h5

end Minor

section NBMat

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- coordinates: local jets `(s, i)`, `i < μ s`, and the global block `j < d`. -/
abbrev NBIdx (S : Type*) [Fintype S] (μ : S → ℕ) (d : ℕ) : Type _ := (Σ s : S, Fin (μ s)) ⊕ Fin d

/-- The matrix `∑_s w_s E_sᵀ H_s E_s`: local Hankel blocks `Φ_s(i + i')` weighted by `w_s`,
coupled to a global polynomial block (coefficient vector `h`) through the values `h(pt s)`. -/
def NB {A : Type*} [CommRing A] (μ : S → ℕ) (d : ℕ) (w pt : S → A) (Φ : S → ℕ → A) :
    Matrix (NBIdx S μ d) (NBIdx S μ d) A :=
  Matrix.of fun x y =>
    match x, y with
    | Sum.inl ⟨s, i⟩, Sum.inl ⟨s', i'⟩ => if s = s' then w s * Φ s ((i : ℕ) + i') else 0
    | Sum.inl ⟨s, i⟩, Sum.inr j => w s * Φ s ((i : ℕ) + μ s) * pt s ^ (j : ℕ)
    | Sum.inr j, Sum.inl ⟨s, i⟩ => w s * Φ s ((i : ℕ) + μ s) * pt s ^ (j : ℕ)
    | Sum.inr j, Sum.inr j' => ∑ s, w s * Φ s (2 * μ s) * pt s ^ ((j : ℕ) + j')

end NBMat

section NBKernel

variable {K : Type*} [Field K] {S : Type*} [Fintype S] [DecidableEq S]

lemma eval_fin {P : K[X]} {d : ℕ} (hP : P.natDegree < d) (x : K) :
    ∑ j : Fin d, P.coeff j * x ^ (j : ℕ) = P.eval x := by
  rw [Polynomial.eval_eq_sum_range' hP x, Fin.sum_univ_eq_sum_range (fun j => P.coeff j * x ^ j) d]

/-- the candidate kernel vector attached to the polynomial `P`. -/
noncomputable def kvec (W : Finset S) (μ : S → ℕ) (d : ℕ) (y : ℕ → K) (pt : S → K) (P : K[X]) :
    NBIdx S μ d → K :=
  Sum.elim (fun x => if x.1 ∈ W then -(y x.2) * P.eval (pt x.1) else 0) (fun j => P.coeff j)

noncomputable def kvecL (W : Finset S) (μ : S → ℕ) (d : ℕ) (y : ℕ → K) (pt : S → K) :
    K[X] →ₗ[K] (NBIdx S μ d → K) where
  toFun P := kvec W μ d y pt P
  map_add' P Q := by
    funext x
    rcases x with ⟨s, i⟩ | j
    · by_cases hs : s ∈ W <;> simp [kvec, hs, mul_add]
    · simp [kvec]
  map_smul' c P := by
    funext x
    rcases x with ⟨s, i⟩ | j
    · by_cases hs : s ∈ W <;> simp [kvec, hs, Polynomial.eval_smul] <;> ring
    · simp [kvec]

/-- **The kernel theorem.**  `W ⊔ Z` is the set of tie residues; the weights `w`, points `pt` and
local constants `Φ` are arbitrary, but on `W` (one class) the block size is a constant `μ0` and the
constants are one sequence `Φ0` with invertible leading `μ0 × μ0` Hankel block.  If the global sums
`∑_{s ∈ W} w_s (Z u)(pt s) pt_s^j` vanish (`Z = ∏_{z ∈ Z}(X - pt z)`, `deg u < x₁`, `j < d`) and
`|Z| + x₁ ≤ d`, then the corank is at least `x₁`. -/
theorem NB_corank (W Z : Finset S) (hWZ : Disjoint W Z) (hcov : W ∪ Z = Finset.univ)
    (μ : S → ℕ) (μ0 d x1 : ℕ) (hμ : ∀ s ∈ W, μ s = μ0) (hx : Z.card + x1 ≤ d)
    (w pt : S → K) (Φ : S → ℕ → K) (Φ0 : ℕ → K) (hΦ : ∀ s ∈ W, Φ s = Φ0)
    (hH : (Matrix.of fun i i' : Fin μ0 => Φ0 ((i : ℕ) + i')).det ≠ 0)
    (hsum : ∀ m < x1, ∀ j < d,
      ∑ s ∈ W, w s * ((∏ z ∈ Z, (pt s - pt z)) * pt s ^ m) * pt s ^ j = 0) :
    (NB μ d w pt Φ).rank + x1 ≤ Fintype.card (NBIdx S μ d) := by
  classical
  rcases Nat.eq_zero_or_pos x1 with hx0 | hx0
  · rw [hx0, add_zero]; exact Matrix.rank_le_card_width _
  set Zp : K[X] := ∏ z ∈ Z, (X - C (pt z)) with hZp
  have hZmonic : Zp.Monic := Polynomial.monic_prod_of_monic _ _ (fun z _ => Polynomial.monic_X_sub_C _)
  have hZdeg : Zp.natDegree = Z.card := by
    rw [hZp, Polynomial.natDegree_prod_of_monic _ _ (fun z _ => Polynomial.monic_X_sub_C _)]
    simp
  -- the solution `y` of the local Hankel system
  set H : Matrix (Fin μ0) (Fin μ0) K := Matrix.of fun i i' => Φ0 ((i : ℕ) + i') with hHdef
  set φv : Fin μ0 → K := fun i => Φ0 ((i : ℕ) + μ0) with hφ
  set Y : Fin μ0 → K := H⁻¹ *ᵥ φv with hY
  set y : ℕ → K := fun i => if hi : i < μ0 then Y ⟨i, hi⟩ else 0 with hy
  have hHY : ∀ i : Fin μ0, ∑ i' : Fin μ0, Φ0 ((i : ℕ) + i') * y i' = φv i := by
    intro i
    have hdet : IsUnit H.det := isUnit_iff_ne_zero.2 hH
    have h1 : H *ᵥ Y = φv := by
      rw [hY, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have h2 := congrFun h1 i
    simp only [Matrix.mulVec, dotProduct, hHdef, Matrix.of_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    simp [hy]
  -- the linear map
  let T : (Polynomial.degreeLT K x1) →ₗ[K] (NBIdx S μ d → K) :=
    (kvecL W μ d y pt) ∘ₗ (LinearMap.mulLeft K Zp) ∘ₗ (Polynomial.degreeLT K x1).subtype
  have hdegP : ∀ u : K[X], u.degree < x1 → (Zp * u).natDegree < d := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0; simp; omega
    · have hunat : u.natDegree < x1 := by
        have := Polynomial.natDegree_lt_iff_degree_lt hu0 |>.2 hu
        exact this
      rw [Polynomial.natDegree_mul hZmonic.ne_zero hu0, hZdeg]
      omega
  have hker : ∀ u : Polynomial.degreeLT K x1, (NB μ d w pt Φ) *ᵥ (T u) = 0 := by
    intro u
    obtain ⟨u, hu⟩ := u
    have hudeg : u.degree < x1 := Polynomial.mem_degreeLT.1 hu
    set P := Zp * u with hP
    have hPd : P.natDegree < d := hdegP u hudeg
    have hPZ : ∀ z ∈ Z, P.eval (pt z) = 0 := by
      intro z hz
      rw [hP, Polynomial.eval_mul, hZp, Polynomial.eval_prod]
      rw [Finset.prod_eq_zero hz (by simp), zero_mul]
    have hPW : ∀ s, s ∉ W → P.eval (pt s) = 0 := by
      intro s hs
      have : s ∈ Z := by
        have : s ∈ W ∪ Z := by rw [hcov]; exact Finset.mem_univ s
        rcases Finset.mem_union.1 this with h | h
        · exact absurd h hs
        · exact h
      exact hPZ s this
    have hTP : T ⟨u, hu⟩ = kvec W μ d y pt P := rfl
    rw [hTP]
    funext x
    rcases x with ⟨s, ⟨i0, hi0⟩⟩ | j'
    · -- row `(s, i)`
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [Fintype.sum_sum_type, Fintype.sum_sigma]
      simp only [NB, Matrix.of_apply, kvec, Sum.elim_inl, Sum.elim_inr, Fin.val_mk]
      have h1 : ∑ a : S, ∑ b : Fin (μ a), (if s = a then w s * Φ s (i0 + b) else 0) *
            (if a ∈ W then -(y b) * P.eval (pt a) else 0) =
          ∑ b : Fin (μ s), w s * Φ s (i0 + b) * (if s ∈ W then -(y b) * P.eval (pt s) else 0) := by
        rw [Finset.sum_eq_single s (fun a _ ha => ?_) (fun h => absurd (Finset.mem_univ s) h)]
        · simp
        · exact Finset.sum_eq_zero fun b _ => by simp [Ne.symm ha]
      have h2 : ∑ j : Fin d, w s * Φ s (i0 + μ s) * pt s ^ (j : ℕ) * P.coeff j =
          w s * Φ s (i0 + μ s) * P.eval (pt s) := by
        rw [← eval_fin hPd (pt s), Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_); ring
      rw [h1, h2]
      by_cases hs : s ∈ W
      · simp only [hs, if_true]
        have hi : i0 < μ0 := (hμ s hs) ▸ hi0
        have hsum' : ∑ b : Fin (μ s), w s * Φ s (i0 + b) * (-(y b) * P.eval (pt s)) =
            - (w s * P.eval (pt s) * Φ0 (i0 + μ0)) := by
          have := Fin.sum_univ_eq_sum_range
            (fun b : ℕ => w s * Φ0 (i0 + b) * (-(y b) * P.eval (pt s))) (μ s)
          simp only [hΦ s hs] at *
          rw [this, hμ s hs]
          have := hHY ⟨i0, hi⟩
          rw [← Fin.sum_univ_eq_sum_range
            (fun b : ℕ => w s * Φ0 (i0 + b) * (-(y b) * P.eval (pt s))) μ0]
          calc ∑ b : Fin μ0, w s * Φ0 (i0 + b) * (-(y b) * P.eval (pt s))
              = -(w s * P.eval (pt s)) * ∑ b : Fin μ0, Φ0 (i0 + b) * y b := by
                rw [Finset.mul_sum] <;> exact Finset.sum_congr rfl (fun b _ => by ring)
            _ = _ := by rw [this]; simp [hφ]
        rw [hsum', hΦ s hs, hμ s hs]; ring
      · simp only [hs, if_false, mul_zero, Finset.sum_const_zero, zero_add]
        rw [hPW s hs]; ring
    · -- row `j'`
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [Fintype.sum_sum_type, Fintype.sum_sigma]
      simp only [NB, Matrix.of_apply, kvec, Sum.elim_inl, Sum.elim_inr, Fin.val_mk]
      have h2 : ∑ j : Fin d, (∑ a, w a * Φ a (2 * μ a) * pt a ^ ((j' : ℕ) + (j : ℕ))) * P.coeff j
            = ∑ a, w a * Φ a (2 * μ a) * pt a ^ (j' : ℕ) * P.eval (pt a) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← eval_fin hPd (pt a), Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [h2, ← Finset.sum_add_distrib]
      set κ : K := Φ0 (2 * μ0) - ∑ b : Fin μ0, Φ0 ((b : ℕ) + μ0) * y b with hκ
      have hper : ∀ a : S, (∑ b : Fin (μ a), w a * Φ a ((b : ℕ) + μ a) * pt a ^ (j' : ℕ) *
            (if a ∈ W then -(y b) * P.eval (pt a) else 0)) +
          w a * Φ a (2 * μ a) * pt a ^ (j' : ℕ) * P.eval (pt a) =
          if a ∈ W then κ * (w a * P.eval (pt a) * pt a ^ (j' : ℕ)) else 0 := by
        intro a
        by_cases ha : a ∈ W
        · simp only [ha, if_true]
          have := Fin.sum_univ_eq_sum_range
            (fun b : ℕ => w a * Φ a (b + μ a) * pt a ^ (j' : ℕ) * (-(y b) * P.eval (pt a))) (μ a)
          rw [this, hΦ a ha, hμ a ha]
          have h3 := Fin.sum_univ_eq_sum_range (fun b : ℕ => Φ0 (b + μ0) * y b) μ0
          have h4 : ∑ b ∈ Finset.range μ0, w a * Φ0 (b + μ0) * pt a ^ (j' : ℕ) *
              (-(y b) * P.eval (pt a)) =
              -(w a * pt a ^ (j' : ℕ) * P.eval (pt a)) * ∑ b ∈ Finset.range μ0, Φ0 (b + μ0) * y b := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
          rw [h4, ← h3, hκ]; ring
        · simp only [ha, if_false, mul_zero, Finset.sum_const_zero, zero_add]
          rw [hPW a ha]; ring
      rw [Finset.sum_congr rfl (fun a _ => hper a), Finset.sum_ite_mem, Finset.univ_inter,
        ← Finset.mul_sum]
      have hunat : u.natDegree < x1 := by
        by_cases hu0 : u = 0
        · subst hu0; simpa using hx0
        · exact (Polynomial.natDegree_lt_iff_degree_lt hu0).2 hudeg
      have hev : ∀ s : S, P.eval (pt s) =
          ∑ m ∈ Finset.range x1, u.coeff m * ((∏ z ∈ Z, (pt s - pt z)) * pt s ^ m) := by
        intro s
        rw [hP, Polynomial.eval_mul, hZp, Polynomial.eval_prod, Polynomial.eval_eq_sum_range' hunat,
          Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        ring
      have hzero : ∑ a ∈ W, w a * P.eval (pt a) * pt a ^ (j' : ℕ) = 0 := by
        simp_rw [hev, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero (fun m hm => ?_)
        have := hsum m (Finset.mem_range.1 hm) j' j'.2
        rw [← mul_zero (u.coeff m), ← this, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => by ring)
      rw [hzero, mul_zero]
  -- injectivity of `T`
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro u hu0
    obtain ⟨u, hu⟩ := u
    have hudeg : u.degree < x1 := Polynomial.mem_degreeLT.1 hu
    have hPd := hdegP u hudeg
    have hc : ∀ j : Fin d, (Zp * u).coeff j = 0 := fun j => congrFun hu0 (Sum.inr j)
    have hP0 : Zp * u = 0 := by
      refine Polynomial.ext (fun m => ?_)
      by_cases hm : m < d
      · simpa using hc ⟨m, hm⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
    have hu0' : u = 0 := by
      rcases mul_eq_zero.1 hP0 with h | h
      · exact absurd h hZmonic.ne_zero
      · exact h
    exact Subtype.ext hu0'
  have hrange : LinearMap.range T ≤ LinearMap.ker (NB μ d w pt Φ).mulVecLin := by
    rintro _ ⟨u, rfl⟩
    exact hker u
  have h1 : Module.finrank K (Polynomial.degreeLT K x1) = x1 := by
    rw [LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv K x1)]; simp
  have h2 := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hinj, h1] at h2
  have h3 := LinearMap.finrank_range_add_finrank_ker (NB μ d w pt Φ).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h3
  have : (NB μ d w pt Φ).rank = Module.finrank K (LinearMap.range (NB μ d w pt Φ).mulVecLin) := rfl
  omega

end NBKernel

section NBSpec

variable {L : Type*} [Field L] {S : Type*} [Fintype S] [DecidableEq S]

lemma NB_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (μ : S → ℕ) (d : ℕ)
    (w pt : S → A) (Φ : S → ℕ → A) :
    (NB μ d w pt Φ).map f =
      NB μ d (fun s => f (w s)) (fun s => f (pt s)) (fun s m => f (Φ s m)) := by
  ext x y
  rcases x with ⟨s, i⟩ | j <;> rcases y with ⟨s', i'⟩ | j' <;>
    simp [NB, apply_ite f, map_sum, map_mul, map_pow]

/-- the generic Hankel determinant is a nonzero polynomial. -/
lemma hankel_generic_det_ne_zero (μ0 : ℕ) :
    (Matrix.of fun i i' : Fin μ0 => (MvPolynomial.X ((i : ℕ) + i') : MvPolynomial ℕ L)).det ≠ 0 := by
  intro h0
  set ev : MvPolynomial ℕ L →+* L :=
    (MvPolynomial.aeval (fun m : ℕ => if m + 1 = μ0 then (1 : L) else 0)).toRingHom with hev
  have h1 := congrArg ev h0
  have h2 : ev (Matrix.of fun i i' : Fin μ0 => (MvPolynomial.X ((i : ℕ) + i') : MvPolynomial ℕ L)).det =
      (Matrix.of fun i i' : Fin μ0 => (if (i : ℕ) + i' + 1 = μ0 then (1 : L) else 0)).det := by
    have := RingHom.map_det ev
      (Matrix.of fun i i' : Fin μ0 => (MvPolynomial.X ((i : ℕ) + i') : MvPolynomial ℕ L))
    rw [this]
    congr 1
    ext i i'
    simp [hev]
  have h3 : (Matrix.of fun i i' : Fin μ0 => (if (i : ℕ) + i' + 1 = μ0 then (1 : L) else 0)) =
      (Fin.revPerm : Equiv.Perm (Fin μ0)).permMatrix L := by
    ext i j
    have hi := i.2
    simp only [Matrix.of_apply, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply,
      Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
    have : ((Fin.rev i : Fin μ0) = j) ↔ ((i : ℕ) + j + 1 = μ0) := by
      rw [Fin.ext_iff, Fin.val_rev]
      omega
    simp only [this]
  rw [h2, h3, Matrix.det_permutation, map_zero] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin μ0))) with h | h <;>
    simp [h] at h1

/-- **Lemma K, generic-constants argument.**  The corank bound of `NB_corank` holds for *all*
constants on `W` (no invertibility), by semicontinuity of the rank. -/
theorem NB_corank_spec (W Z : Finset S) (hWZ : Disjoint W Z) (hcov : W ∪ Z = Finset.univ)
    (μ : S → ℕ) (μ0 d x1 : ℕ) (hμ : ∀ s ∈ W, μ s = μ0) (hx : Z.card + x1 ≤ d)
    (w pt : S → L) (Φ : S → ℕ → L) (Φ0 : ℕ → L) (hΦ : ∀ s ∈ W, Φ s = Φ0)
    (hsum : ∀ m < x1, ∀ j < d,
      ∑ s ∈ W, w s * ((∏ z ∈ Z, (pt s - pt z)) * pt s ^ m) * pt s ^ j = 0) :
    (NB μ d w pt Φ).rank + x1 ≤ Fintype.card (NBIdx S μ d) := by
  classical
  set R := MvPolynomial ℕ L with hR
  set K := FractionRing R with hK
  set ψ : R →+* K := algebraMap R K with hψdef
  have hψ : Function.Injective ψ := IsFractionRing.injective R K
  set φ : R →+* L := (MvPolynomial.aeval Φ0).toRingHom with hφ
  set ΦR : S → ℕ → R := fun s m => if s ∈ W then MvPolynomial.X m else MvPolynomial.C (Φ s m) with hΦR
  set NR : Matrix (NBIdx S μ d) (NBIdx S μ d) R :=
    NB μ d (fun s => MvPolynomial.C (w s)) (fun s => MvPolynomial.C (pt s)) ΦR with hNR
  have hφC : ∀ x : L, φ (MvPolynomial.C x) = x := fun x => by
    rw [hφ]; exact MvPolynomial.aeval_C Φ0 x
  have hφX : ∀ m : ℕ, φ (MvPolynomial.X m) = Φ0 m := fun m => by
    rw [hφ]; exact MvPolynomial.aeval_X Φ0 m
  have hmap : NR.map φ = NB μ d w pt Φ := by
    rw [hNR, NB_map]
    have e1 : (fun s => φ (MvPolynomial.C (w s))) = w := by funext s; exact hφC _
    have e2 : (fun s => φ (MvPolynomial.C (pt s))) = pt := by funext s; exact hφC _
    have e3 : (fun s m => φ (ΦR s m)) = Φ := by
      funext s m
      by_cases hs : s ∈ W
      · simp only [hΦR, hs, if_true, hφX, hΦ s hs]
      · simp only [hΦR, hs, if_false, hφC]
    rw [e1, e2, e3]
  have h1 := rank_map_le φ ψ hψ NR
  rw [hmap] at h1
  rw [hNR, NB_map] at h1
  have hK1 := NB_corank (K := K) W Z hWZ hcov μ μ0 d x1 hμ hx
    (fun s => ψ (MvPolynomial.C (w s))) (fun s => ψ (MvPolynomial.C (pt s)))
    (fun s m => ψ (ΦR s m)) (fun m => ψ (MvPolynomial.X m))
    (fun s hs => by funext m; simp [hΦR, hs])
    (by
      have hdet : (Matrix.of fun i i' : Fin μ0 => ψ (MvPolynomial.X ((i : ℕ) + i') : R)).det =
          ψ (Matrix.of fun i i' : Fin μ0 => (MvPolynomial.X ((i : ℕ) + i') : R)).det := by
        have := RingHom.map_det ψ
          (Matrix.of fun i i' : Fin μ0 => (MvPolynomial.X ((i : ℕ) + i') : R))
        rw [this]; congr 1
      rw [hdet]
      intro h0
      exact hankel_generic_det_ne_zero (L := L) μ0 (hψ (by rw [h0, map_zero])))
    (by
      intro m hm j hj
      have := congrArg (fun z : L => ψ (MvPolynomial.C z)) (hsum m hm j hj)
      simpa [map_sum, map_mul, map_prod, map_sub, map_pow] using this)
  omega

end NBSpec

end CatalanCore.Content

#print axioms CatalanCore.Content.rank_map_le
#print axioms CatalanCore.Content.NB_corank
#print axioms CatalanCore.Content.NB_corank_spec
