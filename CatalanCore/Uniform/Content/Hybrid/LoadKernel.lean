module

public import CatalanCore.Uniform.Content.Hybrid.Barycentric
public import CatalanCore.Uniform.Content.RankLayer
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# UC5–UC7 (lower half): free sector plus pair sector for the compressed Loewner matrix

After exact local elimination the next reduction `C_p` of the hybrid source acts on the local
right-kernel coordinates; its entries depend only on the mass/pole LOADS (`Compression.lean`):

  `C_p(r, c) = ω(x_r, y_c) / (β_c - α_r)`,

with `ω` the alternating form on `K²`, row residues `α_r`, row loads `x_r`, column residues `β_c`
and column loads `y_c`.  Same-fiber entries are `·/0 = 0`, as in the source (zero same-fiber
`p`-coefficient), and the local Loewner displacement gives `ω(x_r, y_c) = 0` on a common fiber
(hypothesis `horth`).

For EVERY constant subspace `V ⊆ K²` (`loadMat_rank_add_le`):

  `rank C_p + F + (d·dim V - Σ_c rank(B_c|V)) ≤ #columns`,

i.e. `G = corank C_p ≥ F + E_pair(V)`, where

* `F = dim ker Λ` is the free sector (right load-zero coordinates), `Λ z = (Σ_{β_c=b} z_c y_c)_b`;
* `d = |Y|`, `Y` the set of column residues;
* the conditions `c` are: at each column residue `b`, `H(b) ∈ V_b = span{y_c : β_c = b}`; at each
  row residue `a ∉ Y` the value condition `ω(x_r, H(a)) = 0` for the rows at `a`; at each row residue
  `a ∈ Y` the DIRECTIONAL DERIVATIVE condition `ω(x_r, H'(a)) = 0`.  Each costs the rank of its
  constant map restricted to `V` (a quotient map `K² → K²/U_c`).

Row-only rank-two loads charge `dim V` (equivalently they lower `c = d - e`); shared rank-one loads
charge their covector twice (`o_a = 2`).  This is the paper's `E(V) = F + E_pair(V)`; merging
proportional covectors into types does not change any restricted rank.  No upper bound is claimed.
-/

open Polynomial Finset Module CatalanCore.Uniform.Content

namespace CatalanCore.Uniform.Content.Hybrid

variable {K : Type*} [Field K] [DecidableEq K]

/-- The alternating form `ω(x, ·)` on `K²`. -/
noncomputable def omegaL (x : K × K) : (K × K) →ₗ[K] K :=
  x.1 • LinearMap.snd K K K - x.2 • LinearMap.fst K K K

lemma omegaL_apply (x y : K × K) : omegaL x y = x.1 * y.2 - x.2 * y.1 := by
  simp [omegaL]

section Load

variable {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
variable (α : R → K) (x : R → K × K) (β : S → K) (y : S → K × K)

/-- The compressed (load) Loewner matrix. -/
noncomputable def loadMat : Matrix R S K :=
  Matrix.of fun r c => omegaL (x r) (y c) / (β c - α r)

/-- Column residues. -/
noncomputable def colRes : Finset K := univ.image β

/-- Row residues. -/
noncomputable def rowRes : Finset K := univ.image α

/-- Column load vectors of the fiber `b`. -/
noncomputable def colVec (b : K) (c : S) : K × K := if β c = b then y c else 0

/-- `V_b`, the span of the column loads at `b`. -/
noncomputable def colSpan (b : K) : Submodule K (K × K) :=
  Submodule.span K (Set.range (colVec β y b))

/-- The row annihilator at `a`: the vectors killed by `ω(x_r, ·)` for every row at `a`. -/
noncomputable def rowAnn (a : K) : Submodule K (K × K) :=
  LinearMap.ker (LinearMap.pi fun r => if α r = a then omegaL (x r) else 0)

/-- The load map `Λ`. -/
noncomputable def lam : (S → K) →ₗ[K] (colRes β → K × K) :=
  LinearMap.pi fun b => ∑ c, (LinearMap.proj c : (S → K) →ₗ[K] K).smulRight (colVec β y b c)

/-- The reduced row map on residue-load vectors. -/
noncomputable def redMap : (colRes β → K × K) →ₗ[K] (R → K) :=
  LinearMap.pi fun r => ∑ b : colRes β, ((b : K) - α r)⁻¹ •
    (omegaL (x r)).comp (LinearMap.proj b)

lemma lam_apply (z : S → K) (b : colRes β) : lam β y z b = ∑ c, z c • colVec β y b c := by
  simp [lam]

lemma redMap_apply (w : colRes β → K × K) (r : R) :
    redMap α x β w r = ∑ b : colRes β, ((b : K) - α r)⁻¹ * omegaL (x r) (w b) := by
  simp [redMap]

lemma mem_colRes (c : S) : β c ∈ colRes β := Finset.mem_image_of_mem β (Finset.mem_univ c)

/-- The load matrix factors through the loads. -/
theorem mulVecLin_loadMat :
    (loadMat α x β y).mulVecLin = (redMap α x β).comp (lam β y) := by
  refine LinearMap.ext fun z => funext fun r => ?_
  rw [LinearMap.comp_apply, redMap_apply, Matrix.mulVecLin_apply]
  simp only [Matrix.mulVec, dotProduct, loadMat, Matrix.of_apply, lam_apply, map_sum,
    map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_coe_sort (colRes β) (fun b => (b - α r)⁻¹ * (z c * omegaL (x r) (colVec β y b c)))]
  simp only [colVec]
  have : ∀ b ∈ colRes β, (b - α r)⁻¹ * (z c * omegaL (x r) (if β c = b then y c else 0)) =
      if β c = b then (b - α r)⁻¹ * (z c * omegaL (x r) (y c)) else 0 := by
    intro b _; split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos (mem_colRes β c)]
  rw [div_eq_mul_inv]; ring

lemma mem_range_lam {w : colRes β → K × K} (hw : ∀ b : colRes β, w b ∈ colSpan β y (b : K)) :
    w ∈ LinearMap.range (lam β y) := by
  have hf : ∀ b : colRes β, ∃ f : S → K, ∑ c, f c • colVec β y b c = w b := fun b =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hw b)
  choose f hf using hf
  refine ⟨fun c => f ⟨β c, mem_colRes β c⟩ c, funext fun b => ?_⟩
  rw [lam_apply, ← hf b]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : β c = b
  · have : (⟨β c, mem_colRes β c⟩ : colRes β) = b := Subtype.ext h
    rw [this]
  · simp [colVec, h]

lemma colSpan_le_ker (horth : ∀ r c, α r = β c → omegaL (x r) (y c) = 0) (r : R) :
    colSpan β y (α r) ≤ LinearMap.ker (omegaL (x r)) := by
  rw [colSpan, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, colVec]
  split_ifs with h
  · exact horth r c h.symm
  · simp

lemma omegaL_eq_zero_of_mem_rowAnn {a : K} {v : K × K} (hv : v ∈ rowAnn α x a) {r : R}
    (hr : α r = a) : omegaL (x r) v = 0 := by
  have := congrFun (LinearMap.mem_ker.1 hv) r
  simpa [hr] using this

/-! ### The pair conditions -/

variable (Vs : Submodule K (K × K))

/-- Condition index: column residues, then row residues. -/
abbrev Cond := colRes β ⊕ rowRes α

/-- The subspace in which the relevant jet must lie. -/
noncomputable def condSpace : Cond α β → Submodule K (K × K)
  | Sum.inl b => colSpan β y b
  | Sum.inr a => rowAnn α x a

/-- The node of a condition. -/
def condNode : Cond α β → K
  | Sum.inl b => b
  | Sum.inr a => a

/-- The jet order: `0` except the derivative at a shared row residue. -/
noncomputable def condOrd : Cond α β → ℕ
  | Sum.inl _ => 0
  | Sum.inr a => if (a : K) ∈ colRes β then 1 else 0

/-- The constant map of a condition, restricted to `V`. -/
noncomputable def condMap (c : Cond α β) : Vs →ₗ[K] (K × K) ⧸ condSpace α x β y c :=
  (condSpace α x β y c).mkQ ∘ₗ Vs.subtype

/-- The jet of a condition. -/
noncomputable def condJet (c : Cond α β) (_ : Fin 1) :
    (Fin (colRes β).card → Vs) →ₗ[K] Vs :=
  taylorJet (condNode α β c) (condOrd α β c)

/-- The pair space: `V`-valued polynomials of degree `< d` satisfying every condition. -/
noncomputable abbrev pairSpace :=
  LinearMap.ker (constraintMap (fun _ : Cond α β => 1) (condMap α x β y Vs) (condJet α β Vs))

/-- Interpolated residue loads `w_b = H(b)/D'(b)`. -/
noncomputable def interp : (Fin (colRes β).card → Vs) →ₗ[K] (colRes β → K × K) :=
  LinearMap.pi fun b => wt (colRes β) (b : K) • (Vs.subtype ∘ₗ taylorJet (b : K) 0)

lemma interp_apply (H : Fin (colRes β).card → Vs) (b : colRes β) :
    interp β Vs H b = wt (colRes β) (b : K) • ((taylorJet (b : K) 0 H : Vs) : K × K) := by
  simp [interp]

/-- A linear functional commutes with vector jets. -/
lemma map_taylorJet {n : ℕ} (φ : Vs →ₗ[K] K) (a : K) (k : ℕ) (H : Fin n → Vs) :
    φ (taylorJet a k H) = taylorJet a k (fun i => φ (H i)) := by
  simp [taylorJet, map_sum, map_smul]

lemma scalarPolynomial_degree {n : ℕ} (f : Fin n → K) : (scalarPolynomial f).degree < n := by
  have : scalarPolynomial f = ∑ i : Fin n, C (f i) * X ^ (i : ℕ) := by
    simp [scalarPolynomial, C_mul_X_pow_eq_monomial]
  rw [this]; exact degree_sum_fin_lt f

lemma scalarPolynomial_coeff {n : ℕ} (f : Fin n → K) (i : Fin n) :
    (scalarPolynomial f).coeff i = f i := by
  simp only [scalarPolynomial, finset_sum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [if_neg]; exact fun h => hj (Fin.ext h)
  · simp

lemma mem_pairSpace_iff (H : Fin (colRes β).card → Vs) :
    H ∈ pairSpace α x β y Vs ↔
      ∀ c, ((taylorJet (condNode α β c) (condOrd α β c) H : Vs) : K × K) ∈
        condSpace α x β y c := by
  rw [LinearMap.mem_ker, constraintMap_eq_zero_iff]
  constructor
  · intro h c
    have := h c 0
    simpa [condMap, condJet, Submodule.Quotient.mk_eq_zero] using this
  · intro h c k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simpa [condMap, condJet, Submodule.Quotient.mk_eq_zero] using h c

lemma interp_mem_range {H : Fin (colRes β).card → Vs} (hH : H ∈ pairSpace α x β y Vs) :
    interp β Vs H ∈ LinearMap.range (lam β y) := by
  apply mem_range_lam
  intro b
  rw [interp_apply]
  exact Submodule.smul_mem _ _ ((mem_pairSpace_iff α x β y Vs H).1 hH (Sum.inl b))

/-- The scalar polynomial `ω(x_r, H)`. -/
noncomputable def rowPoly (r : R) (H : Fin (colRes β).card → Vs) : K[X] :=
  scalarPolynomial (fun i => (omegaL (x r) ∘ₗ Vs.subtype) (H i))

lemma omegaL_taylorJet (r : R) (H : Fin (colRes β).card → Vs) (a : K) (k : ℕ) :
    omegaL (x r) ((taylorJet a k H : Vs) : K × K) = (taylor a (rowPoly x β Vs r H)).coeff k := by
  have := map_taylorJet Vs (omegaL (x r) ∘ₗ Vs.subtype) a k H
  rw [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [this, taylorJet_scalar]; rfl

lemma interp_mem_ker (horth : ∀ r c, α r = β c → omegaL (x r) (y c) = 0)
    {H : Fin (colRes β).card → Vs} (hH : H ∈ pairSpace α x β y Vs) :
    redMap α x β (interp β Vs H) = 0 := by
  have hc := (mem_pairSpace_iff α x β y Vs H).1 hH
  funext r
  rw [redMap_apply, Pi.zero_apply]
  set g := rowPoly x β Vs r H with hg
  have hev : ∀ b : K, omegaL (x r) ((taylorJet b 0 H : Vs) : K × K) = g.eval b := by
    intro b; rw [omegaL_taylorJet, taylor_coeff_zero]
  have hsum : ∑ b : colRes β, ((b : K) - α r)⁻¹ * omegaL (x r) (interp β Vs H b) =
      -∑ b ∈ colRes β, wt (colRes β) b * g.eval b / (α r - b) := by
    rw [← Finset.sum_coe_sort (colRes β), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [interp_apply, map_smul, hev, smul_eq_mul, div_eq_mul_inv, ← neg_sub, inv_neg]; ring
  rw [hsum, neg_eq_zero]
  have hdeg : g.degree < #(colRes β) := scalarPolynomial_degree _
  have hra : α r ∈ rowRes α := Finset.mem_image_of_mem α (Finset.mem_univ r)
  have hrow := hc (Sum.inr ⟨α r, hra⟩)
  by_cases hY : α r ∈ colRes β
  · -- shared residue: value vanishes by orthogonality, derivative by the row condition
    have hval : g.eval (α r) = 0 := by
      rw [← hev]
      exact colSpan_le_ker α x β y horth r (hc (Sum.inl ⟨α r, hY⟩))
    rw [bary_node _ g hdeg hY hval]
    have hder : (taylor (α r) g).coeff 1 = 0 := by
      rw [← omegaL_taylorJet]
      have : condOrd α β (Sum.inr ⟨α r, hra⟩) = 1 := by simp [condOrd, hY]
      simp only [condNode, this] at hrow
      exact omegaL_eq_zero_of_mem_rowAnn α x hrow rfl
    rw [hder, mul_zero]
  · rw [bary_off _ g hdeg hY]
    have hval : g.eval (α r) = 0 := by
      rw [← hev]
      have : condOrd α β (Sum.inr ⟨α r, hra⟩) = 0 := by simp [condOrd, hY]
      simp only [condNode, this] at hrow
      exact omegaL_eq_zero_of_mem_rowAnn α x hrow rfl
    rw [hval, zero_div]

lemma interp_injective : Function.Injective (interp β Vs) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro H hH
  have hz : ∀ b ∈ colRes β, ((taylorJet b 0 H : Vs) : K × K) = 0 := by
    intro b hb
    have := congrFun hH ⟨b, hb⟩
    rw [interp_apply, Pi.zero_apply] at this
    exact (smul_eq_zero.1 this).resolve_left
      (Lagrange.nodalWeight_ne_zero (Set.injOn_id _) hb)
  have hcoord : ∀ φ : (K × K) →ₗ[K] K, ∀ i, φ (H i : K × K) = 0 := by
    intro φ i
    set f : Fin (colRes β).card → K := fun j => (φ ∘ₗ Vs.subtype) (H j)
    have h0 : scalarPolynomial f = 0 := by
      apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (colRes β)
        (scalarPolynomial_degree f)
      intro b hb
      have := map_taylorJet Vs (φ ∘ₗ Vs.subtype) b 0 H
      rw [taylorJet_scalar, taylor_coeff_zero] at this
      rw [← this]
      simp [hz b hb]
    have := scalarPolynomial_coeff f i
    rw [h0, coeff_zero] at this
    simpa [f] using this.symm
  funext i
  apply Subtype.ext
  apply Prod.ext
  · simpa using hcoord (LinearMap.fst K K K) i
  · simpa using hcoord (LinearMap.snd K K K) i

/-- **UC5–UC7 lower bound.** For every constant subspace `V ⊆ K²`,
`rank C_p + F + (d·dim V - Σ_c rank(B_c|V)) ≤ #columns`. -/
theorem loadMat_rank_add_le (horth : ∀ r c, α r = β c → omegaL (x r) (y c) = 0) :
    (loadMat α x β y).rank + finrank K (LinearMap.ker (lam β y)) +
      ((colRes β).card * finrank K Vs -
        ∑ c, finrank K (LinearMap.range (condMap α x β y Vs c))) ≤ Fintype.card S := by
  -- pair lower bound (RankLayer)
  have hpair := rank_layer_lower_nat (fun _ : Cond α β => 1) (condMap α x β y Vs)
    (condJet α β Vs)
  simp only [one_mul] at hpair
  -- the restricted reduced map
  set g := (redMap α x β).domRestrict (LinearMap.range (lam β y)) with hgdef
  let Ψ1 : pairSpace α x β y Vs →ₗ[K] LinearMap.range (lam β y) :=
    ((interp β Vs).comp (pairSpace α x β y Vs).subtype).codRestrict _
      (fun H => interp_mem_range α x β y Vs H.2)
  let Ψ2 : pairSpace α x β y Vs →ₗ[K] LinearMap.ker g :=
    Ψ1.codRestrict _ (fun H => by
      rw [LinearMap.mem_ker, hgdef, LinearMap.domRestrict_apply]
      exact interp_mem_ker α x β y Vs horth H.2)
  have hinj : Function.Injective Ψ2 := by
    intro H H' h
    have h' := congrArg
      (fun z : LinearMap.ker g => ((z : LinearMap.range (lam β y)) : colRes β → K × K)) h
    have h'' : interp β Vs H = interp β Vs H' := h'
    exact Subtype.ext (interp_injective β Vs h'')
  have hQ := LinearMap.finrank_le_finrank_of_injective hinj
  -- rank-nullity twice
  have h1 := (lam β y).finrank_range_add_finrank_ker
  have h2 := g.finrank_range_add_finrank_ker
  have hrg : LinearMap.range g = LinearMap.range (loadMat α x β y).mulVecLin := by
    rw [mulVecLin_loadMat, LinearMap.range_comp, hgdef, LinearMap.range_domRestrict]
  have hrank : (loadMat α x β y).rank = finrank K (LinearMap.range g) := by
    rw [hrg]; rfl
  have hS : finrank K (S → K) = Fintype.card S := Module.finrank_fintype_fun_eq_card K
  have h1' : finrank K (LinearMap.range (lam β y)) + finrank K (LinearMap.ker (lam β y)) =
      Fintype.card S := h1.trans hS
  have h2' : finrank K (LinearMap.range g) + finrank K (LinearMap.ker g) =
      finrank K (LinearMap.range (lam β y)) := h2
  have hQ' : finrank K (pairSpace α x β y Vs) ≤ finrank K (LinearMap.ker g) := hQ
  have hpair' : (colRes β).card * finrank K Vs -
      ∑ c, finrank K (LinearMap.range (condMap α x β y Vs c)) ≤
        finrank K (pairSpace α x β y Vs) := hpair
  omega

/-- Certificate form: upper bounds on the restricted ranks suffice. -/
theorem loadMat_rank_add_le_of_bounds (horth : ∀ r c, α r = β c → omegaL (x r) (y c) = 0)
    (cost : Cond α β → ℕ)
    (hcost : ∀ c, finrank K (LinearMap.range (condMap α x β y Vs c)) ≤ cost c) :
    (loadMat α x β y).rank + finrank K (LinearMap.ker (lam β y)) +
      ((colRes β).card * finrank K Vs - ∑ c, cost c) ≤ Fintype.card S := by
  have h := loadMat_rank_add_le α x β y Vs horth
  have hc : ∑ c, finrank K (LinearMap.range (condMap α x β y Vs c)) ≤ ∑ c, cost c :=
    Finset.sum_le_sum fun c _ => hcost c
  omega

end Load

end CatalanCore.Uniform.Content.Hybrid
