module

public import CatalanCore.Linalg.CauchyBinet
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-!
# Theorem L kernel: Heine / Cauchy–Binet formulas for Hankel determinants and the
bilinear adjugate kernel

Over a commutative ring:
* `det_hankel_sum` (Heine): `det [∑ₐ tₐ qₐ^(i+i')] = ∑_{|A|=n} (∏ t) · vsq q A`;
* `adj_kernel`: `ν(y)ᵀ adj(H) ν(x)` for a two-family Hankel matrix, as a sum over pairs of
  subsets (rank-one update + Cauchy–Binet + Vandermonde).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.ThmL

variable {R : Type*} [CommRing R]

/-! ### Rank-one determinant identity (general commutative ring) -/

theorem det_add_partial {n : Type*} [Fintype n] [DecidableEq n] (u v : n → R) (s : Finset n) :
    ∀ M : Matrix n n R,
    (Matrix.of fun i j => M i j + if j ∈ s then u i * v j else 0).det
      = M.det + ∑ j ∈ s, v j * (M.updateCol j u).det := by
  induction s using Finset.induction_on with
  | empty => intro M; simp only [Finset.notMem_empty, if_false, add_zero, Finset.sum_empty]; rfl
  | insert k s hk ih =>
    intro M
    have h1 : (Matrix.of fun i j => M i j + if j ∈ insert k s then u i * v j else 0)
        = Matrix.of fun i j => (M.updateCol k (fun i => M i k + v k * u i)) i j
            + if j ∈ s then u i * v j else 0 := by
      ext i j
      by_cases hjk : j = k
      · subst hjk; simp [hk, updateCol_apply, mul_comm]
      · simp [hjk, updateCol_apply]
    rw [h1, ih, Finset.sum_insert hk]
    have h2 : (M.updateCol k (fun i => M i k + v k * u i)).det
        = M.det + v k * (M.updateCol k u).det := by
      have : (fun i => M i k + v k * u i) = (fun i => M i k) + v k • u := by
        ext i; simp
      rw [this, det_updateCol_add, det_updateCol_smul]
      simp
    have h3 : ∀ j ∈ s, ((M.updateCol k (fun i => M i k + v k * u i)).updateCol j u).det
        = (M.updateCol j u).det := by
      intro j hj
      have hjk : k ≠ j := fun h => hk (h ▸ hj)
      have := det_updateCol_add_smul_self (M.updateCol j u) hjk (v k)
      rw [← this]
      congr 1
      ext a b
      by_cases hb : b = j
      · subst hb; simp [updateCol_apply, hjk, hjk.symm]
      · by_cases hb' : b = k
        · subst hb'; simp [updateCol_apply, hb]
        · simp [updateCol_apply, hb, hb']
    rw [h2, Finset.sum_congr rfl (fun j hj => by rw [h3 j hj])]
    ring

/-- Matrix determinant lemma over a commutative ring (generalised, no unit hypothesis). -/
theorem det_add_vecMulVec_adj {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R)
    (u v : n → R) :
    (Matrix.of fun i j => M i j + u i * v j).det = M.det + v ⬝ᵥ (M.adjugate *ᵥ u) := by
  have := det_add_partial u v Finset.univ M
  simp only [Finset.mem_univ, ite_true] at this
  rw [this, ← cramer_eq_adjugate_mulVec]
  simp [dotProduct, cramer_apply]

/-! ### Vandermonde products -/

/-- squared Vandermonde of the points q over a finite index set A (ordered pairs a < a') -/
def vsq {K : ℕ} (q : Fin K → R) (A : Finset (Fin K)) : R :=
  ∏ a ∈ A, ∏ a' ∈ A.filter (fun a' => a < a'), (q a' - q a) ^ 2

/-- unsquared Vandermonde product -/
def vprod {K : ℕ} (z : Fin K → R) (A : Finset (Fin K)) : R :=
  ∏ a ∈ A, ∏ a' ∈ A.filter (fun a' => a < a'), (z a' - z a)

theorem vsq_eq {K : ℕ} (q : Fin K → R) (A : Finset (Fin K)) :
    vsq q A = vprod q A * vprod q A := by
  simp only [vsq, vprod, ← Finset.prod_mul_distrib, sq]

theorem vprod_union {m : ℕ} (z : Fin m → R) (T U : Finset (Fin m)) (h : ∀ t ∈ T, ∀ u ∈ U, t < u) :
    vprod z (T ∪ U) = vprod z T * vprod z U * ∏ t ∈ T, ∏ u ∈ U, (z u - z t) := by
  have hd : Disjoint T U := Finset.disjoint_left.2 fun a ha hb => lt_irrefl _ (h a ha a hb)
  unfold vprod
  rw [Finset.prod_union hd]
  have e1 : ∀ t ∈ T, ∏ a' ∈ (T ∪ U).filter (fun a' => t < a'), (z a' - z t)
      = (∏ a' ∈ T.filter (fun a' => t < a'), (z a' - z t)) * ∏ u ∈ U, (z u - z t) := by
    intro t ht
    have : (T ∪ U).filter (fun a' => t < a') = T.filter (fun a' => t < a') ∪ U := by
      rw [Finset.filter_union]
      congr 1
      exact Finset.filter_true_of_mem fun u hu => h t ht u hu
    rw [this, Finset.prod_union]
    exact Finset.disjoint_left.2 fun a ha hb =>
      lt_irrefl _ (h a (Finset.mem_filter.1 ha).1 a hb)
  have e2 : ∀ u ∈ U, ∏ a' ∈ (T ∪ U).filter (fun a' => u < a'), (z a' - z u)
      = ∏ a' ∈ U.filter (fun a' => u < a'), (z a' - z u) := by
    intro u hu
    have : (T ∪ U).filter (fun a' => u < a') = U.filter (fun a' => u < a') := by
      rw [Finset.filter_union, Finset.filter_false_of_mem (s := T), Finset.empty_union]
      intro t ht hlt
      exact lt_asymm hlt (h t ht u hu)
    rw [this]
  rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2, Finset.prod_mul_distrib]
  ring

theorem vprod_image {K m : ℕ} (z : Fin m → R) (e : Fin K → Fin m) (he : StrictMono e)
    (A : Finset (Fin K)) : vprod z (A.image e) = vprod (z ∘ e) A := by
  unfold vprod
  rw [Finset.prod_image (fun a _ b _ h => he.injective h)]
  refine Finset.prod_congr rfl fun a _ => ?_
  have : (A.image e).filter (fun a' => e a < a') = (A.filter (fun a' => a < a')).image e := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨b, hb, rfl⟩, h⟩; exact ⟨b, ⟨hb, he.lt_iff_lt.1 h⟩, rfl⟩
    · rintro ⟨b, ⟨hb, h⟩, rfl⟩; exact ⟨⟨b, hb, rfl⟩, he h⟩
  rw [this, Finset.prod_image (fun a _ b _ h => he.injective h)]
  rfl

/-! ### Vandermonde minors and Heine's formula -/

/-- Rectangular Vandermonde `p ↦ (z p ^ i)_{i < n}`. -/
def vmat {N : ℕ} (z : Fin N → R) (n : ℕ) : Matrix (Fin N) (Fin n) R :=
  Matrix.of fun p i => z p ^ (i : ℕ)

theorem det_vmat_minor {N n : ℕ} (z : Fin N → R) (P : {P : Finset (Fin N) // P.card = n}) :
    ((vmat z n).submatrix (colsOf P) id).det = vprod z P.1 := by
  have h1 : (vmat z n).submatrix (colsOf P) id = vandermonde (z ∘ colsOf P) := by
    ext i j; simp [vmat, vandermonde]
  rw [h1, det_vandermonde]
  have hP : P.1 = Finset.univ.map (colsOf P).toEmbedding := by
    rw [colsOf, Finset.map_orderEmbOfFin_univ]
  rw [hP]
  unfold vprod
  rw [Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (Finset.univ.map (colsOf P).toEmbedding).filter (fun a' => (colsOf P).toEmbedding i < a')
      = (Finset.Ioi i).map (colsOf P).toEmbedding := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_Ioi]
    constructor
    · rintro ⟨⟨b, rfl⟩, h⟩; exact ⟨b, (colsOf P).lt_iff_lt.1 h, rfl⟩
    · rintro ⟨b, h, rfl⟩; exact ⟨⟨b, rfl⟩, (colsOf P).lt_iff_lt.2 h⟩
  rw [this, Finset.prod_map]
  rfl

/-- Hankel matrix `∑ₐ tₐ qₐ^(i+i')`. -/
def hank {N : ℕ} (q t : Fin N → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i i' : Fin n => ∑ a, t a * q a ^ ((i : ℕ) + i')

theorem hank_eq {N n : ℕ} (q t : Fin N → R) :
    hank q t n = (vmat q n)ᵀ * diagonal t * vmat q n := by
  ext i i'
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply, vmat, of_apply, hank]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Hankel determinant as a sum over n-subsets (Heine / CB) -/
theorem det_hankel_sum {K n : ℕ} (q t : Fin K → R) :
    (Matrix.of fun i i' : Fin n => ∑ a, t a * q a ^ ((i:ℕ) + i')).det
      = ∑ A ∈ Finset.powersetCard n Finset.univ, (∏ a ∈ A, t a) * vsq q A := by
  have h : (Matrix.of fun i i' : Fin n => ∑ a, t a * q a ^ ((i:ℕ) + i')) = hank q t n := rfl
  rw [h, hank_eq, det_transpose_mul_diagonal_mul]
  rw [Finset.sum_subtype (powersetCard n (Finset.univ : Finset (Fin K)))
    (p := fun P => P.card = n) (by simp [mem_powersetCard])
    (fun A => (∏ a ∈ A, t a) * vsq q A)]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [det_vmat_minor, vsq_eq]
  ring

/-! ### Extension by one point and the rank-one step -/

/-- append one value at the end. -/
def snc {N : ℕ} (q : Fin N → R) (x : R) : Fin (N + 1) → R := Fin.snoc q x

@[simp] theorem snc_castSucc {N : ℕ} (q : Fin N → R) (x : R) (a : Fin N) :
    snc q x a.castSucc = q a := by simp [snc]

@[simp] theorem snc_last {N : ℕ} (q : Fin N → R) (x : R) : snc q x (Fin.last N) = x := by
  simp [snc]

theorem hankel_ext {N n : ℕ} (q t : Fin N → R) (x y s : R) :
    (vmat (snc q x) n)ᵀ * diagonal (snc t s) * vmat (snc q y) n
      = Matrix.of fun i i' : Fin n =>
          hank q t n i i' + s * (x ^ (i : ℕ) * y ^ (i' : ℕ)) := by
  ext i i'
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply, vmat, of_apply, hank, Fin.sum_univ_castSucc,
    snc_castSucc, snc_last]
  have : ∀ a : Fin N, q a ^ (i : ℕ) * t a * q a ^ (i' : ℕ) = t a * q a ^ ((i : ℕ) + i') := by
    intro a; ring
  simp_rw [this]
  ring

theorem det_ext_sum {N n : ℕ} (q t : Fin N → R) (x y s : R) :
    (Matrix.of fun i i' : Fin n => hank q t n i i' + s * (x ^ (i : ℕ) * y ^ (i' : ℕ))).det
      = ∑ S ∈ powersetCard n (Finset.univ : Finset (Fin (N + 1))),
          (∏ p ∈ S, snc t s p) * (vprod (snc q x) S * vprod (snc q y) S) := by
  rw [← hankel_ext, det_transpose_mul_diagonal_mul]
  rw [Finset.sum_subtype (powersetCard n (Finset.univ : Finset (Fin (N + 1))))
    (p := fun P => P.card = n) (by simp [mem_powersetCard])
    (fun S => (∏ p ∈ S, snc t s p) * (vprod (snc q x) S * vprod (snc q y) S))]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [det_vmat_minor, det_vmat_minor]
  ring

/-- the set `S' ∪ {last}` -/
def ins {N : ℕ} (S : Finset (Fin N)) : Finset (Fin (N + 1)) :=
  S.image Fin.castSucc ∪ {Fin.last N}

theorem mem_ins {N : ℕ} (S : Finset (Fin N)) (p : Fin (N + 1)) :
    p ∈ ins S ↔ p = Fin.last N ∨ ∃ a ∈ S, a.castSucc = p := by
  simp [ins, or_comm]

theorem ins_injective {N : ℕ} : Function.Injective (ins (N := N)) := by
  intro S S' h
  ext a
  have := congrArg (fun F => a.castSucc ∈ F) h
  simp only [mem_ins, eq_iff_iff] at this
  simpa [(Fin.castSucc_lt_last a).ne] using this

theorem card_ins {N : ℕ} (S : Finset (Fin N)) : (ins S).card = S.card + 1 := by
  unfold ins
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
  · simp
  · rw [Finset.disjoint_singleton_right]
    simp [(Fin.castSucc_lt_last _).ne]

theorem vprod_ins {N : ℕ} (z : Fin N → R) (x : R) (S : Finset (Fin N)) :
    vprod (snc z x) (ins S) = vprod z S * ∏ a ∈ S, (x - z a) := by
  unfold ins
  rw [vprod_union _ _ _ (by
    intro t ht u hu
    simp only [Finset.mem_image] at ht
    obtain ⟨a, _, rfl⟩ := ht
    rw [Finset.mem_singleton] at hu
    subst hu
    exact Fin.castSucc_lt_last a)]
  rw [vprod_image _ _ Fin.strictMono_castSucc]
  have h1 : vprod (snc z x) {Fin.last N} = 1 := by simp [vprod, Finset.filter_singleton]
  rw [h1, mul_one, Finset.prod_image (fun a _ b _ h => Fin.castSucc_injective _ h)]
  have h2 : (snc z x ∘ Fin.castSucc) = z := by ext a; simp
  rw [h2]
  simp

/-- the difference of the two weighted sums isolates the subsets containing the new index -/
theorem adj_fin_aux {N m : ℕ} (q t : Fin N → R) (x y : R) :
    (∑ S ∈ powersetCard (m + 1) (Finset.univ : Finset (Fin (N + 1))),
        (∏ p ∈ S, snc t 1 p) * (vprod (snc q x) S * vprod (snc q y) S))
      - (∑ S ∈ powersetCard (m + 1) (Finset.univ : Finset (Fin (N + 1))),
        (∏ p ∈ S, snc t 0 p) * (vprod (snc q x) S * vprod (snc q y) S))
    = ∑ S ∈ powersetCard m (Finset.univ : Finset (Fin N)),
        (∏ p ∈ S, t p) * vsq q S * ∏ p ∈ S, ((x - q p) * (y - q p)) := by
  rw [← Finset.sum_sub_distrib]
  set d : Finset (Fin (N + 1)) → R := fun S =>
    (∏ p ∈ S, snc t 1 p) * (vprod (snc q x) S * vprod (snc q y) S)
      - (∏ p ∈ S, snc t 0 p) * (vprod (snc q x) S * vprod (snc q y) S) with hd
  have himg : (powersetCard m (Finset.univ : Finset (Fin N))).image ins
      ⊆ powersetCard (m + 1) (Finset.univ : Finset (Fin (N + 1))) := by
    intro S hS
    simp only [Finset.mem_image, mem_powersetCard] at hS
    obtain ⟨S', ⟨_, h⟩, rfl⟩ := hS
    simp [mem_powersetCard, card_ins, h]
  rw [← Finset.sum_subset himg (f := d)]
  · rw [Finset.sum_image (fun a _ b _ h => ins_injective h)]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hd]
    have hp : ∀ s : R, ∏ p ∈ ins S, snc t s p = (∏ p ∈ S, t p) * s := by
      intro s
      unfold ins
      rw [Finset.prod_union, Finset.prod_image (fun a _ b _ h => Fin.castSucc_injective _ h)]
      · simp
      · rw [Finset.disjoint_singleton_right]
        simp [(Fin.castSucc_lt_last _).ne]
    rw [hp, hp, vprod_ins, vprod_ins, vsq_eq, Finset.prod_mul_distrib]
    ring
  · intro S hS hS'
    simp only [hd]
    by_cases hl : Fin.last N ∈ S
    · exfalso
      apply hS'
      simp only [Finset.mem_image, mem_powersetCard]
      refine ⟨Finset.univ.filter (fun a : Fin N => a.castSucc ∈ S), ⟨by simp, ?_⟩, ?_⟩
      · have hc : (ins (Finset.univ.filter (fun a : Fin N => a.castSucc ∈ S))) = S := by
          ext p
          refine Fin.lastCases ?_ (fun a => ?_) p
          · simp [mem_ins, hl]
          · simp [mem_ins, (Fin.castSucc_lt_last a).ne]
        have := card_ins (Finset.univ.filter (fun a : Fin N => a.castSucc ∈ S))
        rw [hc] at this
        have h2 := (mem_powersetCard.1 hS).2
        omega
      · ext p
        refine Fin.lastCases ?_ (fun a => ?_) p
        · simp [mem_ins, hl]
        · simp [mem_ins, (Fin.castSucc_lt_last a).ne]
    · have hp : ∀ s : R, ∏ p ∈ S, snc t s p = ∏ p ∈ S, snc t 0 p := by
        intro s
        refine Finset.prod_congr rfl fun p hp => ?_
        induction p using Fin.lastCases with
        | last => exact absurd hp hl
        | cast a => simp
      rw [hp 1]; ring

/-- Single-family adjugate kernel. -/
theorem adj_fin {N m : ℕ} (q t : Fin N → R) (x y : R) :
    (fun i : Fin (m + 1) => y ^ (i : ℕ)) ⬝ᵥ ((hank q t (m + 1)).adjugate
        *ᵥ (fun i : Fin (m + 1) => x ^ (i : ℕ)))
      = ∑ S ∈ powersetCard m (Finset.univ : Finset (Fin N)),
          (∏ p ∈ S, t p) * vsq q S * ∏ p ∈ S, ((x - q p) * (y - q p)) := by
  have r1 := det_add_vecMulVec_adj (hank q t (m + 1)) (fun i : Fin (m + 1) => x ^ (i : ℕ))
    (fun i : Fin (m + 1) => y ^ (i : ℕ))
  have e1 := det_ext_sum (n := m + 1) q t x y 1
  have e0 := det_ext_sum (n := m + 1) q t x y 0
  have h1 : (Matrix.of fun i i' : Fin (m + 1) =>
      hank q t (m + 1) i i' + 1 * (x ^ (i : ℕ) * y ^ (i' : ℕ)))
      = Matrix.of fun i j => hank q t (m + 1) i j + x ^ (i : ℕ) * y ^ (j : ℕ) := by
    ext i j; simp
  have h0 : (Matrix.of fun i i' : Fin (m + 1) =>
      hank q t (m + 1) i i' + 0 * (x ^ (i : ℕ) * y ^ (i' : ℕ))) = hank q t (m + 1) := by
    ext i j; simp
  rw [h1, r1] at e1
  rw [h0] at e0
  rw [← adj_fin_aux, ← e1, ← e0]
  ring

/-! ### Two families: splitting subsets of `Fin (K + r)` into pairs -/

section Blk

variable {K r : ℕ}

/-- the subset of `Fin (K + r)` given by `A` in the left block and `B` in the right block -/
def blk (A : Finset (Fin K)) (B : Finset (Fin r)) : Finset (Fin (K + r)) :=
  A.image (Fin.castAdd r) ∪ B.image (Fin.natAdd K)

theorem castAdd_lt_natAdd' (a : Fin K) (b : Fin r) : Fin.castAdd r a < Fin.natAdd K b := by
  simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd]
  omega

@[simp] theorem natAdd_ne_castAdd' (a : Fin K) (b : Fin r) : Fin.natAdd K b ≠ Fin.castAdd r a :=
  (castAdd_lt_natAdd' a b).ne'

@[simp] theorem castAdd_ne_natAdd' (a : Fin K) (b : Fin r) : Fin.castAdd r a ≠ Fin.natAdd K b :=
  (castAdd_lt_natAdd' a b).ne

theorem disjoint_blk (A : Finset (Fin K)) (B : Finset (Fin r)) :
    Disjoint (A.image (Fin.castAdd r)) (B.image (Fin.natAdd K)) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  simp only [Finset.mem_image] at hp hq
  obtain ⟨a, _, rfl⟩ := hp
  obtain ⟨b, _, hb⟩ := hq
  exact (castAdd_lt_natAdd' a b).ne hb.symm

theorem card_blk (A : Finset (Fin K)) (B : Finset (Fin r)) :
    (blk A B).card = A.card + B.card := by
  unfold blk
  rw [Finset.card_union_of_disjoint (disjoint_blk A B),
    Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
    Finset.card_image_of_injective _ (Fin.natAdd_injective _ _)]

theorem blk_left_inv (S : Finset (Fin (K + r))) :
    blk (Finset.univ.filter (fun a : Fin K => Fin.castAdd r a ∈ S))
      (Finset.univ.filter (fun b : Fin r => Fin.natAdd K b ∈ S)) = S := by
  ext p
  induction p using Fin.addCases with
  | left a => simp [blk]
  | right b => simp [blk]

theorem blk_right_inv (A : Finset (Fin K)) (B : Finset (Fin r)) :
    (Finset.univ.filter (fun a : Fin K => Fin.castAdd r a ∈ blk A B) = A) ∧
    (Finset.univ.filter (fun b : Fin r => Fin.natAdd K b ∈ blk A B) = B) := by
  constructor
  · ext a; simp [blk]
  · ext b; simp [blk]

theorem sum_blk {M : Type*} [AddCommMonoid M] (m : ℕ) (h : Finset (Fin (K + r)) → M) :
    ∑ S ∈ powersetCard m (Finset.univ : Finset (Fin (K + r))), h S
      = ∑ A ∈ (Finset.univ : Finset (Fin K)).powerset,
          ∑ B ∈ (Finset.univ : Finset (Fin r)).powerset,
            if A.card + B.card = m then h (blk A B) else 0 := by
  rw [← Finset.sum_product' (f := fun A B => if A.card + B.card = m then h (blk A B) else 0),
    ← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun S _ => (Finset.univ.filter (fun a : Fin K => Fin.castAdd r a ∈ S),
      Finset.univ.filter (fun b : Fin r => Fin.natAdd K b ∈ S)))
    (fun x _ => blk x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.subset_univ,
      and_self, true_and]
    rw [← card_blk, blk_left_inv]
    exact (mem_powersetCard.1 hS).2
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.subset_univ,
      and_self, true_and] at hx
    rw [mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [card_blk]; exact hx⟩
  · intro S _
    exact blk_left_inv S
  · intro x _
    ext1
    · exact (blk_right_inv x.1 x.2).1
    · exact (blk_right_inv x.1 x.2).2
  · intro S _
    simp [blk_left_inv]

theorem vprod_blk (z : Fin (K + r) → R) (A : Finset (Fin K)) (B : Finset (Fin r)) :
    vprod z (blk A B) = vprod (z ∘ Fin.castAdd r) A * vprod (z ∘ Fin.natAdd K) B
      * ∏ a ∈ A, ∏ b ∈ B, (z (Fin.natAdd K b) - z (Fin.castAdd r a)) := by
  unfold blk
  rw [vprod_union _ _ _ (by
    intro t ht u hu
    simp only [Finset.mem_image] at ht hu
    obtain ⟨a, _, rfl⟩ := ht
    obtain ⟨b, _, rfl⟩ := hu
    exact castAdd_lt_natAdd' a b)]
  have hc : StrictMono (Fin.castAdd r : Fin K → Fin (K + r)) := Fin.strictMono_castAdd r
  have hn : StrictMono (Fin.natAdd K : Fin r → Fin (K + r)) := Fin.strictMono_natAdd K
  rw [vprod_image _ _ hc, vprod_image _ _ hn,
    Finset.prod_image (fun a _ b _ h => Fin.castAdd_injective _ _ h)]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_image (fun a _ b _ h => Fin.natAdd_injective _ _ h)]

end Blk

/-- bilinear adjugate kernel with a node family (Fin K) and a column family (Fin r) -/
theorem adj_kernel {K r n : ℕ} (hn : 1 ≤ n) (qa ta : Fin K → R) (qb tb : Fin r → R) (x y : R) :
    (fun i : Fin n => y ^ (i:ℕ)) ⬝ᵥ ((Matrix.adjugate (Matrix.of fun i i' : Fin n =>
        ∑ a, ta a * qa a ^ ((i:ℕ) + i') + ∑ b, tb b * qb b ^ ((i:ℕ) + i'))) *ᵥ
          (fun i : Fin n => x ^ (i:ℕ)))
      = ∑ A ∈ (Finset.univ : Finset (Fin K)).powerset,
          ∑ B ∈ (Finset.univ : Finset (Fin r)).powerset,
          if A.card + B.card = n - 1 then
            (∏ a ∈ A, ta a) * (∏ b ∈ B, tb b) * vsq qa A * vsq qb B
              * (∏ a ∈ A, ∏ b ∈ B, (qa a - qb b) ^ 2)
              * (∏ a ∈ A, ((x - qa a) * (y - qa a))) * (∏ b ∈ B, ((x - qb b) * (y - qb b)))
          else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hh : (Matrix.of fun i i' : Fin (m + 1) =>
      ∑ a, ta a * qa a ^ ((i:ℕ) + i') + ∑ b, tb b * qb b ^ ((i:ℕ) + i'))
      = hank (Fin.append qa qb) (Fin.append ta tb) (m + 1) := by
    ext i i'
    simp only [hank, of_apply]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hh, adj_fin, sum_blk, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  split_ifs
  · have hq1 : (Fin.append qa qb ∘ Fin.castAdd r) = qa := by ext a; simp
    have hq2 : (Fin.append qa qb ∘ Fin.natAdd K) = qb := by ext a; simp
    have hC : (∏ a ∈ A, ∏ b ∈ B, (qb b - qa a)) * (∏ a ∈ A, ∏ b ∈ B, (qb b - qa a))
        = ∏ a ∈ A, ∏ b ∈ B, (qa a - qb b) ^ 2 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      ring
    have hv : vsq (Fin.append qa qb) (blk A B) = vsq qa A * vsq qb B
        * ∏ a ∈ A, ∏ b ∈ B, (qa a - qb b) ^ 2 := by
      rw [vsq_eq, vprod_blk, hq1, hq2, ← hC, vsq_eq, vsq_eq]
      simp only [Fin.append_left, Fin.append_right]
      ring
    have hp : ∏ p ∈ blk A B, Fin.append ta tb p = (∏ a ∈ A, ta a) * ∏ b ∈ B, tb b := by
      unfold blk
      rw [Finset.prod_union (disjoint_blk A B),
        Finset.prod_image (fun a _ b _ h => Fin.castAdd_injective _ _ h),
        Finset.prod_image (fun a _ b _ h => Fin.natAdd_injective _ _ h)]
      simp only [Fin.append_left, Fin.append_right]
    have hx : ∏ p ∈ blk A B, ((x - Fin.append qa qb p) * (y - Fin.append qa qb p))
        = (∏ a ∈ A, ((x - qa a) * (y - qa a))) * ∏ b ∈ B, ((x - qb b) * (y - qb b)) := by
      unfold blk
      rw [Finset.prod_union (disjoint_blk A B),
        Finset.prod_image (fun a _ b _ h => Fin.castAdd_injective _ _ h),
        Finset.prod_image (fun a _ b _ h => Fin.natAdd_injective _ _ h)]
      simp only [Fin.append_left, Fin.append_right]
    rw [hv, hp, hx]
    ring
  · rfl

end CatalanCore.Star.ThmL
