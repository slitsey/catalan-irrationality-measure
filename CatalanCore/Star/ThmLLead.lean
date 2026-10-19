module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Star.ThmLLead: leading-term calculus on Laurent series in `t = 1/θ`

`OrdGe e x` : all coefficients of `x` below `e` vanish; `HasLead e c x` : in addition the
coefficient at `e` is `c`.  (θ-degree `d` corresponds to order `-d`.)
-/

@[expose] public section

open Finset HahnSeries

namespace CatalanCore.Star.ThmL

abbrev LS := LaurentSeries ℚ

/-- order `≥ e` (all coefficients below `e` vanish) -/
def OrdGe (e : ℤ) (x : LS) : Prop := ∀ d < e, x.coeff d = 0

/-- `OrdGe e` and coefficient at `e` is `c` (`c = 0` allowed). -/
def HasLead (e : ℤ) (c : ℚ) (x : LS) : Prop := OrdGe e x ∧ x.coeff e = c

namespace OrdGe

lemma mono {e e' : ℤ} {x : LS} (h : OrdGe e x) (he : e' ≤ e) : OrdGe e' x :=
  fun d hd => h d (lt_of_lt_of_le hd he)

lemma zero (e : ℤ) : OrdGe e 0 := fun d _ => by simp

lemma add {e : ℤ} {x y : LS} (hx : OrdGe e x) (hy : OrdGe e y) : OrdGe e (x + y) :=
  fun d hd => by simp [hx d hd, hy d hd]

lemma neg {e : ℤ} {x : LS} (hx : OrdGe e x) : OrdGe e (-x) :=
  fun d hd => by simp [hx d hd]

lemma sub {e : ℤ} {x y : LS} (hx : OrdGe e x) (hy : OrdGe e y) : OrdGe e (x - y) :=
  fun d hd => by simp [hx d hd, hy d hd]

lemma smul_rat {e : ℤ} {x : LS} (q : ℚ) (hx : OrdGe e x) : OrdGe e (q • x) :=
  fun d hd => by simp [hx d hd]

lemma mul {e f : ℤ} {x y : LS} (hx : OrdGe e x) (hy : OrdGe f y) : OrdGe (e + f) (x * y) := by
  intro d hd
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [mem_antidiagonal] at hij
  obtain ⟨-, -, hs⟩ := hij
  by_cases h1 : ij.1 < e
  · simp [hx _ h1]
  · have h2 : ij.2 < f := by omega
    simp [hy _ h2]

lemma sum {ι : Type*} (s : Finset ι) {e : ℤ} {x : ι → LS} (h : ∀ i ∈ s, OrdGe e (x i)) :
    OrdGe e (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero e
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

lemma prod {ι : Type*} (s : Finset ι) {e : ι → ℤ} {x : ι → LS} (h : ∀ i ∈ s, OrdGe (e i) (x i)) :
    OrdGe (∑ i ∈ s, e i) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro d hd
    have : d < 0 := by simpa using hd
    simp [HahnSeries.coeff_one, this.ne]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

end OrdGe

namespace HasLead

lemma ordGe {e : ℤ} {c : ℚ} {x : LS} (h : HasLead e c x) : OrdGe e x := h.1

lemma coeff_eq {e : ℤ} {c : ℚ} {x : LS} (h : HasLead e c x) : x.coeff e = c := h.2

lemma zero_of_ordGe {e : ℤ} {x : LS} (h : OrdGe (e + 1) x) : HasLead e 0 x :=
  ⟨fun d hd => h d (by omega), h e (by omega)⟩

lemma zero (e : ℤ) : HasLead e 0 0 := ⟨OrdGe.zero e, by simp⟩

lemma mono_zero {e e' : ℤ} {x : LS} (h : OrdGe e x) (he : e' < e) : HasLead e' 0 x :=
  zero_of_ordGe (h.mono (by omega))

lemma add {e : ℤ} {a b : ℚ} {x y : LS} (hx : HasLead e a x) (hy : HasLead e b y) :
    HasLead (e) (a + b) (x + y) :=
  ⟨hx.1.add hy.1, by simp [hx.2, hy.2]⟩

lemma neg {e : ℤ} {a : ℚ} {x : LS} (hx : HasLead e a x) : HasLead e (-a) (-x) :=
  ⟨hx.1.neg, by simp [hx.2]⟩

lemma sub {e : ℤ} {a b : ℚ} {x y : LS} (hx : HasLead e a x) (hy : HasLead e b y) :
    HasLead e (a - b) (x - y) :=
  ⟨hx.1.sub hy.1, by simp [hx.2, hy.2]⟩

lemma sum {ι : Type*} (s : Finset ι) {e : ℤ} {c : ι → ℚ} {x : ι → LS}
    (h : ∀ i ∈ s, HasLead e (c i) (x i)) : HasLead e (∑ i ∈ s, c i) (∑ i ∈ s, x i) := by
  refine ⟨OrdGe.sum s fun i hi => (h i hi).1, ?_⟩
  rw [HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun i hi => (h i hi).2

lemma smul_rat {e : ℤ} {a : ℚ} {x : LS} (q : ℚ) (hx : HasLead e a x) :
    HasLead e (q * a) (q • x) :=
  ⟨hx.1.smul_rat q, by simp [hx.2]⟩

/-- `HasLead e c x` iff `x - single e c` has order `≥ e + 1`. -/
lemma iff_sub_single {e : ℤ} {c : ℚ} {x : LS} :
    HasLead e c x ↔ OrdGe (e + 1) (x - HahnSeries.single e c) := by
  constructor
  · rintro ⟨h1, h2⟩ d hd
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_single]
    by_cases hde : d = e
    · simp [hde, h2]
    · have : d < e := by omega
      simp [hde, h1 d this]
  · intro h
    refine ⟨fun d hd => ?_, ?_⟩
    · have := h d (by omega)
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_single, if_neg (by omega)] at this
      simpa using this
    · have := h e (by omega)
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_single, if_pos rfl] at this
      linarith

lemma single (e : ℤ) (c : ℚ) : HasLead e c (HahnSeries.single e c) :=
  iff_sub_single.2 (by simpa using OrdGe.zero (e + 1))

lemma mul {e f : ℤ} {a b : ℚ} {x y : LS} (hx : HasLead e a x) (hy : HasLead f b y) :
    HasLead (e + f) (a * b) (x * y) := by
  have hxe : OrdGe e x := hx.1
  have hye : OrdGe f y := hy.1
  rw [iff_sub_single] at hx hy ⊢
  have key : x * y - HahnSeries.single (e + f) (a * b) =
      (x - HahnSeries.single e a) * y + HahnSeries.single e a * (y - HahnSeries.single f b) := by
    rw [mul_sub, sub_mul, HahnSeries.single_mul_single]; ring
  rw [key]
  have h1 : OrdGe (e + 1 + f) ((x - HahnSeries.single e a) * y) := hx.mul hye
  have h2 : OrdGe (e + (f + 1)) (HahnSeries.single e a * (y - HahnSeries.single f b)) :=
    ((single e a).1).mul hy
  exact (h1.mono (by omega)).add (h2.mono (by omega))

lemma one : HasLead 0 1 (1 : LS) :=
  ⟨fun d hd => by simp [HahnSeries.coeff_one, hd.ne], by simp [HahnSeries.coeff_one]⟩

lemma cast_eq {e e' : ℤ} {c c' : ℚ} {x x' : LS} (h : HasLead e c x) (he : e = e') (hc : c = c')
    (hx : x = x') : HasLead e' c' x' := by subst he hc hx; exact h

lemma prod {ι : Type*} (s : Finset ι) {e : ι → ℤ} {c : ι → ℚ} {x : ι → LS}
    (h : ∀ i ∈ s, HasLead (e i) (c i) (x i)) :
    HasLead (∑ i ∈ s, e i) (∏ i ∈ s, c i) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

lemma pow {e : ℤ} {a : ℚ} {x : LS} (hx : HasLead e a x) (n : ℕ) :
    HasLead ((n : ℤ) * e) (a ^ n) (x ^ n) := by
  induction n with
  | zero => simpa using one
  | succ n ih =>
    refine (ih.mul hx).cast_eq ?_ ?_ ?_ <;> first | (push_cast; ring)

lemma ne_zero {e : ℤ} {c : ℚ} {x : LS} (h : HasLead e c x) (hc : c ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact hc (by simpa using h.2.symm)

lemma unique {e : ℤ} {c c' : ℚ} {x : LS} (h : HasLead e c x) (h' : HasLead e c' x) : c = c' :=
  h.2.symm.trans h'.2

lemma order_unique {e e' : ℤ} {c c' : ℚ} {x : LS} (h : HasLead e c x) (h' : HasLead e' c' x)
    (hc : c ≠ 0) (hc' : c' ≠ 0) : e = e' := by
  rcases lt_trichotomy e e' with hl | rfl | hl
  · exact absurd (h.2.symm.trans (h'.1 e hl)) hc
  · rfl
  · exact absurd (h'.2.symm.trans (h.1 e' hl)) hc'

lemma const_mul {e : ℤ} {a : ℚ} {x : LS} (c : ℚ) (hx : HasLead e a x) :
    HasLead e (c * a) (HahnSeries.C c * x) := by
  have hC : HasLead 0 c (HahnSeries.C c : LS) := by
    have := single (0 : ℤ) c
    rwa [← HahnSeries.C_apply] at this
  exact (hC.mul hx).cast_eq (zero_add e) rfl rfl

lemma inv {e : ℤ} {c : ℚ} {x : LS} (hx : HasLead e c x) (hc : c ≠ 0) :
    HasLead (-e) c⁻¹ x⁻¹ := by
  have hx0 : x ≠ 0 := hx.ne_zero hc
  have hy0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hy : HasLead (x⁻¹).order ((x⁻¹).coeff (x⁻¹).order) x⁻¹ :=
    ⟨fun d hd => HahnSeries.coeff_eq_zero_of_lt_order hd, rfl⟩
  have hl : (x⁻¹).coeff (x⁻¹).order ≠ 0 := HahnSeries.coeff_order_eq_zero.not.2 hy0
  have hm := hx.mul hy
  rw [mul_inv_cancel₀ hx0] at hm
  have ho : e + (x⁻¹).order = 0 :=
    order_unique hm one (mul_ne_zero hc hl) one_ne_zero
  have hco : c * (x⁻¹).coeff (x⁻¹).order = 1 := unique (hm.cast_eq ho rfl rfl) one
  exact hy.cast_eq (by omega) (eq_inv_of_mul_eq_one_right hco) rfl

lemma div {e f : ℤ} {a b : ℚ} {x y : LS} (hx : HasLead e a x) (hy : HasLead f b y) (hb : b ≠ 0) :
    HasLead (e - f) (a / b) (x / y) :=
  ((hx.mul (hy.inv hb)).cast_eq (by ring) (by simp [div_eq_mul_inv]) (by simp [div_eq_mul_inv]))

end HasLead

/-! ### Casts and θ -/

lemma hasLead_ratCast (q : ℚ) : HasLead 0 q (q : LS) := by
  have h := HasLead.single (0 : ℤ) q
  rw [← HahnSeries.C_apply] at h
  have : (HahnSeries.C q : LS) = (q : LS) := by
    simpa using map_ratCast (HahnSeries.C : ℚ →+* LS) q
  rwa [this] at h

lemma hasLead_natCast (n : ℕ) : HasLead 0 (n : ℚ) (n : LS) := by
  simpa using hasLead_ratCast (n : ℚ)

lemma hasLead_intCast (z : ℤ) : HasLead 0 (z : ℚ) (z : LS) := by
  simpa using hasLead_ratCast (z : ℚ)

/-- `θ = 1/t`. -/
noncomputable def theta : LS := HahnSeries.single (-1) 1

lemma hasLead_theta : HasLead (-1) 1 theta := HasLead.single (-1) 1

lemma hasLead_theta_add_of_ordGe {c : LS} (hc : OrdGe 0 c) : HasLead (-1) 1 (theta + c) := by
  have h0 : HasLead (-1) 0 c := HasLead.zero_of_ordGe (by simpa using hc)
  simpa using hasLead_theta.add h0

lemma hasLead_theta_add (a : ℚ) : HasLead (-1) 1 (theta + HahnSeries.C a) :=
  hasLead_theta_add_of_ordGe (by rw [HahnSeries.C_apply]; exact (HasLead.single 0 a).1)

lemma hasLead_theta_add_int (a : ℤ) : HasLead (-1) 1 (theta + (a : LS)) :=
  hasLead_theta_add_of_ordGe (hasLead_intCast a).1

lemma hasLead_theta_add_nat (a : ℕ) : HasLead (-1) 1 (theta + (a : LS)) :=
  hasLead_theta_add_of_ordGe (hasLead_natCast a).1

/-! ### Triangular determinant -/

theorem det_hasLead {n : ℕ} (A : Matrix (Fin n) (Fin n) LS) (r c : Fin n → ℤ)
    (L : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ k i, HasLead (r k + c i) (L k i) (A k i)) (htri : ∀ k i, i < k → L k i = 0) :
    HasLead (∑ k, (r k + c k)) (∏ k, L k k) A.det := by
  have hdetL : L.det = ∏ k, L k k := by
    apply Matrix.det_of_isUpperTriangular
    intro i j hij
    exact htri i j hij
  rw [← hdetL, Matrix.det_apply, Matrix.det_apply]
  have hsum := HasLead.sum (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (e := ∑ k, (r k + c k))
    (c := fun σ => (Equiv.Perm.sign σ : ℤˣ) • ∏ i, L (σ i) i)
    (x := fun σ => (Equiv.Perm.sign σ : ℤˣ) • ∏ i, A (σ i) i) (fun σ _ => by
      have hp : HasLead (∑ i, (r (σ i) + c i)) (∏ i, L (σ i) i) (∏ i, A (σ i) i) :=
        HasLead.prod _ fun i _ => h (σ i) i
      have hp' : HasLead (∑ k, (r k + c k)) (∏ i, L (σ i) i) (∏ i, A (σ i) i) := by
        refine hp.cast_eq ?_ rfl rfl
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        congr 1
        exact Equiv.sum_comp σ r
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · simpa [hs] using hp'
      · simpa [hs] using hp'.neg)
  exact hsum

end CatalanCore.Star.ThmL
