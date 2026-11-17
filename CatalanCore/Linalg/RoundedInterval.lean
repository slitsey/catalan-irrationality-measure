module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace CatalanCore.Linalg

structure QInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def intervalValid (J : QInterval) : Bool := decide (J.lo ≤ J.hi)
def excludesZero (J : QInterval) : Bool := decide (J.hi < 0 ∨ 0 < J.lo)
def intervalContains (J : QInterval) (x : ℝ) : Prop := (J.lo : ℝ) ≤ x ∧ x ≤ J.hi
def singletonI (q : ℚ) : QInterval := ⟨q,q⟩

def roundI (b : ℕ) (J : QInterval) : QInterval :=
  let s : ℚ := (2 : ℚ)^b
  ⟨(⌊J.lo*s⌋ : ℤ)/s, (⌈J.hi*s⌉ : ℤ)/s⟩

theorem roundI_lo_le (b : ℕ) (J : QInterval) : (roundI b J).lo ≤ J.lo := by
  change (⌊J.lo*(2 : ℚ)^b⌋ : ℚ)/(2 : ℚ)^b ≤ J.lo
  exact (div_le_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) b)).2 (Int.floor_le _)

theorem le_roundI_hi (b : ℕ) (J : QInterval) : J.hi ≤ (roundI b J).hi := by
  change J.hi ≤ (⌈J.hi*(2 : ℚ)^b⌉ : ℚ)/(2 : ℚ)^b
  exact (le_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) b)).2 (Int.le_ceil _)

theorem roundI_contains (b : ℕ) (J : QInterval) (x : ℝ)
    (h : intervalContains J x) : intervalContains (roundI b J) x := by
  have hlo : ((roundI b J).lo : ℝ) ≤ (J.lo : ℝ) := by exact_mod_cast roundI_lo_le b J
  have hhi : (J.hi : ℝ) ≤ ((roundI b J).hi : ℝ) := by exact_mod_cast le_roundI_hi b J
  exact ⟨hlo.trans h.1,h.2.trans hhi⟩

def addI (b : ℕ) (J K : QInterval) : QInterval := roundI b ⟨J.lo+K.lo,J.hi+K.hi⟩
def negI (J : QInterval) : QInterval := ⟨-J.hi,-J.lo⟩
def subI (b : ℕ) (J K : QInterval) : QInterval := addI b J (negI K)

theorem addI_contains (b : ℕ) (J K : QInterval) (x y : ℝ)
    (hx : intervalContains J x) (hy : intervalContains K y) :
    intervalContains (addI b J K) (x+y) := by
  apply roundI_contains
  constructor
  · simpa only [Rat.cast_add] using add_le_add hx.1 hy.1
  · simpa only [Rat.cast_add] using add_le_add hx.2 hy.2

theorem negI_contains (J : QInterval) (x : ℝ) (hx : intervalContains J x) :
    intervalContains (negI J) (-x) := by
  constructor
  · simpa only [negI, Rat.cast_neg] using neg_le_neg hx.2
  · simpa only [negI, Rat.cast_neg] using neg_le_neg hx.1

theorem subI_contains (b : ℕ) (J K : QInterval) (x y : ℝ)
    (hx : intervalContains J x) (hy : intervalContains K y) :
    intervalContains (subI b J K) (x-y) := by
  simpa only [subI, sub_eq_add_neg] using addI_contains b J (negI K) x (-y) hx (negI_contains K y hy)

private theorem mul_fixed_bounds (a b c x : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    min (a*c) (b*c) ≤ x*c ∧ x*c ≤ max (a*c) (b*c) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right ha hc),
      (mul_le_mul_of_nonneg_right hb hc).trans (le_max_right _ _)⟩
  · have hc' : c ≤ 0 := le_of_not_ge hc
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hb hc'),
      (mul_le_mul_of_nonpos_right ha hc').trans (le_max_left _ _)⟩

private theorem product_bounds (a b c d x y : ℝ)
    (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have h₁ := mul_fixed_bounds c d a y hc hd
  have h₂ := mul_fixed_bounds c d b y hc hd
  have h₃ := mul_fixed_bounds a b y x ha hb
  simp only [mul_comm c a, mul_comm d a, mul_comm y a] at h₁
  simp only [mul_comm c b, mul_comm d b, mul_comm y b] at h₂
  exact ⟨(min_le_min h₁.1 h₂.1).trans h₃.1, h₃.2.trans (max_le_max h₁.2 h₂.2)⟩

def mulI (b : ℕ) (J K : QInterval) : QInterval :=
  roundI b ⟨min (min (J.lo*K.lo) (J.lo*K.hi)) (min (J.hi*K.lo) (J.hi*K.hi)),
    max (max (J.lo*K.lo) (J.lo*K.hi)) (max (J.hi*K.lo) (J.hi*K.hi))⟩

theorem mulI_contains (b : ℕ) (J K : QInterval) (x y : ℝ)
    (hx : intervalContains J x) (hy : intervalContains K y) :
    intervalContains (mulI b J K) (x*y) := by
  apply roundI_contains
  simpa only [intervalContains, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using
    product_bounds J.lo J.hi K.lo K.hi x y hx.1 hx.2 hy.1 hy.2

def invI (b : ℕ) (J : QInterval) : Option QInterval :=
  if intervalValid J && excludesZero J then some (roundI b ⟨1/J.hi,1/J.lo⟩) else none
def divI (b : ℕ) (J K : QInterval) : Option QInterval := (invI b K).map (mulI b J)

private theorem reciprocal_bounds (lo hi x : ℝ) (hx : lo ≤ x ∧ x ≤ hi)
    (h0 : hi < 0 ∨ 0 < lo) : 1/hi ≤ 1/x ∧ 1/x ≤ 1/lo := by
  rcases h0 with hneg | hpos
  · have hxn : x < 0 := hx.2.trans_lt hneg
    have hleft := one_div_le_one_div_of_le (neg_pos.mpr hneg) (neg_le_neg hx.2)
    have hright := one_div_le_one_div_of_le (neg_pos.mpr hxn) (neg_le_neg hx.1)
    constructor
    · simpa only [one_div, inv_neg, neg_neg] using neg_le_neg hleft
    · simpa only [one_div, inv_neg, neg_neg] using neg_le_neg hright
  · have hxp : 0 < x := hpos.trans_le hx.1
    exact ⟨one_div_le_one_div_of_le hxp hx.2, one_div_le_one_div_of_le hpos hx.1⟩

theorem invI_contains (b : ℕ) (J K : QInterval) (x : ℝ)
    (h : invI b J = some K) (hx : intervalContains J x) : intervalContains K (1/x) := by
  unfold invI at h
  split at h
  next hb =>
    have hb' : J.lo ≤ J.hi ∧ (J.hi < 0 ∨ 0 < J.lo) := by
      simpa [intervalValid, excludesZero] using hb
    have hz : J.hi < 0 ∨ 0 < J.lo := hb'.2
    have hzR : (J.hi : ℝ) < 0 ∨ 0 < (J.lo : ℝ) := by exact_mod_cast hz
    cases Option.some.inj h
    apply roundI_contains
    simpa only [intervalContains, Rat.cast_div, Rat.cast_one] using reciprocal_bounds J.lo J.hi x hx hzR
  next => cases h

theorem divI_contains (b : ℕ) (J K Q : QInterval) (x y : ℝ)
    (h : divI b J K = some Q) (hx : intervalContains J x) (hy : intervalContains K y) :
    intervalContains Q (x/y) := by
  unfold divI at h
  cases hi : invI b K with
  | none => simp only [hi, Option.map_none] at h; cases h
  | some R =>
    simp only [hi, Option.map_some, Option.some.injEq] at h
    subst Q
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mulI_contains b J R x (1/y) hx (invI_contains b K R y hi hy)

end CatalanCore.Linalg
