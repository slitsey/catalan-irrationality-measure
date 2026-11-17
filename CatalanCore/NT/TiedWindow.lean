module

public import CatalanCore.NT.Interval
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

@[expose] public section

/-!
# Prime windows tied to several families (ledger LR01, LR02, LR05; Criterion W2U)

A *tied family* `i` is a set `S i` of unit classes modulo a common modulus `M`, a slope `c i > 0`, a
tolerance `e i` and a finite exception set `exc i`.  A prime `ℓ` is *tied to `i` at height `L`* when
`ℓ` is prime, `ℓ mod M ∈ S i`, `ℓ ∉ exc i` and `c i a L < ℓ ≤ c i b L`.  The window mass is the
inclusion-exclusion sum
`𝓜(a, b) = ∑_{∅ ≠ T} (-1)^{|T|+1} (min_T e) · (|⋂_T S i| / φ(M)) · |⋂_T (c i a, c i b]|`,
which is the Lebesgue integral of `max_i e_i 1[(c_i a, c_i b]]` averaged over the unit classes.

* `tied_weight_lower` (PNT in progressions, `theta_interval_asymp`, plus the max-min identity
  `sup_eq_alt`): if `𝓜(a, b) > 1` then `∑_ℓ e(ℓ) log ℓ ≥ (1 + ε₀) L` for large `L`, where
  `e(ℓ) = max {e i : ℓ tied to i}`;
* `exists_tied_prime` (LR02): if every bad tied pair `(i, ℓ)` has `ℓ ^ e i ∣ Wt`, a positive integer
  with `log Wt < (1 + ε₀) L`, then some tied pair is not bad.

The prime classes enter only through `pnt_class` (LR01, `CatalanCore/NT/PNTClass.lean`, used as is).
Overlap between windows is counted once (Criterion W2U), so the windows need not be disjoint.
-/

open Filter Topology Finset

namespace CatalanCore.NT

section Comb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nonempty subsets of the index type. -/
def NESub (ι : Type*) [Fintype ι] [DecidableEq ι] : Finset (Finset ι) :=
  (Finset.univ : Finset ι).powerset.filter Finset.Nonempty

theorem mem_NESub {T : Finset ι} : T ∈ NESub ι ↔ T.Nonempty := by
  simp [NESub]

/-- Inclusion-exclusion indicator: `1[J ≠ ∅] = ∑_{∅ ≠ T ⊆ J} (-1)^{|T|+1}`. -/
theorem alt_sum_subsets (J : Finset ι) :
    ∑ T ∈ NESub ι, (-1 : ℤ) ^ (T.card + 1) * (if T ⊆ J then 1 else 0) =
      if J.Nonempty then 1 else 0 := by
  have h1 : ∑ T ∈ NESub ι, (-1 : ℤ) ^ (T.card + 1) * (if T ⊆ J then 1 else 0) =
      ∑ T ∈ J.powerset.filter Finset.Nonempty, (-1 : ℤ) ^ (T.card + 1) := by
    have hf : (NESub ι).filter (fun T => T ⊆ J) = J.powerset.filter Finset.Nonempty := by
      ext T
      simp only [NESub, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      exact and_comm
    rw [← hf, Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs <;> simp
  rw [h1]
  have h2 : ∑ T ∈ J.powerset, (-1 : ℤ) ^ (T.card + 1) = - (if J = ∅ then 1 else 0) := by
    have := Finset.sum_powerset_neg_one_pow_card (x := J)
    simp only [pow_succ, ← Finset.sum_mul, this]; ring
  have h3 : ∑ T ∈ J.powerset, (-1 : ℤ) ^ (T.card + 1) =
      ∑ T ∈ J.powerset.filter Finset.Nonempty, (-1 : ℤ) ^ (T.card + 1) +
        ∑ T ∈ J.powerset.filter (fun T => ¬ T.Nonempty), (-1 : ℤ) ^ (T.card + 1) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h4 : J.powerset.filter (fun T => ¬ T.Nonempty) = {∅} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
      Finset.not_nonempty_iff_eq_empty]
    constructor
    · exact fun h => h.2
    · intro h; subst h; exact ⟨Finset.empty_subset _, rfl⟩
  rw [h4] at h3
  simp only [Finset.sum_singleton, Finset.card_empty, zero_add, pow_one] at h3
  have h5 : ∑ T ∈ J.powerset.filter Finset.Nonempty, (-1 : ℤ) ^ (T.card + 1) =
      1 - (if J = ∅ then 1 else 0) := by linarith
  rw [h5]
  by_cases hJ : J.Nonempty
  · have : J ≠ ∅ := hJ.ne_empty
    simp [this, hJ]
  · have : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    simp [this]

/-- The number of "layers" `k ∈ [1, K]` with `k ≤ e i` for all `i ∈ T`; the minimum of `e` over a
nonempty `T`. -/
def layerCnt (e : ι → ℕ) (T : Finset ι) : ℕ :=
  ((Finset.Icc 1 (Finset.univ.sup e)).filter fun k => ∀ i ∈ T, k ≤ e i).card

theorem sup_eq_card_layers (e : ι → ℕ) (I : Finset ι) :
    I.sup e = ((Finset.Icc 1 (Finset.univ.sup e)).filter fun k => ∃ i ∈ I, k ≤ e i).card := by
  have hIK : I.sup e ≤ Finset.univ.sup e := Finset.sup_mono (Finset.subset_univ _)
  have : (Finset.Icc 1 (Finset.univ.sup e)).filter (fun k => ∃ i ∈ I, k ≤ e i) =
      Finset.Icc 1 (I.sup e) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, i, hi, hk⟩
      exact ⟨h1, hk.trans (Finset.le_sup (f := e) hi)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, h2.trans hIK⟩, ?_⟩
      exact (Finset.le_sup_iff (by simp only [bot_eq_zero]; omega)).mp h2
  rw [this]; simp

/-- The weight `sup_{i ∈ I} e i` as an alternating sum over nonempty subsets (max-min
inclusion-exclusion). -/
theorem sup_eq_alt (e : ι → ℕ) (I : Finset ι) :
    ((I.sup e : ℕ) : ℤ) = ∑ T ∈ NESub ι, (-1 : ℤ) ^ (T.card + 1) *
      (if T ⊆ I then (layerCnt e T : ℤ) else 0) := by
  have key : ∀ k : ℕ, (if ∃ i ∈ I, k ≤ e i then (1 : ℤ) else 0) =
      ∑ T ∈ NESub ι, (-1 : ℤ) ^ (T.card + 1) *
        (if T ⊆ I ∧ ∀ i ∈ T, k ≤ e i then 1 else 0) := by
    intro k
    have h := alt_sum_subsets (I.filter fun i => k ≤ e i)
    have e1 : (∃ i ∈ I, k ≤ e i) ↔ (I.filter fun i => k ≤ e i).Nonempty := by
      simp [Finset.Nonempty]
    have e2 : ∀ T : Finset ι, (T ⊆ I.filter fun i => k ≤ e i) ↔ (T ⊆ I ∧ ∀ i ∈ T, k ≤ e i) := by
      intro T
      constructor
      · intro hT
        exact ⟨fun i hi => (Finset.mem_filter.mp (hT hi)).1,
          fun i hi => (Finset.mem_filter.mp (hT hi)).2⟩
      · rintro ⟨h1, h2⟩ i hi
        exact Finset.mem_filter.mpr ⟨h1 hi, h2 i hi⟩
    simp only [e2] at h
    rw [h]
    simp only [e1]
  rw [sup_eq_card_layers e I, Finset.card_filter]
  push_cast
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  by_cases hT : T ⊆ I
  · simp only [hT, true_and, if_true, layerCnt]
    rw [Finset.card_filter]
    push_cast
    rfl
  · simp [hT]

end Comb

section Window

variable {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The classes (mod `M`) common to all families of `T`. -/
def overlap (S : ι → Finset (ZMod M)) (T : Finset ι) : Finset (ZMod M) :=
  Finset.univ.filter fun r => ∀ i ∈ T, r ∈ S i

/-- Length of `⋂_{i ∈ T} (c_i a, c_i b]`. -/
noncomputable def winLen (c : ι → ℝ) (a b : ℝ) (T : Finset ι) : ℝ :=
  if h : T.Nonempty then max 0 (b * T.inf' h c - a * T.sup' h c) else 0

/-- The smallest tolerance over `T`. -/
def minTol (e : ι → ℕ) (T : Finset ι) : ℕ := if h : T.Nonempty then T.inf' h e else 0

/-- The inclusion-exclusion mass of a union of windows. -/
noncomputable def unionMass (S : ι → Finset (ZMod M)) (c : ι → ℝ) (e : ι → ℕ) (a b : ℝ) : ℝ :=
  ∑ T ∈ NESub ι, (-1 : ℝ) ^ (T.card + 1) * (minTol e T : ℝ) *
    (((overlap S T).card : ℝ) / (M.totient : ℝ)) * winLen c a b T

/-- `ℓ` is tied to family `i` at height `L`. -/
def Tied (S : ι → Finset (ZMod M)) (c : ι → ℝ) (exc : ι → Finset ℕ) (a b L : ℝ) (i : ι)
    (ℓ : ℕ) : Prop :=
  ℓ.Prime ∧ (ℓ : ZMod M) ∈ S i ∧ ℓ ∉ exc i ∧ c i * a * L < ℓ ∧ (ℓ : ℝ) ≤ c i * b * L

open Classical in
noncomputable def tiedWt (S : ι → Finset (ZMod M)) (c : ι → ℝ) (e : ι → ℕ) (exc : ι → Finset ℕ)
    (a b L : ℝ) (ℓ : ℕ) : ℕ :=
  (Finset.univ.filter fun i => Tied S c exc a b L i ℓ).sup e

open Classical in
noncomputable def tiedSum (S : ι → Finset (ZMod M)) (c : ι → ℝ) (e : ι → ℕ) (exc : ι → Finset ℕ)
    (a b L : ℝ) (N : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range N, (tiedWt S c e exc a b L ℓ : ℝ) * Real.log ℓ

theorem layerCnt_eq {e : ι → ℕ} {T : Finset ι} (hT : T.Nonempty) :
    layerCnt e T = minTol e T := by
  unfold layerCnt minTol
  rw [dif_pos hT]
  have : (Finset.Icc 1 (Finset.univ.sup e)).filter (fun k => ∀ i ∈ T, k ≤ e i) =
      Finset.Icc 1 (T.inf' hT e) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h⟩
      exact ⟨h1, (Finset.le_inf'_iff hT e).mpr h⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, fun i hi => h2.trans (Finset.inf'_le e hi)⟩
      obtain ⟨i, hi⟩ := hT
      exact h2.trans ((Finset.inf'_le e hi).trans (Finset.le_sup (f := e) (Finset.mem_univ i)))
  rw [this]; simp

open Classical in
/-- Window sum over the primes tied simultaneously to every family of `T`. -/
noncomputable def tiedSg (S : ι → Finset (ZMod M)) (c : ι → ℝ) (exc : ι → Finset ℕ) (a b L : ℝ)
    (N : ℕ) (T : Finset ι) : ℝ :=
  ∑ ℓ ∈ Finset.range N, if ∀ i ∈ T, Tied S c exc a b L i ℓ then Real.log ℓ else 0

/-- Inclusion-exclusion decomposition of the tied weight sum. -/
theorem tiedSum_eq (S : ι → Finset (ZMod M)) (c : ι → ℝ) (e : ι → ℕ) (exc : ι → Finset ℕ)
    (a b L : ℝ) (N : ℕ) :
    tiedSum S c e exc a b L N = ∑ T ∈ NESub ι, (-1 : ℝ) ^ (T.card + 1) * (minTol e T : ℝ) *
      tiedSg S c exc a b L N T := by
  classical
  unfold tiedSum tiedSg
  have hw : ∀ ℓ : ℕ, (tiedWt S c e exc a b L ℓ : ℝ) = ∑ T ∈ NESub ι, (-1 : ℝ) ^ (T.card + 1) *
      (if ∀ i ∈ T, Tied S c exc a b L i ℓ then (minTol e T : ℝ) else 0) := by
    intro ℓ
    have h := sup_eq_alt e (Finset.univ.filter fun i => Tied S c exc a b L i ℓ)
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one] at h'
    unfold tiedWt
    rw [h']
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTn : T.Nonempty := mem_NESub.mp hT
    have hsub : (T ⊆ Finset.univ.filter fun i => Tied S c exc a b L i ℓ) ↔
        ∀ i ∈ T, Tied S c exc a b L i ℓ := by
      simp [Finset.subset_iff]
    by_cases hc : ∀ i ∈ T, Tied S c exc a b L i ℓ
    · rw [if_pos (hsub.mpr hc), if_pos hc, layerCnt_eq hTn]; simp
    · rw [if_neg (fun h => hc (hsub.mp h)), if_neg hc]; simp
  simp only [hw, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs <;> ring


theorem tied_iff_closed {S : ι → Finset (ZMod M)} {c : ι → ℝ} {exc : ι → Finset ℕ}
    {a b L : ℝ} {T : Finset ι} (hT : T.Nonempty) (ha : 0 < a) (hb : 0 < b) (hL : 0 < L)
    (ℓ : ℕ) :
    (∀ i ∈ T, Tied S c exc a b L i ℓ) ↔
      ℓ.Prime ∧ (ℓ : ZMod M) ∈ overlap S T ∧ ℓ ∉ T.biUnion exc ∧
        (a * T.sup' hT c) * L < ℓ ∧ (ℓ : ℝ) ≤ (b * T.inf' hT c) * L := by
  obtain ⟨i1, hi1, h1eq⟩ := Finset.exists_mem_eq_sup' hT c
  obtain ⟨i2, hi2, h2eq⟩ := Finset.exists_mem_eq_inf' hT c
  constructor
  · intro h
    refine ⟨(h _ hi1).1, ?_, ?_, ?_, ?_⟩
    · simp only [overlap, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun i hi => (h i hi).2.1
    · simp only [Finset.mem_biUnion, not_exists, not_and]
      exact fun i hi => (h i hi).2.2.1
    · have := (h i1 hi1).2.2.2.1
      rw [h1eq]; linarith
    · have := (h i2 hi2).2.2.2.2
      rw [h2eq]; linarith
  · rintro ⟨hp, hcl, hexc, hlo, hhi⟩ i hi
    simp only [overlap, Finset.mem_filter, Finset.mem_univ, true_and] at hcl
    simp only [Finset.mem_biUnion, not_exists, not_and] at hexc
    refine ⟨hp, hcl i hi, hexc i hi, ?_, ?_⟩
    · have h1 : c i ≤ T.sup' hT c := Finset.le_sup' c hi
      have h2 : c i * (a * L) ≤ T.sup' hT c * (a * L) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      nlinarith
    · have h1 : T.inf' hT c ≤ c i := Finset.inf'_le c hi
      have h2 : T.inf' hT c * (b * L) ≤ c i * (b * L) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      nlinarith

open Classical in
theorem tiedSg_eq_sum {S : ι → Finset (ZMod M)} {c : ι → ℝ} {exc : ι → Finset ℕ}
    {a b L B : ℝ} {T : Finset ι} (hT : T.Nonempty) (hc : ∀ i, 0 < c i) (ha : 0 < a) (hb : 0 < b)
    (hL : 0 < L) (hB : b * T.inf' hT c ≤ B) :
    tiedSg S c exc a b L (⌊B * L⌋₊ + 1) T =
      ∑ ℓ ∈ (Finset.Ioc ⌊(a * T.sup' hT c) * L⌋₊ ⌊(b * T.inf' hT c) * L⌋₊).filter
        (fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ZMod M) ∈ overlap S T ∧ ℓ ∉ T.biUnion exc),
        Real.log ℓ := by
  unfold tiedSg
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ℓ
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, tied_iff_closed hT ha hb hL]
  have hsup : 0 < T.sup' hT c := by
    obtain ⟨i, hi⟩ := hT
    exact (hc i).trans_le (Finset.le_sup' c hi)
  have hinf : 0 < T.inf' hT c := by
    obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_inf' hT c
    rw [h]; exact hc _
  have hα : 0 ≤ (a * T.sup' hT c) * L := by positivity
  have hβ : 0 ≤ (b * T.inf' hT c) * L := by positivity
  have hBL : (b * T.inf' hT c) * L ≤ B * L := mul_le_mul_of_nonneg_right hB hL.le
  constructor
  · rintro ⟨_, hp, hcl, hex, h1, h2⟩
    exact ⟨⟨(Nat.floor_lt hα).mpr h1, (Nat.le_floor_iff hβ).mpr h2⟩, hp, hcl, hex⟩
  · rintro ⟨⟨h1, h2⟩, hp, hcl, hex⟩
    have h1' := (Nat.floor_lt hα).mp h1
    have h2' := (Nat.le_floor_iff hβ).mp h2
    have h3 : ℓ ≤ ⌊B * L⌋₊ := Nat.le_floor (h2'.trans hBL)
    exact ⟨by omega, hp, hcl, hex, h1', h2'⟩


open Classical in
/-- Sum of `log ℓ` over the primes in a window and class set, minus a finite exception set. -/
theorem window_sum_bounds {C : Finset (ZMod M)} {E : Finset ℕ} {lo hi : ℕ} (hlh : lo ≤ hi) :
    ∑ ρ ∈ C, (thetaClassN M ρ hi - thetaClassN M ρ lo) -
        ∑ ℓ ∈ E, Real.log ℓ ≤
      ∑ ℓ ∈ (Finset.Ioc lo hi).filter
        (fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ZMod M) ∈ C ∧ ℓ ∉ E), Real.log ℓ ∧
    ∑ ℓ ∈ (Finset.Ioc lo hi).filter
        (fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ZMod M) ∈ C ∧ ℓ ∉ E), Real.log ℓ ≤
      ∑ ρ ∈ C, (thetaClassN M ρ hi - thetaClassN M ρ lo) := by
  set F' := (Finset.Ioc lo hi).filter (fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ZMod M) ∈ C) with hF'
  set F := (Finset.Ioc lo hi).filter
    (fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ZMod M) ∈ C ∧ ℓ ∉ E) with hF
  have hθ : ∑ ρ ∈ C, (thetaClassN M ρ hi - thetaClassN M ρ lo) = ∑ ℓ ∈ F', Real.log ℓ := by
    rw [hF', ← Finset.sum_fiberwise_of_maps_to (s := (Finset.Ioc lo hi).filter
      (fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ZMod M) ∈ C)) (t := C) (g := fun m : ℕ => (m : ZMod M))
      (fun m hm => (Finset.mem_filter.1 hm).2.2)]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [thetaClassN_sub M ρ hlh]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, h3 ▸ hρ⟩, h3⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h4⟩
  have hFF : F ⊆ F' := by
    intro ℓ hℓ
    simp only [hF, hF', Finset.mem_filter] at hℓ ⊢
    exact ⟨hℓ.1, hℓ.2.1, hℓ.2.2.1⟩
  have hnn : ∀ ℓ : ℕ, 0 ≤ Real.log ℓ := fun ℓ => Real.log_natCast_nonneg ℓ
  have hsd := Finset.sum_sdiff hFF (f := fun ℓ : ℕ => Real.log ℓ)
  have hsub : F' \ F ⊆ E := by
    intro ℓ hℓ
    rw [Finset.mem_sdiff] at hℓ
    by_contra hE
    apply hℓ.2
    simp only [hF, hF', Finset.mem_filter] at hℓ ⊢
    exact ⟨hℓ.1.1, hℓ.1.2.1, hℓ.1.2.2, hE⟩
  have hle : ∑ ℓ ∈ F' \ F, Real.log ℓ ≤ ∑ ℓ ∈ E, Real.log ℓ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun ℓ _ _ => hnn ℓ
  rw [hθ]
  constructor <;> linarith [Finset.sum_nonneg (fun ℓ (_ : ℓ ∈ F' \ F) => hnn ℓ)]

open Classical in
/-- The window sum over the primes tied to every family of `T`, divided by `L`, converges to
`|overlap| / φ(M)` times the window length. -/
theorem tendsto_tiedSg {S : ι → Finset (ZMod M)} (hS : ∀ i, ∀ s ∈ S i, IsUnit s) {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (exc : ι → Finset ℕ) {a b B : ℝ} (ha : 0 < a) (hb : 0 < b)
    {T : Finset ι} (hT : T.Nonempty) (hB : b * T.inf' hT c ≤ B) :
    Tendsto (fun L : ℝ => tiedSg S c exc a b L (⌊B * L⌋₊ + 1) T / L) atTop
      (𝓝 (((overlap S T).card : ℝ) / (M.totient : ℝ) * winLen c a b T)) := by
  have hsup : 0 < T.sup' hT c := by
    obtain ⟨i, hi⟩ := hT
    exact (hc i).trans_le (Finset.le_sup' c hi)
  have hinf : 0 < T.inf' hT c := by
    obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_inf' hT c
    rw [h]; exact hc _
  set α : ℝ := a * T.sup' hT c with hα
  set β : ℝ := b * T.inf' hT c with hβ
  have hα0 : 0 < α := by positivity
  have hβ0 : 0 < β := by positivity
  have hwin : winLen c a b T = max 0 (β - α) := by
    unfold winLen; rw [dif_pos hT]
  have hEq : ∀ L : ℝ, 0 < L → tiedSg S c exc a b L (⌊B * L⌋₊ + 1) T =
      ∑ ℓ ∈ (Finset.Ioc ⌊α * L⌋₊ ⌊β * L⌋₊).filter
        (fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ZMod M) ∈ overlap S T ∧ ℓ ∉ T.biUnion exc),
        Real.log ℓ := fun L hL => tiedSg_eq_sum hT hc ha hb hL hB
  by_cases hab : α ≤ β
  · rw [hwin, max_eq_right (by linarith)]
    set C := overlap S T with hC
    have hCu : ∀ ρ ∈ C, IsUnit ρ := by
      intro ρ hρ
      obtain ⟨i, hi⟩ := hT
      simp only [hC, overlap, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
      exact hS i ρ (hρ i hi)
    set E := T.biUnion exc with hE
    have hmain : Tendsto (fun L : ℝ => (∑ ρ ∈ C, (thetaClass M ρ (β * L) - thetaClass M ρ (α * L))) / L)
        atTop (𝓝 (C.card * ((β - α) / (M.totient : ℝ)))) := by
      have := tendsto_finset_sum C (fun ρ hρ => theta_interval_asymp (m := M) (hCu ρ hρ) hα0 hab)
      simp only [Finset.sum_const, nsmul_eq_mul] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      rw [Finset.sum_div]
    have hlow : Tendsto (fun L : ℝ => (∑ ρ ∈ C, (thetaClass M ρ (β * L) - thetaClass M ρ (α * L))
        - ∑ ℓ ∈ E, Real.log ℓ) / L) atTop (𝓝 (C.card * ((β - α) / (M.totient : ℝ)))) := by
      have h0 : Tendsto (fun L : ℝ => (∑ ℓ ∈ E, Real.log ℓ) / L) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have := hmain.sub h0
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards with L
      rw [sub_div]
    have hres : ((C.card : ℝ) / (M.totient : ℝ)) * (β - α) = C.card * ((β - α) / (M.totient : ℝ)) := by
      ring
    rw [hres]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hmain ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      rw [hEq L hL]
      have hlh : ⌊α * L⌋₊ ≤ ⌊β * L⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right hab hL.le)
      exact div_le_div_of_nonneg_right (window_sum_bounds hlh).1 hL.le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      rw [hEq L hL]
      have hlh : ⌊α * L⌋₊ ≤ ⌊β * L⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right hab hL.le)
      exact div_le_div_of_nonneg_right (window_sum_bounds hlh).2 hL.le
  · push_neg at hab
    rw [hwin, max_eq_left (by linarith), mul_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [hEq L hL]
    have : (Finset.Ioc ⌊α * L⌋₊ ⌊β * L⌋₊) = ∅ := by
      have hlh : ⌊β * L⌋₊ ≤ ⌊α * L⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right hab.le hL.le)
      simp [Finset.Ioc_eq_empty_of_le hlh]
    rw [this]; simp


/-- The union-window condition: the inclusion-exclusion mass of the windows exceeds `1`. -/
def UnionWindowOK (S : ι → Finset (ZMod M)) (c : ι → ℝ) (e : ι → ℕ) (a b : ℝ) : Prop :=
  1 < unionMass S c e a b

open Classical in
/-- **Weighted prime mass in a union of windows** (PNT in progressions, inclusion-exclusion over
the families).  If the union mass exceeds `1`, then for large `L` the weight sum
`∑ ℓ e(ℓ) log ℓ`, with `e(ℓ)` the largest tolerance among the families tying `ℓ`, exceeds
`(1 + ε₀) L`. -/
theorem tied_weight_lower {S : ι → Finset (ZMod M)} (hS : ∀ i, ∀ s ∈ S i, IsUnit s)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) (e : ι → ℕ) (exc : ι → Finset ℕ) {a b B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : ∀ i, b * c i ≤ B) (hmass : UnionWindowOK S c e a b) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      (1 + ε₀) * L ≤ tiedSum S c e exc a b L (⌊B * L⌋₊ + 1) := by
  unfold UnionWindowOK at hmass
  set m := unionMass S c e a b with hm
  have hlim : Tendsto (fun L : ℝ => tiedSum S c e exc a b L (⌊B * L⌋₊ + 1) / L) atTop (𝓝 m) := by
    have hsum : Tendsto (fun L : ℝ => ∑ T ∈ NESub ι, (-1 : ℝ) ^ (T.card + 1) * (minTol e T : ℝ) *
        (tiedSg S c exc a b L (⌊B * L⌋₊ + 1) T / L)) atTop
        (𝓝 (∑ T ∈ NESub ι, (-1 : ℝ) ^ (T.card + 1) * (minTol e T : ℝ) *
          (((overlap S T).card : ℝ) / (M.totient : ℝ) * winLen c a b T))) := by
      refine tendsto_finset_sum _ fun T hT => ?_
      have hTn : T.Nonempty := mem_NESub.mp hT
      have hBT : b * T.inf' hTn c ≤ B := by
        obtain ⟨i, hi⟩ := hTn
        exact (mul_le_mul_of_nonneg_left (Finset.inf'_le c hi) hb.le).trans (hB i)
      exact (tendsto_tiedSg hS hc exc ha hb hTn hBT).const_mul _
    have hval : (∑ T ∈ NESub ι, (-1 : ℝ) ^ (T.card + 1) * (minTol e T : ℝ) *
          (((overlap S T).card : ℝ) / (M.totient : ℝ) * winLen c a b T)) = m := by
      rw [hm]; unfold unionMass
      exact Finset.sum_congr rfl fun T _ => by ring
    rw [hval] at hsum
    refine hsum.congr' ?_
    filter_upwards with L
    rw [tiedSum_eq, Finset.sum_div]
    exact Finset.sum_congr rfl fun T _ => by ring
  have hlt : (1 + m) / 2 < m := by linarith
  have hev := hlim.eventually (lt_mem_nhds hlt)
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp (hev.and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨(m - 1) / 2, by linarith, L₀, fun L hL => ?_⟩
  obtain ⟨h1, h2⟩ := hL₀ L hL
  have := (lt_div_iff₀ h2).mp h1
  linarith

/-- Distinct primes: the product of prime powers dividing `n` divides `n`. -/
theorem prod_prime_pow_dvd (s : Finset ℕ) (k : ℕ → ℕ) (n : ℕ) (hp : ∀ l ∈ s, l.Prime)
    (hd : ∀ l ∈ s, l ^ k l ∣ n) : ∏ l ∈ s, l ^ k l ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hcop : Nat.Coprime (p ^ k p) (∏ x ∈ s, x ^ k x) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro x hx
      have hpx : p ≠ x := fun h => hps (h ▸ hx)
      exact ((Nat.coprime_primes (hp p (Finset.mem_insert_self p s))
        (hp x (Finset.mem_insert_of_mem hx))).mpr hpx).pow _ _
    exact hcop.mul_dvd_of_dvd_of_dvd (hd p (Finset.mem_insert_self p s))
      (ih (fun x hx => hp x (Finset.mem_insert_of_mem hx))
        (fun x hx => hd x (Finset.mem_insert_of_mem hx)))

open Classical in
/-- **A good tied prime exists** (ledger LR02).  Let a finite list of prime families be given, with
class sets `S i ⊆ (ℤ/M)ˣ`, slopes `c i > 0`, tolerances `e i` and exception sets `exc i`.  If the
union window mass of `(c i a, c i b]` exceeds `1`, then for all large `L`: whenever a positive
integer `Wt` is divisible by `ℓ ^ e i` for every bad pair `(i, ℓ)` and `log Wt < (1 + ε₀) L`,
some pair `(i, ℓ)`, with `ℓ` a prime of class `S i` outside `exc i` in the window
`c i a L < ℓ ≤ c i b L`, is not bad. -/
theorem exists_tied_prime {S : ι → Finset (ZMod M)} (hS : ∀ i, ∀ s ∈ S i, IsUnit s)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) (e : ι → ℕ) (exc : ι → Finset ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hmass : UnionWindowOK S c e a b) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ (Bad : ι → ℕ → Prop) (Wt : ℕ),
      0 < Wt → (∀ i ℓ, Bad i ℓ → ℓ ^ e i ∣ Wt) → Real.log Wt < (1 + ε₀) * L →
        ∃ i ℓ, Tied S c exc a b L i ℓ ∧ ¬ Bad i ℓ := by
  have hB : ∀ i, b * c i ≤ b * ∑ j, c j := fun i =>
    mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i))
      hb.le
  obtain ⟨ε₀, hε₀, L₀, hL₀⟩ := tied_weight_lower hS hc e exc ha hb hB hmass
  refine ⟨ε₀, hε₀, L₀, fun L hL Bad Wt hW hdvd hlog => ?_⟩
  by_contra hcon
  push_neg at hcon
  set N := ⌊(b * ∑ j, c j) * L⌋₊ + 1 with hN
  set s := (Finset.range N).filter (fun ℓ => 0 < tiedWt S c e exc a b L ℓ) with hs
  have hpd : ∀ ℓ ∈ s, ℓ.Prime ∧ ℓ ^ tiedWt S c e exc a b L ℓ ∣ Wt := by
    intro ℓ hℓ
    have hpos : 0 < tiedWt S c e exc a b L ℓ := (Finset.mem_filter.mp hℓ).2
    set I := Finset.univ.filter fun i => Tied S c exc a b L i ℓ with hI
    have hne : I.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have : tiedWt S c e exc a b L ℓ = 0 := by unfold tiedWt; rw [← hI, h]; simp
      omega
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup I hne e
    have hti : Tied S c exc a b L i ℓ := (Finset.mem_filter.mp hi).2
    refine ⟨hti.1, ?_⟩
    have : tiedWt S c e exc a b L ℓ = e i := by unfold tiedWt; rw [← hI]; exact heq
    rw [this]
    exact hdvd i ℓ (hcon i ℓ hti)
  have hprod : ∏ ℓ ∈ s, ℓ ^ tiedWt S c e exc a b L ℓ ∣ Wt :=
    prod_prime_pow_dvd s _ Wt (fun ℓ hℓ => (hpd ℓ hℓ).1) (fun ℓ hℓ => (hpd ℓ hℓ).2)
  have hle : ((∏ ℓ ∈ s, ℓ ^ tiedWt S c e exc a b L ℓ : ℕ) : ℝ) ≤ Wt :=
    by exact_mod_cast Nat.le_of_dvd hW hprod
  have hprodpos : (0 : ℝ) < ((∏ ℓ ∈ s, ℓ ^ tiedWt S c e exc a b L ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_pos fun ℓ hℓ => ?_
    have := (hpd ℓ hℓ).1.pos
    positivity
  have hlogle := Real.log_le_log hprodpos hle
  rw [Nat.cast_prod, Real.log_prod (fun ℓ hℓ => by
    have := (hpd ℓ hℓ).1.pos
    positivity)] at hlogle
  have hsum : tiedSum S c e exc a b L N =
      ∑ ℓ ∈ s, (tiedWt S c e exc a b L ℓ : ℝ) * Real.log ℓ := by
    unfold tiedSum
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun ℓ _ hℓs => ?_).symm
    have : tiedWt S c e exc a b L ℓ = 0 := by
      by_contra h
      exact hℓs (Finset.mem_filter.mpr ⟨by assumption, Nat.pos_of_ne_zero h⟩)
    simp [this]
  have hlow : (1 + ε₀) * L ≤ tiedSum S c e exc a b L N := hL₀ L hL
  have hterm : ∑ ℓ ∈ s, (tiedWt S c e exc a b L ℓ : ℝ) * Real.log ℓ ≤ Real.log Wt := by
    refine le_trans (le_of_eq ?_) hlogle
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    push_cast
    rw [Real.log_pow]
  rw [hsum] at hlow
  linarith


/-- The union mass is jointly continuous in the endpoints `(a, b)`. -/
theorem continuous_unionMass (S : ι → Finset (ZMod M)) (c : ι → ℝ) (e : ι → ℕ) :
    Continuous fun p : ℝ × ℝ => unionMass S c e p.1 p.2 := by
  unfold unionMass
  refine continuous_finset_sum _ fun T hT => ?_
  have hTn : T.Nonempty := mem_NESub.mp hT
  have : (fun p : ℝ × ℝ => winLen c p.1 p.2 T) =
      fun p => max 0 (p.2 * T.inf' hTn c - p.1 * T.sup' hTn c) := by
    funext p; unfold winLen; rw [dif_pos hTn]
  have hc : Continuous fun p : ℝ × ℝ => winLen c p.1 p.2 T := by
    rw [this]; fun_prop
  exact continuous_const.mul hc

end Window

end CatalanCore.NT
