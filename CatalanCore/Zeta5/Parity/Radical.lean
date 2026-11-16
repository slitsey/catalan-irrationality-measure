module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import CatalanCore.Zeta5.Parity.Symbol

@[expose] public section

/-!
# ZC25: the radical of the full ordinary leading form of an even-`ℓ` group

The abstract (field-valued) form of the parity refinement PR1–PR2.

`ParityData F` records one even-`ℓ` group of sources `a : S` (classes with `ℓ_K(a) = ℓ`):
* `L a` rows per class, `P a` (even `ν`) or `Q` (odd `ν`), `ext a` (`ε_a = 1`), the base `T`;
* the local numerator polynomials `Bn a` (`B_{N,a}^3`, `J`-fixed for `a ∈ P`), the source scalars
  `δ a`, the own-source bilinear forms `Cf a` (`C_a(U, V) = τ₀(U V / B_{K,a})`, `J`-odd by ZC24),
  and the Cauchy-graph coefficients `cc a b` (`c_ab`).

For a coefficient vector `v : Row → F` (`Row = Σ a, Fin (L a)`; the coordinate `(a, i)` is the
coefficient of the normalised row `i` of class `a`, with local monomial `z^i`, `z = r + 1/2`) the
local image at the source `a` is (CG2)
`Ψ_a(v) = B_a · (∑_i v_{a,i} z^i + [a nonextra] · s_a(v) z^{L_a})`, `s_a(v) = ∑_{b active extra} c_ab t_b(v)`,
`t_b(v) = v_{b, L_b - 1}`, and the leading form is (CG3) `𝓛(v, w) = ∑_a δ_a C_a(Ψ_a v, Ψ_a w)`.

`radical_T_odd` / `radical_T_even`: there are at least `d - c` linearly independent vectors `v` with
`𝓛(v, w) = 0` for all `w`, where `d = #{a ∈ P : L_a odd}` and `c` is the number of Q conditions:
(T odd) `[#{P nonextra} - #{Q active extra}]`, (T even) `[#{P extra} - #{Q nonextra}]`.
-/

open Finset Polynomial
open scoped Classical

namespace Apery

structure ParityData (F : Type*) [Field F] where
  S : Type
  [instFin : Fintype S]
  L : S → ℕ
  P : S → Prop
  ext : S → Prop
  T : ℕ
  Bn : S → F[X]
  cc : S → S → F
  δ : S → F
  Cf : S → F[X] →ₗ[F] F[X] →ₗ[F] F
  hL : ∀ a, P a → L a % 2 = (T + (if ext a then 1 else 0)) % 2
  hB : ∀ a, P a → Jr (Bn a) = Bn a
  hodd : ∀ a U V, Cf a (Jr U) (Jr V) = - Cf a U V
  h2 : (2 : F) ≠ 0

attribute [instance] ParityData.instFin

namespace ParityData
variable {F : Type*} [Field F] (D : ParityData F)

/-- Coordinates of the row space. -/
abbrev Row : Type := Σ a : D.S, Fin (D.L a)

instance : Fintype D.Row := inferInstance

lemma row_eq {a b : D.S} {i : Fin (D.L a)} {j : Fin (D.L b)} :
    (⟨a, i⟩ : D.Row) = ⟨b, j⟩ ↔ a = b ∧ i.val = j.val := by
  constructor
  · intro h
    obtain rfl : a = b := (Sigma.mk.inj_iff.mp h).1
    exact ⟨rfl, congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)⟩
  · rintro ⟨rfl, h⟩
    exact congrArg (Sigma.mk a) (Fin.ext h)

/-- active extra classes: they own a top row. -/
def active (b : D.S) : Prop := D.ext b ∧ 0 < D.L b

/-- the top coordinate functional `t_b`. -/
noncomputable def topL (b : D.S) : (D.Row → F) →ₗ[F] F :=
  if h : 0 < D.L b then LinearMap.proj (⟨b, ⟨D.L b - 1, by omega⟩⟩ : D.Row) else 0

/-- `s_a(v) = ∑_{b active extra} c_ab t_b(v)`. -/
noncomputable def scL (a : D.S) : (D.Row → F) →ₗ[F] F :=
  ∑ b : D.S, if D.active b then D.cc a b • D.topL b else 0

/-- the own polynomial `∑_i v_{a,i} z^i`. -/
noncomputable def ownL (a : D.S) : (D.Row → F) →ₗ[F] F[X] :=
  ∑ i : Fin (D.L a), (LinearMap.proj (⟨a, i⟩ : D.Row)).smulRight ((zv : F[X]) ^ (i : ℕ))

/-- the local image `Ψ_a` (CG2). -/
noncomputable def PsiL (a : D.S) : (D.Row → F) →ₗ[F] F[X] :=
  LinearMap.mulLeft F (D.Bn a) ∘ₗ (D.ownL a +
    if D.ext a then 0 else (D.scL a).smulRight ((zv : F[X]) ^ D.L a))

/-- the leading ordinary graded form (CG3). -/
noncomputable def leadL : (D.Row → F) →ₗ[F] (D.Row → F) →ₗ[F] F :=
  ∑ a : D.S, D.δ a • (D.Cf a).compl₁₂ (D.PsiL a) (D.PsiL a)

lemma lead_apply (v w : D.Row → F) :
    D.leadL v w = ∑ a : D.S, D.δ a * D.Cf a (D.PsiL a v) (D.PsiL a w) := by
  simp [leadL, LinearMap.sum_apply]

/-! ### Unit-vector formulas -/

/-- the unit vector of the coordinate `r`. -/
noncomputable def e (r : D.Row) : D.Row → F := Pi.single r 1

lemma topL_e (b c : D.S) (j : Fin (D.L c)) :
    D.topL b (D.e ⟨c, j⟩) = if (b = c ∧ D.L b - 1 = j.val ∧ 0 < D.L b) then 1 else 0 := by
  unfold topL e
  by_cases hb : 0 < D.L b
  · rw [dif_pos hb]
    simp only [LinearMap.coe_proj, Function.eval, Pi.single_apply, row_eq]
    simp [hb]
  · rw [dif_neg hb]
    simp only [LinearMap.zero_apply]
    rw [if_neg (by tauto)]

lemma scL_e (a c : D.S) (j : Fin (D.L c)) :
    D.scL a (D.e ⟨c, j⟩) = if (D.active c ∧ D.L c - 1 = j.val) then D.cc a c else 0 := by
  unfold scL
  rw [LinearMap.sum_apply, Finset.sum_eq_single c]
  · by_cases h : D.active c ∧ D.L c - 1 = j.val
    · rw [if_pos h.1]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [topL_e, if_pos ⟨rfl, h.2, h.1.2⟩, if_pos h]; ring
    · by_cases ha : D.active c
      · rw [if_pos ha]
        simp only [LinearMap.smul_apply, smul_eq_mul]
        rw [topL_e, if_neg (by
          rintro ⟨_, h2, _⟩; exact h ⟨ha, h2⟩), if_neg h]; ring
      · rw [if_neg ha, if_neg (by tauto)]; simp
  · intro b _ hb
    by_cases ha : D.active b
    · rw [if_pos ha]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [topL_e, if_neg (by rintro ⟨h1, _⟩; exact hb h1)]; ring
    · rw [if_neg ha]; simp
  · intro h; exact absurd (Finset.mem_univ c) h

lemma ownL_e (a c : D.S) (j : Fin (D.L c)) :
    D.ownL a (D.e ⟨c, j⟩) = if a = c then (zv : F[X]) ^ j.val else 0 := by
  unfold ownL e
  rw [LinearMap.sum_apply]
  by_cases h : a = c
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp only [LinearMap.smulRight_apply, LinearMap.coe_proj, Function.eval, Pi.single_apply,
        row_eq, true_and]
      rw [if_neg (fun h => hi (Fin.ext h)), zero_smul]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [LinearMap.smulRight_apply, LinearMap.coe_proj, Function.eval, Pi.single_apply,
      row_eq]
    rw [if_neg (by tauto), zero_smul]

lemma Psi_e (a c : D.S) (j : Fin (D.L c)) :
    D.PsiL a (D.e ⟨c, j⟩) = D.Bn a * ((if a = c then (zv : F[X]) ^ j.val else 0) +
      if D.ext a then 0 else
        (if (D.active c ∧ D.L c - 1 = j.val) then D.cc a c else 0) • (zv : F[X]) ^ D.L a) := by
  unfold PsiL
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.add_apply]
  rw [ownL_e]
  by_cases hext : D.ext a
  · simp [hext]
  · simp only [hext, if_false, LinearMap.smulRight_apply, scL_e]

lemma Psi_apply (a : D.S) (v : D.Row → F) :
    D.PsiL a v = D.Bn a * (∑ i : Fin (D.L a), v ⟨a, i⟩ • (zv : F[X]) ^ (i : ℕ) +
      if D.ext a then 0 else D.scL a v • (zv : F[X]) ^ D.L a) := by
  unfold PsiL ownL
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.coe_proj, Function.eval]
  by_cases hext : D.ext a
  · simp [hext]
  · simp [hext]

/-! ### Parity facts -/

lemma Jr_smul (c : F) (U : F[X]) : Jr (c • U) = c • Jr U := by
  rw [smul_eq_C_mul, smul_eq_C_mul, Jr_C_mul]

lemma Jr_sum {ι : Type*} (s : Finset ι) (f : ι → F[X]) : Jr (∑ i ∈ s, f i) = ∑ i ∈ s, Jr (f i) := by
  simp [Jr]

lemma Jr_zero : Jr (0 : F[X]) = 0 := by simp [Jr]

lemma Cf_fix_zero (a : D.S) {U V : F[X]} (hU : Jr U = U) (hV : Jr V = V) : D.Cf a U V = 0 := by
  have h := D.hodd a U V
  rw [hU, hV] at h
  have : (2 : F) * D.Cf a U V = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left D.h2

lemma zvpow_fixed (hF : (2 : F) ≠ 0) {j : ℕ} (hj : Even j) :
    Jr ((zv : F[X]) ^ j) = (zv : F[X]) ^ j := by
  rw [Jr_zpow hF, hj.neg_one_pow]; simp

/-- Vectors supported on the even rows of the `P` classes. -/
def Evec (v : D.Row → F) : Prop := ∀ r : D.Row, ¬ (D.P r.1 ∧ Even r.2.val) → v r = 0

lemma Jr_own {v : D.Row → F} (hv : D.Evec v) {a : D.S} (ha : D.P a) :
    Jr (∑ i : Fin (D.L a), v ⟨a, i⟩ • (zv : F[X]) ^ (i : ℕ)) =
      ∑ i : Fin (D.L a), v ⟨a, i⟩ • (zv : F[X]) ^ (i : ℕ) := by
  rw [Jr_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Jr_smul]
  by_cases hi : Even i.val
  · rw [zvpow_fixed D.h2 hi]
  · rw [hv ⟨a, i⟩ (by simp [ha, hi]), zero_smul, zero_smul]

lemma own_zero {v : D.Row → F} (hv : D.Evec v) {a : D.S} (ha : ¬ D.P a) :
    ∑ i : Fin (D.L a), v ⟨a, i⟩ • (zv : F[X]) ^ (i : ℕ) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hv ⟨a, i⟩ (by simp [ha]), zero_smul]

lemma topL_apply (b : D.S) (v : D.Row → F) :
    D.topL b v = if h : 0 < D.L b then v ⟨b, ⟨D.L b - 1, by omega⟩⟩ else 0 := by
  unfold topL
  by_cases h : 0 < D.L b <;> simp [h]

/-- For an active extra `b ∈ P` the top index `L_b - 1` has the parity of `T`. -/
lemma top_parity {b : D.S} (hb : D.P b) (hact : D.active b) :
    (D.L b - 1) % 2 = D.T % 2 := by
  have h := D.hL b hb
  rw [if_pos hact.1] at h
  have := hact.2
  omega

lemma topL_Evec {v : D.Row → F} (hv : D.Evec v) (hT : D.T % 2 = 1) (b : D.S)
    (hb : D.active b) : D.topL b v = 0 := by
  rw [topL_apply, dif_pos hb.2]
  by_cases hP : D.P b
  · apply hv
    have := D.top_parity hP hb
    simp only [not_and, Nat.not_even_iff_odd]
    intro _; show Odd (D.L b - 1); rw [Nat.odd_iff]; omega
  · apply hv; simp [hP]

lemma topL_Q {v : D.Row → F} (hv : D.Evec v) (b : D.S) (hb : ¬ D.P b) (h : 0 < D.L b) :
    D.topL b v = 0 := by
  rw [topL_apply, dif_pos h]; apply hv; simp [hb]

lemma scL_apply (a : D.S) (v : D.Row → F) :
    D.scL a v = ∑ b : D.S, if D.active b then D.cc a b * D.topL b v else 0 := by
  unfold scL
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : D.active b <;> simp [h]

lemma scL_Todd {v : D.Row → F} (hv : D.Evec v) (hT : D.T % 2 = 1) (a : D.S) : D.scL a v = 0 := by
  rw [scL_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h : D.active b
  · rw [if_pos h, D.topL_Evec hv hT b h, mul_zero]
  · rw [if_neg h]

/-! ### Vanishing of the pairings -/

lemma Psi_zero_Q {v : D.Row → F} (hv : D.Evec v) {c : D.S} (hc : ¬ D.P c)
    (hs : ¬ D.ext c → D.scL c v = 0) : D.PsiL c v = 0 := by
  rw [Psi_apply, D.own_zero hv hc]
  by_cases he : D.ext c
  · simp [he]
  · simp [he, hs he]

lemma Psi_fix_P {v : D.Row → F} (hv : D.Evec v) {c : D.S} (hc : D.P c)
    (hs : ¬ D.ext c → D.L c % 2 = 0 ∨ D.scL c v = 0) : Jr (D.PsiL c v) = D.PsiL c v := by
  rw [Psi_apply, Jr_mul, D.hB c hc, Jr_add, D.Jr_own hv hc]
  by_cases he : D.ext c
  · simp [he, Jr_zero]
  · simp only [he, if_false]
    rcases hs he with h | h
    · have hev : Even (D.L c) := Nat.even_iff.mpr h
      rw [Jr_smul, zvpow_fixed D.h2 hev]
    · rw [h]; simp [Jr_zero]

lemma lead_e_zero_of {v : D.Row → F} (r : D.Row)
    (h : ∀ c, D.PsiL c v = 0 ∨ D.PsiL c (D.e r) = 0 ∨
      (Jr (D.PsiL c v) = D.PsiL c v ∧ Jr (D.PsiL c (D.e r)) = D.PsiL c (D.e r))) :
    D.leadL v (D.e r) = 0 := by
  rw [lead_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases h c with h1 | h2 | ⟨h3, h4⟩
  · rw [h1]; simp
  · rw [h2]; simp
  · rw [D.Cf_fix_zero c h3 h4, mul_zero]

lemma lead_e_zero_Todd {v : D.Row → F} (hv : D.Evec v) (hT : D.T % 2 = 1) (r : D.Row)
    (hr : ¬ ((D.P r.1 ∧ ¬ Even r.2.val) ∨ (¬ D.P r.1 ∧ D.active r.1 ∧ D.L r.1 - 1 = r.2.val))) :
    D.leadL v (D.e r) = 0 := by
  obtain ⟨b, j⟩ := r
  refine D.lead_e_zero_of _ fun c => ?_
  by_cases hc : D.P c
  · by_cases hb : D.P b
    · have hj : Even j.val := by
        by_contra hj; exact hr (Or.inl ⟨hb, hj⟩)
      right; right
      refine ⟨D.Psi_fix_P hv hc fun _ => Or.inr (D.scL_Todd hv hT c), ?_⟩
      have hsc : ¬ (D.active b ∧ D.L b - 1 = j.val) := by
        rintro ⟨h1, h2⟩
        have := D.top_parity hb h1
        rw [h2] at this
        have h3 := Nat.even_iff.mp hj
        omega
      rw [Psi_e]
      simp only [hsc, if_false, zero_smul, add_zero, ite_self, Jr_mul, D.hB c hc]
      by_cases hcb : c = b
      · simp [hcb, zvpow_fixed D.h2 hj]
      · simp [hcb, Jr_zero]
    · right; left
      have hsc : ¬ (D.active b ∧ D.L b - 1 = j.val) := fun h => hr (Or.inr ⟨hb, h⟩)
      have hcb : c ≠ b := fun h => hb (h ▸ hc)
      rw [Psi_e]
      simp [hsc, hcb]
  · left
    exact D.Psi_zero_Q hv hc fun _ => D.scL_Todd hv hT c

lemma lead_e_zero_Teven {v : D.Row → F} (hv : D.Evec v) (hT : D.T % 2 = 0)
    (hQ : ∀ a, ¬ D.P a → ¬ D.ext a → D.scL a v = 0) (r : D.Row)
    (hr : ¬ (D.P r.1 ∧ ¬ Even r.2.val)) : D.leadL v (D.e r) = 0 := by
  obtain ⟨b, j⟩ := r
  refine D.lead_e_zero_of _ fun c => ?_
  by_cases hc : D.P c
  · right; right
    have hLc : ¬ D.ext c → D.L c % 2 = 0 := fun he => by
      have := D.hL c hc; rw [if_neg he] at this; omega
    refine ⟨D.Psi_fix_P hv hc fun he => Or.inl (hLc he), ?_⟩
    rw [Psi_e]
    simp only [Jr_mul, D.hB c hc]
    have hadd : ∀ s : F, Jr (if D.ext c then (0 : F[X]) else s • (zv : F[X]) ^ D.L c) =
        (if D.ext c then (0 : F[X]) else s • (zv : F[X]) ^ D.L c) := fun s => by
      by_cases he : D.ext c
      · simp [he, Jr_zero]
      · simp only [he, if_false, Jr_smul, zvpow_fixed D.h2 (Nat.even_iff.mpr (hLc he))]
    have hown : Jr (if c = b then (zv : F[X]) ^ j.val else 0) =
        (if c = b then (zv : F[X]) ^ j.val else 0) := by
      by_cases hcb : c = b
      · subst hcb
        have hj : Even j.val := by
          by_contra hj; exact hr ⟨hc, hj⟩
        simp [zvpow_fixed D.h2 hj]
      · simp [hcb, Jr_zero]
    rw [Jr_add, hown, hadd]
  · left
    exact D.Psi_zero_Q hv hc fun he => hQ c hc he

/-! ### Rank bookkeeping -/

lemma finrank_ker_ge {V J : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype J] (g : V →ₗ[F] (J → F)) :
    Module.finrank F V - Fintype.card J ≤ Module.finrank F (LinearMap.ker g) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : Module.finrank F (LinearMap.range g) ≤ Fintype.card J := by
    have := Submodule.finrank_le (LinearMap.range g)
    simpa using this
  omega

/-- the even rows of `P` classes -/
noncomputable def evenRows : Finset D.Row :=
  Finset.univ.filter fun r => D.P r.1 ∧ Even r.2.val

/-- the odd rows of `P` classes -/
noncomputable def oddRows : Finset D.Row :=
  Finset.univ.filter fun r => D.P r.1 ∧ ¬ Even r.2.val

/-- extension by zero from the even rows -/
noncomputable def extE : (↥D.evenRows → F) →ₗ[F] (D.Row → F) where
  toFun x r := if h : r ∈ D.evenRows then x ⟨r, h⟩ else 0
  map_add' x y := by funext r; by_cases h : r ∈ D.evenRows <;> simp [h]
  map_smul' c x := by funext r; by_cases h : r ∈ D.evenRows <;> simp [h]

lemma extE_evec (x : ↥D.evenRows → F) : D.Evec (D.extE x) := by
  intro r hr
  have : r ∉ D.evenRows := by simp [evenRows, hr]
  simp [extE, this]

lemma extE_inj : Function.Injective D.extE := by
  intro x y h
  funext ⟨r, hr⟩
  have := congrFun h r
  simpa [extE, hr] using this

lemma lead_eq_zero_of {v : D.Row → F} (h : ∀ r, D.leadL v (D.e r) = 0) (w : D.Row → F) :
    D.leadL v w = 0 := by
  have hw : w = ∑ r, w r • D.e r := by
    funext s; simp [e, Pi.single_apply, Finset.sum_apply]
  rw [hw, map_sum]
  simp [map_smul, h]

lemma card_even_fin (n : ℕ) :
    ∑ i : Fin n, (if Even i.val then 1 else 0) =
      ∑ i : Fin n, (if Even i.val then 0 else 1) + n % 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if Even i then 1 else 0) n,
    Fin.sum_univ_eq_sum_range (fun i => if Even i then 0 else 1) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd n with h | h
    · rw [if_pos h, if_pos h]
      have h2 : n % 2 = 0 := Nat.even_iff.mp h
      omega
    · rw [if_neg (Nat.not_even_iff_odd.mpr h), if_neg (Nat.not_even_iff_odd.mpr h)]
      have h2 : n % 2 = 1 := Nat.odd_iff.mp h
      omega

lemma card_even_rows :
    D.evenRows.card = D.oddRows.card +
      (Finset.univ.filter fun a : D.S => D.P a ∧ D.L a % 2 = 1).card := by
  unfold evenRows oddRows
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sigma,
    Fintype.sum_sigma, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : D.P a
  · have h1 := card_even_fin (D.L a)
    have h2 : (∑ i : Fin (D.L a), if ¬Even i.val then 1 else 0) =
        ∑ i : Fin (D.L a), if Even i.val then 0 else 1 :=
      Finset.sum_congr rfl fun i _ => by split_ifs <;> simp_all
    simp only [ha, true_and]
    rw [h2, h1]
    have h3 : (if D.L a % 2 = 1 then 1 else 0) = D.L a % 2 := by
      have : D.L a % 2 = 0 ∨ D.L a % 2 = 1 := by omega
      rcases this with h | h <;> simp [h]
    rw [h3]
  · simp [ha]

/-! ### The radical vectors -/

/-- **ZC25, `T` odd (PR1).**  There are at least `#{a ∈ P : ¬ ext a} - #{b ∉ P : active b}` linearly
independent coefficient vectors in the radical of the leading form of the group. -/
theorem radical_T_odd (hT : D.T % 2 = 1) :
    ∃ (k : ℕ) (u : Fin k → D.Row → F),
      (Finset.univ.filter fun a : D.S => D.P a ∧ ¬ D.ext a).card -
        (Finset.univ.filter fun b : D.S => ¬ D.P b ∧ D.active b).card ≤ k ∧
      LinearIndependent F u ∧ ∀ i w, D.leadL (u i) w = 0 := by
  classical
  set testOdd : Finset D.Row := Finset.univ.filter fun r : D.Row =>
    (D.P r.1 ∧ ¬ Even r.2.val) ∨ (¬ D.P r.1 ∧ D.active r.1 ∧ D.L r.1 - 1 = r.2.val) with htest
  let g : (↥D.evenRows → F) →ₗ[F] (↥testOdd → F) :=
    LinearMap.pi fun r => (D.leadL.flip (D.e r.1)).comp D.extE
  set K := LinearMap.ker g with hK
  have hge : Module.finrank F (↥D.evenRows → F) - Fintype.card ↥testOdd ≤ Module.finrank F K :=
    finrank_ker_ge g
  have hV : Module.finrank F (↥D.evenRows → F) = D.evenRows.card := by simp
  have hJ : Fintype.card ↥testOdd = testOdd.card := by simp
  have hcard : testOdd.card ≤ D.oddRows.card +
      (Finset.univ.filter fun b : D.S => ¬ D.P b ∧ D.active b).card := by
    have h1 : testOdd ⊆ D.oddRows ∪ (Finset.univ.filter fun r : D.Row =>
        ¬ D.P r.1 ∧ D.active r.1 ∧ D.L r.1 - 1 = r.2.val) := by
      intro r hr
      simp only [htest, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simp only [oddRows, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have h2 : (Finset.univ.filter fun r : D.Row =>
        ¬ D.P r.1 ∧ D.active r.1 ∧ D.L r.1 - 1 = r.2.val).card ≤
        (Finset.univ.filter fun b : D.S => ¬ D.P b ∧ D.active b).card := by
      refine Finset.card_le_card_of_injOn (fun r => r.1) ?_ ?_
      · intro r hr
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hr ⊢
        exact ⟨hr.1, hr.2.1⟩
      · intro r hr s hs hrs
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hr hs
        obtain ⟨a, i⟩ := r
        obtain ⟨b, j⟩ := s
        simp only at hrs
        subst hrs
        have : i = j := Fin.ext (by have := hr.2.2; have := hs.2.2; simp only at *; omega)
        rw [this]
    exact (Finset.card_le_card h1).trans ((Finset.card_union_le _ _).trans (by omega))
  have hcnt := D.card_even_rows
  have hset : (Finset.univ.filter fun a : D.S => D.P a ∧ D.L a % 2 = 1) =
      Finset.univ.filter fun a : D.S => D.P a ∧ ¬ D.ext a := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ha, h⟩
      refine ⟨ha, fun he => ?_⟩
      have := D.hL a ha
      rw [if_pos he] at this; omega
    · rintro ⟨ha, h⟩
      refine ⟨ha, ?_⟩
      have := D.hL a ha
      rw [if_neg h] at this; omega
  rw [hset] at hcnt
  let b := Module.finBasis F K
  refine ⟨Module.finrank F K, fun i => D.extE (b i : ↥D.evenRows → F), ?_, ?_, ?_⟩
  · rw [hV, hJ] at hge
    omega
  · have hind := b.linearIndependent
    have := hind.map' (D.extE.comp K.subtype) (by
      rw [LinearMap.ker_eq_bot]
      exact D.extE_inj.comp Subtype.val_injective)
    exact this
  · intro i w
    apply D.lead_eq_zero_of
    intro r
    have hx : g (b i : ↥D.evenRows → F) = 0 := (b i).2
    by_cases hr : r ∈ testOdd
    · have := congrFun hx ⟨r, hr⟩
      simpa [g] using this
    · refine D.lead_e_zero_Todd (D.extE_evec _) hT r ?_
      intro h
      exact hr (by simp only [htest, Finset.mem_filter, Finset.mem_univ, true_and]; exact h)

/-- **ZC25, `T` even (PR2).**  At least `#{a ∈ P : ext a} - #{b ∉ P : ¬ ext b}` independent radical
vectors. -/
theorem radical_T_even (hT : D.T % 2 = 0) :
    ∃ (k : ℕ) (u : Fin k → D.Row → F),
      (Finset.univ.filter fun a : D.S => D.P a ∧ D.ext a).card -
        (Finset.univ.filter fun b : D.S => ¬ D.P b ∧ ¬ D.ext b).card ≤ k ∧
      LinearIndependent F u ∧ ∀ i w, D.leadL (u i) w = 0 := by
  classical
  set Qn : Finset D.S := Finset.univ.filter fun b : D.S => ¬ D.P b ∧ ¬ D.ext b with hQn
  let g : (↥D.evenRows → F) →ₗ[F] ((↥D.oddRows ⊕ ↥Qn) → F) :=
    LinearMap.pi fun j => match j with
      | Sum.inl r => (D.leadL.flip (D.e r.1)).comp D.extE
      | Sum.inr a => (D.scL a.1).comp D.extE
  set K := LinearMap.ker g with hK
  have hge : Module.finrank F (↥D.evenRows → F) - Fintype.card (↥D.oddRows ⊕ ↥Qn) ≤
      Module.finrank F K := finrank_ker_ge g
  have hV : Module.finrank F (↥D.evenRows → F) = D.evenRows.card := by simp
  have hJ : Fintype.card (↥D.oddRows ⊕ ↥Qn) = D.oddRows.card + Qn.card := by simp
  have hcnt := D.card_even_rows
  have hset : (Finset.univ.filter fun a : D.S => D.P a ∧ D.L a % 2 = 1) =
      Finset.univ.filter fun a : D.S => D.P a ∧ D.ext a := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ha, h⟩
      refine ⟨ha, ?_⟩
      by_contra he
      have := D.hL a ha
      rw [if_neg he] at this; omega
    · rintro ⟨ha, h⟩
      refine ⟨ha, ?_⟩
      have := D.hL a ha
      rw [if_pos h] at this; omega
  rw [hset] at hcnt
  let b := Module.finBasis F K
  refine ⟨Module.finrank F K, fun i => D.extE (b i : ↥D.evenRows → F), ?_, ?_, ?_⟩
  · rw [hV, hJ] at hge
    omega
  · have hind := b.linearIndependent
    have := hind.map' (D.extE.comp K.subtype) (by
      rw [LinearMap.ker_eq_bot]
      exact D.extE_inj.comp Subtype.val_injective)
    exact this
  · intro i w
    apply D.lead_eq_zero_of
    intro r
    have hx : g (b i : ↥D.evenRows → F) = 0 := (b i).2
    have hQ : ∀ a, ¬ D.P a → ¬ D.ext a → D.scL a (D.extE (b i : ↥D.evenRows → F)) = 0 := by
      intro a ha1 ha2
      have := congrFun hx (Sum.inr ⟨a, by simp [hQn, ha1, ha2]⟩)
      simpa [g] using this
    by_cases hr : D.P r.1 ∧ ¬ Even r.2.val
    · have hmem : r ∈ D.oddRows := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
      have := congrFun hx (Sum.inl ⟨r, hmem⟩)
      simpa [g] using this
    · exact D.lead_e_zero_Teven (D.extE_evec _) hT hQ r hr

end ParityData
end Apery
