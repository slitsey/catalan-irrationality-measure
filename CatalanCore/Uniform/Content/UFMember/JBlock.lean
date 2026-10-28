module

public import CatalanCore.Uniform.Content.UFMember.FullWit

@[expose] public section

/-!
# UF member package, obligation O4b: kernels supported on a joint type `J`

Section 4 of `SMITH-EXTENSION-THEOREM.md` in Lean form.  Let `W` be square over `R` (index `B`,
`|B| = m`), `Jr`, `Jc` the rows and columns of one joint type, and suppose the `Jr × Jc` block of
`W` is divisible by `π`: `W = π · Hc` there.  Then there are `σ = |Jr| + |Jc| - m` independent
left kernel vectors of `W mod π` supported on `Jr` (the remaining equations are the `m - |Jc|`
columns outside `Jc`), likewise on the right, and their divided pairing is `X Hc Z`, whose
rank is at most that of the `Jr × Jc` block of `Hc mod π`.

`twoLevelData_of_jblock` therefore produces `TwoLevelData W σ b` from
(S7) restricted to `J`: `W_{zy} = π Hc_{zy}` for `z ∈ Jr`, `y ∈ Jc`, and `rank(Hc_{Jr,Jc} mod π) ≤ b`
(e.g. `b = |retained poles|` by `Smith.rank_le_card_of_sum` for the Cauchy form).
-/

open Matrix Finset Module

namespace CatalanCore.Uniform.Content.UFMember

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- Left kernel family supported on `Jr`, given the vanishing of the `Jr × Jc` block. -/
theorem exists_left_jfamily {B : Type*} [Fintype B] [DecidableEq B] (φ : R →+* K) {π : R}
    (hker : ∀ x, φ x = 0 ↔ π ∣ x) (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z)
    (W : Matrix B B R) (Jr Jc : Finset B) (hJ : ∀ z ∈ Jr, ∀ y ∈ Jc, π ∣ W z y) :
    ∃ X : Matrix (Fin (Jr.card + Jc.card - Fintype.card B)) B R,
      LinearIndependent K (fun i t => φ (X i t)) ∧ (∀ i t, t ∉ Jr → X i t = 0) ∧
      (∀ i t, π ∣ (X * W) i t) := by
  classical
  set a := Jr.card + Jc.card - Fintype.card B
  let Wb : Matrix B B K := W.map φ
  -- the remaining equations: columns outside `Jc`
  let f : (Jr → K) →ₗ[K] ({t // t ∉ Jc} → K) :=
    { toFun := fun x t => ∑ z, x z * Wb z t.1
      map_add' := by intro x y; funext t; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c x; funext t; simp [Finset.mul_sum, mul_assoc] }
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hr : finrank K (LinearMap.range f) ≤ Fintype.card {t // t ∉ Jc} := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  have hcc : Fintype.card {t // t ∉ Jc} = Fintype.card B - Jc.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have hJcle : Jc.card ≤ Fintype.card B := by simpa using Finset.card_le_univ Jc
  have hdom : finrank K (Jr → K) = Jr.card := by simp
  have ha : a ≤ finrank K (LinearMap.ker f) := by omega
  let bK := Module.finBasis K (LinearMap.ker f)
  let g : Fin a → Jr → K := fun i => (bK (Fin.castLE ha i) : Jr → K)
  have hg : LinearIndependent K g :=
    (bK.linearIndependent.comp _ (Fin.castLE_injective ha)).map' (LinearMap.ker f).subtype
      (Submodule.ker_subtype _)
  have hgk : ∀ i, f (g i) = 0 := fun i => (bK (Fin.castLE ha i)).2
  choose c x hc hx using fun i => exists_vec_lift φ hlift (g i)
  let X : Matrix (Fin a) B R := Matrix.of fun i t => if h : t ∈ Jr then x i ⟨t, h⟩ else 0
  refine ⟨X, ?_, ?_, ?_⟩
  · -- restriction to `Jr` is injective on vectors supported in `Jr`
    let restr : (B → K) →ₗ[K] (Jr → K) := LinearMap.funLeft K K Subtype.val
    have h3 := hg.units_smul (fun i => Units.mk0 (φ (c i)) (hc i))
    refine LinearIndependent.of_comp restr ?_
    convert h3 using 1
    funext i z
    simp [restr, X, LinearMap.funLeft, hx, Units.smul_def]
  · intro i t ht
    simp [X, ht]
  · intro i t
    rw [← hker, Matrix.mul_apply, map_sum]
    have hsum : ∑ z, φ (X i z * W z t) = φ (c i) * ∑ z : Jr, g i z * Wb z t := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ (Jr : Finset B)) (fun z _ hz => by
        simp [X, hz])]
      rw [← Finset.sum_coe_sort Jr]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [X, z.2, hx, Wb, Matrix.map_apply, mul_assoc]
    rw [hsum]
    by_cases ht : t ∈ Jc
    · have h0 : ∀ z : Jr, Wb z t = 0 := fun z => (hker _).2 (hJ z z.2 t ht)
      simp [h0]
    · have := congrFun (hgk i) ⟨t, ht⟩
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      rw [this, mul_zero]

/-- **Two-level data from a vanishing `J` block** (σ = `|Jr| + |Jc| - m`). -/
theorem exists_twoLevelData_of_jblock {B : Type*} [Fintype B] [DecidableEq B] (φ : R →+* K)
    {π : R} (hker : ∀ x, φ x = 0 ↔ π ∣ x) (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z)
    (W : Matrix B B R) (Jr Jc : Finset B) (Hc : Matrix B B R)
    (hJ : ∀ z ∈ Jr, ∀ y ∈ Jc, W z y = π * Hc z y) (b : ℕ)
    (hb : ((Hc.map φ).submatrix (Subtype.val : Jr → B) (Subtype.val : Jc → B)).rank ≤ b) :
    Nonempty (TwoLevelData φ π W (Jr.card + Jc.card - Fintype.card B) b) := by
  classical
  set a := Jr.card + Jc.card - Fintype.card B
  obtain ⟨X, hX1, hX2, hX3⟩ := exists_left_jfamily φ hker hlift W Jr Jc
    (fun z hz y hy => ⟨Hc z y, hJ z hz y hy⟩)
  have hJT : ∀ z ∈ Jc, ∀ y ∈ Jr, π ∣ Wᵀ z y := fun z hz y hy => ⟨Hc y z, hJ y hy z hz⟩
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_left_jfamily φ hker hlift Wᵀ Jc Jr hJT
  have hcard : Jc.card + Jr.card - Fintype.card B = a := by simp only [a]; omega
  -- reindex the right family to `Fin a`
  let Z : Matrix B (Fin a) R := fun t j => Y (Fin.cast hcard.symm j) t
  have hZ1 : LinearIndependent K (fun j t => φ (Z t j)) :=
    hY1.comp _ (Fin.cast_injective _)
  have hZ2 : ∀ t j, t ∉ Jc → Z t j = 0 := fun t j ht => hY2 _ t ht
  have hZ3 : ∀ t j, π ∣ (W * Z) t j := by
    intro t j
    have h := hY3 (Fin.cast hcard.symm j) t
    have e : (W * Z) t j = (Y * Wᵀ) (Fin.cast hcard.symm j) t := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Matrix.transpose_apply, mul_comm]
    rw [e]; exact h
  -- the pairing
  have hH : X * W * Z = π • (X * Hc * Z) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : z ∈ Jr
    · by_cases hy : y ∈ Jc
      · rw [hJ z hz y hy]; ring
      · rw [hZ2 y j hy]; ring
    · rw [hX2 i z hz]; ring
  have hrank : ((X * Hc * Z).map φ).rank ≤ b := by
    let Xr : Matrix (Fin a) Jr K := fun i z => φ (X i z)
    let Zc : Matrix Jc (Fin a) K := fun y j => φ (Z y j)
    have e : (X * Hc * Z).map φ =
        Xr * (Hc.map φ).submatrix (Subtype.val : Jr → B) (Subtype.val : Jc → B) * Zc := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
      rw [← Finset.sum_subset (Finset.subset_univ (Jc : Finset B)) (fun y _ hy => by
        simp [hZ2 y j hy])]
      rw [← Finset.sum_coe_sort Jc]
      refine Finset.sum_congr rfl fun y _ => ?_
      congr 1
      rw [← Finset.sum_subset (Finset.subset_univ (Jr : Finset B)) (fun z _ hz => by
        simp [hX2 i z hz])]
      rw [← Finset.sum_coe_sort Jr]
      rfl
    rw [e]
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hb
  exact ⟨TwoLevelData.ofFamilies φ hlift W X Z hX1 hZ1 hX3 hZ3 (X * Hc * Z) hH b hrank⟩

end CatalanCore.Uniform.Content.UFMember
