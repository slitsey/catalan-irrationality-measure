module

public import CatalanCore.Arith.Hybrid.DefC5

@[expose] public section

/-!
# Lemma E, class 1: the abstract rank count (pair block + scalar Schur complement)

`P` carries an involution `τ` (the partner map `a ↔ a + p`) and a predicate `lo` marking the low
member of each pair; the fixed points of `τ` are the diagonal block `B₁`.  The block `Mp` of the
reduction has diagonal entries `0` (low), `π₁` (fixed), `π₂` (high) and `e` between partners, with
explicit inverse `pairInv` (`-π₂/e²`, `π₁⁻¹`, `0` on the diagonal and `e⁻¹` between partners).
If the unpaired block sees only the fixed points of `P` and its Schur complement is `s₀ I`, and the
zone rows/columns are single entries `σ e_{c_x}` with distinct `c_x ≠ c_y`, then the whole reduction
has rank `≤ |P| + |U|`, i.e. corank `≥ m`.
-/

open Matrix CatalanCore.Linalg

namespace CatalanCore.Arith.Hybrid

section Pair

variable {K : Type*} [Field K] {P : Type*} [Fintype P] [DecidableEq P]

/-- The pair block. -/
def pairMat (τ : P → P) (lo : P → Prop) [DecidablePred lo] (e π₁ π₂ : K) : Matrix P P K :=
  Matrix.of fun c c' => if c' = c then (if lo c then 0 else if τ c = c then π₁ else π₂)
    else if c' = τ c then e else 0

/-- Its inverse. -/
def pairInv (τ : P → P) (lo : P → Prop) [DecidablePred lo] (e π₁ π₂ : K) : Matrix P P K :=
  Matrix.of fun c c' => if c' = c then (if lo c then -π₂ / e ^ 2 else if τ c = c then π₁⁻¹ else 0)
    else if c' = τ c then e⁻¹ else 0

variable (τ : P → P) (lo : P → Prop) [DecidablePred lo] (e π₁ π₂ : K)

/-- sum over a vertex with at most two nonzero entries -/
lemma sum_two (f g : P → K) (c : P) :
    ∑ c', (if c' = c then f c' else if c' = τ c then g c' else 0) =
      f c + (if τ c = c then 0 else g (τ c)) := by
  by_cases h : τ c = c
  · have : ∀ x, (if x = c then f x else if x = τ c then g x else 0) = if x = c then f x else 0 := by
      intro x
      by_cases hx : x = c
      · simp [hx]
      · simp [hx, h]
    rw [Finset.sum_congr rfl (fun x _ => this x)]
    simp [h]
  · rw [Finset.sum_eq_add_of_mem c (τ c) (Finset.mem_univ _) (Finset.mem_univ _) (Ne.symm h)]
    · simp [h]
    · intro c' _ hc'
      simp [hc'.1, hc'.2]

lemma pairInv_self (c : P) : pairInv τ lo e π₁ π₂ c c =
    (if lo c then -π₂ / e ^ 2 else if τ c = c then π₁⁻¹ else 0) := by simp [pairInv]

lemma pairInv_tau (c : P) (h : τ c ≠ c) : pairInv τ lo e π₁ π₂ c (τ c) = e⁻¹ := by
  simp [pairInv, h]

lemma pairInv_oth (c c'' : P) (h1 : c'' ≠ c) (h2 : c'' ≠ τ c) :
    pairInv τ lo e π₁ π₂ c c'' = 0 := by simp [pairInv, h1, h2]

theorem pairMat_mul_pairInv (hτ : ∀ c, τ (τ c) = c) (hlo : ∀ c, lo c → τ c ≠ c ∧ ¬ lo (τ c))
    (hhi : ∀ c, ¬ lo c → τ c ≠ c → lo (τ c)) (he : e ≠ 0) (hπ : π₁ ≠ 0) :
    pairMat τ lo e π₁ π₂ * pairInv τ lo e π₁ π₂ = 1 := by
  ext c c''
  rw [Matrix.mul_apply]
  have key : ∀ c', pairMat τ lo e π₁ π₂ c c' * pairInv τ lo e π₁ π₂ c' c'' =
      (if c' = c then (if lo c then 0 else if τ c = c then π₁ else π₂) *
        pairInv τ lo e π₁ π₂ c c''
       else if c' = τ c then e * pairInv τ lo e π₁ π₂ (τ c) c'' else 0) := by
    intro c'
    by_cases h1 : c' = c
    · subst h1; simp [pairMat]
    · by_cases h2 : c' = τ c
      · subst h2; simp [pairMat, h1]
      · simp [pairMat, h1, h2]
  simp only [key]
  rw [sum_two τ (fun c' => (if lo c then 0 else if τ c = c then π₁ else π₂) *
        pairInv τ lo e π₁ π₂ c c'') (fun c' => e * pairInv τ lo e π₁ π₂ (τ c) c'') c]
  by_cases hc : lo c
  · obtain ⟨h1, h2⟩ := hlo c hc
    have hτc : τ (τ c) ≠ τ c := by rw [hτ]; exact Ne.symm h1
    have h3 : pairInv τ lo e π₁ π₂ (τ c) c = e⁻¹ := by
      have := pairInv_tau τ lo e π₁ π₂ (τ c) hτc
      rwa [hτ] at this
    have h4 : pairInv τ lo e π₁ π₂ (τ c) (τ c) = 0 := by
      rw [pairInv_self]; simp [h2, hτc]
    simp only [hc, if_true, zero_mul, zero_add, if_neg h1]
    by_cases hc3 : c'' = c
    · subst hc3; simp [h3, he]
    · by_cases hc4 : c'' = τ c
      · subst hc4; simp [h4, Matrix.one_apply, Ne.symm h1]
      · rw [pairInv_oth τ lo e π₁ π₂ (τ c) c'' hc4 (by rw [hτ]; exact hc3)]
        simp [Matrix.one_apply, Ne.symm hc3]
  · by_cases hfix : τ c = c
    · simp only [hc, hfix, if_false, if_true, add_zero]
      by_cases hc3 : c'' = c
      · subst hc3; rw [pairInv_self]; simp [hc, hfix, hπ]
      · rw [pairInv_oth τ lo e π₁ π₂ c c'' hc3 (by rw [hfix]; exact hc3)]
        simp [Matrix.one_apply, Ne.symm hc3]
    · have hl := hhi c hc hfix
      obtain ⟨h1, h2⟩ := hlo _ hl
      rw [hτ] at h1
      have h5 : pairInv τ lo e π₁ π₂ (τ c) (τ c) = -π₂ / e ^ 2 := by
        rw [pairInv_self]; simp [hl]
      have h6 : pairInv τ lo e π₁ π₂ (τ c) c = e⁻¹ := by
        have := pairInv_tau τ lo e π₁ π₂ (τ c) (by rw [hτ]; exact h1)
        rwa [hτ] at this
      have h7 : pairInv τ lo e π₁ π₂ c c = 0 := by
        rw [pairInv_self]; simp [hc, hfix]
      simp only [hc, hfix, if_false]
      by_cases hc3 : c'' = c
      · subst hc3; simp [h6, h7, he]
      · by_cases hc4 : c'' = τ c
        · subst hc4
          rw [h5, pairInv_tau τ lo e π₁ π₂ c hfix]
          rw [Matrix.one_apply, if_neg (Ne.symm hfix)]
          field_simp
          ring
        · rw [pairInv_oth τ lo e π₁ π₂ c c'' hc3 hc4,
            pairInv_oth τ lo e π₁ π₂ (τ c) c'' hc4 (by rw [hτ]; exact hc3)]
          simp [Matrix.one_apply, Ne.symm hc3]

/-- The Schur contribution of the pair block: only the fixed points of `τ` survive. -/
theorem pair_schur {A : Type*} (Up : A → P → K) (hUp : ∀ a c, lo c → Up a c = 0)
    (hhi : ∀ c, ¬ lo c → τ c ≠ c → lo (τ c)) (a a' : A) :
    ∑ c', (∑ c, Up a c * pairInv τ lo e π₁ π₂ c c') * Up a' c' =
      π₁⁻¹ * ∑ c, (if τ c = c then Up a c * Up a' c else 0) := by
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have key : ∀ c', Up a c * pairInv τ lo e π₁ π₂ c c' * Up a' c' =
      (if c' = c then Up a c * (if lo c then -π₂ / e ^ 2 else if τ c = c then π₁⁻¹ else 0) *
        Up a' c else if c' = τ c then Up a c * e⁻¹ * Up a' (τ c) else 0) := by
    intro c'
    by_cases h1 : c' = c
    · subst h1; simp [pairInv]
    · by_cases h2 : c' = τ c
      · subst h2; simp [pairInv, h1]
      · simp [pairInv, h1, h2]
  simp only [key]
  rw [sum_two τ (fun c' => Up a c * (if lo c then -π₂ / e ^ 2 else if τ c = c then π₁⁻¹ else 0) *
      Up a' c) (fun c' => Up a c * e⁻¹ * Up a' (τ c)) c]
  by_cases hc : lo c
  · simp [hUp a c hc]
  · by_cases hfix : τ c = c
    · simp [hc, hfix]; ring
    · have hl := hhi c hc hfix
      simp [hc, hfix, hUp a' (τ c) hl]

end Pair

section Rank

variable {K : Type*} [Field K] {U P X Y : Type*}
  [Fintype U] [Fintype P] [Fintype X] [Fintype Y]
  [DecidableEq U] [DecidableEq P] [DecidableEq X] [DecidableEq Y]

/-- **The rank count of Lemma E (class 1).** -/
theorem rank_E_abs (T : Matrix (U ⊕ X) (U ⊕ Y) K) (Up : Matrix (U ⊕ X) P K)
    (Wp : Matrix P (U ⊕ Y) K) (τ : P → P) (lo : P → Prop) [DecidablePred lo] (e π₁ π₂ s0 σ : K)
    (hτ : ∀ c, τ (τ c) = c) (hlo : ∀ c, lo c → τ c ≠ c ∧ ¬ lo (τ c))
    (hhi : ∀ c, ¬ lo c → τ c ≠ c → lo (τ c)) (he : e ≠ 0) (hπ : π₁ ≠ 0) (hs0 : s0 ≠ 0)
    (hUpX : ∀ x c, Up (Sum.inr x) c = 0) (hWpY : ∀ c y, Wp c (Sum.inr y) = 0)
    (hUpLo : ∀ a c, lo c → Up (Sum.inl a) c = 0)
    (hWp : ∀ c a, Wp c (Sum.inl a) = Up (Sum.inl a) c)
    (hTUU : ∀ a a', T (Sum.inl a) (Sum.inl a') = (if a = a' then s0 else 0) +
      π₁⁻¹ * ∑ c, (if τ c = c then Up (Sum.inl a) c * Up (Sum.inl a') c else 0))
    (hTXY : ∀ x y, T (Sum.inr x) (Sum.inr y) = 0)
    (cX : X → U) (cY : Y → U)
    (hGx : ∀ x u, T (Sum.inr x) (Sum.inl u) = if u = cX x then σ else 0)
    (hGy : ∀ u y, T (Sum.inl u) (Sum.inr y) = if u = cY y then σ else 0)
    (hc : ∀ x y, cX x ≠ cY y)
    (Mp : Matrix P P K) (hMp : Mp = pairMat τ lo e π₁ π₂) :
    (fromBlocks T Up Wp Mp).rank ≤ Fintype.card P + Fintype.card U := by
  classical
  have hmul := pairMat_mul_pairInv τ lo e π₁ π₂ hτ hlo hhi he hπ
  rw [← hMp] at hmul
  letI : Invertible Mp := invertibleOfRightInverse Mp _ hmul
  have hinv : ⅟Mp = pairInv τ lo e π₁ π₂ := invOf_eq_right_inv hmul
  have hSchur : T - Up * ⅟Mp * Wp =
      fromBlocks (s0 • (1 : Matrix U U K))
        (Matrix.of fun u y => T (Sum.inl u) (Sum.inr y))
        (Matrix.of fun x u => T (Sum.inr x) (Sum.inl u)) 0 := by
    rw [hinv]
    ext (i | x) (j | y)
    · simp only [Matrix.sub_apply, Matrix.mul_apply, fromBlocks_apply₁₁, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, hTUU, hWp]
      rw [pair_schur τ lo e π₁ π₂ (fun a c => Up (Sum.inl a) c) hUpLo hhi i j]
      by_cases h : i = j <;> simp [h]
    · simp [Matrix.sub_apply, Matrix.mul_apply, hWpY]
    · simp [Matrix.sub_apply, Matrix.mul_apply, hUpX]
    · simp [Matrix.sub_apply, Matrix.mul_apply, hUpX, hTXY]
  have := rank_BbarC5_le T Up Wp Mp s0 hs0 (Matrix.of fun x u => T (Sum.inr x) (Sum.inl u))
    (Matrix.of fun u y => T (Sum.inl u) (Sum.inr y)) hSchur Finset.univ Finset.univ cX cY σ
    (fun x _ u => by simpa using hGx x u) (fun y _ u => by simpa using hGy u y)
    (fun x _ y _ => hc x y)
  simpa using this

end Rank

end CatalanCore.Arith.Hybrid
