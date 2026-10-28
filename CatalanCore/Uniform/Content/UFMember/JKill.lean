module

public import CatalanCore.Uniform.Content.UFMember.FullJ

@[expose] public section

/-!
# UF member package, step 3: the wedge-kill set

Section 4 of `SMITH-EXTENSION-THEOREM.md`: a retained pole `c` contributes the rank-one term
`(X A_c)(B_c Z)` to the divided pairing, and it disappears if either PROJECTED factor vanishes.
The left family `X` annihilates EVERY column of `W mod π` (`X W ≡ 0`), so if some column `t` of
`W mod π` (an occupied border column outside `J`, or any other) restricts on `Jr` to a NONZERO
multiple of the Cauchy column `A_{·c}`, then `X A_c = 0` and `c` is killed (`KillR`); likewise
on the right (`KillC`).  This is the paper's rule "an occupied outside-`J` border row/column kills
its residue when its first-layer projective wedge with `J` is nonzero": the wedge is the
proportionality constant `λ`, and only `λ ≠ 0` is needed.

`exists_twoLevelData_of_jblock_kill`: two-level data with `b = |Ret \ (KillR ∪ KillC)|`.
`JBlockKill`, `smithWitK_of_jblock`, `SmithJKDatum`, `smithJKLayer`: the full-matrix witness and
the debit-1 layer at price `2(|C| + m) - (m + σ + (σ - |Ret \ Kill|))`, which is Theorem UF's
`2|C| + m - max(σ, 2σ - s_J)` with `s_J = |Ret \ Kill|`.
-/

open Polynomial Matrix Finset Module CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.UFMember

section Abstract

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- **Two-level data from a vanishing `J` block, with wedge kills.** -/
theorem exists_twoLevelData_of_jblock_kill {B : Type*} [Fintype B] [DecidableEq B]
    (φ : R →+* K) {π : R} (hker : ∀ x, φ x = 0 ↔ π ∣ x)
    (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z)
    (W : Matrix B B R) (Jr Jc : Finset B) (Hc : Matrix B B R)
    (hJ : ∀ z ∈ Jr, ∀ y ∈ Jc, W z y = π * Hc z y) {P : Type*} (Ret : Finset P)
    (A : B → P → K) (Bv : P → B → K)
    (hcauchy : ∀ z ∈ Jr, ∀ y ∈ Jc, φ (Hc z y) = ∑ c ∈ Ret, A z c * Bv c y)
    (KillR KillC : Finset P) [DecidableEq P]
    (hKR : ∀ c ∈ KillR, ∃ t : B, ∃ l : K, l ≠ 0 ∧ ∀ z ∈ Jr, φ (W z t) = l * A z c)
    (hKC : ∀ c ∈ KillC, ∃ t : B, ∃ l : K, l ≠ 0 ∧ ∀ y ∈ Jc, φ (W t y) = l * Bv c y) :
    Nonempty (TwoLevelData φ π W (Jr.card + Jc.card - Fintype.card B)
      (Ret \ (KillR ∪ KillC)).card) := by
  classical
  set a := Jr.card + Jc.card - Fintype.card B
  obtain ⟨X, hX1, hX2, hX3⟩ := exists_left_jfamily φ hker hlift W Jr Jc
    (fun z hz y hy => ⟨Hc z y, hJ z hz y hy⟩)
  have hJT : ∀ z ∈ Jc, ∀ y ∈ Jr, π ∣ Wᵀ z y := fun z hz y hy => ⟨Hc y z, hJ y hy z hz⟩
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_left_jfamily φ hker hlift Wᵀ Jc Jr hJT
  have hcard : Jc.card + Jr.card - Fintype.card B = a := by simp only [a]; omega
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
  have hH : X * W * Z = π • (X * Hc * Z) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : z ∈ Jr
    · by_cases hy : y ∈ Jc
      · rw [hJ z hz y hy]; ring
      · rw [hZ2 y j hy]; ring
    · rw [hX2 i z hz]; ring
  -- the projected factors
  let XA : Fin a → P → K := fun i c => ∑ z : Jr, φ (X i z) * A z c
  let BZ : P → Fin a → K := fun c j => ∑ y : Jc, Bv c y * φ (Z y j)
  have hXW0 : ∀ i t, ∑ z : Jr, φ (X i z) * φ (W z t) = 0 := by
    intro i t
    have h := (hker _).2 (hX3 i t)
    rw [Matrix.mul_apply, map_sum] at h
    rw [← Finset.sum_subset (Finset.subset_univ (Jr : Finset B)) (fun z _ hz => by
      simp [hX2 i z hz])] at h
    rw [← Finset.sum_coe_sort Jr] at h
    simpa [map_mul] using h
  have hWZ0 : ∀ t j, ∑ y : Jc, φ (W t y) * φ (Z y j) = 0 := by
    intro t j
    have h := (hker _).2 (hZ3 t j)
    rw [Matrix.mul_apply, map_sum] at h
    rw [← Finset.sum_subset (Finset.subset_univ (Jc : Finset B)) (fun y _ hy => by
      simp [hZ2 y j hy])] at h
    rw [← Finset.sum_coe_sort Jc] at h
    simpa [map_mul] using h
  have hXA0 : ∀ c ∈ KillR, ∀ i, XA i c = 0 := by
    intro c hc i
    obtain ⟨t, l, hl, hlt⟩ := hKR c hc
    have h := hXW0 i t
    have e : ∑ z : Jr, φ (X i z) * φ (W z t) = l * XA i c := by
      simp only [XA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [hlt z z.2]; ring
    rw [e] at h
    exact (mul_eq_zero.1 h).resolve_left hl
  have hBZ0 : ∀ c ∈ KillC, ∀ j, BZ c j = 0 := by
    intro c hc j
    obtain ⟨t, l, hl, hlt⟩ := hKC c hc
    have h := hWZ0 t j
    have e : ∑ y : Jc, φ (W t y) * φ (Z y j) = l * BZ c j := by
      simp only [BZ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hlt y y.2]; ring
    rw [e] at h
    exact (mul_eq_zero.1 h).resolve_left hl
  have hrank : ((X * Hc * Z).map φ).rank ≤ (Ret \ (KillR ∪ KillC)).card := by
    refine Smith.rank_le_card_of_sum (Ret \ (KillR ∪ KillC)) _ XA BZ fun i j => ?_
    have e1 : ((X * Hc * Z).map φ) i j = ∑ c ∈ Ret, XA i c * BZ c j := by
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
      rw [← Finset.sum_subset (Finset.subset_univ (Jc : Finset B)) (fun y _ hy => by
        simp [hZ2 y j hy])]
      rw [← Finset.sum_coe_sort Jc]
      have e2 : ∀ y : Jc, (∑ z, φ (X i z) * φ (Hc z y)) =
          ∑ c ∈ Ret, (∑ z : Jr, φ (X i z) * A z c) * Bv c y := by
        intro y
        rw [← Finset.sum_subset (Finset.subset_univ (Jr : Finset B)) (fun z _ hz => by
          simp [hX2 i z hz])]
        rw [← Finset.sum_coe_sort Jr]
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hcauchy z z.2 y y.2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
      simp only [e2, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [XA, BZ, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [e1]
    symm
    refine Finset.sum_subset Finset.sdiff_subset fun c hc hc' => ?_
    have : c ∈ KillR ∪ KillC := by
      by_contra hn; exact hc' (Finset.mem_sdiff.2 ⟨hc, hn⟩)
    rcases Finset.mem_union.1 this with h | h
    · rw [hXA0 c h i, zero_mul]
    · rw [hBZ0 c h j, mul_zero]
  exact ⟨TwoLevelData.ofFamilies φ hlift W X Z hX1 hZ1 hX3 hZ3 (X * Hc * Z) hH _ hrank⟩

end Abstract

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The `J`-block of (S7) with wedge kills. -/
structure JBlockKill (W : Matrix κ κ (LocRing p)[X]) extends JBlockCauchy W where
  KillR : Finset (ZMod p)
  KillC : Finset (ZMod p)
  hKR : ∀ c ∈ KillR, ∃ t : κ, ∃ l : RatFunc (ZMod p), l ≠ 0 ∧
    ∀ z ∈ Jr, phiP p (W z t) = l * A z c
  hKC : ∀ c ∈ KillC, ∃ t : κ, ∃ l : RatFunc (ZMod p), l ≠ 0 ∧
    ∀ y ∈ Jc, phiP p (W t y) = l * B c y

/-- The retained count `s_J = |Ret \ (KillR ∪ KillC)|`. -/
noncomputable def JBlockKill.sJ {W : Matrix κ κ (LocRing p)[X]} (J : JBlockKill W) : ℕ :=
  (J.Ret \ (J.KillR ∪ J.KillC)).card

theorem JBlockKill.twoLevel {W : Matrix κ κ (LocRing p)[X]} (J : JBlockKill W) :
    Nonempty (TwoLevelData (phiP p) (Polynomial.C ((p : ℕ) : LocRing p)) W
      (J.Jr.card + J.Jc.card - Fintype.card κ) J.sJ) :=
  exists_twoLevelData_of_jblock_kill (phiP p) (phiP_eq_zero_iff p) (UFMember.phiP_lift p) W
    J.Jr J.Jc J.Hc J.hJ J.Ret J.A J.B J.hcauchy J.KillR J.KillC J.hKR J.hKC

/-- **The Smith witness of the full matrix, with wedge kills.** -/
noncomputable def smithWitK_of_jblock (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
    (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p))
    (J : JBlockKill (schurW c xs ys (hint_of_poleData D hN hc hx hy))) :
    ThreeLevelWit p ((FullN Fr c xs ys (X : ℚ[X])).map (scaleU p)) J.sJ :=
  fullSmithWit D hN c xs ys hc hx hy hdist (Classical.choice J.twoLevel)

theorem smithWitK_of_jblock_price (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
    (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p))
    (J : JBlockKill (schurW c xs ys (hint_of_poleData D hN hc hx hy))) :
    (smithWitK_of_jblock D hN c xs ys hc hx hy hdist J).price =
      2 * Fintype.card (ι ⊕ κ) - (Fintype.card κ +
        ((J.Jr.card + J.Jc.card - Fintype.card κ) +
          ((J.Jr.card + J.Jc.card - Fintype.card κ) - J.sJ))) :=
  fullSmithWit_price D hN c xs ys hc hx hy hdist _

/-- Smith data at `(r, p)` with wedge kills. -/
structure SmithJKDatum (G : BlockGeom) (Fr : Frame) (r p : ℕ) [Fact p.Prime] where
  N : ℕ
  D : PoleData Fr p N
  hN : N < p * p
  hc : ∀ a : (G.geometry r).C, (a : ℕ) < N
  hx : ∀ i, (G.geometry r).xs i < N
  hy : ∀ j, (G.geometry r).ys j < N
  hdist : ∀ i j, (((G.geometry r).xs i : ℕ) : ZMod p) ≠ (((G.geometry r).ys j : ℕ) : ZMod p)
  J : JBlockKill (schurW (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
    (G.geometry r).ys (hint_of_poleData D hN hc hx hy))

/-- The Smith price `2(|C| + m) - (m + σ + (σ - s_J))`. -/
noncomputable def SmithJKDatum.price {G : BlockGeom} {Fr : Frame} {r p : ℕ} [Fact p.Prime]
    (S : SmithJKDatum G Fr r p) : ℕ :=
  2 * Fintype.card ((G.geometry r).C ⊕ Fin (G.geometry r).k) -
    (Fintype.card (Fin (G.geometry r).k) +
      ((S.J.Jr.card + S.J.Jc.card - Fintype.card (Fin (G.geometry r).k)) +
        ((S.J.Jr.card + S.J.Jc.card - Fintype.card (Fin (G.geometry r).k)) - S.J.sJ)))

/-- **The Smith layer (debit 1) with wedge kills.** -/
noncomputable def smithJKLayer {G : BlockGeom} {Fr : Frame} {depth : ℕ}
    (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (S : ∀ r p : ℕ, [Fact p.Prime] → valid r p → SmithJKDatum G Fr r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (S r p h).price ≤ base r p) :
    DebitLayer G Fr depth :=
  smithLayer valid base
    (fun r p _ h => ⟨(S r p h).J.sJ,
      smithWitK_of_jblock (S r p h).D (S r p h).hN _ _ _ (S r p h).hc (S r p h).hx
        (S r p h).hy (S r p h).hdist (S r p h).J⟩)
    (fun r p _ h => by
      rw [smithWitK_of_jblock_price]
      exact hbase r p h)

end CatalanCore.Uniform.Content.UFMember
