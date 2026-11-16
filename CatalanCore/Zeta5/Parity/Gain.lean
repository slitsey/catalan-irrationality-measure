module

public import CatalanCore.Zeta5.Parity.WeightRaise
public import CatalanCore.Zeta5.Local.DirectBound
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Basis

@[expose] public section

/-!
# ZC26 in determinant form: independent radical vectors give a determinant gain

* `exists_completion`: `k` linearly independent vectors over `𝔽_p`, supported on the even rows,
  extend to an integral change of basis `Cm` of `p`-unit determinant that mixes only even rows
  and has the lifted vectors as its pivot rows.
* `zc26_gain_of_radical`: if the normalised Gram matrix `Gn` has base weights `θ`
  (`0` on even rows, `1/2` on odd rows) and `k` independent vectors `u_j` over `𝔽_p` on the even rows
  with `∑_s û_{j,s} Gn_{s,t} ≡ 0 (p)` for every even `t` (the left radical of the leading form),
  then `v_p^G(det G) ≥ 2 ∑ w + k`.
* `parity_gain_delta`: the same for the Hankel Gram matrix of a unimodular basis, in terms of
  `Δ_K`.
-/

open Finset Polynomial

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

/-- Completion of independent even vectors to an integral unimodular change of basis. -/
theorem exists_completion {ι : Type*} [Fintype ι] [DecidableEq ι] (Ev : ι → Prop)
    {k : ℕ} (u : Fin k → ι → ZMod p) (hu : LinearIndependent (ZMod p) u)
    (hsupp : ∀ j s, u j s ≠ 0 → Ev s) :
    ∃ (Cm : Matrix ι ι ℤ) (ρ : Fin k → ι), Function.Injective ρ ∧ (∀ j, Ev (ρ j)) ∧
      ¬ (p : ℤ) ∣ Cm.det ∧ (∀ i s, ¬ (Ev i ↔ Ev s) → Cm i s = 0) ∧
      ∀ j s, Cm (ρ j) s = (((u j s).val : ℕ) : ℤ) := by
  classical
  let E0 := {i // Ev i}
  let r : (ι → (ZMod p)) →ₗ[(ZMod p)] (E0 → (ZMod p)) := LinearMap.funLeft (ZMod p) (ZMod p) Subtype.val
  have hr : ∀ v i, r v i = v i.1 := fun v i => rfl
  have hind' : LinearIndependent (ZMod p) (fun j => r (u j)) := by
    rw [Fintype.linearIndependent_iff] at hu ⊢
    intro g hg
    apply hu g
    funext s
    by_cases hs : Ev s
    · have := congrFun hg ⟨s, hs⟩
      simpa [hr, Finset.sum_apply] using this
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : u j s = 0 := by by_contra h; exact hs (hsupp j s h)
      simp [this]
  set v : Fin k → (E0 → (ZMod p)) := fun j => r (u j) with hv
  have hvs : LinearIndepOn (ZMod p) id (Set.range v) := hind'.linearIndepOn_id
  let b := Module.Basis.extend hvs
  let σ := b.indexEquiv (Pi.basisFun (ZMod p) E0)
  let b' : Module.Basis E0 (ZMod p) (E0 → (ZMod p)) := b.reindex σ
  have hmem : ∀ j, v j ∈ hvs.extend (Set.subset_univ _) := fun j =>
    hvs.subset_extend (Set.subset_univ _) (Set.mem_range_self j)
  let ρ0 : Fin k → E0 := fun j => σ ⟨v j, hmem j⟩
  have hb'ρ : ∀ j, b' (ρ0 j) = v j := by
    intro j
    simp only [b', ρ0, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    rw [Module.Basis.coe_extend]
  -- the matrix of the basis
  let Ce : Matrix E0 E0 (ZMod p) := Matrix.of fun i s => b' i s
  have hdetCe : Ce.det ≠ 0 := by
    haveI := Module.Basis.invertibleToMatrix (Pi.basisFun (ZMod p) E0) b'
    have h1 : ((Pi.basisFun (ZMod p) E0).toMatrix b').det ≠ 0 :=
      (Matrix.isUnit_det_of_invertible _).ne_zero
    have h2 : (Pi.basisFun (ZMod p) E0).toMatrix b' = Ce.transpose := by
      ext i j
      simp [Module.Basis.toMatrix_apply, Ce]
    rwa [h2, Matrix.det_transpose] at h1
  let Cz : Matrix E0 E0 ℤ := Ce.map fun x => ((x.val : ℕ) : ℤ)
  have hCz : Cz.map (Int.castRingHom (ZMod p)) = Ce := by
    ext i s; simp [Cz]
  have hdetCz : ¬ (p : ℤ) ∣ Cz.det := by
    intro h
    have hmap : ((Cz.det : ℤ) : ZMod p) = Ce.det := by
      have := RingHom.map_det (Int.castRingHom (ZMod p)) Cz
      rw [RingHom.mapMatrix_apply, hCz] at this
      simpa using this
    apply hdetCe
    rw [← hmap]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  let Cm : Matrix ι ι ℤ := Matrix.of fun i s =>
    if h : Ev i ∧ Ev s then Cz ⟨i, h.1⟩ ⟨s, h.2⟩ else if i = s then 1 else 0
  let e : ι ≃ E0 ⊕ {i // ¬ Ev i} := (Equiv.sumCompl Ev).symm
  have hblocks : Matrix.reindex e e Cm = Matrix.fromBlocks Cz 0 0 1 := by
    refine Matrix.ext fun i s => ?_
    rcases i with i | i <;> rcases s with s | s
    · show Cm i.1 s.1 = Cz i s
      simp only [Cm, Matrix.of_apply]
      rw [dif_pos ⟨i.2, s.2⟩]
    · show Cm i.1 s.1 = 0
      have : (i : ι) ≠ s.1 := fun h => s.2 (h ▸ i.2)
      simp only [Cm, Matrix.of_apply]
      rw [dif_neg (fun h => s.2 h.2), if_neg this]
    · show Cm i.1 s.1 = 0
      have : (i : ι) ≠ s.1 := fun h => i.2 (h ▸ s.2)
      simp only [Cm, Matrix.of_apply]
      rw [dif_neg (fun h => i.2 h.1), if_neg this]
    · show Cm i.1 s.1 = (1 : Matrix {i // ¬ Ev i} {i // ¬ Ev i} ℤ) i s
      simp only [Cm, Matrix.of_apply, Matrix.one_apply]
      rw [dif_neg (fun h => i.2 h.1)]
      by_cases h : i = s
      · subst h; simp
      · have : (i : ι) ≠ s.1 := fun h' => h (Subtype.ext h')
        simp [this, h]
  have hdetCm : Cm.det = Cz.det := by
    rw [← Matrix.det_reindex_self e Cm, hblocks, Matrix.det_fromBlocks_zero₂₁]
    simp
  refine ⟨Cm, fun j => (ρ0 j).1, ?_, fun j => (ρ0 j).2, by rwa [hdetCm], ?_, ?_⟩
  · intro j j' h
    have h1 : ρ0 j = ρ0 j' := Subtype.ext h
    have h2 : b' (ρ0 j) = b' (ρ0 j') := by rw [h1]
    rw [hb'ρ, hb'ρ] at h2
    have h3 : r (u j) = r (u j') := h2
    -- `u j = u j'` since both are supported on the even rows
    have h4 : u j = u j' := by
      funext s
      by_cases hs : Ev s
      · exact congrFun h3 ⟨s, hs⟩
      · have a1 : u j s = 0 := by by_contra h; exact hs (hsupp j s h)
        have a2 : u j' s = 0 := by by_contra h; exact hs (hsupp j' s h)
        rw [a1, a2]
    exact hu.injective h4
  · intro i s hne
    simp only [Cm, Matrix.of_apply]
    rw [dif_neg (fun h => hne ⟨fun _ => h.2, fun _ => h.1⟩)]
    rw [if_neg]
    rintro rfl; exact hne Iff.rfl
  · intro j s
    simp only [Cm, Matrix.of_apply]
    by_cases hs : Ev s
    · rw [dif_pos ⟨(ρ0 j).2, hs⟩]
      simp only [Cz, Ce, Matrix.map_apply, Matrix.of_apply]
      have := congrFun (hb'ρ j) ⟨s, hs⟩
      rw [this]
      simp [hv, hr]
    · rw [dif_neg (fun h => hs h.2), if_neg (by rintro rfl; exact hs (ρ0 j).2)]
      have : u j s = 0 := by by_contra h; exact hs (hsupp j s h)
      simp [this]

/-- **ZC26 in determinant form.**  Independent vectors `u_j` over `𝔽_p` on the even rows that are
left radical vectors of the normalised Gram matrix modulo `p` (`∑_s û_{j,s} Gn_{s,t} ≡ 0` for every
even `t`) give `v_p^G(det G) ≥ 2 ∑ w + k`. -/
theorem zc26_gain_of_radical {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℚ[X]) (ν : ι → ℤ) (θ : ι → ℚ) (hθ : ∀ i, θ i = 0 ∨ θ i = 1 / 2)
    (hbase : ∀ i j, GV p (normGram (p := p) ν G i j) (θ i + θ j))
    (hsym : ∀ i j, G i j = G j i) {k : ℕ} (u : Fin k → ι → ZMod p)
    (hu : LinearIndependent (ZMod p) u) (hsupp : ∀ j s, u j s ≠ 0 → θ s = 0)
    (hrad : ∀ j t, θ t = 0 → GV p
      (∑ s, C ((((u j s).val : ℕ) : ℤ) : ℚ) * normGram (p := p) ν G s t) 1) :
    GV p G.det (2 * ∑ i, ((ν i : ℚ) + θ i) + k) := by
  classical
  obtain ⟨Cz, ρ, hρinj, hρev, hdet, hblkZ, hpiv⟩ :=
    exists_completion (p := p) (fun i => θ i = 0) u hu hsupp
  set Cm : Matrix ι ι ℚ := Cz.map (Int.castRingHom ℚ) with hCm
  have hdetQ : Cm.det = (Cz.det : ℚ) := by
    rw [hCm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; simp
  have hdet0 : Cz.det ≠ 0 := fun h => hdet (h ▸ dvd_zero _)
  have hdetne : Cm.det ≠ 0 := by rw [hdetQ]; exact_mod_cast hdet0
  have hunit : padicValRat p Cm.det = 0 := by rw [hdetQ]; exact padicValRat_int_eq_zero hdet
  have hint : ∀ i s, VG p (Cm i s) 0 := fun i s => by
    simpa [hCm] using VG.intCast (p := p) (Cz i s)
  have hblk : ∀ i s, θ i ≠ θ s → Cm i s = 0 := by
    intro i s hne
    have : ¬ ((θ i = 0) ↔ (θ s = 0)) := by
      intro h
      apply hne
      rcases hθ i with h1 | h1 <;> rcases hθ s with h2 | h2
      · rw [h1, h2]
      · rw [h1] at h; exact absurd (h.mp rfl) (by rw [h2]; norm_num)
      · rw [h2] at h; exact absurd (h.mpr rfl) (by rw [h1]; norm_num)
      · rw [h1, h2]
    simp [hCm, hblkZ i s this]
  set R : Finset ι := Finset.univ.image ρ with hR
  have hRcard : R.card = k := by
    rw [hR, Finset.card_image_of_injective _ hρinj]; simp
  have hRev : ∀ i ∈ R, θ i = 0 := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hρev j
  have hret : ∀ i ∈ R, ∀ j, θ j = 0 → GV p ((Cm.map (C : ℚ →+* ℚ[X]) * normGram (p := p) ν G *
      (Cm.map (C : ℚ →+* ℚ[X])).transpose) i j) 1 := by
    intro i hi j hj
    obtain ⟨j0, _, rfl⟩ := Finset.mem_image.mp hi
    have hM : (Cm.map (C : ℚ →+* ℚ[X]) * normGram (p := p) ν G *
        (Cm.map (C : ℚ →+* ℚ[X])).transpose) (ρ j0) j =
        ∑ t, (∑ s, C (Cm (ρ j0) s) * normGram (p := p) ν G s t) * C (Cm j t) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [hM]
    refine GV.sum _ fun t _ => ?_
    by_cases ht : θ t = 0
    · have h1 := hrad j0 t ht
      have h2 : ∀ s, (C (Cm (ρ j0) s) : ℚ[X]) = C ((((u j0 s).val : ℕ) : ℤ) : ℚ) := by
        intro s
        simp [hCm, hpiv j0 s]
      simp only [h2]
      have h3 : GV p (C (Cm j t)) 0 := GV.C (hint j t)
      have := h1.mul h3
      simpa using this
    · have : Cm j t = 0 := hblk j t (by rw [hj]; exact fun h => ht h.symm)
      rw [this, C_0, mul_zero]; exact GV.zero _
  have := zc26_weight_raise G ν θ R hθ hbase hsym Cm hdetne hunit hint hblk hRev hret
  rwa [hRcard] at this

/-! ### The Hankel form -/

lemma fract_half {w : ℚ} (hw : ∃ z : ℤ, w = z / 2) : Int.fract w = 0 ∨ Int.fract w = 1 / 2 := by
  obtain ⟨z, rfl⟩ := hw
  rcases Int.even_or_odd' z with ⟨q, rfl | rfl⟩
  · left
    have : ((2 * q : ℤ) : ℚ) / 2 = (q : ℚ) := by push_cast; ring
    rw [this, Int.fract_intCast]
  · right
    rw [Int.fract_eq_iff]
    refine ⟨by norm_num, by norm_num, q, ?_⟩
    push_cast; ring

/-- **ZC26 for the Hankel determinant.**  For a unimodular basis `E` with half-integral weights `w`
(`GV (μ_X(D_N⁶ E_a E_b / D_K)) ≥ w_a + w_b`), `k` independent vectors over `𝔽_p` on the rows of
integral weight that are left radical modulo `p` for the normalised Gram matrix
(`p^{-⌊w_s⌋-⌊w_t⌋} μ_X(...)`) give `v_p^G(Δ_K) ≥ 2 ∑ w + k`. -/
theorem parity_gain_delta (n : ℕ) (E : Fin (37 * n) → ℚ[X]) (hE : ∀ a, (E a).natDegree < 37 * n)
    (hdet : (coeffMat E).det ≠ 0) (hunit : padicValRat p (coeffMat E).det = 0)
    (w : Fin (37 * n) → ℚ) (hw : ∀ a, ∃ z : ℤ, w a = z / 2)
    (h : ∀ a b, GV p (μX (40 * n) (D (3 * n) ^ 6 * E a * E b)) (w a + w b))
    {k : ℕ} (u : Fin k → Fin (37 * n) → ZMod p) (hu : LinearIndependent (ZMod p) u)
    (hsupp : ∀ j s, u j s ≠ 0 → Int.fract (w s) = 0)
    (hrad : ∀ j t, Int.fract (w t) = 0 → GV p
      (∑ s, C ((((u j s).val : ℕ) : ℤ) : ℚ) * normGram (p := p) (fun i => ⌊w i⌋)
        (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)) s t) 1) :
    GV p (Δ n) (2 * ∑ a, w a + k) := by
  set G : Matrix (Fin (37 * n)) (Fin (37 * n)) ℚ[X] :=
    Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b) with hG
  have hθ : ∀ i, Int.fract (w i) = 0 ∨ Int.fract (w i) = 1 / 2 := fun i => fract_half (hw i)
  have hbase : ∀ i j, GV p (normGram (p := p) (fun i => ⌊w i⌋) G i j)
      (Int.fract (w i) + Int.fract (w j)) := by
    intro i j
    have h1 := GV.C_mul (VG.primePow (p := p) (-⌊w i⌋ - ⌊w j⌋)) (h i j)
    refine h1.mono (le_of_eq ?_)
    simp only [Int.fract]
    push_cast; ring
  have hsym : ∀ i j, G i j = G j i := fun i j => by
    simp only [hG, Matrix.of_apply]; congr 1; ring
  have key := zc26_gain_of_radical G (fun i => ⌊w i⌋) (fun i => Int.fract (w i)) hθ hbase hsym
    u hu hsupp hrad
  have hsum : ∑ i, ((⌊w i⌋ : ℚ) + Int.fract (w i)) = ∑ i, w i :=
    Finset.sum_congr rfl fun i _ => by simp [Int.floor_add_fract]
  rw [hsum] at key
  have hbc := det_basis_change n E hE
  rw [← hG] at hbc
  have hΔ : Δ n = C (((coeffMat E).det ^ 2)⁻¹) * (C ((coeffMat E).det ^ 2) * Δ n) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hdet), C_1, one_mul]
  rw [hΔ, ← hbc]
  have hu' : VG p (((coeffMat E).det ^ 2)⁻¹) 0 := by
    refine (VG_inv_unit (p := p) (pow_ne_zero _ hdet) ?_)
    rw [padicValRat.pow, hunit]; simp
  simpa using GV.C_mul hu' key

end Apery
