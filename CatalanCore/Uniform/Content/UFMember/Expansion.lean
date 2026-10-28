module

public import CatalanCore.Uniform.Content.UFMember.KillMom

@[expose] public section

/-!
# UF member package: (S7) on `J × J` from PER-NODE moment expansions

The displacement numerator is a wedge of one-node moments.  If every border node of the joint
type `J` has moments on ONE common direction `(a_J, p b_J)` to first order, with second-order
corrections `(a¹, b¹)`,

  `α_z = λ_z (a_J + p a¹_z) + O(p²)`,   `β_z = p λ_z (b_J + p b¹_z) + O(p³)`   (rows and columns),

then (`wedge_expansion`)

  `α_z β'_y - β_z α'_y = p² λ_z λ'_y (Φ(y) - Φ(z)) + O(p³)`,   `Φ(t) = a_J b¹_t - b_J a¹_t`.

So the `J`-block hypothesis `hnum` of `JBlockCauchy.of_moments` follows from the per-node
expansions plus ONE identification `Φ(t) ≡ det Q · h(t̄) + const` with `h` the derived-frame
function (`hnum_of_expansion`).  This is the exact form of (S6)–(S7) left to prove per frame:
the first-order direction is the transport statement (equal joint type), and `Φ` carries the
weights `v(c) = B²(w(c) - w_J) + γ_J - γ(c)`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMember

/-- **The wedge of two expanded moment pairs.** -/
theorem wedge_expansion {R : Type*} [CommRing R] (π : R)
    (αz βz αy βy lz ly aJ bJ a1z b1z a1y b1y E1 E2 E3 E4 : R)
    (hαz : αz = lz * (aJ + π * a1z) + π ^ 2 * E1)
    (hβz : βz = π * lz * (bJ + π * b1z) + π ^ 3 * E2)
    (hαy : αy = ly * (aJ + π * a1y) + π ^ 2 * E3)
    (hβy : βy = π * ly * (bJ + π * b1y) + π ^ 3 * E4) :
    αz * βy - βz * αy = π ^ 2 * (lz * ly * ((aJ * b1y - bJ * a1y) - (aJ * b1z - bJ * a1z)) +
      π * (lz * ly * a1z * b1y + lz * aJ * E4 + π * lz * a1z * E4 + E1 * ly * bJ +
        π * E1 * ly * b1y + π ^ 2 * E1 * E4 -
        (lz * ly * b1z * a1y + lz * bJ * E3 + π * lz * b1z * E3 + E2 * ly * aJ +
          π * E2 * ly * a1y + π ^ 2 * E2 * E3))) := by
  rw [hαz, hβz, hαy, hβy]
  ring

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The row moments `α_z`, `β_z` of the scaled lift. -/
noncomputable def rowMomA (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (z : κ) : (LocRing p)[X] :=
  A.toBlocks₁₁.det - ∑ i, A.toBlocks₂₁ z i * ∑ k, A.toBlocks₁₁.adjugate i k

noncomputable def rowMomB (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (Fr : Frame) (c : ι → ℕ)
    (xs : κ → ℕ) (z : κ) : (LocRing p)[X] :=
  A.toBlocks₁₁.det * PF p Fr (xs z) -
    ∑ i, A.toBlocks₂₁ z i * ∑ k, A.toBlocks₁₁.adjugate i k * PF p Fr (c k)

/-- The column moments `α'_y`, `β'_y` of the scaled lift. -/
noncomputable def colMomA (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (y : κ) : (LocRing p)[X] :=
  A.toBlocks₁₁.det - ∑ j, (∑ k, A.toBlocks₁₁.adjugate k j) * A.toBlocks₁₂ j y

noncomputable def colMomB (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (Fr : Frame) (c : ι → ℕ)
    (ys : κ → ℕ) (y : κ) : (LocRing p)[X] :=
  A.toBlocks₁₁.det * PF p Fr (ys y) -
    ∑ j, (∑ k, PF p Fr (c k) * A.toBlocks₁₁.adjugate k j) * A.toBlocks₁₂ j y

lemma dispNum_eq_moments (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (c : ι → ℕ)
    (xs ys : κ → ℕ) (z y : κ) :
    dispNum A Fr c xs ys z y =
      rowMomA A z * colMomB A Fr c ys y - rowMomB A Fr c xs z * colMomA A y := rfl

/-- Per-node second-order moment expansion along a common direction `(a_J, b_J)`. -/
structure MomentExp (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (Fr : Frame) (c : ι → ℕ)
    (xs ys : κ → ℕ) (Jr Jc : Finset κ) where
  aJ : (LocRing p)[X]
  bJ : (LocRing p)[X]
  lam : κ → (LocRing p)[X]
  lam' : κ → (LocRing p)[X]
  a1 : κ → (LocRing p)[X]
  b1 : κ → (LocRing p)[X]
  a1' : κ → (LocRing p)[X]
  b1' : κ → (LocRing p)[X]
  E1 : κ → (LocRing p)[X]
  E2 : κ → (LocRing p)[X]
  E3 : κ → (LocRing p)[X]
  E4 : κ → (LocRing p)[X]
  hαr : ∀ z ∈ Jr, rowMomA A z =
    lam z * (aJ + Polynomial.C ((p : ℕ) : LocRing p) * a1 z) +
      Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * E1 z
  hβr : ∀ z ∈ Jr, rowMomB A Fr c xs z =
    Polynomial.C ((p : ℕ) : LocRing p) * lam z *
        (bJ + Polynomial.C ((p : ℕ) : LocRing p) * b1 z) +
      Polynomial.C ((p : ℕ) : LocRing p) ^ 3 * E2 z
  hαc : ∀ y ∈ Jc, colMomA A y =
    lam' y * (aJ + Polynomial.C ((p : ℕ) : LocRing p) * a1' y) +
      Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * E3 y
  hβc : ∀ y ∈ Jc, colMomB A Fr c ys y =
    Polynomial.C ((p : ℕ) : LocRing p) * lam' y *
        (bJ + Polynomial.C ((p : ℕ) : LocRing p) * b1' y) +
      Polynomial.C ((p : ℕ) : LocRing p) ^ 3 * E4 y

/-- **`hnum` from the per-node expansions and the identification of `Φ`.** -/
theorem hnum_of_expansion (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (c : ι → ℕ)
    (xs ys : κ → ℕ) (Jr Jc : Finset κ) (M : MomentExp A Fr c xs ys Jr Jc)
    (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p)) (mR mC : κ → RatFunc (ZMod p))
    (hid : ∀ z ∈ Jr, ∀ y ∈ Jc, phiP p (M.lam z * M.lam' y *
      ((M.aJ * M.b1' y - M.bJ * M.a1' y) - (M.aJ * M.b1 z - M.bJ * M.a1 z))) =
        phiP p A.toBlocks₁₁.det * (mR z * mC y * (hDer Ret v (ys y) - hDer Ret v (xs z)))) :
    ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum A Fr c xs ys z y = Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det *
        (mR z * mC y * (hDer Ret v (ys y) - hDer Ret v (xs z))) := by
  intro z hz y hy
  set π : (LocRing p)[X] := Polynomial.C ((p : ℕ) : LocRing p)
  have h := wedge_expansion π _ _ _ _ (M.lam z) (M.lam' y) M.aJ M.bJ (M.a1 z) (M.b1 z) (M.a1' y)
    (M.b1' y) (M.E1 z) (M.E2 z) (M.E3 y) (M.E4 y) (M.hαr z hz) (M.hβr z hz) (M.hαc y hy)
    (M.hβc y hy)
  refine ⟨_, by rw [dispNum_eq_moments]; exact h, ?_⟩
  have hπ0 : phiP p π = 0 := (phiP_eq_zero_iff p π).2 dvd_rfl
  rw [map_add, map_mul (phiP p) π, hπ0, zero_mul, add_zero]
  exact hid z hz y hy

/-- **Column wedge kills from the expansions.**  For an outside column `t` with
`β'_t = p b_t`, the numerator against a `J` row is `p λ_z (a_J b_t - b_J α'_t) + O(p²)`: the
first-layer wedge of `t` with the direction of `J`. -/
theorem hTC_of_expansion (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (c : ι → ℕ)
    (xs ys : κ → ℕ) (Jr Jc : Finset κ) (M : MomentExp A Fr c xs ys Jr Jc)
    (TC : Finset κ) (bt : κ → (LocRing p)[X])
    (hbt : ∀ t ∈ TC, colMomB A Fr c ys t = Polynomial.C ((p : ℕ) : LocRing p) * bt t)
    (mR : κ → RatFunc (ZMod p)) (wC : κ → RatFunc (ZMod p))
    (hid : ∀ t ∈ TC, ∀ z ∈ Jr,
      phiP p (M.lam z * (M.aJ * bt t - M.bJ * colMomA A t)) =
        phiP p A.toBlocks₁₁.det * (mR z * wC t)) :
    ∀ t ∈ TC, ∀ z ∈ Jr, ∃ q : (LocRing p)[X],
      dispNum A Fr c xs ys z t = Polynomial.C ((p : ℕ) : LocRing p) * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det * (mR z * wC t) := by
  intro t ht z hz
  set π : (LocRing p)[X] := Polynomial.C ((p : ℕ) : LocRing p)
  refine ⟨M.lam z * (M.aJ * bt t - M.bJ * colMomA A t) +
    π * (M.lam z * M.a1 z * bt t + π * M.E1 z * bt t - M.lam z * M.b1 z * colMomA A t -
      π * M.E2 z * colMomA A t), ?_, ?_⟩
  · rw [dispNum_eq_moments, M.hαr z hz, M.hβr z hz, hbt t ht]
    ring
  · have hπ0 : phiP p π = 0 := (phiP_eq_zero_iff p π).2 dvd_rfl
    rw [map_add, map_mul (phiP p) π, hπ0, zero_mul, add_zero]
    exact hid t ht z hz

/-- **Row wedge kills from the expansions** (symmetric). -/
theorem hTR_of_expansion (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (c : ι → ℕ)
    (xs ys : κ → ℕ) (Jr Jc : Finset κ) (M : MomentExp A Fr c xs ys Jr Jc)
    (TR : Finset κ) (bt : κ → (LocRing p)[X])
    (hbt : ∀ t ∈ TR, rowMomB A Fr c xs t = Polynomial.C ((p : ℕ) : LocRing p) * bt t)
    (mC : κ → RatFunc (ZMod p)) (wR : κ → RatFunc (ZMod p))
    (hid : ∀ t ∈ TR, ∀ y ∈ Jc,
      phiP p (M.lam' y * (rowMomA A t * M.bJ - bt t * M.aJ)) =
        phiP p A.toBlocks₁₁.det * (wR t * mC y)) :
    ∀ t ∈ TR, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum A Fr c xs ys t y = Polynomial.C ((p : ℕ) : LocRing p) * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det * (wR t * mC y) := by
  intro t ht y hy
  set π : (LocRing p)[X] := Polynomial.C ((p : ℕ) : LocRing p)
  refine ⟨M.lam' y * (rowMomA A t * M.bJ - bt t * M.aJ) +
    π * (rowMomA A t * M.lam' y * M.b1' y + π * rowMomA A t * M.E4 y -
      bt t * M.lam' y * M.a1' y - π * bt t * M.E3 y), ?_, ?_⟩
  · rw [dispNum_eq_moments, M.hαc y hy, M.hβc y hy, hbt t ht]
    ring
  · have hπ0 : phiP p π = 0 := (phiP_eq_zero_iff p π).2 dvd_rfl
    rw [map_add, map_mul (phiP p) π, hπ0, zero_mul, add_zero]
    exact hid t ht y hy

/-- The once-divided prefix value `p F(a)`. -/
noncomputable def PF1 (p : ℕ) [Fact p.Prime] (Fr : Frame) (a : ℕ) : (LocRing p)[X] :=
  Polynomial.C (Hybrid.liftQ p ((p : ℚ) * Fp Fr a))

lemma p_Fp_mem (D : PoleData Fr p N) {a : ℕ} (ha : a < N) : (p : ℚ) * Fp Fr a ∈ LocRing p := by
  unfold Fp
  rw [Finset.mul_sum]
  exact Subring.sum_mem _ fun k hk => by
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.1 hk
    exact D.delta_mem k (by omega) (by omega)

/-- `p² F(a) = p · (p F(a))` in `ℤ_(p)[X]`. -/
lemma PF_eq (D : PoleData Fr p N) {a : ℕ} (ha : a < N) :
    PF p Fr a = Polynomial.C ((p : ℕ) : LocRing p) * PF1 p Fr a := by
  unfold PF PF1
  rw [← C_mul]
  congr 1
  apply Subtype.ext
  push_cast
  rw [Hybrid.liftQ_val (show (p : ℚ) ^ 2 * Fp Fr a ∈ S p from sq_Fp_mem D ha),
    Hybrid.liftQ_val (show (p : ℚ) * Fp Fr a ∈ S p from p_Fp_mem D ha)]
  ring

/-- The `β` moments are divisible by `p` (the prefixes carry at most one pole). -/
theorem rowMomB_eq (D : PoleData Fr p N) (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (c : ι → ℕ) (xs : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (z : κ) :
    rowMomB A Fr c xs z = Polynomial.C ((p : ℕ) : LocRing p) *
      (A.toBlocks₁₁.det * PF1 p Fr (xs z) -
        ∑ i, A.toBlocks₂₁ z i * ∑ k, A.toBlocks₁₁.adjugate i k * PF1 p Fr (c k)) := by
  unfold rowMomB
  rw [PF_eq D (hx z)]
  simp_rw [PF_eq D (hc _)]
  simp only [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem colMomB_eq (D : PoleData Fr p N) (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (c : ι → ℕ) (ys : κ → ℕ) (hc : ∀ a, c a < N) (hy : ∀ j, ys j < N) (y : κ) :
    colMomB A Fr c ys y = Polynomial.C ((p : ℕ) : LocRing p) *
      (A.toBlocks₁₁.det * PF1 p Fr (ys y) -
        ∑ j, (∑ k, PF1 p Fr (c k) * A.toBlocks₁₁.adjugate k j) * A.toBlocks₁₂ j y) := by
  unfold colMomB
  rw [PF_eq D (hy y)]
  simp_rw [PF_eq D (hc _)]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring

/-- **Expansions from the first-order (transport) congruences alone.**  If the `J` rows and
columns have moments on one direction modulo `p` (`α ≡ λ a_J`) and `p²` (`β ≡ p λ b_J`), the
second-order coefficients are DEFINED as the quotients (`E = 0`); `hnum_of_expansion` then needs
only the identification of `Φ` built from these quotients. -/
noncomputable def MomentExp.ofFirstOrder (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (c : ι → ℕ) (xs ys : κ → ℕ) (Jr Jc : Finset κ) (aJ bJ : (LocRing p)[X])
    (lam lam' : κ → (LocRing p)[X])
    (hαr : ∀ z ∈ Jr, Polynomial.C ((p : ℕ) : LocRing p) ∣ rowMomA A z - lam z * aJ)
    (hβr : ∀ z ∈ Jr, Polynomial.C ((p : ℕ) : LocRing p) ^ 2 ∣
      rowMomB A Fr c xs z - Polynomial.C ((p : ℕ) : LocRing p) * lam z * bJ)
    (hαc : ∀ y ∈ Jc, Polynomial.C ((p : ℕ) : LocRing p) ∣ colMomA A y - lam' y * aJ)
    (hβc : ∀ y ∈ Jc, Polynomial.C ((p : ℕ) : LocRing p) ^ 2 ∣
      colMomB A Fr c ys y - Polynomial.C ((p : ℕ) : LocRing p) * lam' y * bJ)
    (hl : ∀ z ∈ Jr, IsUnit (lam z)) (hl' : ∀ y ∈ Jc, IsUnit (lam' y)) :
    MomentExp A Fr c xs ys Jr Jc := by
  classical
  set π : (LocRing p)[X] := Polynomial.C ((p : ℕ) : LocRing p)
  let qa : κ → (LocRing p)[X] := fun z => if h : z ∈ Jr then (hαr z h).choose else 0
  let qb : κ → (LocRing p)[X] := fun z => if h : z ∈ Jr then (hβr z h).choose else 0
  let qa' : κ → (LocRing p)[X] := fun y => if h : y ∈ Jc then (hαc y h).choose else 0
  let qb' : κ → (LocRing p)[X] := fun y => if h : y ∈ Jc then (hβc y h).choose else 0
  let inv : κ → (LocRing p)[X] := fun z => if h : z ∈ Jr then ((hl z h).unit⁻¹ : _) else 0
  let inv' : κ → (LocRing p)[X] := fun y => if h : y ∈ Jc then ((hl' y h).unit⁻¹ : _) else 0
  have hinv : ∀ z ∈ Jr, lam z * inv z = 1 := fun z h => by simp [inv, h]
  have hinv' : ∀ y ∈ Jc, lam' y * inv' y = 1 := fun y h => by simp [inv', h]
  exact
  { aJ := aJ
    bJ := bJ
    lam := lam
    lam' := lam'
    a1 := fun z => inv z * qa z
    b1 := fun z => inv z * qb z
    a1' := fun y => inv' y * qa' y
    b1' := fun y => inv' y * qb' y
    E1 := fun _ => 0
    E2 := fun _ => 0
    E3 := fun _ => 0
    E4 := fun _ => 0
    hαr := by
      intro z h
      have hs := (hαr z h).choose_spec
      have e : qa z = (hαr z h).choose := by simp [qa, h]
      have e2 : lam z * (aJ + π * (inv z * qa z)) =
          lam z * aJ + π * ((lam z * inv z) * qa z) := by ring
      rw [mul_zero, add_zero, e2, hinv z h, one_mul, e, ← hs]
      ring
    hβr := by
      intro z h
      have hs := (hβr z h).choose_spec
      have e : qb z = (hβr z h).choose := by simp [qb, h]
      have e2 : π * lam z * (bJ + π * (inv z * qb z)) =
          π * lam z * bJ + π ^ 2 * ((lam z * inv z) * qb z) := by ring
      rw [mul_zero, add_zero, e2, hinv z h, one_mul, e, ← hs]
      ring
    hαc := by
      intro y h
      have hs := (hαc y h).choose_spec
      have e : qa' y = (hαc y h).choose := by simp [qa', h]
      have e2 : lam' y * (aJ + π * (inv' y * qa' y)) =
          lam' y * aJ + π * ((lam' y * inv' y) * qa' y) := by ring
      rw [mul_zero, add_zero, e2, hinv' y h, one_mul, e, ← hs]
      ring
    hβc := by
      intro y h
      have hs := (hβc y h).choose_spec
      have e : qb' y = (hβc y h).choose := by simp [qb', h]
      have e2 : π * lam' y * (bJ + π * (inv' y * qb' y)) =
          π * lam' y * bJ + π ^ 2 * ((lam' y * inv' y) * qb' y) := by ring
      rw [mul_zero, add_zero, e2, hinv' y h, one_mul, e, ← hs]
      ring }

/-- **`hnum` from first-order data, no units needed.**  Write the `J` moments as
`α_z = λ_z a_J + p qa_z`, `β_z = p λ_z b_J + p² qb_z` (rows; primed for columns), with `λ`
arbitrary (in practice primitive, e.g. products of the other fibers' core determinants).  Then
`α_z β'_y - β_z α'_y = p² (λ_z Ψ'(y) - λ'_y Ψ(z)) + p³ (qa_z qb'_y - qb_z qa'_y)` with
`Ψ(t) = a_J qb_t - b_J qa_t`, and `hnum` holds as soon as `λ_z Ψ'(y) - λ'_y Ψ(z)` reduces to
`det Q · m_z m'_y (h(y) - h(z))`. -/
theorem hnum_of_firstOrder (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (c : ι → ℕ)
    (xs ys : κ → ℕ) (Jr Jc : Finset κ) (aJ bJ : (LocRing p)[X])
    (lam lam' qa qb qa' qb' : κ → (LocRing p)[X])
    (hαr : ∀ z ∈ Jr, rowMomA A z = lam z * aJ + Polynomial.C ((p : ℕ) : LocRing p) * qa z)
    (hβr : ∀ z ∈ Jr, rowMomB A Fr c xs z =
      Polynomial.C ((p : ℕ) : LocRing p) * lam z * bJ +
        Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * qb z)
    (hαc : ∀ y ∈ Jc, colMomA A y = lam' y * aJ + Polynomial.C ((p : ℕ) : LocRing p) * qa' y)
    (hβc : ∀ y ∈ Jc, colMomB A Fr c ys y =
      Polynomial.C ((p : ℕ) : LocRing p) * lam' y * bJ +
        Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * qb' y)
    (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p)) (mR mC : κ → RatFunc (ZMod p))
    (hid : ∀ z ∈ Jr, ∀ y ∈ Jc,
      phiP p (lam z * (aJ * qb' y - bJ * qa' y) - lam' y * (aJ * qb z - bJ * qa z)) =
        phiP p A.toBlocks₁₁.det * (mR z * mC y * (hDer Ret v (ys y) - hDer Ret v (xs z)))) :
    ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum A Fr c xs ys z y = Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det *
        (mR z * mC y * (hDer Ret v (ys y) - hDer Ret v (xs z))) := by
  intro z hz y hy
  set π : (LocRing p)[X] := Polynomial.C ((p : ℕ) : LocRing p)
  refine ⟨(lam z * (aJ * qb' y - bJ * qa' y) - lam' y * (aJ * qb z - bJ * qa z)) +
    π * (qa z * qb' y - qb z * qa' y), ?_, ?_⟩
  · rw [dispNum_eq_moments, hαr z hz, hβr z hz, hαc y hy, hβc y hy]
    ring
  · have hπ0 : phiP p π = 0 := (phiP_eq_zero_iff p π).2 dvd_rfl
    rw [map_add, map_mul (phiP p) π, hπ0, zero_mul, add_zero]
    exact hid z hz y hy

end CatalanCore.Uniform.Content.UFMember
