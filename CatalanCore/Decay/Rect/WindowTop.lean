module

public import CatalanCore.Decay.Rect.WindowR
public import CatalanCore.Decay.Rect.EnergyPerturb
public import CatalanCore.Rect.Geometry

@[expose] public section

/-!
# Window for DO's second member `afterTop r m` (MEM2D)

`afterTop r m` has common nodes `[0,r) ∪ {b}`, `b = r + 2m`, and the same extra nodes as
`after r m`.  Its `Full` minors are the minors of the pattern `(r, m+1)` (extra pair `(r+2m,
r+2m+1)` kept) with the column node `r+2m+1` moved to `r+2m`; by `rectEnergy_perturb` this costs
`O(r)` in the energy.  The minors that omit `b` are minors of the pattern `(r, m)`.
-/

open Finset Polynomial

namespace CatalanCore.Rect

variable (Fr : Frame) (r m : ℕ)

/-- the common nodes of member 2, indexed by `Fin (r+1)`: `0,…,r-1` and `b = r+2m`. -/
def cT : Fin (r + 1) → ℕ := fun a => if (a : ℕ) < r then (a : ℕ) else r + 2 * m

theorem cT_inj : Function.Injective (cT r m) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  simp only [cT] at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem cT_ne_row (a : Fin (r + 1)) (j : Fin m) : cT r m a ≠ r + 2 * (j : ℕ) := by
  have := a.isLt; have := j.isLt
  simp only [cT]; split_ifs <;> omega

theorem cT_ne_col (a : Fin (r + 1)) (j : Fin m) : cT r m a ≠ r + 2 * (j : ℕ) + 1 := by
  have := a.isLt; have := j.isLt
  simp only [cT]; split_ifs <;> omega

theorem det_full_afterTop :
    (afterTop r m).fullPolyG Fr = (FullN Fr (cT r m) (fun i : Fin m => r + 2 * (i : ℕ))
      (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  have hk : (afterTop r m).k = m := after_k r m
  let f : Fin (r + 1) → ↥(afterTop r m).C := fun a => ⟨cT r m a, by
    simp only [afterTop, cT, mem_insert, mem_range]
    split_ifs with h
    · exact Or.inr h
    · exact Or.inl rfl⟩
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => cT_inj r m (congrArg Subtype.val h), ?_⟩
    rw [Fintype.card_fin, Fintype.card_coe, afterTop_card_C]
  let eι : Fin (r + 1) ≃ ↥(afterTop r m).C := Equiv.ofBijective f hf
  unfold Geometry.fullPolyG Geometry.Full
  refine (det_fullN_reindex Fr (fun a : (afterTop r m).C => (a : ℕ)) (afterTop r m).xs
    (afterTop r m).ys (cT r m) (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) eι (finCongr hk).symm (fun _ => rfl)
    (fun i => by rw [afterTop_xs]; simp) (fun i => by rw [afterTop_ys]; simp) (X : ℚ[X])).symm

theorem aeval_fullPolyTop (x : ℝ) :
    Polynomial.aeval x ((afterTop r m).fullPolyG Fr)
      = (FullN Fr (cT r m) (fun i : Fin m => r + 2 * (i : ℕ))
          (fun i : Fin m => r + 2 * (i : ℕ) + 1) x).det := by
  rw [det_full_afterTop]
  have h2 : (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ)
      (FullN Fr (cT r m) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det
      = ((FullN Fr (cT r m) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).map
          (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ)).det :=
    map_det' (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ).toRingHom _
  rw [h2, map_fullN]

/-- row / column node of the index set `S ⊕ Fin m`. -/
def rowN (S : Finset (Fin (r + 1))) : (↥S ⊕ Fin m) → ℕ :=
  Sum.elim (fun a => cT r m a.1) (fun j => r + 2 * (j : ℕ))
def colN (S : Finset (Fin (r + 1))) : (↥S ⊕ Fin m) → ℕ :=
  Sum.elim (fun a => cT r m a.1) (fun j => r + 2 * (j : ℕ) + 1)

theorem rowN_inj (S : Finset (Fin (r + 1))) : Function.Injective (rowN r m S) := by
  intro p q h
  rcases p with a | i <;> rcases q with b | j <;> simp only [rowN, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Subtype.ext (cT_inj r m h))
  · exact absurd h (cT_ne_row r m a.1 j)
  · exact absurd h.symm (cT_ne_row r m b.1 i)
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem colN_inj (S : Finset (Fin (r + 1))) : Function.Injective (colN r m S) := by
  intro p q h
  rcases p with a | i <;> rcases q with b | j <;> simp only [colN, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Subtype.ext (cT_inj r m h))
  · exact absurd h (cT_ne_col r m a.1 j)
  · exact absurd h.symm (cT_ne_col r m b.1 i)
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem fullNS_top_eq (S : Finset (Fin (r + 1))) :
    FullN Fr (fun a : ↥S => cT r m a.1) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)
      = Matrix.of fun p q => Fr.Tent (rowN r m S p) (colN r m S q) := by
  ext p q
  rcases p with a | i <;> rcases q with b | j
  · simp only [FullN, Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, blkA, Matrix.of_apply, rowN, colN, Sum.elim_inl, Frame.Tent, smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp [add_comm]
    · have h2 : cT r m a.1 ≠ cT r m b.1 := fun h => hab (Subtype.ext (cT_inj r m h))
      simp [hab, h2]
  · simp only [FullN, Blk, Matrix.fromBlocks_apply₁₂, blkB, Matrix.of_apply, rowN, colN,
      Sum.elim_inl, Sum.elim_inr, Frame.Tent]
    simp [cT_ne_col r m a.1 j]
  · simp only [FullN, Blk, Matrix.fromBlocks_apply₂₁, blkC, Matrix.of_apply, rowN, colN,
      Sum.elim_inl, Sum.elim_inr, Frame.Tent]
    simp [(cT_ne_row r m b.1 i).symm]
  · simp only [FullN, Blk, Matrix.fromBlocks_apply₂₂, blkD, Matrix.of_apply, rowN, colN,
      Sum.elim_inr, Frame.Tent]
    have h2 : r + 2 * (i : ℕ) ≠ r + 2 * (j : ℕ) + 1 := by omega
    simp [h2]

end CatalanCore.Rect

namespace CatalanCore

open Decay

/-- Theorem N for a pattern given as an arbitrary finite index set. -/
theorem det_pattern_le {Fr : Frame} (hFr : Fr.DecayOK') {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {N0 : ℕ} {R : ℝ} (hR : (N0 : ℝ) ≤ R)
    {P : Type} [Fintype P] [DecidableEq P] (rowN colN : P → ℕ) (hr : Function.Injective rowN)
    (hc : Function.Injective colN) {k : ℕ} (eq : P ≃ Fin k) {Nn : ℕ} (hkN : k ≤ Nn) {T : ℝ}
    (hE : Frame.RectEnergy Fr N0 k e m0 (max (Real.log Fr.Aco) 0) T
      (fun i => rowN (eq.symm i)) (fun i => colN (eq.symm i))) :
    |(Matrix.of fun p q : P => Fr.Tent (rowN p) (colN q)).det|
      ≤ Real.exp (T + Nn * Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
          + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1))) := by
  have hdet : (Matrix.of fun p q : P => Fr.Tent (rowN p) (colN q)).det
      = (Matrix.of fun i j : Fin k => Fr.Tent (rowN (eq.symm i)) (colN (eq.symm j))).det :=
    (Matrix.det_submatrix_equiv_self eq.symm _).symm
  rw [hdet]
  exact Frame.theoremN_rect hFr he0 he1 hm0xs hm0μ hkN hR
    (fun a b h => eq.symm.injective (hr h)) (fun a b h => eq.symm.injective (hc h)) hE

theorem term_arith {t cc r : ℝ} (hq : |t| * Real.exp (cc * r) ≤ 1) (n : ℕ) {X Y D : ℝ}
    (hD : D ≤ Real.exp (cc * r) ^ n * Real.exp X) (hXY : X ≤ Y) (hD0 : 0 ≤ D) :
    |t| ^ n * D ≤ Real.exp Y := by
  calc |t| ^ n * D ≤ |t| ^ n * (Real.exp (cc * r) ^ n * Real.exp X) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (|t| * Real.exp (cc * r)) ^ n * Real.exp X := by rw [mul_pow]; ring
    _ ≤ 1 * Real.exp X := mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hq) (Real.exp_pos _).le
    _ ≤ Real.exp Y := by rw [one_mul]; exact Real.exp_le_exp.2 hXY


/-- the embedding of the member-2 pattern with `b` kept into the `(r, m+1)` index set. -/
def phiTop (r m : ℕ) (S : Finset (Fin (r + 1))) : (↥S ⊕ Fin m) → Fin (r + m + 1) :=
  Sum.elim (fun a => if h : (a.1 : ℕ) < r then ⟨a.1, by omega⟩ else ⟨r + m, by omega⟩)
    (fun j => ⟨r + (j : ℕ), by have := j.isLt; omega⟩)

theorem phiTop_x (r m : ℕ) (S : Finset (Fin (r + 1))) (p : ↥S ⊕ Fin m) :
    xnode r ((phiTop r m S p : Fin (r + m + 1)) : ℕ) = Rect.rowN r m S p := by
  rcases p with a | j
  · by_cases h : (a.1 : ℕ) < r
    · simp [phiTop, Rect.rowN, Rect.cT, h, xnode]
    · simp [phiTop, Rect.rowN, Rect.cT, h, xnode]
  · simp [phiTop, Rect.rowN, xnode]

theorem phiTop_y_inl (r m : ℕ) (S : Finset (Fin (r + 1))) (a : ↥S) :
    ynode r ((phiTop r m S (Sum.inl a) : Fin (r + m + 1)) : ℕ)
      = Rect.colN r m S (Sum.inl a) + (if (a.1 : ℕ) < r then 0 else 1) := by
  by_cases h : (a.1 : ℕ) < r
  · simp [phiTop, Rect.colN, Rect.cT, h, ynode]
  · simp [phiTop, Rect.colN, Rect.cT, h, ynode]

theorem phiTop_y_inr (r m : ℕ) (S : Finset (Fin (r + 1))) (j : Fin m) :
    ynode r ((phiTop r m S (Sum.inr j) : Fin (r + m + 1)) : ℕ)
      = Rect.colN r m S (Sum.inr j) := by
  simp [phiTop, Rect.colN, ynode]


/-- Member-2 term bound when `b` is kept: pattern `(r, m+1)` with one column node moved. -/
theorem term_top_in {Fr : Frame} (hFr : Fr.DecayOK') {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {r m N0 : ℕ} {R : ℝ}
    (hR : (N0 : ℝ) ≤ R) {T1 cc : ℝ} {t : ℝ} (hq : |t| * Real.exp (cc * r) ≤ 1)
    (hEn1 : ∀ (k : ℕ) (s : Fin k → Fin (r + m + 1)), Function.Injective s →
        (∀ b : Fin (r + m + 1), r ≤ (b : ℕ) → ∃ i, s i = b) →
        Frame.RectEnergy Fr N0 k e m0 (max (Real.log Fr.Aco) 0)
          (T1 + r * (((r : ℝ) + m + 1) - k) * cc)
          (fun i => xnode r (s i)) (fun i => ynode r (s i)))
    (S : Finset (Fin (r + 1))) (hl : Fin.last r ∈ S) :
    |t| ^ (Fintype.card (Fin (r + 1)) - S.card) *
        |(Rect.FullN Fr (fun a : ↥S => Rect.cT r m a.1) (fun i : Fin m => r + 2 * (i : ℕ))
          (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)).det|
      ≤ Real.exp (T1 + ((r : ℝ) + m + 1) * (Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
          + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)) + Real.log (4 * (1 + 1 / m0)))) := by
  classical
  set L0 : ℝ := Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
      + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)) with hL0
  set κ : ℝ := Real.log (4 * (1 + 1 / m0)) with hκ
  have hκ0 : 0 ≤ κ := Real.log_nonneg (by
    have : 0 ≤ 1 / m0 := by positivity
    linarith)
  have hScard : S.card ≤ r + 1 := by simpa using Finset.card_le_univ S
  set k : ℕ := S.card + m with hk
  have hcard : Fintype.card (↥S ⊕ Fin m) = k := by simp [Fintype.card_sum, hk]
  let eq : (↥S ⊕ Fin m) ≃ Fin k := Fintype.equivFinOfCardEq hcard
  set s' : Fin k → Fin (r + m + 1) := fun i => phiTop r m S (eq.symm i) with hs'
  have hs'inj : Function.Injective s' := by
    intro a b h
    apply eq.symm.injective
    apply Rect.rowN_inj r m S
    rw [← phiTop_x, ← phiTop_x]
    exact congrArg (fun z : Fin (r + m + 1) => xnode r (z : ℕ)) h
  have hkeep : ∀ b : Fin (r + m + 1), r ≤ (b : ℕ) → ∃ i, s' i = b := by
    intro b hb
    have hbl := b.isLt
    by_cases hbm : (b : ℕ) = r + m
    · refine ⟨eq (Sum.inl ⟨Fin.last r, hl⟩), Fin.ext ?_⟩
      simp only [hs', Equiv.symm_apply_apply]
      have : ((phiTop r m S (Sum.inl ⟨Fin.last r, hl⟩) : Fin (r + m + 1)) : ℕ) = r + m := by
        simp [phiTop]
      omega
    · refine ⟨eq (Sum.inr ⟨(b : ℕ) - r, by omega⟩), ?_⟩
      simp only [hs', Equiv.symm_apply_apply, phiTop, Sum.elim_inr]
      exact Fin.ext (by simp; omega)
  have hE1 := hEn1 k s' hs'inj hkeep
  have hrow : (fun i => xnode r ((s' i : Fin (r + m + 1)) : ℕ)) = fun i => Rect.rowN r m S (eq.symm i) :=
    funext (fun i => phiTop_x r m S (eq.symm i))
  rw [hrow] at hE1
  -- the moved column node
  set p0 : ↥S ⊕ Fin m := Sum.inl ⟨Fin.last r, hl⟩ with hp0
  have hne : ∀ i, i ≠ eq p0 → Rect.colN r m S (eq.symm i) = ynode r ((s' i : Fin (r + m + 1)) : ℕ) := by
    intro i hi
    have hp : eq.symm i ≠ p0 := fun h => hi (by rw [← h]; simp)
    simp only [hs']
    rcases hq' : eq.symm i with a | j
    · rw [hq'] at hp
      have hal : (a.1 : ℕ) < r := by
        have h1 := a.1.isLt
        have h2 : a.1 ≠ Fin.last r := fun h => hp (congrArg Sum.inl (Subtype.ext h))
        have : (a.1 : ℕ) ≠ r := fun h => h2 (Fin.ext (by simpa using h))
        omega
      rw [phiTop_y_inl, if_pos hal, add_zero]
    · rw [phiTop_y_inr]
  have hp : Rect.colN r m S (eq.symm (eq p0)) + 1 = ynode r ((s' (eq p0) : Fin (r + m + 1)) : ℕ) := by
    simp only [hs', Equiv.symm_apply_apply, hp0]
    rw [phiTop_y_inl]
    simp [Rect.colN, Rect.cT]
  have hyinj : Function.Injective (fun i => ynode r ((s' i : Fin (r + m + 1)) : ℕ)) := by
    intro a b h
    exact hs'inj (Fin.ext (ynode_inj r h))
  have hE2 := Frame.rectEnergy_perturb hm0 (eq p0) hne hp hyinj
    (fun a b h => eq.symm.injective (Rect.colN_inj r m S h)) hE1
  have hdet := det_pattern_le hFr he0 he1 hm0xs hm0μ hR (Rect.rowN r m S) (Rect.colN r m S)
    (Rect.rowN_inj r m S) (Rect.colN_inj r m S) eq (Nn := r + m + 1) (by omega) hE2
  rw [← Rect.fullNS_top_eq] at hdet
  have hn : Fintype.card (Fin (r + 1)) - S.card = r + 1 - S.card := by simp
  have hnR : ((r + 1 - S.card : ℕ) : ℝ) = (r : ℝ) + m + 1 - k := by
    rw [Nat.cast_sub hScard, hk]; push_cast; ring
  have hkR : (k : ℝ) ≤ (r : ℝ) + m + 1 := by
    have : k ≤ r + m + 1 := by omega
    exact_mod_cast this
  rw [hn]
  refine term_arith hq (r + 1 - S.card) (X := T1 + k * κ + ((r : ℝ) + m + 1) * L0) ?_ ?_
    (abs_nonneg _)
  · refine hdet.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add, hnR]
    congr 1
    push_cast
    ring
  · nlinarith [mul_le_mul_of_nonneg_right hkR hκ0]


/-- the embedding of the member-2 pattern with `b` omitted into the `(r, m)` index set. -/
def phiOut (r m : ℕ) (S : Finset (Fin (r + 1))) (hl : Fin.last r ∉ S) :
    (↥S ⊕ Fin m) → Fin (r + m) :=
  Sum.elim (fun a => ⟨a.1, by
      have h1 := a.1.isLt
      have h2 : a.1 ≠ Fin.last r := fun h => hl (h ▸ a.2)
      have h3 : (a.1 : ℕ) ≠ r := fun h => h2 (Fin.ext (by simpa using h))
      have h4 : (a.1 : ℕ) < r := by omega
      omega⟩)
    (fun j => ⟨r + (j : ℕ), by have := j.isLt; omega⟩)

theorem phiOut_x (r m : ℕ) (S : Finset (Fin (r + 1))) (hl : Fin.last r ∉ S)
    (p : ↥S ⊕ Fin m) : xnode r ((phiOut r m S hl p : Fin (r + m)) : ℕ) = Rect.rowN r m S p := by
  rcases p with a | j
  · have h1 := a.1.isLt
    have h2 : a.1 ≠ Fin.last r := fun h => hl (h ▸ a.2)
    have h3 : (a.1 : ℕ) ≠ r := fun h => h2 (Fin.ext (by simpa using h))
    have h4 : (a.1 : ℕ) < r := by omega
    simp [phiOut, Rect.rowN, Rect.cT, h4, xnode]
  · simp [phiOut, Rect.rowN, xnode]

theorem phiOut_y (r m : ℕ) (S : Finset (Fin (r + 1))) (hl : Fin.last r ∉ S)
    (p : ↥S ⊕ Fin m) : ynode r ((phiOut r m S hl p : Fin (r + m)) : ℕ) = Rect.colN r m S p := by
  rcases p with a | j
  · have h1 := a.1.isLt
    have h2 : a.1 ≠ Fin.last r := fun h => hl (h ▸ a.2)
    have h3 : (a.1 : ℕ) ≠ r := fun h => h2 (Fin.ext (by simpa using h))
    have h4 : (a.1 : ℕ) < r := by omega
    simp [phiOut, Rect.colN, Rect.cT, h4, ynode]
  · simp [phiOut, Rect.colN, ynode]

/-- Member-2 term bound when `b` is omitted: a pattern of `(r, m)`. -/
theorem term_top_out {Fr : Frame} (hFr : Fr.DecayOK') {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {r m N0 : ℕ} {R : ℝ}
    (hR : (N0 : ℝ) ≤ R) {T0 cc : ℝ} {t : ℝ} (hq : |t| * Real.exp (cc * r) ≤ 1) (ht1 : |t| ≤ 1)
    (hEn0 : ∀ (k : ℕ) (s : Fin k → Fin (r + m)), Function.Injective s →
        (∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s i = b) →
        Frame.RectEnergy Fr N0 k e m0 (max (Real.log Fr.Aco) 0)
          (T0 + r * (((r : ℝ) + m) - k) * cc)
          (fun i => xnode r (s i)) (fun i => ynode r (s i)))
    (S : Finset (Fin (r + 1))) (hl : Fin.last r ∉ S) :
    |t| ^ (Fintype.card (Fin (r + 1)) - S.card) *
        |(Rect.FullN Fr (fun a : ↥S => Rect.cT r m a.1) (fun i : Fin m => r + 2 * (i : ℕ))
          (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)).det|
      ≤ Real.exp (T0 + ((r : ℝ) + m) * Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
          + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1))) := by
  classical
  set L0 : ℝ := Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
      + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)) with hL0
  have hScard : S.card ≤ r := by
    have : S ⊆ Finset.univ.erase (Fin.last r) := fun a ha =>
      Finset.mem_erase.2 ⟨fun h => hl (h ▸ ha), Finset.mem_univ _⟩
    simpa using Finset.card_le_card this
  set k : ℕ := S.card + m with hk
  have hcard : Fintype.card (↥S ⊕ Fin m) = k := by simp [Fintype.card_sum, hk]
  let eq : (↥S ⊕ Fin m) ≃ Fin k := Fintype.equivFinOfCardEq hcard
  set s' : Fin k → Fin (r + m) := fun i => phiOut r m S hl (eq.symm i) with hs'
  have hs'inj : Function.Injective s' := by
    intro a b h
    apply eq.symm.injective
    apply Rect.rowN_inj r m S
    rw [← phiOut_x r m S hl, ← phiOut_x r m S hl]
    exact congrArg (fun z : Fin (r + m) => xnode r (z : ℕ)) h
  have hkeep : ∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s' i = b := by
    intro b hb
    have hbl := b.isLt
    refine ⟨eq (Sum.inr ⟨(b : ℕ) - r, by omega⟩), ?_⟩
    simp only [hs', Equiv.symm_apply_apply, phiOut, Sum.elim_inr]
    exact Fin.ext (by simp; omega)
  have hE := hEn0 k s' hs'inj hkeep
  have hrow : (fun i => xnode r ((s' i : Fin (r + m)) : ℕ)) = fun i => Rect.rowN r m S (eq.symm i) :=
    funext (fun i => phiOut_x r m S hl (eq.symm i))
  have hcol : (fun i => ynode r ((s' i : Fin (r + m)) : ℕ)) = fun i => Rect.colN r m S (eq.symm i) :=
    funext (fun i => phiOut_y r m S hl (eq.symm i))
  rw [hrow, hcol] at hE
  have hdet := det_pattern_le hFr he0 he1 hm0xs hm0μ hR (Rect.rowN r m S) (Rect.colN r m S)
    (Rect.rowN_inj r m S) (Rect.colN_inj r m S) eq (Nn := r + m) (by omega) hE
  rw [← Rect.fullNS_top_eq] at hdet
  have hn : Fintype.card (Fin (r + 1)) - S.card = (r - S.card) + 1 := by simp; omega
  have hnR : ((r - S.card : ℕ) : ℝ) = (r : ℝ) + m - k := by
    rw [Nat.cast_sub hScard, hk]; push_cast; ring
  rw [hn, pow_succ]
  have hmain : |t| ^ (r - S.card) * |(Rect.FullN Fr (fun a : ↥S => Rect.cT r m a.1)
      (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
      (Fr.const : ℝ)).det| ≤ Real.exp (T0 + ((r : ℝ) + m) * L0) := by
    refine term_arith hq (r - S.card) (X := T0 + ((r : ℝ) + m) * L0) ?_ le_rfl (abs_nonneg _)
    refine hdet.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add, hnR]
    congr 1
    push_cast
    ring
  calc |t| ^ (r - S.card) * |t| * _ ≤ |t| ^ (r - S.card) * 1 * _ := by
        gcongr
    _ ≤ _ := by rw [mul_one]; exact hmain


/-- **The window for member 2.**  Same hypotheses as `window_rect` for the two patterns `(r, m)`
and `(r, m+1)`; the bound has the `(r,m+1)` term perturbed by `O(r)`. -/
theorem window_rect_top {Fr : Frame} (hFr : Fr.DecayOK') {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {r m N0 : ℕ} {R : ℝ}
    (hR : (N0 : ℝ) ≤ R) {T0 T1 cc : ℝ} (hcc : 0 ≤ cc)
    (hEn0 : ∀ (k : ℕ) (s : Fin k → Fin (r + m)), Function.Injective s →
        (∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s i = b) →
        Frame.RectEnergy Fr N0 k e m0 (max (Real.log Fr.Aco) 0)
          (T0 + r * (((r : ℝ) + m) - k) * cc)
          (fun i => xnode r (s i)) (fun i => ynode r (s i)))
    (hEn1 : ∀ (k : ℕ) (s : Fin k → Fin (r + m + 1)), Function.Injective s →
        (∀ b : Fin (r + m + 1), r ≤ (b : ℕ) → ∃ i, s i = b) →
        Frame.RectEnergy Fr N0 k e m0 (max (Real.log Fr.Aco) 0)
          (T1 + r * (((r : ℝ) + m + 1) - k) * cc)
          (fun i => xnode r (s i)) (fun i => ynode r (s i)))
    {t : ℝ} (ht : |t| ≤ Real.exp (-cc * r)) :
    |Polynomial.aeval (Fr.const + t) ((Rect.afterTop r m).fullPolyG Fr)|
      ≤ 2 ^ (r + 1) * Real.exp (max
          (T0 + ((r : ℝ) + m) * Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
            + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)))
          (T1 + ((r : ℝ) + m + 1) * (Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
            + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)) + Real.log (4 * (1 + 1 / m0))))) := by
  classical
  rw [Rect.aeval_fullPolyTop, Rect.det_fullN_expansion Fr _ _ _ (Fr.const : ℝ) t]
  have hq : |t| * Real.exp (cc * r) ≤ 1 := by
    calc |t| * Real.exp (cc * r) ≤ Real.exp (-cc * r) * Real.exp (cc * r) :=
          mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have ht1 : |t| ≤ 1 := by
    refine ht.trans ?_
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin (r + 1))).powerset,
      |t ^ (Fintype.card (Fin (r + 1)) - S.card) * (Rect.FullN Fr (fun a : ↥S => Rect.cT r m a.1)
          (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
          (Fr.const : ℝ)).det|
        ≤ Real.exp (max
          (T0 + ((r : ℝ) + m) * Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
            + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)))
          (T1 + ((r : ℝ) + m + 1) * (Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
            + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)) + Real.log (4 * (1 + 1 / m0))))) := by
    intro S _
    rw [abs_mul, abs_pow]
    by_cases hl : Fin.last r ∈ S
    · exact (term_top_in hFr he0 he1 hm0 hm0xs hm0μ hR hq hEn1 S hl).trans
        (Real.exp_le_exp.2 (le_max_right _ _))
    · exact (term_top_out hFr he0 he1 hm0xs hm0μ hR hq ht1 hEn0 S hl).trans
        (Real.exp_le_exp.2 (le_max_left _ _))
  calc |∑ S ∈ (Finset.univ : Finset (Fin (r + 1))).powerset,
          t ^ (Fintype.card (Fin (r + 1)) - S.card) *
          (Rect.FullN Fr (fun a : ↥S => Rect.cT r m a.1) (fun i : Fin m => r + 2 * (i : ℕ))
            (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)).det|
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin (r + 1))).powerset,
          |t ^ (Fintype.card (Fin (r + 1)) - S.card) *
          (Rect.FullN Fr (fun a : ↥S => Rect.cT r m a.1) (fun i : Fin m => r + 2 * (i : ℕ))
            (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)).det| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin (r + 1))).powerset, Real.exp (max
          (T0 + ((r : ℝ) + m) * Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
            + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)))
          (T1 + ((r : ℝ) + m + 1) * (Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
            + 2 * (Fr.Aco ^ e / Frame.betaE e) + 1)) + Real.log (4 * (1 + 1 / m0))))) :=
        Finset.sum_le_sum hterm
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
        simp

end CatalanCore
