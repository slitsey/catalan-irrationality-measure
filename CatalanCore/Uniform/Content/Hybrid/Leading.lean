module

public import CatalanCore.Arith.Hybrid.TwoLevelGLE

@[expose] public section

/-!
# UC4: leading matrix, exact unit elimination and one `p`-division

Frame-generic form of the first two negative-order stages of the hybrid rank layer
(Uniform Content Theorem §3, `NORTH-STAR-HYBRID-RANK-CONTENT-PROOF` §§3–4).

Data (`LeadingData p Φ`) for a square matrix `Φ` over `ℚ[X]`, indexed by any finite type `ι`
(so the same API applies verbatim to submatrices and member cores):

* a CONSTANT `p`-integral leading matrix `K` and an integral remainder `Cr` with
  `p² Φ = K + p · Cr` exactly (in the original variable `X`);
* exact constant `p`-integral changes of basis `L`, `P`, units modulo `p`, and an index set `s`
  such that `L K P` vanishes EXACTLY on the rows and on the columns of `s`
  (exact rational kernels, not modular lifts).

The next matrix is `M_next = (L Cr P)|_{s×s}`.  With `G` a lower bound for the corank of
`M_next mod p` over `𝔽_p(X)` the theorem is

  `GLE p (2h - |s| - G) (det Φ)`,

i.e. `denexp_p(det Φ) ≤ h + R0 - G` when `|s| = h - R0` (`LeadingData.gle_det_R0`).  For a
block-diagonal leading part `K = diag(K_a)` one has `R0 = Σ rank K_a`; the theorem itself only
needs `|s| + R0 = h`.
-/

open Polynomial CatalanCore.Basic CatalanCore.Arith.Hybrid Matrix

namespace CatalanCore.Uniform.Content.Hybrid

variable {p : ℕ} [hp : Fact p.Prime]

/-- Leading data of `p² Φ`. -/
structure LeadingData (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Φ : Matrix ι ι ℚ[X]) where
  K : Matrix ι ι (LocRing p)
  Cr : Matrix ι ι (LocRing p)[X]
  hB : ∀ i j, toQ p (C (K i j) + C ((p : ℕ) : LocRing p) * Cr i j) = C ((p : ℚ) ^ 2) * Φ i j
  L : Matrix ι ι (LocRing p)
  P : Matrix ι ι (LocRing p)
  hL : redQ p L.det ≠ 0
  hP : redQ p P.det ≠ 0
  s : Finset ι
  hrow : ∀ i ∈ s, ∀ j, (L * K * P) i j = 0
  hcol : ∀ i, ∀ j ∈ s, (L * K * P) i j = 0

lemma rfC_ne_zero {a : ZMod p} (ha : a ≠ 0) : rfC p a ≠ 0 := by
  unfold rfC
  rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod p)), Polynomial.C_eq_zero]
  exact ha

lemma Cp_ne_zero : (C ((p : ℕ) : LocRing p) : (LocRing p)[X]) ≠ 0 := by
  rw [Ne, Polynomial.C_eq_zero]
  intro h
  have := congrArg (fun z : LocRing p => (z : ℚ)) h
  simp only [Subring.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this
  exact hp.out.ne_zero this

lemma quotP_Cp_mul (y : (LocRing p)[X]) : quotP p (C ((p : ℕ) : LocRing p) * y) = y := by
  have h := quotP_spec p (dvd_mul_right (C ((p : ℕ) : LocRing p)) y)
  exact mul_left_cancel₀ Cp_ne_zero h

lemma phiP_det_mapC {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (LocRing p))
    (hA : redQ p A.det ≠ 0) : phiP p (A.map C).det ≠ 0 := by
  have : (A.map (C : LocRing p →+* (LocRing p)[X])).det = C A.det := by
    rw [RingHom.map_det]; rfl
  rw [this, phiP_C]
  exact rfC_ne_zero hA

namespace LeadingData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Matrix ι ι ℚ[X]}

/-- The integral lift `p² Φ = K + p·Cr`. -/
noncomputable def Bl (D : LeadingData p Φ) : Matrix ι ι (LocRing p)[X] :=
  Matrix.of fun i j => C (D.K i j) + C ((p : ℕ) : LocRing p) * D.Cr i j

/-- The uncompressed next matrix `L · Cr · P`. -/
noncomputable def nextFull (D : LeadingData p Φ) : Matrix ι ι (LocRing p)[X] :=
  D.L.map C * D.Cr * D.P.map C

/-- The actual next matrix `M_next` on the exact kernel coordinates `s`. -/
noncomputable def next (D : LeadingData p Φ) : Matrix D.s D.s (LocRing p)[X] :=
  Matrix.of fun i j => D.nextFull i j

/-- `M_next mod p`, over `𝔽_p(X)`. -/
noncomputable def nextRed (D : LeadingData p Φ) : Matrix D.s D.s (RatFunc (ZMod p)) :=
  D.next.map (phiP p)

lemma sandwich (D : LeadingData p Φ) :
    D.L.map C * D.Bl * D.P.map C =
      (D.L * D.K * D.P).map C + C ((p : ℕ) : LocRing p) • D.nextFull := by
  have hBl : D.Bl = D.K.map C + C ((p : ℕ) : LocRing p) • D.Cr := by
    ext i j; simp [Bl]
  have hmap : (D.L * D.K * D.P).map (C : LocRing p →+* (LocRing p)[X]) =
      D.L.map C * D.K.map C * D.P.map C := by
    rw [Matrix.map_mul (f := (C : LocRing p →+* (LocRing p)[X])),
      Matrix.map_mul (f := (C : LocRing p →+* (LocRing p)[X]))]
  rw [hBl, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, nextFull, hmap]

lemma sandwich_apply (D : LeadingData p Φ) (i j : ι) :
    (D.L.map C * D.Bl * D.P.map C) i j =
      C ((D.L * D.K * D.P) i j) + C ((p : ℕ) : LocRing p) * D.nextFull i j := by
  rw [sandwich, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]

/-- The two-level witness produced by the leading data. -/
noncomputable def toWit (D : LeadingData p Φ) (b : ℕ) (hb : D.nextRed.rank ≤ b) :
    TwoLevelWit p Φ b where
  Bl := D.Bl
  u := fun _ => 1
  v := fun _ => 1
  hB := fun i j => D.hB i j
  s := D.s
  L := D.L.map C
  P := D.P.map C
  hL := phiP_det_mapC _ D.hL
  hP := phiP_det_mapC _ D.hP
  hrow := fun i hi j => by
    rw [sandwich_apply, D.hrow i hi j, map_zero, zero_add]; exact dvd_mul_right _ _
  hcol := fun i j hj => by
    rw [sandwich_apply, D.hcol i j hj, map_zero, zero_add]; exact dvd_mul_right _ _
  hH := by
    have : (Matrix.of fun i j : D.s => phiP p (quotP p ((D.L.map C * D.Bl * D.P.map C) i j))) =
        D.nextRed := by
      ext i j
      rw [Matrix.of_apply, sandwich_apply, D.hrow i i.2 j, map_zero, zero_add, quotP_Cp_mul]
      rfl
    rw [this]; exact hb

/-- **UC4 (exponent form).** If `M_next mod p` has corank at least `G` then
`p^(2h - |s| - G) det Φ` is `p`-integral. -/
theorem gle_det (D : LeadingData p Φ) (G : ℕ) (hG : D.nextRed.rank + G ≤ D.s.card) :
    GLE p (2 * Fintype.card ι - D.s.card - G) Φ.det := by
  have h := (D.toWit (D.s.card - G) (by omega)).gle
  have hc : (D.toWit (D.s.card - G) (by omega)).cost = 2 * Fintype.card ι - D.s.card - G := by
    simp only [TwoLevelWit.cost, toWit, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one]
    omega
  rwa [hc] at h

/-- **UC4.** `denexp_p(det Φ) ≤ h + R0 - G`, with `h = |ι|` and `|s| = h - R0`. -/
theorem gle_det_R0 (D : LeadingData p Φ) (R0 G : ℕ) (hR : R0 + D.s.card = Fintype.card ι)
    (hG : D.nextRed.rank + G ≤ D.s.card) :
    GLE p (Fintype.card ι + R0 - G) Φ.det := by
  have h := D.gle_det G hG
  have e : 2 * Fintype.card ι - D.s.card - G = Fintype.card ι + R0 - G := by omega
  rwa [e] at h

end LeadingData

end CatalanCore.Uniform.Content.Hybrid
