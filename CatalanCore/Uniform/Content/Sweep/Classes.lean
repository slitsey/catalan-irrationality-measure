module

public import CatalanCore.Uniform.Content.Sweep.PivotG

@[expose] public section

/-!
# The class matrices and their solutions (lane H, wave H2b; ledger P204)

Theorem ND meets the plane 2 matrix.  For a half `h` and a class `o ∈ {0,1}` the class matrix `B^h_o`
(`BclP` over `ℤ_(p)[X]`, `BclR` over `R`) has rows `Cper (1-o)` and columns `Cper o` (`rowPer`, `colPer`
enumerate them by `Fin κ ⊕ Fin k'`).  Its reduction in `𝔽_p(X)` is `ND.Bbar` for the sequence
`s = sZ h` of `p² S` modulo `p` (`phiP_BclP_one`), whose step is `-v/(j+1)²` (`sZ_step`, from
`PFacts.sig_step`), so `det B^h_o` is a unit of `R` once `UnitProp p ξ` holds
(`isUnit_det_BclR`; for `o = 0` the matrix is the transpose, `BclP_zero_eq_transpose`).

* `Yr_class`: the exact solutions `Yr b h o j = ((B^h_o)⁻¹ Γ^b_h)(j)` satisfy the class equations
  `∑_{j ∈ C_o} Bm h l j · Yr b h o j = Γ^b_h(l)` for `l ∈ C_{1-o}` (`GamR`).
* `Yr_half`: the two halves agree modulo `p` (`B_1 (Y_1 - Y_0) = (Γ_1 - Γ_0) - (B_1 - B_0) Y_0`).

These are the hypotheses `hclassR`, `hYhR` of `PivotG.lemmaG_S`.
-/
open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep.Gen

namespace CatalanCore.Uniform.Content.Sweep

section NDLink

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}

open Classical in
/-- The `ℤ_(p)`-element of a `p`-integral rational (and `0` of any other). -/
noncomputable def toL (p : ℕ) [Fact p.Prime] (x : ℚ) : LocRing p :=
  if h : x ∈ LocRing p then ⟨x, h⟩ else 0

theorem toL_val {x : ℚ} (hx : x ∈ LocRing p) : ((toL p x : LocRing p) : ℚ) = x := by
  unfold toL; rw [dif_pos hx]

theorem toL_add {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    toL p (x + y) = toL p x + toL p y := by
  apply Subtype.ext
  rw [toL_val ((LocRing p).add_mem hx hy)]
  push_cast; rw [toL_val hx, toL_val hy]

theorem toL_sub {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    toL p (x - y) = toL p x - toL p y := by
  apply Subtype.ext
  rw [toL_val ((LocRing p).sub_mem hx hy)]
  push_cast; rw [toL_val hx, toL_val hy]

theorem toR_eq_algebraMap_toL (x : ℚ) {R : Type*} [CommRing R] [Algebra (LocRing p) R] :
    toR p x = (algebraMap (LocRing p) R (toL p x) : R) := by
  unfold toR toL
  by_cases hx : x ∈ LocRing p
  · rw [dif_pos hx, dif_pos hx]
  · rw [dif_neg hx, dif_neg hx, map_zero]

/-- A `p`-integral rational divisible by `p` reduces to `0`. -/
theorem redQ_toL_of_Dv {x : ℚ} (hx : Dv p 1 x) : redQ p (toL p x) = 0 := by
  rw [redQ_eq_zero_iff]
  have hxm : x ∈ LocRing p := hx.mem
  have : (toL p x : LocRing p) = (p : LocRing p) * toL p (x / (p : ℚ) ^ 1) := by
    apply Subtype.ext
    have hq : x / (p : ℚ) ^ 1 ∈ LocRing p := hx
    rw [toL_val hxm]
    push_cast
    rw [toL_val hq]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    field_simp
  rw [this]
  exact Dvd.intro _ rfl

end NDLink

section NDLink2

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}

theorem toL_mul {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    toL p (x * y) = toL p x * toL p y := by
  apply Subtype.ext
  rw [toL_val ((LocRing p).mul_mem hx hy)]
  push_cast; rw [toL_val hx, toL_val hy]

noncomputable def sZ (h j : ℕ) : ZMod p := redQ p (toL p ((p : ℚ) ^ 2 * Scell v u p (j, h)))
noncomputable def gZ (h j : ℕ) : ZMod p := redQ p (toL p ((p : ℚ) ^ 3 * Gcell v u p (j, h)))

theorem redQ_toL_inv_sq {j : ℕ} (hj : j + 1 < p) :
    redQ p (toL p ((v : ℚ) / ((j : ℚ) + 1) ^ 2)) = (v : ZMod p) * ((((j : ZMod p) + 1) ^ 2))⁻¹ := by
  have hz : ¬ (p : ℤ) ∣ (((j + 1 : ℕ) : ℤ) ^ 2) := by
    intro hd
    have h1 := (Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow hd
    have h2 := Int.natCast_dvd_natCast.1 h1
    have := Nat.le_of_dvd (by omega) h2
    omega
  have hinv := inv_int_mem (p := p) hz
  have hv := int_mem_locRing (ℓ := p) v
  have e : (v : ℚ) / ((j : ℚ) + 1) ^ 2 = (v : ℚ) * ((((j + 1 : ℕ) : ℤ) ^ 2 : ℤ) : ℚ)⁻¹ := by
    push_cast; ring
  rw [e, toL_mul hv hinv]
  have h1 : toL p (v : ℚ) = (v : LocRing p) := by
    apply Subtype.ext; rw [toL_val hv]; simp
  have h2 : toL p ((((((j + 1 : ℕ) : ℤ) ^ 2 : ℤ) : ℚ))⁻¹) = invZ p (((j + 1 : ℕ) : ℤ) ^ 2) := by
    apply Subtype.ext; rw [toL_val hinv, coe_invZ, if_neg hz]
  rw [h1, h2, map_mul, map_intCast, redQ_invZ]
  push_cast; ring

theorem sZ_step (hodd : p % 2 = 1) (hN : 2 * N < p * p) {j h : ℕ} (hh : h ≤ 1)
    (hj : (j + 2) * p ≤ N) (hjp : j + 1 < p) :
    ((j + 1 : ℕ) : ZMod p) ^ 2 * (sZ v u h (j + 1) - sZ v u h j) = -(v : ZMod p) := by
  have hd := sig_step v u hodd hN hh hj hjp
  have hA := sig_mem_cell v u hodd hN (j := j + 1) hh (by nlinarith)
  have hB := sig_mem_cell v u hodd hN (j := j) hh (by nlinarith)
  have hz : ¬ (p : ℤ) ∣ (((j + 1 : ℕ) : ℤ) ^ 2) := by
    intro hd'
    have h1 := (Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow hd'
    have h2 := Int.natCast_dvd_natCast.1 h1
    have := Nat.le_of_dvd (by omega) h2
    omega
  have hinv := inv_int_mem (p := p) hz
  have hw : (v : ℚ) / ((j : ℚ) + 1) ^ 2 ∈ LocRing p := by
    have e : (v : ℚ) / ((j : ℚ) + 1) ^ 2 = (v : ℚ) * ((((j + 1 : ℕ) : ℤ) ^ 2 : ℤ) : ℚ)⁻¹ := by
      push_cast; ring
    rw [e]; exact (LocRing p).mul_mem (int_mem_locRing v) hinv
  have hAB : (p : ℚ) ^ 2 * Scell v u p (j + 1, h) - (p : ℚ) ^ 2 * Scell v u p (j, h) ∈ LocRing p :=
    (LocRing p).sub_mem hA hB
  have e1 : (p : ℚ) ^ 2 * (Scell v u p (j + 1, h) - Scell v u p (j, h)) + (v : ℚ) / ((j : ℚ) + 1) ^ 2 =
      ((p : ℚ) ^ 2 * Scell v u p (j + 1, h) - (p : ℚ) ^ 2 * Scell v u p (j, h)) +
        (v : ℚ) / ((j : ℚ) + 1) ^ 2 := by ring
  rw [e1] at hd
  have h0 := redQ_toL_of_Dv hd
  rw [toL_add hAB hw, toL_sub hA hB, map_add, map_sub, redQ_toL_inv_sq v hjp] at h0
  unfold sZ
  have hne : (((j : ZMod p) + 1) ^ 2) ≠ 0 := by
    have : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd'; have := Nat.le_of_dvd (by omega) hd'; omega
    push_cast at this; exact pow_ne_zero 2 this
  push_cast
  have : (((j : ZMod p) + 1) ^ 2) * (redQ p (toL p ((p : ℚ) ^ 2 * Scell v u p (j + 1, h))) -
      redQ p (toL p ((p : ℚ) ^ 2 * Scell v u p (j, h)))) =
      -((v : ZMod p) * ((((j : ZMod p) + 1) ^ 2))⁻¹ * (((j : ZMod p) + 1) ^ 2)) := by
    linear_combination (((j : ZMod p) + 1) ^ 2) * h0
  rw [this, mul_assoc, inv_mul_cancel₀ hne, mul_one]

theorem redQ_toL_off (hodd : p % 2 = 1) (hN : 2 * N < p * p) {l j h : ℕ} (hh : h ≤ 1)
    (hl : (l + 1) * p ≤ N) (hj : (j + 1) * p ≤ N) (hlj : l ≠ j) :
    redQ p (toL p ((p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) / ((l : ℚ) - j))) =
      (sZ v u h l - sZ v u h j) * (((l : ZMod p) - j))⁻¹ := by
  have hlp : l < p := by nlinarith
  have hjp : j < p := by nlinarith
  have hu := unit_diff (p := p) hlj hlp hjp
  have hA := sig_mem_cell v u hodd hN hh hl
  have hB := sig_mem_cell v u hodd hN hh hj
  have hz : ¬ (p : ℤ) ∣ (l : ℤ) - j := by
    intro hd
    apply hlj
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((l : ℤ) - j) p).2 hd
    push_cast at this
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlp, Nat.mod_eq_of_lt hjp] at this
    exact this
  have hinv : (((l : ℚ) - j)⁻¹) ∈ LocRing p := by
    have := inv_int_mem (p := p) hz; push_cast at this; exact this
  have e : (p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) / ((l : ℚ) - j) =
      ((p : ℚ) ^ 2 * Scell v u p (l, h) - (p : ℚ) ^ 2 * Scell v u p (j, h)) * (((l : ℚ) - j)⁻¹) := by
    rw [mul_sub, div_eq_mul_inv]
  rw [e, toL_mul ((LocRing p).sub_mem hA hB) hinv, toL_sub hA hB, map_mul, map_sub]
  have h2 : toL p ((((l : ℚ) - j)⁻¹)) = invZ p ((l : ℤ) - j) := by
    apply Subtype.ext
    rw [toL_val hinv, coe_invZ, if_neg hz]; push_cast; rfl
  rw [h2, redQ_invZ]
  unfold sZ; push_cast; rfl

end NDLink2

section Class

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}

/-- The polynomial entry of the period matrix: `X + p³G(l,h)` on the diagonal. -/
noncomputable def BentP (h l j : ℕ) : (LocRing p)[X] :=
  if l = j then X + C (toL p ((p : ℚ) ^ 3 * Gcell v u p (l, h))) else
    C (toL p ((p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) / ((l : ℚ) - j)))

/-- The reduction of the period matrix entry in `𝔽_p`. -/
noncomputable def entZ (h l j : ℕ) : ZMod p :=
  if l = j then gZ (p := p) v u h l else (sZ (p := p) v u h l - sZ (p := p) v u h j) * (((l : ZMod p) - j))⁻¹

theorem Bm_eq_aeval {R : Type*} [CommRing R] [Algebra (LocRing p) R] (ξ : R) (h l j : ℕ) :
    Bm (p := p) v u ξ h l j = Polynomial.aeval ξ (BentP (p := p) v u h l j) := by
  unfold Bm BentP
  by_cases hlj : l = j
  · simp only [hlj, if_true, map_add, aeval_X, aeval_C]
    unfold ggR; rw [toR_eq_algebraMap_toL]
  · simp only [hlj, if_false, aeval_C]
    rw [toR_eq_algebraMap_toL]

theorem phiP_BentP (hodd : p % 2 = 1) (hN : 2 * N < p * p) {h l j : ℕ} (hh : h ≤ 1)
    (hl : (l + 1) * p ≤ N) (hj : (j + 1) * p ≤ N) :
    phiP p (BentP (p := p) v u h l j) = (if l = j then rfX p else 0) + rfC p (entZ v u h l j) := by
  unfold BentP entZ
  by_cases hlj : l = j
  · simp only [hlj, if_true, map_add, phiP_X, phiP_C]; unfold gZ; rfl
  · simp only [hlj, if_false, phiP_C, zero_add]
    rw [redQ_toL_off v u hodd hN hh hl hj hlj]

variable (κ k' : ℕ)

/-- Row periods of the class `o`: `[0,κ)` and `κ + 2i + (1-o)`. -/
def rowPer (o : ℕ) : Fin κ ⊕ Fin k' → ℕ :=
  Sum.elim (fun a => (a : ℕ)) (fun i => κ + 2 * (i : ℕ) + (1 - o))
/-- Column periods of the class `o`: `[0,κ)` and `κ + 2i + o`. -/
def colPer (o : ℕ) : Fin κ ⊕ Fin k' → ℕ :=
  Sum.elim (fun a => (a : ℕ)) (fun i => κ + 2 * (i : ℕ) + o)

/-- The class matrix `B^h_o` over `ℤ_(p)[X]`. -/
noncomputable def BclP (h o : ℕ) : Matrix (Fin κ ⊕ Fin k') (Fin κ ⊕ Fin k') (LocRing p)[X] :=
  fun a b => BentP (p := p) v u h (rowPer κ k' o a) (colPer κ k' o b)

theorem BentP_symm (h l j : ℕ) : BentP (p := p) v u h l j = BentP (p := p) v u h j l := by
  unfold BentP
  by_cases hlj : l = j
  · subst hlj; rfl
  · rw [if_neg hlj, if_neg (Ne.symm hlj)]
    congr 2
    have h1 : (l : ℚ) - j ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hlj)
    have h2 : (j : ℚ) - l ≠ 0 := sub_ne_zero.2 (by exact_mod_cast Ne.symm hlj)
    field_simp
    ring

theorem BclP_zero_eq_transpose (h : ℕ) : BclP (p := p) v u κ k' h 0 = (BclP (p := p) v u κ k' h 1)ᵀ := by
  ext a b
  simp only [BclP, Matrix.transpose_apply]
  rw [BentP_symm]
  have e1 : rowPer κ k' 0 a = colPer κ k' 1 a := by
    rcases a with a | i <;> simp [rowPer, colPer]
  have e2 : colPer κ k' 0 b = rowPer κ k' 1 b := by
    rcases b with a | i <;> simp [rowPer, colPer]
  rw [e1, e2]

theorem sub_inv_swap {K : Type*} [Field K] (x y a b : K) : (x - y) * (a - b)⁻¹ = (y - x) / (b - a) := by
  rw [div_eq_mul_inv, ← neg_sub a b, inv_neg]; ring

/-- The entry of the reduced period matrix for a general sequence. -/
noncomputable def entS (s g : ℕ → ZMod p) (l j : ℕ) : ZMod p :=
  if l = j then g l else (s l - s j) * (((l : ZMod p) - j))⁻¹

theorem Bbar_entry (s g : ℕ → ZMod p) (a b : Fin κ ⊕ Fin k') :
    CatalanCore.Uniform.Content.Sweep.ND.Bbar κ k' s g a b =
      (if rowPer κ k' 1 a = colPer κ k' 1 b then (X : (ZMod p)[X]) else 0) +
        C (entS s g (rowPer κ k' 1 a) (colPer κ k' 1 b)) := by
  unfold CatalanCore.Uniform.Content.Sweep.ND.Bbar CatalanCore.Uniform.Content.Sweep.ND.blockA
    CatalanCore.Uniform.Content.Sweep.ND.blockB CatalanCore.Uniform.Content.Sweep.ND.blockC
    CatalanCore.Uniform.Content.Sweep.ND.crossBlock
  rcases a with a | i <;> rcases b with b | j
  · have ha := a.2; have hb := b.2
    by_cases hab : (a : ℕ) = b
    · have : a = b := Fin.ext hab
      subst this
      simp [rowPer, colPer, entS, Matrix.one_apply]
    · have : a ≠ b := fun h => hab (by rw [h])
      simp [rowPer, colPer, entS, Matrix.one_apply, hab, this, sub_inv_swap]
  · have ha := a.2; have hj := j.2
    have hne : (a : ℕ) ≠ κ + 2 * (j : ℕ) + 1 := by omega
    simp [rowPer, colPer, entS, hne, sub_inv_swap]
  · have hb := b.2; have hi := i.2
    have hne : κ + 2 * (i : ℕ) ≠ (b : ℕ) := by omega
    simp [rowPer, colPer, entS, hne, sub_inv_swap]
  · have hne : κ + 2 * (i : ℕ) ≠ κ + 2 * (j : ℕ) + 1 := by omega
    simp [rowPer, colPer, entS, hne, sub_inv_swap]

theorem phiP_BclP_one (hodd : p % 2 = 1) (hN : 2 * N < p * p) {h : ℕ} (hh : h ≤ 1)
    (hper : ∀ j, j < κ + 2 * k' → (j + 1) * p ≤ N) :
    (phiP p).mapMatrix (BclP (p := p) v u κ k' h 1) =
      (algebraMap (ZMod p)[X] (RatFunc (ZMod p))).mapMatrix
        (CatalanCore.Uniform.Content.Sweep.ND.Bbar κ k' (sZ (p := p) v u h) (gZ (p := p) v u h)) := by
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, BclP]
  have hrow : ∀ a, rowPer κ k' 1 a < κ + 2 * k' := by
    intro a; rcases a with a | i
    · have := a.2; simp [rowPer] <;> omega
    · have := i.2; simp [rowPer] <;> omega
  have hcol : ∀ b, colPer κ k' 1 b < κ + 2 * k' := by
    intro b; rcases b with a | i
    · have := a.2; simp [colPer] <;> omega
    · have := i.2; simp [colPer] <;> omega
  rw [phiP_BentP v u hodd hN hh (hper _ (hrow a)) (hper _ (hcol b)), Bbar_entry]
  unfold entZ entS rfX rfC
  by_cases hc : rowPer κ k' 1 a = colPer κ k' 1 b
  · simp [hc]
  · simp [hc]

/-- The unit hypothesis on `(R, ξ)`: a polynomial over `ℤ_(p)` whose reduction in `𝔽_p(X)` is nonzero
becomes a unit at `ξ`. (True for `R = ℤ_(p)[X]_(p)`, `ξ = X`.) -/
def UnitProp (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra (LocRing p) R] (ξ : R) : Prop :=
  ∀ g : (LocRing p)[X], phiP p g ≠ 0 → IsUnit (Polynomial.aeval ξ g)

/-- The class matrix over `R`. -/
noncomputable def BclR {R : Type*} [CommRing R] [Algebra (LocRing p) R] (ξ : R) (h o : ℕ) :
    Matrix (Fin κ ⊕ Fin k') (Fin κ ⊕ Fin k') R :=
  fun a b => Bm (p := p) v u ξ h (rowPer κ k' o a) (colPer κ k' o b)

theorem BclR_eq {R : Type*} [CommRing R] [Algebra (LocRing p) R] (ξ : R) (h o : ℕ) :
    BclR (p := p) v u κ k' ξ h o =
      (Polynomial.aeval ξ : (LocRing p)[X] →ₐ[LocRing p] R).toRingHom.mapMatrix (BclP (p := p) v u κ k' h o) := by
  ext a b
  simp [BclR, BclP, Bm_eq_aeval]

theorem isUnit_det_BclR {R : Type*} [CommRing R] [Algebra (LocRing p) R] {ξ : R} (hU : UnitProp p ξ)
    (hodd : p % 2 = 1) (hN : 2 * N < p * p) {h o : ℕ} (hh : h ≤ 1) (ho : o ≤ 1)
    (hH : (κ + 2 * k') * p ≤ N) (hv : ¬ (p : ℤ) ∣ v) :
    IsUnit (BclR (p := p) v u κ k' ξ h o).det := by
  have hper : ∀ j, j < κ + 2 * k' → (j + 1) * p ≤ N := fun j hj => by nlinarith
  have hlt : κ + 2 * k' < p := by
    by_contra hge
    have := Nat.mul_le_mul_left p (not_lt.1 hge)
    nlinarith
  have hc : (-(v : ZMod p)) ≠ 0 := by
    rw [neg_ne_zero, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hv
  have hstep : ∀ i, i + 1 < 2 * k' →
      ((κ + i + 1 : ℕ) : ZMod p) ^ 2 * (sZ (p := p) v u h (κ + i + 1) - sZ (p := p) v u h (κ + i)) = -(v : ZMod p) := by
    intro i hi
    have := sZ_step v u hodd hN (j := κ + i) hh (by have := hper (κ + i + 1) (by omega); nlinarith) (by omega)
    exact this
  have hdet1 : phiP p (BclP (p := p) v u κ k' h 1).det ≠ 0 := by
    have e := RingHom.map_det (phiP p) (BclP (p := p) v u κ k' h 1)
    have e2 := phiP_BclP_one v u κ k' hodd hN hh hper
    rw [e, e2, ← RingHom.map_det]
    intro h0
    exact CatalanCore.Uniform.Content.Sweep.ND.det_Bbar_ne_zero κ k' (sZ (p := p) v u h) (gZ (p := p) v u h)
      hlt hc hstep ((map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))).1 h0)
  have hdet : phiP p (BclP (p := p) v u κ k' h o).det ≠ 0 := by
    obtain rfl | rfl : o = 0 ∨ o = 1 := by omega
    · rw [BclP_zero_eq_transpose, Matrix.det_transpose]; exact hdet1
    · exact hdet1
  rw [BclR_eq, ← RingHom.map_det]
  exact hU _ hdet

theorem colPer_injective (o : ℕ) : Function.Injective (colPer κ k' o) := by
  intro a b hab
  rcases a with a | i <;> rcases b with b | j <;> simp [colPer] at hab
  · exact congrArg Sum.inl (Fin.ext hab)
  · have := a.2; omega
  · have := b.2; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem colPer_mem (o : ℕ) (ho : o ≤ 1) (a : Fin κ ⊕ Fin k') : colPer κ k' o a ∈ Cper κ k' o := by
  rw [mem_Cper]
  rcases a with a | i
  · have := a.2; simp [colPer]; omega
  · have := i.2; simp only [colPer, Sum.elim_inr]; refine ⟨by omega, Or.inr (by omega)⟩

theorem rowPer_mem (o : ℕ) (ho : o ≤ 1) (a : Fin κ ⊕ Fin k') : rowPer κ k' o a ∈ Cper κ k' (1 - o) := by
  rw [mem_Cper]
  rcases a with a | i
  · have := a.2; simp [rowPer]; omega
  · have := i.2; simp only [rowPer, Sum.elim_inr]; refine ⟨by omega, Or.inr (by omega)⟩

theorem exists_rowPer (o : ℕ) (ho : o ≤ 1) {l : ℕ} (hl : l ∈ Cper κ k' (1 - o)) :
    ∃ c, rowPer κ k' o c = l := by
  rw [mem_Cper] at hl
  obtain ⟨h1, h2⟩ := hl
  by_cases hlk : l < κ
  · exact ⟨Sum.inl ⟨l, hlk⟩, by simp [rowPer]⟩
  · have h3 : (l - κ) % 2 = 1 - o := h2.resolve_left hlk
    refine ⟨Sum.inr ⟨(l - κ) / 2, by omega⟩, ?_⟩
    simp only [rowPer, Sum.elim_inr]
    omega

theorem exists_colPer (o : ℕ) (ho : o ≤ 1) {l : ℕ} (hl : l ∈ Cper κ k' o) :
    ∃ c, colPer κ k' o c = l := by
  rw [mem_Cper] at hl
  obtain ⟨h1, h2⟩ := hl
  by_cases hlk : l < κ
  · exact ⟨Sum.inl ⟨l, hlk⟩, by simp [colPer]⟩
  · have h3 : (l - κ) % 2 = o := h2.resolve_left hlk
    refine ⟨Sum.inr ⟨(l - κ) / 2, by omega⟩, ?_⟩
    simp only [colPer, Sum.elim_inr]
    omega

section Solutions

variable {R : Type*} [CommRing R] [Algebra (LocRing p) R] (ξ : R)

/-- The coordinates `(B^h_o)⁻¹ Γ^b_h` of the class solution. -/
noncomputable def Wvec (b h o : ℕ) : Fin κ ⊕ Fin k' → R :=
  (BclR (p := p) v u κ k' ξ h o)⁻¹ *ᵥ (fun c => GamR (p := p) v u b h (rowPer κ k' o c))

/-- The class solution `Y^b_{h,o}(j)`, indexed by the period `j`. -/
noncomputable def Yr (b h o j : ℕ) : R :=
  ∑ a, if colPer κ k' o a = j then Wvec (p := p) v u κ k' ξ b h o a else 0

theorem Yr_colPer (b h o : ℕ) (a : Fin κ ⊕ Fin k') :
    Yr (p := p) v u κ k' ξ b h o (colPer κ k' o a) = Wvec (p := p) v u κ k' ξ b h o a := by
  unfold Yr
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ hne
    rw [if_neg (fun h => hne (colPer_injective κ k' o h))]
  · intro h; exact absurd (Finset.mem_univ a) h

variable {ξ}

/-- The unit hypothesis of the sweep: the class matrices `B^h_o` have unit determinant.  It follows from
`UnitProp` (`unitDet_of_unitProp`, for `ξ = X`) and is all that the chain uses; at `ξ = p X` (row `E₂`)
it is proved directly. -/
def UnitDet (p : ℕ) [Fact p.Prime] (v u : ℤ) (κ k' : ℕ) {R : Type*} [CommRing R] [Algebra (LocRing p) R]
    (ξ : R) : Prop :=
  ∀ h o : ℕ, h ≤ 1 → o ≤ 1 → IsUnit (BclR (p := p) v u κ k' ξ h o).det

theorem unitDet_of_unitProp {R : Type*} [CommRing R] [Algebra (LocRing p) R] {ξ : R} (hU : UnitProp p ξ)
    (hodd : p % 2 = 1) (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N) (hv : ¬ (p : ℤ) ∣ v) :
    UnitDet p v u κ k' ξ :=
  fun _ _ hh ho => isUnit_det_BclR v u κ k' hU hodd hN hh ho hH hv

theorem Yr_class (hU : UnitDet p v u κ k' ξ) (hodd : p % 2 = 1) (hN : 2 * N < p * p)
    (hH : (κ + 2 * k') * p ≤ N) (hv : ¬ (p : ℤ) ∣ v) {h o : ℕ} (hh : h ≤ 1) (ho : o ≤ 1) (b : ℕ)
    {l : ℕ} (hl : l ∈ Cper κ k' (1 - o)) :
    ∑ j ∈ Cper κ k' o, Bm (p := p) v u ξ h l j * Yr (p := p) v u κ k' ξ b h o j =
      GamR (p := p) v u b h l := by
  have hdet := hU _ _ hh ho
  obtain ⟨c, rfl⟩ := exists_rowPer κ k' o ho hl
  have e1 : ∑ j ∈ Cper κ k' o, Bm (p := p) v u ξ h (rowPer κ k' o c) j * Yr (p := p) v u κ k' ξ b h o j =
      ∑ a, Bm (p := p) v u ξ h (rowPer κ k' o c) (colPer κ k' o a) * Wvec (p := p) v u κ k' ξ b h o a := by
    unfold Yr
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq (Cper κ k' o) (colPer κ k' o a)]
    rw [if_pos (colPer_mem κ k' o ho a)]
  rw [e1]
  have e2 : (BclR (p := p) v u κ k' ξ h o *ᵥ Wvec (p := p) v u κ k' ξ b h o) c =
      GamR (p := p) v u b h (rowPer κ k' o c) := by
    unfold Wvec
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  rw [← e2]
  rfl

theorem Yr_half (hU : UnitDet p v u κ k' ξ) (hodd : p % 2 = 1) (hN : 2 * N < p * p)
    (hH : (κ + 2 * k') * p ≤ N) (hv : ¬ (p : ℤ) ∣ v) {o : ℕ} (ho : o ≤ 1) (b : ℕ)
    {j : ℕ} (hj : j ∈ Cper κ k' o) :
    (p : R) ∣ Yr (p := p) v u κ k' ξ b 1 o j - Yr (p := p) v u κ k' ξ b 0 o j := by
  have hdet1 := hU 1 o (by norm_num) ho
  have hper : ∀ j, j < κ + 2 * k' → (j + 1) * p ≤ N := fun j hj => by nlinarith
  obtain ⟨a, rfl⟩ := exists_colPer κ k' o ho hj
  rw [Yr_colPer, Yr_colPer]
  -- d = Γ_1 - B_1 W_0
  set W0 := Wvec (p := p) v u κ k' ξ b 0 o with hW0
  set B1 := BclR (p := p) v u κ k' ξ 1 o with hB1
  set B0 := BclR (p := p) v u κ k' ξ 0 o with hB0
  set G1 : Fin κ ⊕ Fin k' → R := fun c => GamR (p := p) v u b 1 (rowPer κ k' o c) with hG1
  set G0 : Fin κ ⊕ Fin k' → R := fun c => GamR (p := p) v u b 0 (rowPer κ k' o c) with hG0
  have hdet0 := hU 0 o (by norm_num) ho
  have hB0W : B0 *ᵥ W0 = G0 := by
    rw [hW0, Wvec, hB0, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet0, Matrix.one_mulVec]
  have hd : ∀ c, (p : R) ∣ (G1 - B1 *ᵥ W0) c := by
    intro c
    have e : (G1 - B1 *ᵥ W0) c = (G1 c - G0 c) - ((B1 - B0) *ᵥ W0) c := by
      have := congrFun hB0W c
      simp only [Pi.sub_apply, Matrix.sub_mulVec]
      rw [← this]; ring
    rw [e]
    refine dvd_sub ?_ ?_
    · have hl := (rowPer_mem κ k' o ho c)
      have hlt : rowPer κ k' o c < κ + 2 * k' := ((mem_Cper (κ := κ) (k' := k')).1 hl).1
      simp only [hG1, hG0, GamR]
      by_cases hb : b = 0
      · simp [hb]
      · simp only [hb, if_false]
        exact sigR_halves v u hodd hN (hper _ hlt)
    · simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
      refine Finset.dvd_sum fun a' _ => ?_
      refine Dvd.dvd.mul_right ?_ _
      have hr : rowPer κ k' o c < κ + 2 * k' := ((mem_Cper (κ := κ) (k' := k')).1 (rowPer_mem κ k' o ho c)).1
      have hc : colPer κ k' o a' < κ + 2 * k' := ((mem_Cper (κ := κ) (k' := k')).1 (colPer_mem κ k' o ho a')).1
      exact Bm_halves v u hodd hN ξ (hper _ hr) (hper _ hc)
  have hdiff : Wvec (p := p) v u κ k' ξ b 1 o - W0 = B1⁻¹ *ᵥ (G1 - B1 *ᵥ W0) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet1, Matrix.one_mulVec]
    rfl
  have := congrFun hdiff a
  simp only [Pi.sub_apply] at this
  rw [this]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun c _ => Dvd.dvd.mul_left (hd c) _

end Solutions

end Class

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.isUnit_det_BclR
#print axioms CatalanCore.Uniform.Content.Sweep.Yr_class
#print axioms CatalanCore.Uniform.Content.Sweep.Yr_half
