module

public import CatalanCore.Uniform.Content.Hybrid.Price
public import CatalanCore.Uniform.Content.Hybrid.PoleSplit

@[expose] public section

/-!
# The hybrid rank-layer price for a rational Loewner frame at one prime

Combines the exact pole split (`PoleSplit`), UC4 (`Leading`), compression and the
free + pair lower bound (`Price`).  The source data are:

* an exact pole split of the prefixes and the digit hypothesis;
* exact constant changes of basis `L`, `P` (units mod `p`) with `L K P` vanishing on the rows and
  columns of `s` (exact rational kernels of the fiber blocks `K_a`, completed), whose kernel rows
  and columns are supported in one residue fiber modulo `p`;
* `R0` with `R0 + |s| = h` (for `K = diag(K_a)` this is `Σ rank K_a`);
* a constant subspace `V` and certified bounds on the restricted ranks of the pair conditions.

The local orthogonality hypothesis of the load matrix is DERIVED here from the displacement
identity of the fiber blocks and the exact kernel relations (`horth_of_split`).
-/

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid Finset Module Matrix

namespace CatalanCore.Uniform.Content.Hybrid

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace LeadingData

variable {Φ : Matrix ι ι ℚ[X]}

lemma redQ_LKP (D : LeadingData p Φ) :
    (D.L.map (redQ p)) * (D.K.map (redQ p)) * (D.P.map (redQ p)) =
      (D.L * D.K * D.P).map (redQ p) := by
  rw [Matrix.map_mul, Matrix.map_mul]

/-- Exact left kernel rows are left kernel rows of `K mod p`. -/
lemma row_ker (D : LeadingData p Φ) {i : ι} (hi : i ∈ D.s) (l : ι) :
    ∑ k, redQ p (D.L i k) * redQ p (D.K k l) = 0 := by
  set A := D.L.map (redQ p)
  set B := D.K.map (redQ p)
  set Pm := D.P.map (redQ p)
  set w : ι → ZMod p := fun k => (A * B) i k with hw
  have h0 : w ᵥ* Pm = 0 := by
    funext j
    have : (A * B * Pm) i j = 0 := by
      rw [D.redQ_LKP, Matrix.map_apply, D.hrow i hi j, map_zero]
    rw [Matrix.mul_apply] at this
    simpa [Matrix.vecMul, dotProduct, hw] using this
  have hdet : IsUnit Pm.det := by
    have e : Pm.det = redQ p D.P.det := (RingHom.map_det (redQ p) D.P).symm
    rw [isUnit_iff_ne_zero, e]; exact D.hP
  have hw0 : w = 0 := by
    have := congrArg (fun v => v ᵥ* Pm⁻¹) h0
    simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv Pm hdet, Matrix.vecMul_one,
      Matrix.zero_vecMul] at this
    exact this
  have := congrFun hw0 l
  simpa [hw, Matrix.mul_apply, A, B] using this

/-- Exact right kernel columns are right kernel columns of `K mod p`. -/
lemma col_ker (D : LeadingData p Φ) {j : ι} (hj : j ∈ D.s) (k : ι) :
    ∑ l, redQ p (D.K k l) * redQ p (D.P l j) = 0 := by
  set A := D.L.map (redQ p)
  set B := D.K.map (redQ p)
  set Pm := D.P.map (redQ p)
  set w : ι → ZMod p := fun k => (B * Pm) k j with hw
  have h0 : A *ᵥ w = 0 := by
    funext i
    have : (A * B * Pm) i j = 0 := by
      rw [D.redQ_LKP, Matrix.map_apply, D.hcol i j hj, map_zero]
    rw [Matrix.mul_assoc, Matrix.mul_apply] at this
    simpa [Matrix.mulVec, dotProduct, hw] using this
  have hdet : IsUnit A.det := by
    have e : A.det = redQ p D.L.det := (RingHom.map_det (redQ p) D.L).symm
    rw [isUnit_iff_ne_zero, e]; exact D.hL
  have hw0 : w = 0 := by
    have := congrArg (fun v => A⁻¹ *ᵥ v) h0
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  have := congrFun hw0 k
  simpa [hw, Matrix.mul_apply, B, Pm] using this

end LeadingData

variable {a b : ι → ℕ} {B : ℕ} {f e : ℕ → ℚ}

/-- The leading data of a pole-split frame, given exact kernel bases. -/
noncomputable def PoleSplit.leading (PS : PoleSplit p B f e) (hd : DigitHyp p B a b)
    (L P : Matrix ι ι (LocRing p)) (hL : redQ p L.det ≠ 0) (hP : redQ p P.det ≠ 0)
    (s : Finset ι) (hrow : ∀ i ∈ s, ∀ j, (L * PS.K a b * P) i j = 0)
    (hcol : ∀ i, ∀ j ∈ s, (L * PS.K a b * P) i j = 0) : LeadingData p (loewner a b f e) where
  K := PS.K a b
  Cr := PS.Cr a b
  hB := PS.hB hd
  L := L
  P := P
  hL := hL
  hP := hP
  s := s
  hrow := hrow
  hcol := hcol

/-- **Local orthogonality, derived.** Left and right load vectors of a common fiber are
`ω`-orthogonal. -/
theorem horth_of_split (PS : PoleSplit p B f e) (hd : DigitHyp p B a b)
    (D : LeadingData p (loewner a b f e)) (hK : D.K = PS.K a b)
    (ρ σ : D.s → ZMod p)
    (hu : ∀ (i : D.s) k, redQ p (D.L i k) ≠ 0 → (a k : ZMod p) = ρ i)
    (hv : ∀ (j : D.s) l, redQ p (D.P l j) ≠ 0 → (b l : ZMod p) = σ j)
    (i j : D.s) (hij : ρ i = σ j) :
    omegaL (D.rowLoad (fun k => PS.lf (a k)) i) (D.colLoad (fun l => PS.lf (b l)) j) = 0 := by
  refine omega_load_eq_zero (fun k l => redQ p (D.K k l)) (fun k => (a k : ZMod p))
    (fun l => (b l : ZMod p)) (fun k => ((a k / p : ℕ) : ZMod p)) (fun l => ((b l / p : ℕ) : ZMod p))
    (fun k => PS.lf (a k)) (fun l => PS.lf (b l)) (ρ i) ?_ _ _ (hu i) ?_ ?_ ?_
  · intro k l hk hl
    rw [hK]
    exact PS.disp hd k l (hk.trans hl.symm)
  · intro l hl; rw [hij]; exact hv j l hl
  · intro l _; exact D.row_ker i.2 l
  · intro k _; exact D.col_ker j.2 k

open scoped Classical in
/-- **Hybrid rank-layer price of a rational Loewner frame at one prime.**

`denexp_p(det Φ) ≤ h + R0 - (F₀ + (|Y|·dim V - Σ cost))`, where `F₀` counts the load-zero right
kernel vectors and `Y` is the set of column residues of the right kernel vectors. -/
theorem gle_det_frame (PS : PoleSplit p B f e) (hd : DigitHyp p B a b)
    (L P : Matrix ι ι (LocRing p)) (hL : redQ p L.det ≠ 0) (hP : redQ p P.det ≠ 0)
    (s : Finset ι) (hrow : ∀ i ∈ s, ∀ j, (L * PS.K a b * P) i j = 0)
    (hcol : ∀ i, ∀ j ∈ s, (L * PS.K a b * P) i j = 0)
    (ρ σ : s → ZMod p)
    (hu : ∀ (i : s) k, redQ p (L i k) ≠ 0 → (a k : ZMod p) = ρ i)
    (hv : ∀ (j : s) l, redQ p (P l j) ≠ 0 → (b l : ZMod p) = σ j)
    (R0 : ℕ) (hR : R0 + s.card = Fintype.card ι)
    (Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)))
    (cost : Cond (fun i => rfH p (ρ i)) (fun j => rfH p (σ j)) → ℕ)
    (hcost : ∀ c, finrank (RatFunc (ZMod p)) (LinearMap.range (condMap (fun i => rfH p (ρ i))
        (fun i => mapPair (rfH p) (load (fun k => PS.lf (a k)) (fun k => redQ p (L i k))))
        (fun j => rfH p (σ j))
        (fun j => mapPair (rfH p) (load (fun l => PS.lf (b l)) (fun l => redQ p (P l j))))
        Vs c)) ≤ cost c) :
    GLE p (Fintype.card ι + R0 -
      (Fintype.card {j : s // load (fun l => PS.lf (b l)) (fun l => redQ p (P l j)) = 0} +
        ((colRes (fun j => rfH p (σ j))).card * finrank (RatFunc (ZMod p)) Vs -
          ∑ c, cost c))) (loewner a b f e).det := by
  set D := PS.leading hd L P hL hP s hrow hcol
  exact gle_det_hybrid_of_bounds D (fun i => (a i : ZMod p)) (fun j => (b j : ZMod p))
    (fun k => PS.lf (a k)) (fun l => PS.lf (b l)) (PS.hCr hd) ρ σ hu hv
    (horth_of_split PS hd D rfl ρ σ hu hv) R0 hR Vs cost hcost

end CatalanCore.Uniform.Content.Hybrid
