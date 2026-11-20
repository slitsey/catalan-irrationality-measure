module

public import CatalanCore.Lai.B83Half
public import CatalanCore.Lai.WilsonHankel
public import CatalanCore.Lai.Construction
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

/-!
# The half block of Theorem B83: from `Lf n` to Lai's functional, and the unit determinant (bridge `lb-hbridge`)

`B83Half.lemma_G3_monomial` is stated for `Lf n` over `ℚ`.  Here:

* `laiL_eval_b`: `Lf n P = laiL n P` evaluated at `(a, b, X) = (0, 1, 0)` (`E_k = c_k V_k`, `U_k = -2 c_k H⁽³⁾_k`);
* `gGram`: the `g`-block of the Gram matrix of `J_n` at `(0, 1, 0)` in the basis `g_j = t^j Π`,
  `gGram i j = laiL n (g_i g_j)(0, 1, 0) = Lf n (Π² t^{i+j})`;
* `gRed`: the reduced block `p⁻³ · gGram` (the entries of `N̄_half`);
* `gRed_entry`: `gRed i j ≡ 15 K₀ (-1)^{i+j} λ(D_a³ x^{i+j}) (mod p)`, from `lemma_G3_monomial`;
* `half_block_unit`: for a band prime (`8n < 3p`, `p + 1 < 3n`, `p ≥ 5`), `det gRed` is a `p`-adic unit
  (`PUnit'`), by `wilson_hankel_padic_unit` and `hankel_sign_twist`.  No condition `p ∉ {3, 5}` is needed:
  the band forces `p ≥ 17`.
-/

set_option autoImplicit false

namespace CatalanCore.Lai.B83HalfBridge

open Polynomial Finset CatalanCore.Basic CatalanCore.NT CatalanCore.Lai.B83Half CatalanCore.Lai.Wilson
open scoped Nat

/-! ## `Lf n` is Lai's functional at `(0, 1, 0)` -/

theorem harm_eq_Hq (r k : ℕ) : CatalanCore.NT.harm r k = CatalanCore.Lai.Hq r k := by
  unfold CatalanCore.NT.harm CatalanCore.Lai.Hq
  refine sum_congr rfl fun i _ => ?_
  rw [one_div]

theorem cc_eq (n k : ℕ) : cc n k = (CatalanCore.Lai.laiCoef n k : ℚ) := by
  unfold cc CatalanCore.Lai.laiCoef
  push_cast
  ring

/-- **The bridge.**  `Lf n P = L_n(P)(0, 1, 0)` for Lai's functional `laiL`. -/
theorem laiL_eval_b (n : ℕ) (P : ℚ[X]) :
    MvPolynomial.eval ![(0 : ℚ), 1, 0] (CatalanCore.Lai.laiL n P) = Lf n P := by
  have h0 : (![(0 : ℚ), 1, 0] : Fin 3 → ℚ) 0 = 0 := rfl
  have h1 : (![(0 : ℚ), 1, 0] : Fin 3 → ℚ) 1 = 1 := rfl
  have h2 : (![(0 : ℚ), 1, 0] : Fin 3 → ℚ) 2 = 0 := rfl
  unfold CatalanCore.Lai.laiL CatalanCore.Lai.laiU CatalanCore.Lai.laiV Lf
  simp only [map_sum, map_mul, map_add, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, h0, h1, h2]
  refine sum_congr rfl fun k _ => ?_
  unfold CatalanCore.Lai.B83Half.EE CatalanCore.Lai.B83Half.UU CatalanCore.Lai.B83Half.dd CatalanCore.Lai.laiH
  simp only [cc_eq, harm_eq_Hq]
  ring

/-! ## The `g`-block of the Gram matrix -/

/-- The basis `g_j = t^j Π`. -/
noncomputable def gBasis (a A j : ℕ) : ℚ[X] := X ^ j * PiA a A

/-- The `g`-block of the Gram matrix of `J_n` at `(a, b, X) = (0, 1, 0)`: `L_n(g_i g_j)(0, 1, 0)`. -/
noncomputable def gGram (n a A K : ℕ) : Matrix (Fin K) (Fin K) ℚ :=
  Matrix.of fun i j => MvPolynomial.eval ![(0 : ℚ), 1, 0]
    (CatalanCore.Lai.laiL n (gBasis a A i * gBasis a A j))

theorem gGram_eq (n a A K : ℕ) (i j : Fin K) :
    gGram n a A K i j = Lf n (PiA a A ^ 2 * X ^ ((i : ℕ) + j)) := by
  unfold gGram
  simp only [Matrix.of_apply]
  rw [laiL_eval_b]
  congr 1
  unfold gBasis
  ring

/-- The reduced block `N̄_half`: `p⁻³ · gGram`. -/
noncomputable def gRed (p n a A K : ℕ) : Matrix (Fin K) (Fin K) ℚ :=
  Matrix.of fun i j => ((p : ℚ) ^ 3)⁻¹ * gGram n a A K i j

/-! ## Entries -/


theorem lamB_eq_bL (g : ℚ[X]) : lamB g = bL g := by
  unfold lamB bL
  rw [Polynomial.lsum_apply, Polynomial.sum_over_range]
  · refine sum_congr rfl fun e _ => ?_
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring
  · intro e; simp

theorem Dp_eq_Dfall (a : ℕ) : Dp a = Dfall a := rfl

section Entries

variable {p n a A : ℕ} [hp : Fact p.Prime]

omit hp in
theorem band_p_ge (hB : Band p n a A) : 17 ≤ p := by
  have := hB.ha; have := hB.hA; have := hB.hAa; have := hB.hn; omega

theorem natDegree_Dfall_le (a : ℕ) : (Dfall a).natDegree ≤ a := by
  unfold Dfall
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i ∈ range a, ((X : ℚ[X]) - C (i : ℚ)).natDegree ≤ ∑ _i ∈ range a, 1 :=
        sum_le_sum fun i _ => by rw [natDegree_X_sub_C]
    _ = a := by simp

theorem lam_mem (hB : Band p n a A) {e : ℕ} (he : e + 2 ≤ 2 * (3 * n - 1 - p)) :
    lamB (Dfall a ^ 3 * X ^ e) ∈ LocRing p := by
  rw [lamB_eq_bL]
  have hmem : PInt p (Dfall a ^ 3 * (X : ℚ[X]) ^ e) :=
    ((PInt.dfall a).pow 3).mul (PInt.pow PInt.ofX e)
  have hdeg : (Dfall a ^ 3 * (X : ℚ[X]) ^ e).natDegree ≤ p - 3 := by
    refine (natDegree_mul_le).trans ?_
    have h1 : (Dfall a ^ 3).natDegree ≤ 3 * a := by
      refine (natDegree_pow_le).trans ?_
      have := natDegree_Dfall_le a
      omega
    rw [natDegree_X_pow]
    have := hB.ha; have := hB.hA; have := hB.hAa; have := hB.hn
    omega
  exact Adm.bL_mem hB.p5 ⟨hmem, hdeg⟩

theorem K0_mem (hB : Band p n a A) : K0 p n A ∈ LocRing p := by
  have hp17 := band_p_ge hB
  have hA : A < p := by have := hB.hA; have := hB.hAa; have := hB.ha; omega
  have h2n : 2 * n < p := by have := hB.hA; have := hB.hAa; have := hB.ha; omega
  have hnd : ¬ p ∣ ((2 * n) !) ^ 3 := fun h => by
    have := (Nat.Prime.dvd_factorial hp.out).1 (hp.out.dvd_of_dvd_pow h)
    omega
  unfold K0
  rw [div_eq_mul_inv]
  have e : (((2 * n) ! : ℕ) : ℚ) ^ 3 = ((((2 * n) ! ^ 3 : ℕ)) : ℚ) := by push_cast; ring
  rw [e]
  refine (LocRing p).mul_mem ((LocRing p).mul_mem ((LocRing p).mul_mem ?_ ?_) ?_)
    (inv_natCast_mem_locRing hnd)
  · exact_mod_cast int_mem_locRing (ℓ := p) 32
  · exact (LocRing p).pow_mem (natCast_mem _) 3
  · exact (LocRing p).pow_mem (natCast_mem _) 2

theorem K0_unit (hB : Band p n a A) : PUnit' p (K0 p n A) := by
  have hp17 := band_p_ge hB
  have hA : A < p := by have := hB.hA; have := hB.hAa; have := hB.ha; omega
  have h2n : 2 * n < p := by have := hB.hA; have := hB.hAa; have := hB.ha; omega
  have h32 : PUnit' p (32 : ℚ) := by
    refine ⟨by norm_num, ?_⟩
    have := padicValRat.of_nat (p := p) (n := 32)
    rw [show ((32 : ℕ) : ℚ) = 32 from by norm_num] at this
    rw [this]
    have hnd : ¬ p ∣ 32 := fun h => by
      have h2 : p ∣ 2 := hp.out.dvd_of_dvd_pow (show p ∣ 2 ^ 5 by simpa using h)
      have := Nat.le_of_dvd (by norm_num) h2; omega
    simp [padicValNat.eq_zero_of_not_dvd hnd]
  unfold K0
  exact ((h32.mul ((PUnit'.fact (by omega : p - 1 < p)).pow 3)).mul
    ((PUnit'.fact hA).pow 2)).div ((PUnit'.fact h2n).pow 3)

theorem fifteen_unit (hB : Band p n a A) : PUnit' p (15 : ℚ) := by
  have hp17 := band_p_ge hB
  refine ⟨by norm_num, ?_⟩
  have := padicValRat.of_nat (p := p) (n := 15)
  rw [show ((15 : ℕ) : ℚ) = 15 from by norm_num] at this
  rw [this]
  have hnd : ¬ p ∣ 15 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  simp [padicValNat.eq_zero_of_not_dvd hnd]

/-- The target of the congruence: `15 K₀ (-1)^{i+j} λ(D_a³ x^{i+j})`. -/
noncomputable def gTarget (p n a A K : ℕ) : Matrix (Fin K) (Fin K) ℚ :=
  Matrix.of fun i j => 15 * K0 p n A * ((-1) ^ ((i : ℕ) + j) * lamB (Dp a ^ 3 * X ^ ((i : ℕ) + j)))

/-- **The half block, entrywise.**  `p⁻³ L(Π² t^{i+j}) ≡ 15 K₀ (-1)^{i+j} λ(D_a³ x^{i+j}) (mod p)`. -/
theorem gRed_entry (hB : Band p n a A) (i j : Fin (3 * n - 1 - p)) :
    PDv p 1 (gRed p n a A (3 * n - 1 - p) i j - gTarget p n a A (3 * n - 1 - p) i j) := by
  have hi := i.2
  have hj := j.2
  have h := lemma_G3_monomial hB (e := (i : ℕ) + j) (by omega)
  obtain ⟨z, hz, hzz⟩ := h
  refine ⟨z, hz, ?_⟩
  unfold gRed gTarget
  simp only [Matrix.of_apply]
  rw [gGram_eq, Dp_eq_Dfall]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : Lf n (PiA a A ^ 2 * X ^ ((i : ℕ) + j)) =
      15 * K0 p n A * (p : ℚ) ^ 3 * ((-1) ^ ((i : ℕ) + j) * bL (Dfall a ^ 3 * X ^ ((i : ℕ) + j))) +
        (p : ℚ) ^ 4 * z := by linear_combination hzz
  rw [this, lamB_eq_bL]
  field_simp
  ring

theorem gTarget_mem (hB : Band p n a A) (i j : Fin (3 * n - 1 - p)) :
    gTarget p n a A (3 * n - 1 - p) i j ∈ LocRing p := by
  have hi := i.2
  have hj := j.2
  unfold gTarget
  simp only [Matrix.of_apply]
  rw [Dp_eq_Dfall]
  refine (LocRing p).mul_mem ((LocRing p).mul_mem ?_ (K0_mem hB)) ?_
  · exact_mod_cast int_mem_locRing (ℓ := p) 15
  · refine (LocRing p).mul_mem ?_ (lam_mem hB (by omega))
    rcases neg_one_pow_eq_or ℚ ((i : ℕ) + j) with h | h <;> rw [h]
    · exact (LocRing p).one_mem
    · exact (LocRing p).neg_mem (LocRing p).one_mem

end Entries

/-! ## Determinants modulo `p` -/

section Det

variable {p : ℕ} [hp : Fact p.Prime]

/-- Entrywise congruence modulo `p` of two `ℤ_(p)`-matrices gives congruent determinants. -/
theorem det_congr {K : ℕ} (M N : Matrix (Fin K) (Fin K) ℚ) (hM : ∀ i j, M i j ∈ LocRing p)
    (hN : ∀ i j, N i j ∈ LocRing p) (h : ∀ i j, PDv p 1 (M i j - N i j)) :
    PDv p 1 (M.det - N.det) := by
  let M' : Matrix (Fin K) (Fin K) (LocRing p) := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix (Fin K) (Fin K) (LocRing p) := Matrix.of fun i j => ⟨N i j, hN i j⟩
  let pR : LocRing p := ⟨(p : ℚ), p_mem⟩
  let I : Ideal (LocRing p) := Ideal.span {pR}
  have key : ((Ideal.Quotient.mk I).mapMatrix M').det = ((Ideal.Quotient.mk I).mapMatrix N').det := by
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨z, hz, hxz⟩ := h i j
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    simp only [M', N', Matrix.of_apply, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, pR]
    linear_combination (-1 : ℚ) * hxz
  rw [← RingHom.map_det, ← RingHom.map_det, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at key
  obtain ⟨w, hw⟩ := key
  refine ⟨w, w.2, ?_⟩
  have e1 : ((M'.det : LocRing p) : ℚ) = M.det := by
    have := RingHom.map_det (LocRing p).subtype M'
    rw [show (LocRing p).subtype.mapMatrix M' = M from by ext i j; rfl] at this
    exact this
  have e2 : ((N'.det : LocRing p) : ℚ) = N.det := by
    have := RingHom.map_det (LocRing p).subtype N'
    rw [show (LocRing p).subtype.mapMatrix N' = N from by ext i j; rfl] at this
    exact this
  have h3 := congrArg (fun x : LocRing p => (x : ℚ)) hw
  simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, pR] at h3
  rw [e1, e2] at h3
  linear_combination (-1 : ℚ) * h3

theorem padicValRat_nonneg_of_mem {z : ℚ} (hz : z ∈ LocRing p) : 0 ≤ padicValRat p z := by
  have hd : ¬ p ∣ z.den := hz
  unfold padicValRat
  rw [padicValNat.eq_zero_of_not_dvd hd]
  simp

/-- A unit plus an element of `p ℤ_(p)` is a unit. -/
theorem PUnit'.add_pdv {x y : ℚ} (hx : PUnit' p x) (hy : PDv p 1 y) : PUnit' p (x + y) := by
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]; exact hx
  obtain ⟨z, hz, hyz⟩ := hy
  have hz0 : z ≠ 0 := fun h => hy0 (by rw [hyz, h]; simp)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hvy : 1 ≤ padicValRat p y := by
    rw [hyz, pow_one, padicValRat.mul hp0 hz0, padicValRat.self hp.out.one_lt]
    have := padicValRat_nonneg_of_mem hz
    omega
  have hvx : padicValRat p x = 0 := hx.2
  have hsum : x + y ≠ 0 := by
    intro h
    have hyx : y = -x := by linarith
    have := padicValRat.neg (p := p) x
    rw [hyx, this, hvx] at hvy
    omega
  refine ⟨hsum, ?_⟩
  rw [padicValRat.add_eq_of_lt hsum hx.1 hy0 (by omega), hvx]

end Det

/-! ## The half block is a `p`-adic unit -/

section Main

variable {p n a A : ℕ} [hp : Fact p.Prime]

theorem gTarget_det (hB : Band p n a A) :
    PUnit' p (gTarget p n a A (3 * n - 1 - p)).det := by
  have hp17 := band_p_ge hB
  obtain ⟨m, hm⟩ := hp.out.eq_two_or_odd'.resolve_left (by omega)
  have hha := hB.ha
  have hhA := hB.hA
  have hhAa := hB.hAa
  have hhn := hB.hn
  -- a = 2c + 1
  have ha : a = 2 * (m - n) + 1 := by omega
  set K := 3 * n - 1 - p with hK
  have hc : K + 3 * (m - n) + 1 < p := by omega
  have hsplit : gTarget p n a A K = (15 * K0 p n A) •
      (Matrix.of fun i j : Fin K => (-1 : ℚ) ^ ((i : ℕ) + j) * lamB (Dp a ^ 3 * X ^ ((i : ℕ) + j))) := by
    ext i j
    simp [gTarget]
  rw [hsplit, Matrix.det_smul, hankel_sign_twist K (fun e => lamB (Dp a ^ 3 * X ^ e))]
  have hW := wilson_hankel_padic_unit (p := p) (m - n) K hc
  rw [← ha] at hW
  exact ((fifteen_unit hB).mul (K0_unit hB)).pow _ |>.mul hW

/-- **The half block.**  For a band prime (`p ≥ 5`, `8n < 3p`, `p + 1 < 3n`), the reduced determinant of the
`g`-block `p⁻³ [L_n(g_i g_j)(0, 1, 0)]_{i,j < 3n-1-p}` is a `p`-adic unit.  In particular it is nonzero. -/
theorem half_block_unit (hB : Band p n a A) :
    PUnit' p (gRed p n a A (3 * n - 1 - p)).det := by
  have h := det_congr (gRed p n a A (3 * n - 1 - p)) (gTarget p n a A (3 * n - 1 - p))
    (fun i j => by
      have := gRed_entry hB i j
      have h1 : gRed p n a A (3 * n - 1 - p) i j =
          (gRed p n a A (3 * n - 1 - p) i j - gTarget p n a A (3 * n - 1 - p) i j) +
            gTarget p n a A (3 * n - 1 - p) i j := by ring
      rw [h1]
      exact (LocRing p).add_mem this.zero_pow_mem (gTarget_mem hB i j))
    (gTarget_mem hB) (gRed_entry hB)
  have h2 := PUnit'.add_pdv (gTarget_det hB) h
  rwa [add_sub_cancel] at h2

theorem half_block_padicValRat (hB : Band p n a A) :
    padicValRat p (gRed p n a A (3 * n - 1 - p)).det = 0 := (half_block_unit hB).2

theorem half_block_det_ne_zero (hB : Band p n a A) :
    (gRed p n a A (3 * n - 1 - p)).det ≠ 0 := (half_block_unit hB).1

/-- The form for a prime in the open band, from the numerical hypotheses. -/
theorem half_block_unit_of_range (h5 : 5 ≤ p) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) :
    PUnit' p (gRed p n (p - 2 * n) (6 * n - 2 * p) (3 * n - 1 - p)).det :=
  half_block_unit (Band.of_range h5 h1 h2)

end Main

#print axioms CatalanCore.Lai.B83HalfBridge.laiL_eval_b
#print axioms CatalanCore.Lai.B83HalfBridge.gGram_eq
#print axioms CatalanCore.Lai.B83HalfBridge.gRed_entry
#print axioms CatalanCore.Lai.B83HalfBridge.half_block_unit

end CatalanCore.Lai.B83HalfBridge
