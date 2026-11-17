module

public import CatalanCore.Lai.ContentCert

@[expose] public section

/-!
# `CatalanCore.Lai.ContentBand7`: Lai Lemma 5.4 Cases 2-4 (`7n/2 < p ≤ 6n`), `Band7Stmt`

Paper: `lai-lean-plan/BAND7-2026-11-17.md`.  One shifted-root CRT basis: the residues `r < D` carry the roots
`-(r + p)` (the `ℓ = 1` node itself), the others `-r`.  Entry bounds `v(L_n(f_x f_y)) ≥ π_x + π_y`
(`entryB`), the determinant by `GV.det`, `GV_laiJ_of_crt` (`band_gen`), and the three parameter choices
(`band7_proof : Band7Stmt`).  The discharge `lai_content_unconditional` applies `lai_content_cert`.

Rows B7-01 to B7-14 of the note.
-/

open Finset CatalanCore.Basic CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

section Nodes

variable {p : ℕ} [hp : Fact p.Prime]

/-- B7-01. The class constant on the band `3n < p ≤ 6n`. -/
lemma sig_band {n p : ℕ} (h1 : 3 * n < p) (h2 : p ≤ 6 * n) (s : ℕ) :
    sig n p s = (if s ≤ 6 * n - p then 0 else 2) + (if p - 2 * n ≤ s then 3 else 0) := by
  have e6 : 6 * n % p = 6 * n - p := by
    rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)]
  have e2 : 2 * n % p = 2 * n := Nat.mod_eq_of_lt (by omega)
  unfold sig r6 r2
  rw [e6, e2]

/-- B7-02. `v(U_k) ≥ -3` for `k / p < p`. -/
lemma laiU_ge3 (k : ℕ) (hk : k / p < p) : GV p (-3) (laiU k) := by
  have h := laiU_expand (p := p) k hk
  have h3 := Hq_mem (p := p) 3 (k / p) hk
  have a : GV p (-3) (MvPolynomial.C (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) * MvPolynomial.X 1 :
      MvPolynomial (Fin 3) ℚ) := by
    have hp0 := p_ne_zero' (p := p)
    have := GV_CX_nat (p := p) 3 (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) 1 (by
      have : (p : ℚ) ^ 3 * (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) = -2 * Hq 3 (k / p) := by
        field_simp
      rw [this]
      exact (LocRing p).mul_mem lm2 h3)
    simpa using this
  have e : laiU k = (laiU k - MvPolynomial.C (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) * MvPolynomial.X 1) +
      MvPolynomial.C (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) * MvPolynomial.X 1 := by ring
  rw [e]
  exact (h.mono (by norm_num)).add a

/-- B7-03. A node with `ℓ ≥ 1` seen from its own exact root `-k`. -/
theorem node1_root (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p)
    (m : ℕ) (R : Polynomial ℚ) (hR : IntPoly p R) (e : ℤ)
    (he : e ≤ (sig n p (k % p) : ℤ) - 4 + (min m 1 : ℕ) ∨ 2 ≤ m) :
    GV p e (laiNd n k ((Polynomial.X + Polynomial.C (k : ℚ)) ^ m * R)) := by
  have hkp : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using (show k < p ^ 2 by omega)
  rcases m with _ | _ | m
  · have := node_ge (p := p) n k h8 h3 hk hl 0 R hR
    simp only [pow_zero, one_mul, Nat.cast_zero, add_zero] at this ⊢
    refine this.mono ?_
    rcases he with he | he
    · simpa using he
    · omega
  · obtain ⟨u, hu, -, -⟩ := laiCoef_unit (p := p) h8 h3 k hk
    have hu' : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u := by exact_mod_cast hu
    have hcσ : GV p (sig n p (k % p) : ℤ) (MvPolynomial.C (laiCoef n k : ℚ) : MP) :=
      GV_C_zpow _ _ (u : ℚ) (by rw [hu', zpow_natCast]) (natq_mem u)
    have hkq : (-(k : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem _)
    have hR0 : R.eval (-(k : ℚ)) ∈ LocRing p := hR.eval_mem hkq
    have e1 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (0 + 1) * R).eval (-(k : ℚ)) = 0 := by simp
    have e2 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (0 + 1) * R).derivative.eval (-(k : ℚ)) =
        R.eval (-(k : ℚ)) := by
      simp [Polynomial.derivative_mul]
    unfold laiNd
    rw [e1, e2]
    simp only [map_zero, mul_zero, add_zero]
    have := hcσ.mul ((laiU_ge3 (p := p) k hkp).mul (GV.const_loc hR0))
    refine this.mono ?_
    rcases he with he | he
    · simp at he ⊢; omega
    · omega
  · have e1 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (m + 1 + 1) * R).eval (-(k : ℚ)) = 0 := by simp
    have e2 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (m + 1 + 1) * R).derivative.eval (-(k : ℚ)) = 0 := by
      simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
    unfold laiNd
    rw [e1, e2]
    simp only [map_zero, mul_zero, add_zero]
    exact GV.zero _

/-- B7-04. A node with `ℓ = 0` seen from the shifted root `-(k + p)`. -/
theorem node0_shift (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hkp : k < p)
    (m : ℕ) (R : Polynomial ℚ) (hR : IntPoly p R) :
    GV p ((sig n p k : ℤ) - 1 + m)
      (laiNd n k ((Polynomial.X + Polynomial.C ((k + p : ℕ) : ℚ)) ^ m * R)) := by
  obtain ⟨u, hu, -, -⟩ := laiCoef_unit (p := p) h8 h3 k hk
  have hmod : k % p = k := Nat.mod_eq_of_lt hkp
  rw [hmod] at hu
  have hu' : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p k) * u := by exact_mod_cast hu
  have hcσ : GV p (sig n p k : ℤ) (MvPolynomial.C (laiCoef n k : ℚ) : MP) :=
    GV_C_zpow _ _ (u : ℚ) (by rw [hu', zpow_natCast]) (natq_mem u)
  have hkq : (-(k : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem _)
  have hR0 : R.eval (-(k : ℚ)) ∈ LocRing p := hR.eval_mem hkq
  have hR1 : (Polynomial.derivative R).eval (-(k : ℚ)) ∈ LocRing p := hR.derivative.eval_mem hkq
  have hU := laiU_zero (p := p) k hkp
  have hV := laiV_zero (p := p) n k h8 hk hkp
  have hp0 := p_ne_zero' (p := p)
  have hc : (-(k : ℚ)) + ((k + p : ℕ) : ℚ) = p := by push_cast; ring
  -- the value
  have hF : ((Polynomial.X + Polynomial.C ((k + p : ℕ) : ℚ)) ^ m * R).eval (-(k : ℚ)) =
      (p : ℚ) ^ (m : ℤ) * R.eval (-(k : ℚ)) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, hc, zpow_natCast]
  -- the derivative
  have hD : ∃ y ∈ LocRing p, ((Polynomial.X + Polynomial.C ((k + p : ℕ) : ℚ)) ^ m * R).derivative.eval
      (-(k : ℚ)) = (p : ℚ) ^ ((m : ℤ) - 1) * y := by
    rcases m with _ | m
    · refine ⟨(p : ℚ) * (Polynomial.derivative R).eval (-(k : ℚ)), (LocRing p).mul_mem lp hR1, ?_⟩
      simp only [pow_zero, one_mul, Nat.cast_zero, zero_sub, zpow_neg, zpow_one]
      field_simp
    · refine ⟨((m + 1 : ℕ) : ℚ) * R.eval (-(k : ℚ)) + (p : ℚ) * (Polynomial.derivative R).eval (-(k : ℚ)),
        (LocRing p).add_mem ((LocRing p).mul_mem (natq_mem _) hR0) ((LocRing p).mul_mem lp hR1), ?_⟩
      simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_natCast,
        Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, hc, add_zero, mul_one]
      have : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
      rw [this, zpow_natCast]
      push_cast
      field_simp
      ring
  obtain ⟨y, hy, hDy⟩ := hD
  have hGD : GV p ((m : ℤ) - 1)
      (MvPolynomial.C (((Polynomial.X + Polynomial.C ((k + p : ℕ) : ℚ)) ^ m * R).derivative.eval
        (-(k : ℚ))) : MP) := GV_C_zpow _ _ y hDy hy
  have hGF : GV p (m : ℤ)
      (MvPolynomial.C (((Polynomial.X + Polynomial.C ((k + p : ℕ) : ℚ)) ^ m * R).eval
        (-(k : ℚ))) : MP) := GV_C_zpow _ _ _ hF hR0
  unfold laiNd
  have := hcσ.mul (((hU.mul hGD).mono (show (m : ℤ) - 1 ≤ 0 + ((m : ℤ) - 1) by omega)).add
    ((hV.mul hGF).mono (show (m : ℤ) - 1 ≤ -1 + (m : ℤ) by omega)))
  refine this.mono ?_
  omega

/-- B7-05. `V_k` is integral at the special residues `6n - k < p`, `2n + k < p`. -/
lemma laiV_special (n k : ℕ) (hk : k < p) (h6 : 6 * n < p + k) (h2 : 2 * n + k < p) :
    GV p 0 (laiV n k) := by
  have hH : laiH n k ∈ LocRing p := by
    unfold laiH
    have a1 := Hq_mem (p := p) 1 (2 * n + k) h2
    have a2 := Hq_mem (p := p) 1 (6 * n - k) (by omega)
    have a3 := Hq_mem (p := p) 1 k hk
    exact (LocRing p).sub_mem ((LocRing p).add_mem ((LocRing p).mul_mem l3 a1)
      ((LocRing p).mul_mem l2 a2)) ((LocRing p).mul_mem l5 a3)
  have h2' := Hq_mem (p := p) 2 k hk
  have h3 := Hq_mem (p := p) 3 k hk
  have h4 := Hq_mem (p := p) 4 k hk
  have e : laiV n k = MvPolynomial.C (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * MvPolynomial.X 0 +
      MvPolynomial.C (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) * MvPolynomial.X 1 +
      MvPolynomial.C 6 * MvPolynomial.X 2 := by
    unfold laiV
    simp only [map_sub, map_add, map_mul, map_neg, map_ofNat]
    ring
  have l6 : (6 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) 6
  rw [e]
  have a : GV p 0 (MvPolynomial.C (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * MvPolynomial.X 0 :
      MvPolynomial (Fin 3) ℚ) := by
    simpa using (GV.const_loc ((LocRing p).sub_mem ((LocRing p).mul_mem ((LocRing p).mul_mem l3 hH) h2')
      ((LocRing p).mul_mem l6 h3)) : GV p 0 _).mul (GV.var (0 : Fin 3))
  have b : GV p 0 (MvPolynomial.C (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) * MvPolynomial.X 1 :
      MvPolynomial (Fin 3) ℚ) := by
    simpa using (GV.const_loc ((LocRing p).sub_mem ((LocRing p).mul_mem ((LocRing p).mul_mem l2 hH) h3)
      ((LocRing p).mul_mem l6 h4)) : GV p 0 _).mul (GV.var (1 : Fin 3))
  have c : GV p 0 (MvPolynomial.C 6 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℚ) := by
    simpa using (GV.const_loc l6 : GV p 0 _).mul (GV.var (2 : Fin 3))
  exact (a.add b).add c

/-- B7-06. A node with `ℓ = 0` at a special residue: `v ≥ σ`, for every integral `F`. -/
theorem node0_special (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hkp : k < p)
    (h6 : 6 * n < p + k) (h2 : 2 * n + k < p) (F : Polynomial ℚ) (hF : IntPoly p F) :
    GV p (sig n p k : ℤ) (laiNd n k F) := by
  obtain ⟨u, hu, -, -⟩ := laiCoef_unit (p := p) h8 h3 k hk
  have hmod : k % p = k := Nat.mod_eq_of_lt hkp
  rw [hmod] at hu
  have hu' : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p k) * u := by exact_mod_cast hu
  have hcσ : GV p (sig n p k : ℤ) (MvPolynomial.C (laiCoef n k : ℚ) : MP) :=
    GV_C_zpow _ _ (u : ℚ) (by rw [hu', zpow_natCast]) (natq_mem u)
  have hkq : (-(k : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem _)
  have hR0 : F.eval (-(k : ℚ)) ∈ LocRing p := hF.eval_mem hkq
  have hR1 : (Polynomial.derivative F).eval (-(k : ℚ)) ∈ LocRing p := hF.derivative.eval_mem hkq
  have hU := laiU_zero (p := p) k hkp
  have hV := laiV_special (p := p) n k hkp h6 h2
  unfold laiNd
  have := hcσ.mul ((hU.mul (GV.const_loc hR1)).add (hV.mul (GV.const_loc hR0)))
  exact this.mono (by omega)

end Nodes

section Poly

variable {p : ℕ} [hp : Fact p.Prime]

/-- B7-07. `∏_r (X + τ_r)^{ν_r}`. -/
noncomputable def PdZ (τ ν : Fin p → ℕ) : Polynomial ℚ :=
  ∏ r : Fin p, (Polynomial.X + Polynomial.C ((τ r : ℕ) : ℚ)) ^ ν r

/-- the cofactor at `s`. -/
noncomputable def RRZ (τ ν : Fin p → ℕ) (s : Fin p) : Polynomial ℚ :=
  ∏ r ∈ (Finset.univ : Finset (Fin p)).erase s, (Polynomial.X + Polynomial.C ((τ r : ℕ) : ℚ)) ^ ν r

lemma PdZ_mul (τ ν₁ ν₂ : Fin p → ℕ) :
    PdZ τ ν₁ * PdZ τ ν₂ = PdZ τ (fun r => ν₁ r + ν₂ r) := by
  unfold PdZ
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun r _ => (pow_add _ _ _).symm

lemma PdZ_decomp (τ ν : Fin p → ℕ) (s : Fin p) :
    PdZ τ ν = (Polynomial.X + Polynomial.C ((τ s : ℕ) : ℚ)) ^ (ν s) * RRZ τ ν s := by
  unfold PdZ RRZ
  exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin p)) _ (Finset.mem_univ s)).symm

lemma PdZ_int (τ ν : Fin p → ℕ) : IntPoly p (PdZ τ ν) :=
  IntPoly.prod _ _ fun r _ => (IntPoly.X_add_C_nat _).pow _

lemma RRZ_int (τ ν : Fin p → ℕ) (s : Fin p) : IntPoly p (RRZ τ ν s) :=
  IntPoly.prod _ _ fun r _ => (IntPoly.X_add_C_nat _).pow _

end Poly

section Basis

/-- B7-08. The shifted position of the residue `r`: `r + p` if `r < D`, else `r`. -/
def tauB (p D : ℕ) (r : Fin p) : ℕ := if (r : ℕ) < D then (r : ℕ) + p else (r : ℕ)

/-- the roots `-τ_r`. -/
def aB (p D : ℕ) (r : Fin p) : ℤ := -((tauB p D r : ℕ) : ℤ)

/-- multiplicities: `2` below `t`, `1` up to `D + N`, `0` above. -/
def muB (D t N r : ℕ) : ℕ := if r < t then 2 else if r < D + N then 1 else 0

/-- the index type (no `g_j` part). -/
abbrev BI (p D t N : ℕ) : Type := (Σ r : Fin p, Fin (muB D t N (r : ℕ))) ⊕ Fin 0

/-- the basis. -/
noncomputable def fB (p D t N : ℕ) : BI p D t N → Polynomial ℚ :=
  crtFam (fun r : Fin p => ((aB p D r : ℤ) : ℚ)) (fun r : Fin p => muB D t N (r : ℕ)) 0

/-- exponents of `(X + τ_r)`. -/
def nuB (p D t N : ℕ) : BI p D t N → Fin p → ℕ
  | Sum.inl ⟨r0, i⟩ => fun r => if r = r0 then (i : ℕ) else muB D t N (r : ℕ)
  | Sum.inr _ => fun _ => 0

/-- potentials. -/
def piB (p D t N : ℕ) : BI p D t N → ℤ
  | Sum.inl ⟨r0, i⟩ => if (r0 : ℕ) < D then (i : ℤ) - 2 else 1
  | Sum.inr _ => 0

lemma fB_eq {p : ℕ} (D t N : ℕ) (x : BI p D t N) : fB p D t N x = PdZ (tauB p D) (nuB p D t N x) := by
  have hX : ∀ r : Fin p, (Polynomial.X - Polynomial.C ((aB p D r : ℤ) : ℚ) : Polynomial ℚ) =
      Polynomial.X + Polynomial.C ((tauB p D r : ℕ) : ℚ) := by
    intro r; simp [aB, sub_eq_add_neg]
  rcases x with ⟨r0, i⟩ | j
  · simp only [fB, crtFam, Sum.elim_inl, crtE, nuB, PdZ, pow_zero, one_mul]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin p)) _ (Finset.mem_univ r0)]
    simp only [hX, if_true]
    congr 1
    refine Finset.prod_congr rfl fun r hr => ?_
    have : r ≠ r0 := (Finset.mem_erase.1 hr).1
    simp [this]
  · exact j.elim0

lemma aB_inj {p : ℕ} [hp : Fact p.Prime] (D : ℕ) :
    Function.Injective fun r : Fin p => (Int.castRingHom (ZMod p)) (aB p D r) := by
  intro r r' hrr
  have key : ∀ r : Fin p, (Int.castRingHom (ZMod p)) (aB p D r) = -((r : ℕ) : ZMod p) := by
    intro r
    simp only [aB, tauB]
    split_ifs
    · simp
    · simp
  have hrr' : -((r : ℕ) : ZMod p) = -((r' : ℕ) : ZMod p) := by rw [← key, ← key]; exact hrr
  have := (ZMod.natCast_eq_natCast_iff' (r : ℕ) (r' : ℕ) p).1 (neg_inj.1 hrr')
  rw [Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] at this
  exact Fin.ext this

/-- the parameters G1-G5 of the note: `D = min a (A + 1)`, `t ≤ D`, `t + D + N = 3n`, `N > 0 → t = D`,
`D + N ≤ a`, with `a = p - 2n`, `A = 6n - p`. -/
structure BPar (n p D t N : ℕ) : Prop where
  hD : D = min (p - 2 * n) (6 * n - p + 1)
  ht : t ≤ D
  hsum : t + D + N = 3 * n
  hN : 0 < N → t = D
  hDN : D + N ≤ p - 2 * n

lemma muB_facts (D t N r : ℕ) (htD : t ≤ D + N) :
    (r < t → muB D t N r = 2) ∧ (t ≤ r → r < D + N → muB D t N r = 1) ∧ (D + N ≤ r → muB D t N r = 0) := by
  unfold muB
  refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_⟩ <;> split_ifs <;> omega

lemma muB_le (D t N r : ℕ) : muB D t N r ≤ 2 := by
  unfold muB; split_ifs <;> omega

end Basis

section Pair

/-- B7-09, case `s < D`. -/
theorem pairB_i {n p D t N : ℕ} (hpar : BPar n p D t N) (h1 : 3 * n < p) (h2 : p ≤ 6 * n)
    (x y : BI p D t N) (s : ℕ) (hs : s < p) (hsD : s < D) :
    (piB p D t N x + piB p D t N y ≤ -4 + ((min (nuB p D t N x ⟨s, hs⟩ + nuB p D t N y ⟨s, hs⟩) 1 : ℕ) : ℤ) ∨
        2 ≤ nuB p D t N x ⟨s, hs⟩ + nuB p D t N y ⟨s, hs⟩) ∧
      piB p D t N x + piB p D t N y ≤ ((nuB p D t N x ⟨s, hs⟩ + nuB p D t N y ⟨s, hs⟩ : ℕ) : ℤ) - 1 := by
  have hD := hpar.hD
  have ht := hpar.ht
  have hsum := hpar.hsum
  have hN := hpar.hN
  have hDN := hpar.hDN
  rcases x with ⟨r0, i⟩ | j
  swap; exact j.elim0
  rcases y with ⟨r1, j⟩ | j'
  swap; exact j'.elim0
  have hi : (i : ℕ) < muB D t N (r0 : ℕ) := i.2
  have hj : (j : ℕ) < muB D t N (r1 : ℕ) := j.2
  have m0 := muB_facts D t N (r0 : ℕ) (by omega)
  have m1 := muB_facts D t N (r1 : ℕ) (by omega)
  have ms := muB_facts D t N s (by omega)
  have b0 := muB_le D t N (r0 : ℕ)
  have b1 := muB_le D t N (r1 : ℕ)
  have bs := muB_le D t N s
  simp only [nuB, piB, Fin.ext_iff]
  split_ifs <;> omega

/-- B7-09, case `D ≤ s ≤ A`. -/
theorem pairB_ii {n p D t N : ℕ} (hpar : BPar n p D t N) (h1 : 3 * n < p) (h2 : p ≤ 6 * n)
    (x y : BI p D t N) (hsD : D ≤ 6 * n - p) :
    piB p D t N x + piB p D t N y ≤ -2 := by
  have hD := hpar.hD
  have ht := hpar.ht
  have hsum := hpar.hsum
  have hN := hpar.hN
  have hDN := hpar.hDN
  rcases x with ⟨r0, i⟩ | j
  swap; exact j.elim0
  rcases y with ⟨r1, j⟩ | j'
  swap; exact j'.elim0
  have hi : (i : ℕ) < muB D t N (r0 : ℕ) := i.2
  have hj : (j : ℕ) < muB D t N (r1 : ℕ) := j.2
  have m0 := muB_facts D t N (r0 : ℕ) (by omega)
  have m1 := muB_facts D t N (r1 : ℕ) (by omega)
  have b0 := muB_le D t N (r0 : ℕ)
  have b1 := muB_le D t N (r1 : ℕ)
  simp only [piB]
  split_ifs <;> omega

/-- B7-09, every pair: `π_x + π_y ≤ 2`. -/
theorem pairB_iii {n p D t N : ℕ} (x y : BI p D t N) :
    piB p D t N x + piB p D t N y ≤ 2 := by
  rcases x with ⟨r0, i⟩ | j
  swap; exact j.elim0
  rcases y with ⟨r1, j⟩ | j'
  swap; exact j'.elim0
  have hi : (i : ℕ) < muB D t N (r0 : ℕ) := i.2
  have hj : (j : ℕ) < muB D t N (r1 : ℕ) := j.2
  have b0 := muB_le D t N (r0 : ℕ)
  have b1 := muB_le D t N (r1 : ℕ)
  simp only [piB]
  split_ifs <;> omega

end Pair

section Entry

variable {p : ℕ} [hp : Fact p.Prime]

/-- B7-10. **The entry bound**: `v(L_n(f_x f_y)) ≥ π_x + π_y`. -/
theorem entryB {n D t N : ℕ} (hpar : BPar n p D t N) (h1 : 3 * n < p) (h2 : p ≤ 6 * n)
    (x y : BI p D t N) :
    GV p (piB p D t N x + piB p D t N y) (laiL n (fB p D t N x * fB p D t N y)) := by
  have hD := hpar.hD
  have ht := hpar.ht
  have hsum := hpar.hsum
  have hN := hpar.hN
  have hDN := hpar.hDN
  have hn : 1 ≤ n := by have := hp.out.two_le; omega
  have h8 : 8 * n < p ^ 2 := by nlinarith
  have h3 : 3 ≤ p := by omega
  have hpos := hp.out.pos
  rw [fB_eq, fB_eq, PdZ_mul]
  set ν : Fin p → ℕ := fun r => nuB p D t N x r + nuB p D t N y r with hν
  have hFint : IntPoly p (PdZ (tauB p D) ν) := PdZ_int _ _
  rw [laiL_eq_sum]
  refine GV.sum fun k hk => ?_
  have hk6 : k ≤ 6 * n := by have := Finset.mem_range.1 hk; omega
  by_cases hl : 1 ≤ k / p
  · -- ℓ = 1, k = s + p
    have hpk : p ≤ k := by
      by_contra hc
      have : k / p = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have hmod : k % p = k - p := by rw [Nat.mod_eq_sub_mod hpk, Nat.mod_eq_of_lt (by omega)]
    have hs : k % p < p := Nat.mod_lt _ hpos
    by_cases hsD : k % p < D
    · have hσ : sig n p (k % p) = 0 := by
        rw [sig_band h1 h2]; split_ifs <;> omega
      have hτ : tauB p D ⟨k % p, hs⟩ = k := by
        unfold tauB; simp only [hsD, if_true]; omega
      have hdec := PdZ_decomp (tauB p D) ν ⟨k % p, hs⟩
      rw [hτ] at hdec
      rw [hdec]
      obtain ⟨hpi, -⟩ := pairB_i hpar h1 h2 x y (k % p) hs hsD
      refine node1_root (p := p) n k h8 h3 hk6 hl _ _ (RRZ_int _ _ _) _ ?_
      rw [hσ]
      rcases hpi with h | h
      · left; simp only [hν]; omega
      · right; simp only [hν]; omega
    · have hσ : sig n p (k % p) = 3 := by
        rw [sig_band h1 h2]; split_ifs <;> omega
      have := node_ge (p := p) n k h8 h3 hk6 hl 0 (PdZ (tauB p D) ν) hFint
      simp only [pow_zero, one_mul, Nat.cast_zero, add_zero] at this
      refine this.mono ?_
      have := pairB_ii hpar h1 h2 x y (by omega)
      rw [hσ]; omega
  · have hkp : k < p := by
      by_contra hc
      exact hl (Nat.div_pos (by omega) hpos)
    by_cases hsD : k < D
    · have hσ : sig n p k = 0 := by
        rw [sig_band h1 h2]; split_ifs <;> omega
      have hτ : tauB p D ⟨k, hkp⟩ = k + p := by
        unfold tauB; simp only [hsD, if_true]
      have hdec := PdZ_decomp (tauB p D) ν ⟨k, hkp⟩
      rw [hτ] at hdec
      rw [hdec]
      obtain ⟨-, hpi⟩ := pairB_i hpar h1 h2 x y k hkp hsD
      refine (node0_shift (p := p) n k h8 h3 hk6 hkp _ _ (RRZ_int _ _ _)).mono ?_
      rw [hσ]; simp only [hν]; omega
    · by_cases hA : k ≤ 6 * n - p
      · have hσ : sig n p k = 3 := by
          rw [sig_band h1 h2]; split_ifs <;> omega
        have := node0_ge (p := p) n k h8 h3 hk6 hkp 0 (PdZ (tauB p D) ν) hFint
        simp only [pow_zero, one_mul] at this
        refine this.mono ?_
        have := pairB_ii hpar h1 h2 x y (by omega)
        rw [hσ]; omega
      · by_cases ha : k < p - 2 * n
        · have hσ : sig n p k = 2 := by
            rw [sig_band h1 h2]; split_ifs <;> omega
          refine (node0_special (p := p) n k h8 h3 hk6 hkp (by omega) (by omega) _ hFint).mono ?_
          have := pairB_iii (n := n) (p := p) (D := D) (t := t) (N := N) x y
          rw [hσ]; omega
        · have hσ : sig n p k = 5 := by
            rw [sig_band h1 h2]; split_ifs <;> omega
          have := node0_ge (p := p) n k h8 h3 hk6 hkp 0 (PdZ (tauB p D) ν) hFint
          simp only [pow_zero, one_mul] at this
          refine this.mono ?_
          have := pairB_iii (n := n) (p := p) (D := D) (t := t) (N := N) x y
          rw [hσ]; omega

end Entry

section Sums

/-- the per-residue potential sum. -/
def gB (D t N r : ℕ) : ℤ := if r < t then -3 else if r < D then -2 else if r < D + N then 1 else 0

lemma sum_range_muB (D t N : ℕ) (htD : t ≤ D + N) (T : ℕ) :
    ∑ r ∈ Finset.range T, muB D t N r = 2 * min T t + (min T (D + N) - min T t) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    unfold muB
    split_ifs <;> omega

lemma sum_range_gB (D t N : ℕ) (htD : t ≤ D) (T : ℕ) :
    ∑ r ∈ Finset.range T, gB D t N r =
      -3 * ((min T t : ℕ) : ℤ) - 2 * ((min T D : ℕ) - (min T t : ℕ)) +
        (((min T (D + N) : ℕ) : ℤ) - (min T D : ℕ)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    unfold gB
    split_ifs <;> omega

lemma inner_piB (D t N r : ℕ) (htD : t ≤ D) :
    ∑ i ∈ Finset.range (muB D t N r), (if r < D then (i : ℤ) - 2 else 1) = gB D t N r := by
  unfold muB gB
  split_ifs <;> simp [Finset.sum_range_succ] <;> omega

/-- B7-11. `∑ μ_r = 3n`. -/
lemma sum_muB {n p D t N : ℕ} (hpar : BPar n p D t N) :
    ∑ r : Fin p, muB D t N (r : ℕ) = 3 * n := by
  have hD := hpar.hD
  have ht := hpar.ht
  have hsum := hpar.hsum
  have hDN := hpar.hDN
  rw [Fin.sum_univ_eq_sum_range (fun r => muB D t N r) p, sum_range_muB D t N (by omega)]
  omega

/-- B7-11. `∑ π = N - t - 2D`. -/
lemma sum_piB {n p D t N : ℕ} (hpar : BPar n p D t N) :
    ∑ x : BI p D t N, piB p D t N x = (N : ℤ) - t - 2 * D := by
  have hD := hpar.hD
  have ht := hpar.ht
  have hsum := hpar.hsum
  have hDN := hpar.hDN
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [piB, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  have : ∀ r : Fin p, ∑ i : Fin (muB D t N (r : ℕ)), (if (r : ℕ) < D then (i : ℤ) - 2 else 1) =
      gB D t N (r : ℕ) := fun r => by
    rw [Fin.sum_univ_eq_sum_range (fun i => if (r : ℕ) < D then (i : ℤ) - 2 else 1) (muB D t N (r : ℕ))]
    exact inner_piB D t N r ht
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun r => gB D t N r) p, sum_range_gB D t N ht]
  omega

end Sums

section Gen

variable {p : ℕ} [hp : Fact p.Prime]

/-- B7-12. **The general bound** under the parameters G1-G5. -/
theorem band_gen {n D t N : ℕ} (hpar : BPar n p D t N) (h1 : 3 * n < p) (h2 : p ≤ 6 * n) :
    GV p (2 * ((N : ℤ) - t - 2 * D)) (laiJ n) := by
  have hN : ∑ r : Fin p, muB D t N (r : ℕ) + 0 = 3 * n := by simpa using sum_muB hpar
  have hcard : Fintype.card (BI p D t N) = 3 * n := by
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    simpa using sum_muB hpar
  let e : BI p D t N ≃ Fin (3 * n) := Fintype.equivFinOfCardEq hcard
  have hG : GV p (∑ x, piB p D t N x + ∑ x, piB p D t N x)
      (Matrix.of fun x y : BI p D t N => laiL n (fB p D t N x * fB p D t N y)).det :=
    GV.det _ _ _ fun x y => entryB hpar h1 h2 x y
  have := GV_laiJ_of_crt (p := p) n (aB p D) (aB_inj D) (fun r : Fin p => muB D t N (r : ℕ)) 0 hN e _ hG
  rw [nuP_zero (by omega)] at this
  rw [sum_piB hpar] at this
  simpa [two_mul] using this

end Gen

section Final

/-- the statement of the discharge. -/
theorem band7_proof : Band7Stmt := by
  intro n p _ hn h7 h6
  rcases (show p ≤ 4 * n ∨ (4 * n < p ∧ 2 * p ≤ 9 * n + 1) ∨ 9 * n + 2 ≤ 2 * p by omega) with h | h | h
  · -- case 2: p ≤ 4n
    have hpar : BPar n p (p - 2 * n) (5 * n - p) 0 :=
      ⟨by omega, by omega, by omega, by omega, by omega⟩
    have := band_gen hpar (by omega) h6
    unfold w7
    rw [if_pos h]
    refine this.mono ?_
    omega
  · -- case 3
    have hpar : BPar n p (6 * n - p + 1) (p - 3 * n - 1) 0 :=
      ⟨by omega, by omega, by omega, by omega, by omega⟩
    have := band_gen hpar (by omega) h6
    unfold w7
    rw [if_neg (by omega)]
    split_ifs
    · refine this.mono ?_
      omega
    · refine this.mono ?_
      omega
  · -- case 4
    have hpar : BPar n p (6 * n - p + 1) (6 * n - p + 1) (2 * p - 9 * n - 2) :=
      ⟨by omega, by omega, by omega, by omega, by omega⟩
    have := band_gen hpar (by omega) h6
    unfold w7
    rw [if_neg (by omega), if_neg (by omega)]
    refine this.mono ?_
    omega

/-- B7-14. **`lai_content_cert` with `Band7Stmt` discharged**: the content limit of Lai's `J_n`, with only the
W2 prefix datum `(Ŝ, hS, hR)` left. -/
theorem lai_content_unconditional (Shat : ℚ)
    (hS : CatalanCore.Content.PartialSums.partialS e23 d23 1000 ≤ Shat)
    (hR : Shat + CatalanCore.Content.PartialSums.Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ n : ℕ, R₀ ≤ n →
      0 < signedDen n laiW ∧
      (∀ q : ℕ, ∀ [Fact q.Prime], GV q 0 (MvPolynomial.C (signedDen n laiW) * laiJ n)) ∧
      Real.log ((signedDen n laiW : ℚ) : ℝ) ≤ (2868723663 / 10 ^ 8 + ε) * (n : ℝ) ^ 2 :=
  lai_content_cert band7_proof Shat hS hR hε

end Final

end CatalanCore.Lai

#print axioms CatalanCore.Lai.entryB
#print axioms CatalanCore.Lai.band_gen
#print axioms CatalanCore.Lai.band7_proof
#print axioms CatalanCore.Lai.lai_content_unconditional
