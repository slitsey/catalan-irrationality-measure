module

public import CatalanCore.Lai.NV7Inst
public import CatalanCore.Lai.NV7Dual
public import CatalanCore.Content.UnitClass
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Matrix.Block

@[expose] public section

/-! # `CatalanCore.Lai.B83Blocks`: the integral side of Theorem B83 (ledger LB03-LB06, algebraic core)

Note `N9-LAI-SMALLPRIME-NV-2026-11-20.md` §3.4.  Band `8n/3 < p < 3n - 1`, `a = p - 2n` odd,
`A₂ = 6n - 2p`, classes `A = [0, A₂]` (multiplicity 4), `C = (A₂, a)` (multiplicity 3).

* **Part 1 (`hA`, `hC`, `det_MA`, `det_MC`)**: the Hankel sequences of Lemmas A and C (own-node main
  terms `NV7.Mb` plus the D-node corrections at `m = 5, 6` resp. `m = 3, 4`), the cancellations
  `h₅ = h₆ = 0`, and the determinants `det M_A = -2²·13²·24359`, `det M_C = 2¹⁵`.
* **Part 2 (`det_intBlock_ne`)**: a block diagonal matrix with blocks `w_r • M_A`, `w_r • M_C` and unit
  weights is nonsingular when `p ∉ {2, 13, 24359}`.
* **Part 3 (`u83_A`, `u83_C`)**: Lemma U83, `K₀ P_r(r)³ ≡ 32 ĉ_r Ψ_r(-r)²` on `A` and `≡ 8 ĉ_r Ψ_r(-r)²`
  on `C`, in `ZMod p`, with `ĉ_r` the unit part of `c_r` (`Lai.kappa`, `Lai.chat` of `ContentLaw`).
-/

open Matrix Finset CatalanCore.Lai CatalanCore.Lai.NV7
open scoped Nat

namespace CatalanCore.Lai.B83

/-! ### Part 1: the Hankel sequences, their cancellations and determinants -/

section Hankel

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- D-node correction of the A-block at `m = i + i'` in units of `ĉΨ²`: `-7·32` at `m = 5`
(`-7 p K₀ Σ_D G`, `K₀P³ ≡ 32 ĉΨ²`), `+12·32` at `m = 6` (`12 K₀ P³`); `0` otherwise. -/
def corrA (m : ℕ) : ℤ := if m = 5 then -7 * 32 else if m = 6 then 12 * 32 else 0

/-- `h_m`: own nodes (`4 Mb(m,1,-2,-6) + Mb(m,2,-9/4,-105/8)`, as `NV7.hh`) plus the D-node correction. -/
def hA (ℓ : ℕ) [Fact ℓ.Prime] (m : ℕ) : ZMod ℓ := NV7.hh ℓ m + (corrA m : ZMod ℓ)

/-- D-node correction of the C-block: `-7·8` at `m = 3`, `-16·8` at `m = 4`. -/
def corrC (m : ℕ) : ℤ := if m = 3 then -7 * 8 else if m = 4 then -16 * 8 else 0

/-- Own-node main term of a C residue: the single node `j = 1`, `(U, E) = (-2, -10)`. -/
def PhiC (ℓ : ℕ) [Fact ℓ.Prime] (m : ℕ) : ZMod ℓ := Mb m 1 (-2) (-10) 1

def hC (ℓ : ℕ) [Fact ℓ.Prime] (m : ℕ) : ZMod ℓ := PhiC ℓ m + (corrC m : ZMod ℓ)

theorem hA_vals (h2 : (2 : ZMod ℓ) ≠ 0) :
    hA ℓ 0 = -297 / 8 ∧ hA ℓ 1 = 40 ∧ hA ℓ 2 = -103 / 2 ∧ hA ℓ 3 = 78 ∧ hA ℓ 4 = -130 ∧
      hA ℓ 5 = 0 ∧ hA ℓ 6 = 0 := by
  obtain ⟨h4, h8⟩ := ne48 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hA, hh, Mb, corrA] <;> simp <;> field_simp <;> ring

theorem hC_vals : hC ℓ 0 = -10 ∧ hC ℓ 1 = 8 ∧ hC ℓ 2 = -6 ∧ hC ℓ 3 = -52 ∧ hC ℓ 4 = -130 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hC, PhiC, Mb, corrC] <;> simp <;> ring

/-- the `4 × 4` Hankel matrix of Lemma A. -/
def MA (ℓ : ℕ) [Fact ℓ.Prime] : Matrix (Fin 4) (Fin 4) (ZMod ℓ) :=
  Matrix.of fun i j => hA ℓ ((i : ℕ) + j)

/-- the `3 × 3` Hankel matrix of Lemma C. -/
def MC (ℓ : ℕ) [Fact ℓ.Prime] : Matrix (Fin 3) (Fin 3) (ZMod ℓ) :=
  Matrix.of fun i j => hC ℓ ((i : ℕ) + j)

/-- **Lemma A, determinant.** `det M_A = -16466684 = -2²·13²·24359`. -/
theorem det_MA (h2 : (2 : ZMod ℓ) ≠ 0) : (MA ℓ).det = -16466684 := by
  obtain ⟨h4, h8⟩ := ne48 h2
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := hA_vals h2
  have hM : MA ℓ = (Matrix.of ![![(-297 : ZMod ℓ) / (8 : ZMod ℓ), 40, (-103 : ZMod ℓ) / (2 : ZMod ℓ), 78],
      ![40, (-103 : ZMod ℓ) / (2 : ZMod ℓ), 78, -130],
      ![(-103 : ZMod ℓ) / (2 : ZMod ℓ), 78, -130, 0], ![78, -130, 0, 0]] :
      Matrix (Fin 4) (Fin 4) (ZMod ℓ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [MA, v0, v1, v2, v3, v4, v5, v6]
  rw [hM, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  field_simp
  ring

/-- **Lemma C, determinant.** `det M_C = 2^15`. -/
theorem det_MC : (MC ℓ).det = 32768 := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := hC_vals (ℓ := ℓ)
  rw [Matrix.det_fin_three]
  simp [MC, v0, v1, v2, v3, v4]
  ring

theorem zmod_ne_zero_of_ne_prime {q : ℕ} (hq : q.Prime) (h : ℓ ≠ q) : (q : ZMod ℓ) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact h ((Nat.prime_dvd_prime_iff_eq hℓ.out hq).1 hd)

theorem det_MA_ne (h2 : ℓ ≠ 2) (h13 : ℓ ≠ 13) (h24359 : ℓ ≠ 24359) : (MA ℓ).det ≠ 0 := by
  have z2 : (2 : ZMod ℓ) ≠ 0 := by
    simpa using zmod_ne_zero_of_ne_prime (ℓ := ℓ) Nat.prime_two h2
  have z13 : (13 : ZMod ℓ) ≠ 0 := by
    simpa using zmod_ne_zero_of_ne_prime (ℓ := ℓ) (by norm_num : Nat.Prime 13) h13
  have z24359 : (24359 : ZMod ℓ) ≠ 0 := by
    simpa using zmod_ne_zero_of_ne_prime (ℓ := ℓ) (by norm_num : Nat.Prime 24359) h24359
  rw [det_MA z2]
  have e : (-16466684 : ZMod ℓ) = -(2 ^ 2 * 13 ^ 2 * 24359) := by norm_num
  rw [e, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ z2) (pow_ne_zero _ z13)) z24359

theorem det_MC_ne (h2 : ℓ ≠ 2) : (MC ℓ).det ≠ 0 := by
  have z2 : (2 : ZMod ℓ) ≠ 0 := by
    simpa using zmod_ne_zero_of_ne_prime (ℓ := ℓ) Nat.prime_two h2
  rw [det_MC]
  have e : (32768 : ZMod ℓ) = 2 ^ 15 := by norm_num
  rw [e]
  exact pow_ne_zero _ z2

end Hankel

/-! ### Part 2: block diagonal assembly -/

section Assembly

variable {F : Type*} [Field F]

/-- Block diagonal matrix with blocks `B r • H`, indexed by `Fin α × Fin k`, is nonsingular. -/
theorem det_blockDiag_ne {α k : ℕ} (B : Fin α → F) (hB : ∀ r, B r ≠ 0) (H : Matrix (Fin k) (Fin k) F)
    (hH : H.det ≠ 0) :
    (Matrix.of fun (x y : Fin α × Fin k) => if x.1 = y.1 then B x.1 * H x.2 y.2 else 0).det ≠ 0 := by
  classical
  have hmat : (Matrix.of fun (x y : Fin α × Fin k) => if x.1 = y.1 then B x.1 * H x.2 y.2 else 0) =
      (blockDiagonal (fun r : Fin α => B r • H)).submatrix (Equiv.prodComm (Fin α) (Fin k))
        (Equiv.prodComm (Fin α) (Fin k)) := by
    ext ⟨r, i⟩ ⟨r', i'⟩
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      blockDiagonal_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hmat, det_submatrix_equiv_self, det_blockDiagonal]
  refine Finset.prod_ne_zero_iff.2 fun r _ => ?_
  rw [det_smul]
  exact mul_ne_zero (pow_ne_zero _ (hB r)) hH

end Assembly

section IntBlock

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {α γ : ℕ}

/-- The reduced integral block `N̄_int` of Theorem B83 on the index set `A × Fin 4 ⊕ C × Fin 3`:
block diagonal with the blocks `ĉ_rΨ_r(-r)² · M_A` (`r ∈ A`, weight `wA r`) and
`ĉ_rΨ_r(-r)² · M_C` (`r ∈ C`, weight `wC r`). -/
def intBlock (wA : Fin α → ZMod ℓ) (wC : Fin γ → ZMod ℓ) :
    Matrix ((Fin α × Fin 4) ⊕ (Fin γ × Fin 3)) ((Fin α × Fin 4) ⊕ (Fin γ × Fin 3)) (ZMod ℓ) :=
  Matrix.fromBlocks (Matrix.of fun (x y : Fin α × Fin 4) => if x.1 = y.1 then wA x.1 * MA ℓ x.2 y.2 else 0) 0 0
    (Matrix.of fun (x y : Fin γ × Fin 3) => if x.1 = y.1 then wC x.1 * MC ℓ x.2 y.2 else 0)

/-- **Output of LB04-LB06 for LB09.** For `p ∉ {2, 13, 24359}` and unit weights, `det N̄_int ≠ 0`. -/
theorem det_intBlock_ne (wA : Fin α → ZMod ℓ) (wC : Fin γ → ZMod ℓ) (hwA : ∀ r, wA r ≠ 0)
    (hwC : ∀ r, wC r ≠ 0) (h2 : ℓ ≠ 2) (h13 : ℓ ≠ 13) (h24359 : ℓ ≠ 24359) :
    (intBlock wA wC).det ≠ 0 := by
  unfold intBlock
  rw [det_fromBlocks_zero₂₁]
  exact mul_ne_zero (det_blockDiag_ne wA hwA (MA ℓ) (det_MA_ne h2 h13 h24359))
    (det_blockDiag_ne wC hwC (MC ℓ) (det_MC_ne h2))

end IntBlock

/-! ### Part 3: Lemma U83 (unit identities), generic field cores -/

section Cores

/-- Algebraic core of U83 on `A`: `K₀ P³ = 32 ĉ Ψ²` from `(p-1)! = -1` and Wilson reflection `e g = -σ`. -/
theorem coreA {F : Type*} [Field F] (A2f rf f2 f2n g e σ Y : F) (hrf : rf ≠ 0) (hf2 : f2 ≠ 0)
    (hf2n : f2n ≠ 0) (hY : Y * f2 = g) (heg : e * g = -σ) :
    (32 * (-1) ^ 3 * A2f ^ 2 / f2n ^ 3) * (rf * σ * g) ^ 3 =
      32 * ((A2f / (rf * f2)) ^ 2 * (e / (f2n * rf)) ^ 3) * (rf ^ 4 * f2 ^ 4 * Y ^ 3) ^ 2 := by
  have key : e ^ 3 * g ^ 3 = -σ ^ 3 := by rw [← mul_pow, heg]; ring
  have hg : g = Y * f2 := hY.symm
  subst hg
  field_simp
  linear_combination (-(32 * A2f ^ 2 * Y ^ 3)) * key

/-- Algebraic core of U83 on `C`: `K₀ P³ = 8 (4 ĉ) Ψ²` (`ĉ` here is the low-digit `chat`, `κ(0) = 4`). -/
theorem coreC {F : Type*} [Field F] (A2f rf x y g e σ Z sx f2n : F) (hrf : rf ≠ 0) (hx : x ≠ 0)
    (hy : y ≠ 0) (hf2n : f2n ≠ 0) (hg : g ≠ 0) (hZ : Z * x = rf) (hxy : x * y = -sx)
    (hsx : sx ^ 2 = 1) (heg : e * g = -σ) :
    (32 * (-1) ^ 3 * A2f ^ 2 / f2n ^ 3) * (rf * σ * g) ^ 3 =
      8 * (4 * ((A2f / (rf * y)) ^ 2 * (e / (f2n * rf)) ^ 3)) * (Z ^ 4 * (sx * x) ^ 3 * g ^ 3) ^ 2 := by
  have key : e ^ 3 * g ^ 3 = -σ ^ 3 := by rw [← mul_pow, heg]; ring
  have hZ' : Z = rf / x := by field_simp; exact hZ
  have hxy2 : x ^ 2 * y ^ 2 = 1 := by
    have : (x * y) ^ 2 = 1 := by rw [hxy]; linear_combination hsx
    linear_combination this
  subst hZ'
  field_simp
  linear_combination (-32 * A2f ^ 2 * sx ^ 6) * key + 32 * A2f ^ 2 * σ ^ 3 * (sx ^ 4 + sx ^ 2 + 1) * hsx
    - 32 * A2f ^ 2 * σ ^ 3 * hxy2

end Cores

section U83

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_ne_zero_zmod (h5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  simpa using zmod_ne_zero_of_ne_prime (ℓ := p) Nat.prime_two (by omega)

/-- the multiplicity of the residue `t` in the band: `4` on `A = [0, A₂]`, `3` on `C`. -/
def muB (A2 t : ℕ) : ℕ := if t ≤ A2 then 4 else 3

theorem muB_le {A2 t : ℕ} (h : t ≤ A2) : muB A2 t = 4 := by simp [muB, h]

theorem muB_gt {A2 t : ℕ} (h : ¬ t ≤ A2) : muB A2 t = 3 := by simp [muB, h]

/-- `P_r(r) = ∏_{t < a, t ≠ r} (r - t)`. -/
def PrB (p a r : ℕ) : ZMod p := ∏ t ∈ (range a).erase r, ((r : ZMod p) - ((t : ℕ) : ZMod p))

/-- `Ψ_r(-r) = ∏_{t < a, t ≠ r} (t - r)^{μ_t}`. -/
def PsiB (p A2 a r : ℕ) : ZMod p := ∏ t ∈ (range a).erase r, (((t : ℕ) : ZMod p) - r) ^ muB A2 t

/-- `K₀ = 32 (p-1)!³ A₂!² / (2n)!³`. -/
def K0B (p n A2 : ℕ) [Fact p.Prime] : ZMod p := 32 * fz p (p - 1) ^ 3 * fz p A2 ^ 2 / fz p (2 * n) ^ 3

/-- the unit part `ĉ_r` of `c_r = C(6n,r)² C(2n+r,r)³` (`κ(0) ĉ`, Lemma N), with `b = [r > A₂]`. -/
def cunit (p n A2 b r : ℕ) [Fact p.Prime] : ZMod p := kappa p 2 0 b 0 0 * chat p A2 (2 * n) b 0 r

theorem prod_neg_Ico {a b : ℕ} (r : ℕ) :
    ∏ t ∈ Ico a b, ((r : ZMod p) - ((t : ℕ) : ZMod p)) =
      (-1) ^ (b - a) * ∏ t ∈ Ico a b, (((t : ℕ) : ZMod p) - r) := by
  have : ∀ t ∈ Ico a b, ((r : ZMod p) - ((t : ℕ) : ZMod p)) = (-1) * (((t : ℕ) : ZMod p) - r) :=
    fun t _ => by ring
  rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]

theorem PrB_eq {a r : ℕ} (hr : r < a) :
    PrB p a r = ((r ! : ℕ) : ZMod p) * (-1) ^ (a - 1 - r) * (((a - 1 - r) ! : ℕ) : ZMod p) := by
  unfold PrB
  have hsplit : (range a).erase r = range r ∪ Ico (r + 1) a := by
    ext t; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hd : Disjoint (range r) (Ico (r + 1) a) := by
    rw [Finset.disjoint_left]; intro t h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.prod_union hd]
  have h1 := prod_range_sub (ℓ := p) r r le_rfl
  rw [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one] at h1
  have h3 := prod_Ico_after (ℓ := p) r (a - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at h3
  rw [h1, prod_neg_Ico, h3]
  have : a - (r + 1) = a - 1 - r := by omega
  rw [this]; ring

theorem PsiB_A {A2 a r : ℕ} (hr : r ≤ A2) (hA2 : A2 < a) :
    PsiB p A2 a r = ((r ! : ℕ) : ZMod p) ^ 4 * (((A2 - r) ! : ℕ) : ZMod p) ^ 4 *
        (∏ t ∈ Ico (A2 + 1) a, (((t : ℕ) : ZMod p) - r)) ^ 3 ∧
      (∏ t ∈ Ico (A2 + 1) a, (((t : ℕ) : ZMod p) - r)) * (((A2 - r) ! : ℕ) : ZMod p) =
        (((a - 1 - r) ! : ℕ) : ZMod p) := by
  have hsplit : (range a).erase r = range r ∪ Ico (r + 1) (A2 + 1) ∪ Ico (A2 + 1) a := by
    ext t; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hd1 : Disjoint (range r) (Ico (r + 1) (A2 + 1)) := by
    rw [Finset.disjoint_left]; intro t h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega
  have hd2 : Disjoint (range r ∪ Ico (r + 1) (A2 + 1)) (Ico (A2 + 1) a) := by
    rw [Finset.disjoint_left]; intro t h1 h2
    simp only [mem_union, mem_range, mem_Ico] at h1 h2; omega
  have h1 := prod_range_sub (ℓ := p) r r le_rfl
  rw [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one] at h1
  have h2 := prod_Ico_after (ℓ := p) r A2 hr
  have h3 := prod_Ico_after (ℓ := p) r (a - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at h3
  have hcons := Finset.prod_Ico_consecutive (fun t : ℕ => (((t : ℕ) : ZMod p) - r)) (show r + 1 ≤ A2 + 1 by omega)
    (show A2 + 1 ≤ a by omega)
  refine ⟨?_, ?_⟩
  · unfold PsiB
    rw [hsplit, Finset.prod_union hd2, Finset.prod_union hd1]
    have e1 : ∏ t ∈ range r, (((t : ℕ) : ZMod p) - r) ^ muB A2 t = (((r ! : ℕ) : ZMod p)) ^ 4 := by
      rw [← h1, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun t ht => ?_
      have : muB A2 t = 4 := muB_le (by have := mem_range.1 ht; omega)
      rw [this]
      have : (((t : ℕ) : ZMod p) - r) = -((r : ZMod p) - t) := by ring
      rw [this]; exact Even.neg_pow (by decide) _
    have e2 : ∏ t ∈ Ico (r + 1) (A2 + 1), (((t : ℕ) : ZMod p) - r) ^ muB A2 t =
        (((A2 - r) ! : ℕ) : ZMod p) ^ 4 := by
      rw [← h2, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun t ht => ?_
      have : muB A2 t = 4 := muB_le (by have := mem_Ico.1 ht; omega)
      rw [this]
    have e3 : ∏ t ∈ Ico (A2 + 1) a, (((t : ℕ) : ZMod p) - r) ^ muB A2 t =
        (∏ t ∈ Ico (A2 + 1) a, (((t : ℕ) : ZMod p) - r)) ^ 3 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun t ht => ?_
      have : muB A2 t = 3 := muB_gt (by have := mem_Ico.1 ht; omega)
      rw [this]
    rw [e1, e2, e3]
  · rw [h2, h3] at hcons
    rw [mul_comm]; exact hcons

theorem PsiB_C {A2 a r : ℕ} (h1 : A2 < r) (h2 : r < a) :
    PsiB p A2 a r =
        (∏ t ∈ range (A2 + 1), ((r : ZMod p) - ((t : ℕ) : ZMod p))) ^ 4 *
          ((-1) ^ (r - (A2 + 1)) * (((r - (A2 + 1)) ! : ℕ) : ZMod p)) ^ 3 *
          (((a - 1 - r) ! : ℕ) : ZMod p) ^ 3 := by
  have hsplit : (range a).erase r = range (A2 + 1) ∪ Ico (A2 + 1) r ∪ Ico (r + 1) a := by
    ext t; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hd1 : Disjoint (range (A2 + 1)) (Ico (A2 + 1) r) := by
    rw [Finset.disjoint_left]; intro t h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega
  have hd2 : Disjoint (range (A2 + 1) ∪ Ico (A2 + 1) r) (Ico (r + 1) a) := by
    rw [Finset.disjoint_left]; intro t h1 h2
    simp only [mem_union, mem_range, mem_Ico] at h1 h2; omega
  have hI := prod_Ico_sub (ℓ := p) r (A2 + 1) r (by omega) le_rfl
  rw [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one] at hI
  have h3 := prod_Ico_after (ℓ := p) r (a - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at h3
  unfold PsiB
  rw [hsplit, Finset.prod_union hd2, Finset.prod_union hd1]
  have e1 : ∏ t ∈ range (A2 + 1), (((t : ℕ) : ZMod p) - r) ^ muB A2 t =
      (∏ t ∈ range (A2 + 1), ((r : ZMod p) - ((t : ℕ) : ZMod p))) ^ 4 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    have : muB A2 t = 4 := muB_le (by have := mem_range.1 ht; omega)
    rw [this]
    have : (((t : ℕ) : ZMod p) - r) = -((r : ZMod p) - t) := by ring
    rw [this]; exact Even.neg_pow (by decide) _
  have e2 : ∏ t ∈ Ico (A2 + 1) r, (((t : ℕ) : ZMod p) - r) ^ muB A2 t =
      ((-1) ^ (r - (A2 + 1)) * (((r - (A2 + 1)) ! : ℕ) : ZMod p)) ^ 3 := by
    have hs : ∏ t ∈ Ico (A2 + 1) r, (((t : ℕ) : ZMod p) - r) =
        (-1) ^ (r - (A2 + 1)) * (((r - (A2 + 1)) ! : ℕ) : ZMod p) := by
      have : ∀ t ∈ Ico (A2 + 1) r, (((t : ℕ) : ZMod p) - r) = (-1) * ((r : ZMod p) - ((t : ℕ) : ZMod p)) :=
        fun t _ => by ring
      rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, hI]
    rw [← hs, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    have : muB A2 t = 3 := muB_gt (by have := mem_Ico.1 ht; omega)
    rw [this]
  have e3 : ∏ t ∈ Ico (r + 1) a, (((t : ℕ) : ZMod p) - r) ^ muB A2 t =
      (((a - 1 - r) ! : ℕ) : ZMod p) ^ 3 := by
    rw [← h3, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    have : muB A2 t = 3 := muB_gt (by have := mem_Ico.1 ht; omega)
    rw [this]
  rw [e1, e2, e3]

theorem kappa_A0 (h5 : 5 ≤ p) : kappa p 2 0 0 0 0 = 1 := by
  have h2 := two_ne_zero_zmod (p := p) h5
  simp [kappa, fz, Nat.factorial]
  field_simp
  exact Or.inl h2

theorem kappa_C0 : kappa p 2 0 1 0 0 = 4 := by
  simp [kappa, fz, Nat.factorial]
  norm_num

/-- Wilson reflection in the form used by U83: `(2n + r)! (a - 1 - r)! = -(-1)^{a-1-r}` for `a` odd. -/
theorem reflect_B83 {n a r : ℕ} (ha : a + 2 * n = p) (hodd : a % 2 = 1) (hr : r < a) :
    (((2 * n + r) ! : ℕ) : ZMod p) * (((a - 1 - r) ! : ℕ) : ZMod p) = -(-1) ^ (a - 1 - r) := by
  have hW := fact_reflect (p := p) (2 * n + r) (by omega)
  have e : p - 1 - (2 * n + r) = a - 1 - r := by omega
  rw [e] at hW
  rw [hW]
  rcases Nat.even_or_odd (a - 1 - r) with he | ho
  · have hodd2 : Odd (2 * n + r + 1) := by
      rw [Nat.odd_iff]; have := Nat.even_iff.1 he; omega
    rw [hodd2.neg_one_pow, he.neg_one_pow]
  · have heven : Even (2 * n + r + 1) := by
      rw [Nat.even_iff]; have := Nat.odd_iff.1 ho; omega
    rw [heven.neg_one_pow, ho.neg_one_pow]; simp

/-- **Lemma U83 on `A`** (`LB03`): `K₀ P_r(r)³ = 32 ĉ_r Ψ_r(-r)²` in `ZMod p`, `r ≤ A₂`. -/
theorem u83_A {n A2 a r : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n)
    (hA2 : A2 < a) (hodd : a % 2 = 1) (hr : r ≤ A2) :
    K0B p n A2 * PrB p a r ^ 3 = 32 * cunit p n A2 0 r * PsiB p A2 a r ^ 2 := by
  have hrA : r < a := by omega
  obtain ⟨hPs, hY⟩ := PsiB_A (p := p) hr hA2
  have hrf : ((r ! : ℕ) : ZMod p) ≠ 0 := fz_ne_zero (p := p) (by omega)
  have hf2 : (((A2 - r) ! : ℕ) : ZMod p) ≠ 0 := fz_ne_zero (p := p) (by omega)
  have hf2n : (((2 * n) ! : ℕ) : ZMod p) ≠ 0 := fz_ne_zero (p := p) (by omega)
  have heg := reflect_B83 (p := p) ha hodd hrA
  have hfin := coreA (((A2 ! : ℕ) : ZMod p)) _ _ _ _ _ _ _ hrf hf2 hf2n hY heg
  unfold K0B cunit chat
  rw [kappa_A0 h5, one_mul, PrB_eq hrA, hPs]
  have hW : fz p (p - 1) = -1 := CatalanCore.Content.wilson p
  rw [hW]
  simp only [zero_mul, Nat.sub_zero]
  exact hfin

/-- **Lemma U83 on `C`** (`LB03`): `K₀ P_r(r)³ = 8 ĉ_r Ψ_r(-r)²` in `ZMod p`, `A₂ < r < a`. -/
theorem u83_C {n A2 a r : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n)
    (hodd : a % 2 = 1) (h1 : A2 < r) (h2 : r < a) :
    K0B p n A2 * PrB p a r ^ 3 = 8 * cunit p n A2 1 r * PsiB p A2 a r ^ 2 := by
  have hZ := prod_range_sub (ℓ := p) r (A2 + 1) (by omega)
  have hrf : ((r ! : ℕ) : ZMod p) ≠ 0 := fz_ne_zero (p := p) (by omega)
  have hx : (((r - (A2 + 1)) ! : ℕ) : ZMod p) ≠ 0 := fz_ne_zero (p := p) (by omega)
  have hy : (((A2 + 1 * p - r) ! : ℕ) : ZMod p) ≠ 0 := fz_ne_zero (p := p) (by omega)
  have hg : (((a - 1 - r) ! : ℕ) : ZMod p) ≠ 0 := fz_ne_zero (p := p) (by omega)
  have hf2n : (((2 * n) ! : ℕ) : ZMod p) ≠ 0 := fz_ne_zero (p := p) (by omega)
  have heg := reflect_B83 (p := p) ha hodd h2
  have hxy : (((r - (A2 + 1)) ! : ℕ) : ZMod p) * (((A2 + 1 * p - r) ! : ℕ) : ZMod p) =
      -(-1) ^ (r - (A2 + 1)) := by
    have hW := fact_reflect (p := p) (r - (A2 + 1)) (by omega)
    have e : p - 1 - (r - (A2 + 1)) = A2 + 1 * p - r := by omega
    rw [e] at hW
    rw [hW, pow_succ]; ring
  have hsx : ((-1 : ZMod p) ^ (r - (A2 + 1))) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have hfin := coreC (((A2 ! : ℕ) : ZMod p)) _ _ _ _ _ _ _ _ _ hrf hx hy hf2n hg hZ hxy hsx heg
  unfold K0B cunit chat
  rw [kappa_C0, PrB_eq h2, PsiB_C (p := p) h1 h2]
  have hW : fz p (p - 1) = -1 := CatalanCore.Content.wilson p
  rw [hW]
  simp only [zero_mul, Nat.sub_zero]
  exact hfin

/-- the weight `ĉ_r Ψ_r(-r)²` of the block of the residue `r` (`b = [r > A₂]`). -/
def wtB (p n A2 a b r : ℕ) [Fact p.Prime] : ZMod p := cunit p n A2 b r * PsiB p A2 a r ^ 2

theorem PsiB_ne_zero {A2 a r : ℕ} (hap : a ≤ p) (hr : r < a) : PsiB p A2 a r ≠ 0 := by
  unfold PsiB
  refine Finset.prod_ne_zero_iff.2 fun t ht => pow_ne_zero _ ?_
  have ht' := Finset.mem_erase.1 ht
  have htl := Finset.mem_range.1 ht'.2
  exact sub_ne_zero.2 fun h => ht'.1 (cast_inj_lt (by omega) (by omega) h)

theorem cunit_ne_zero {n A2 a b r : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA2 : A2 < a) (hr : r < a)
    (hb : (b = 0 ∧ r ≤ A2) ∨ (b = 1 ∧ A2 < r)) : cunit p n A2 b r ≠ 0 := by
  have h2 := two_ne_zero_zmod (p := p) h5
  have hk : kappa p 2 0 b 0 0 ≠ 0 := by
    rcases hb with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [kappa_A0 h5]; exact one_ne_zero
    · rw [kappa_C0]
      have : (4 : ZMod p) = 2 ^ 2 := by norm_num
      rw [this]; exact pow_ne_zero _ h2
  have hf : ∀ m, m < p → fz p m ≠ 0 := fun m hm => fz_ne_zero (p := p) hm
  have hc : chat p A2 (2 * n) b 0 r ≠ 0 := by
    unfold chat
    have e1 : A2 + b * p - r < p := by rcases hb with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp <;> omega
    have e2 : 2 * n + r - 0 * p < p := by omega
    exact mul_ne_zero (pow_ne_zero _ (div_ne_zero (hf _ (by omega)) (mul_ne_zero (hf _ (by omega)) (hf _ e1))))
      (pow_ne_zero _ (div_ne_zero (hf _ e2) (mul_ne_zero (hf _ (by omega)) (hf _ (by omega)))))
  exact mul_ne_zero hk hc

theorem wtB_ne_zero {n A2 a b r : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA2 : A2 < a) (hr : r < a)
    (hb : (b = 0 ∧ r ≤ A2) ∨ (b = 1 ∧ A2 < r)) : wtB p n A2 a b r ≠ 0 :=
  mul_ne_zero (cunit_ne_zero h5 ha hA2 hr hb) (pow_ne_zero _ (PsiB_ne_zero (by omega) hr))

/-- **The integral block of Theorem B83 is nonsingular** (output of LB03-LB06 for LB09).
In the band, with the blocks `wtB • M_A` on `A = [0, A₂]` and `wtB • M_C` on `C = (A₂, a)`,
`det N̄_int ≠ 0` for `p ∉ {2, 13, 24359}`. -/
theorem det_intBlock_band_ne {n A2 a : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA2 : A2 < a)
    (h13 : p ≠ 13) (h24359 : p ≠ 24359) :
    (intBlock (α := A2 + 1) (γ := a - 1 - A2)
      (fun r => wtB p n A2 a 0 r.val) (fun r => wtB p n A2 a 1 (A2 + 1 + r.val))).det ≠ 0 :=
  det_intBlock_ne _ _
    (fun r => wtB_ne_zero h5 ha hA2 (by have := r.2; omega) (Or.inl ⟨rfl, by have := r.2; omega⟩))
    (fun r => wtB_ne_zero h5 ha hA2 (by have := r.2; omega) (Or.inr ⟨rfl, by omega⟩))
    (by omega) h13 h24359

end U83


end CatalanCore.Lai.B83

#print axioms CatalanCore.Lai.B83.det_MA
#print axioms CatalanCore.Lai.B83.det_MC
#print axioms CatalanCore.Lai.B83.det_intBlock_ne
#print axioms CatalanCore.Lai.B83.u83_A
#print axioms CatalanCore.Lai.B83.u83_C
#print axioms CatalanCore.Lai.B83.det_intBlock_band_ne
