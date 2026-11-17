module

public import CatalanCore.Lai.ContentCert
public import CatalanCore.Lai.DecayCert
public import CatalanCore.Lai.NVTied
public import CatalanCore.Lai.NV7Tied
public import CatalanCore.Lai.Tied
public import CatalanCore.Measure.TiedNV
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `CatalanCore.Lai.Roots`: the plane and ratio roots of Lai's families (ledger LR10, LR11)

The prime-tied criterion `measure_of_family_tiedNV_index` applied to the rescaled families
`laiPlaneFamS a b` and `laiRatioFamS` (`Q n = m_n * J_n`, content constant `0`, decay exponent
`D' = D - 28.68723663`), with the three `TiedNV` families of primes `ℓ ≡ 1 (18)` (Lai), `ℓ ≡ 5, 3 (7)`
(NV7).

* `tiedScaled`: the one-step adaptor from a `TiedNV` over `Fam` to a `TiedNV` over `scaleFam Fam P m`
  (`evalQ` is multiplied by `m n > 0`; the admissibility `P` is supplied on the tied members);
* `laiExc b`: the exception primes (`ℓ < 100`, `73`, `1039`, the divisors of `b`); the tied members of the
  remaining primes have `n ≥ 10`;
* `lai_roots_of`: both roots, in the plain measure form, from the three inputs `LaiInputs`
  (`Band7Stmt`, the decay data `LaiDecayData`, the C01 prefix datum).

Say μ, never B, for the irrationality measure.
-/

open Filter Topology CatalanCore.Measure CatalanCore.Uniform CatalanCore.Lai.DecayCert

namespace CatalanCore.Lai

/-! ### 1. The adaptor to a rescaled family -/

/-- A `TiedNV` over `Fam` gives one over the rescaled family `scaleFam Fam P m` when `m > 0` and the tied
members satisfy `P`. -/
noncomputable def tiedScaled {Fam : PolyFamily} {scale : Fam.ι → ℕ} {M : ℕ} {W : ℤ → ℕ → ℕ}
    (T : TiedNV Fam scale M W) (P : Fam.ι → Prop) (m : Fam.ι → ℚ) (hm : ∀ n, 0 < m n)
    (hP : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ZMod M) ∈ T.S → ℓ ∉ T.exc → P (T.mem ℓ)) :
    TiedNV (scaleFam Fam P m) scale M W where
  S := T.S
  S_unit := T.S_unit
  c := T.c
  c_pos := T.c_pos
  d := T.d
  e := T.e
  exc := T.exc
  mem := T.mem
  adm := fun ℓ hp hs hx => ⟨T.adm ℓ hp hs hx, hP ℓ hp hs hx⟩
  size_eq := T.size_eq
  Bad := T.Bad
  bad_dvd := T.bad_dvd
  nv := fun ℓ hp hs hx p q hq hb => by
    rw [scaleFam_evalQ]
    exact mul_ne_zero (hm _).ne' (T.nv ℓ hp hs hx p q hq hb)

/-! ### 2. The exception set -/

/-- Exception primes common to plane and ratio: `ℓ < 100`, `73`, `1039`. -/
def laiExc0 : Finset ℕ := Finset.range 100 ∪ {73, 1039}

/-- Exception primes of the plane `a ζ3 + b ζ4`: `laiExc0` and the divisors of `b`. -/
def laiExc (b : ℤ) : Finset ℕ := laiExc0 ∪ Nat.divisors b.natAbs

theorem ge100_of_not_mem {ℓ : ℕ} {s : Finset ℕ} (hs : laiExc0 ⊆ s) (h : ℓ ∉ s) : 100 ≤ ℓ := by
  by_contra h'
  exact h (hs (by unfold laiExc0; simp only [Finset.mem_union, Finset.mem_range]; left; omega))

theorem laiExc0_sub_laiExc (b : ℤ) : laiExc0 ⊆ laiExc b := Finset.subset_union_left

theorem exc_lt11 {s : Finset ℕ} (hs : laiExc0 ⊆ s) : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 11 → ℓ ∈ s := by
  intro ℓ _ h
  exact hs (by unfold laiExc0; simp only [Finset.mem_union, Finset.mem_range]; left; omega)

theorem exc_73 {s : Finset ℕ} (hs : laiExc0 ⊆ s) : 73 ∈ s :=
  hs (by unfold laiExc0; simp)

theorem exc_1039 {s : Finset ℕ} (hs : laiExc0 ⊆ s) : 1039 ∈ s :=
  hs (by unfold laiExc0; simp)

theorem exc_dvd {b : ℤ} (hb : b ≠ 0) : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ b → ℓ ∈ laiExc b := by
  intro ℓ _ hd
  unfold laiExc
  exact Finset.mem_union_right _ (Nat.mem_divisors.mpr ⟨Int.natCast_dvd.1 hd, by simpa using hb⟩)

/-- Class membership at modulus `126` for large primes. -/
theorem class_of_mem {ℓ m' r0 : ℕ} (hp : ℓ.Prime) (h100 : 100 ≤ ℓ) (hm' : m' ∣ 126)
    (h : (ℓ : ZMod 126) ∈ classSet 126 m' r0) : ℓ % m' = r0 :=
  (mem_classSet_iff hp (by omega) hm').mp h

/-! ### 3. The scaled `TiedNV` families -/

section Tied

variable {Fam : PolyFamily}

/-- `n ≥ 10` for the Lai primes `ℓ ≡ 1 (18)`, `ℓ ≥ 100` (`n = 2 ((ℓ - 1)/9)`). -/
theorem lai_mem10 {ℓ : ℕ} (hp : ℓ.Prime) (h100 : 100 ≤ ℓ)
    (h : (ℓ : ZMod 126) ∈ classSet 126 18 1) : 10 ≤ 2 * ((ℓ - 1) / 9) := by
  have := class_of_mem hp h100 (by norm_num) h
  omega

theorem nv7a_mem10 {ℓ : ℕ} (hp : ℓ.Prime) (h100 : 100 ≤ ℓ)
    (h : (ℓ : ZMod 126) ∈ classSet 126 7 5) : 10 ≤ (3 * ℓ - 1) / 7 := by
  have := class_of_mem hp h100 (by norm_num) h
  omega

theorem nv7b_mem10 {ℓ : ℕ} (hp : ℓ.Prime) (h100 : 100 ≤ ℓ)
    (h : (ℓ : ZMod 126) ∈ classSet 126 7 3) : 10 ≤ (3 * ℓ - 2) / 7 := by
  have := class_of_mem hp h100 (by norm_num) h
  omega

/-- The three scaled plane families (`b ≠ 0`). -/
noncomputable def planeTiedS (a b : ℤ) (hb : b ≠ 0) :
    Fin 3 → TiedNV (laiPlaneFamS a b) id 126 planeW :=
  ![tiedScaled (NV.laiPlaneTied a b (laiExc b) (exc_lt11 (laiExc0_sub_laiExc b)) (exc_dvd hb))
      (fun n : ℕ => 10 ≤ n) laiM laiM_pos
      (fun ℓ hp hs hx => lai_mem10 hp (ge100_of_not_mem (laiExc0_sub_laiExc b) hx) hs),
    tiedScaled (NV7.nv7aPlaneTied a b (laiExc b) (exc_lt11 (laiExc0_sub_laiExc b)) (exc_dvd hb)
        (exc_73 (laiExc0_sub_laiExc b)) (exc_1039 (laiExc0_sub_laiExc b)))
      (fun n : ℕ => 10 ≤ n) laiM laiM_pos
      (fun ℓ hp hs hx => nv7a_mem10 hp (ge100_of_not_mem (laiExc0_sub_laiExc b) hx) hs),
    tiedScaled (NV7.nv7bPlaneTied a b (laiExc b) (exc_lt11 (laiExc0_sub_laiExc b)) (exc_dvd hb)
        (exc_73 (laiExc0_sub_laiExc b)) (exc_1039 (laiExc0_sub_laiExc b)))
      (fun n : ℕ => 10 ≤ n) laiM laiM_pos
      (fun ℓ hp hs hx => nv7b_mem10 hp (ge100_of_not_mem (laiExc0_sub_laiExc b) hx) hs)]

/-- The three scaled ratio families. -/
noncomputable def ratioTiedS : Fin 3 → TiedNV laiRatioFamS id 126 ratioW :=
  ![tiedScaled (NV.laiRatioTied laiExc0 (exc_lt11 (Finset.Subset.refl _)))
      (fun n : ℕ => 10 ≤ n) laiM laiM_pos
      (fun ℓ hp hs hx => lai_mem10 hp (ge100_of_not_mem (Finset.Subset.refl _) hx) hs),
    tiedScaled (NV7.nv7aRatioTied laiExc0 (exc_lt11 (Finset.Subset.refl _))
        (exc_73 (Finset.Subset.refl _)) (exc_1039 (Finset.Subset.refl _)))
      (fun n : ℕ => 10 ≤ n) laiM laiM_pos
      (fun ℓ hp hs hx => nv7a_mem10 hp (ge100_of_not_mem (Finset.Subset.refl _) hx) hs),
    tiedScaled (NV7.nv7bRatioTied laiExc0 (exc_lt11 (Finset.Subset.refl _))
        (exc_73 (Finset.Subset.refl _)) (exc_1039 (Finset.Subset.refl _)))
      (fun n : ℕ => 10 ≤ n) laiM laiM_pos
      (fun ℓ hp hs hx => nv7b_mem10 hp (ge100_of_not_mem (Finset.Subset.refl _) hx) hs)]

end Tied

/-! ### 4. The three inputs -/

/-- The inputs still produced elsewhere: Lai Lemma 4.4 on `(7n/2, 6n]` (`Band7Stmt`), the decay data of
the wedge (`LaiDecayData`), and the C01 prefix datum `(Ŝ, hS, hR)`. -/
def LaiInputs : Prop :=
  Band7Stmt ∧
  (∃ (c : ℕ → ℝ) (N : ℕ) (wA wB a0 AA : ℝ), LaiDecayData c N wA wB a0 AA) ∧
  ∃ Shat : ℚ, CatalanCore.Content.PartialSums.partialS e23 d23 1000 ≤ Shat ∧
    Shat + CatalanCore.Content.PartialSums.Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000

/-! ### 5. The plane root (LR10) -/

/-- **LR10, plane root, plain form**, `μ = 34.14`. -/
theorem lai_plane_of (h : LaiInputs) (a b : ℤ) (hb : b ≠ 0) :
    ∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(34.14 : ℝ)) < |((a : ℝ) * zeta3 + (b : ℝ) * zeta4) - (p : ℝ) / q| := by
  obtain ⟨hB7, ⟨c, N, wA, wB, a0, AA, d⟩, Shat, hS, hR⟩ := h
  have hD := lai_plane_decay d a b hb
  have hDS := lai_plane_decay_scaled_cert hB7 Shat hS hR a b hD
  have hC := lai_plane_hasScaledContent_cert hB7 a b
  have hη : (3344019129 / 10 ^ 8 - 2868723663 / 10 ^ 8 - 0 : ℝ) = laiEta := by
    unfold laiEta; ring
  have hmass := windowOK_of_fields (planeTiedS a b hb) (fun i => by fin_cases i <;> rfl)
    (fun i => by fin_cases i <;> rfl) (fun i => by fin_cases i <;> rfl) plane_unionWindowOK
  have key := measure_of_family_tiedNV_index (planeTiedS a b hb) (Λ := 0)
    (D := 3344019129 / 10 ^ 8 - 2868723663 / 10 ^ 8) (ρ := 4294856306 / 10 ^ 8) (κ := 3)
    (β := 1637 / 10000) (Kh := 1) (μ := 34.14) hC hDS (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun n _ => by
      have hn : ∀ m : ℕ, ((3 * m : ℕ) : ℝ) ≤ 3 * ((id m : ℕ) : ℝ) := fun m => by simp
      exact hn n)
    (planeW_hW _) (by rw [hη]; exact hmass)
    (by norm_num)
  exact key

/-! ### 6. The ratio root (LR11) -/

/-- The ratio criterion output at `ζ3/ζ4`, `μ' = 55.499`. -/
theorem lai_ratio_family_of (h : LaiInputs) :
    ∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(55.499 : ℝ)) < |zeta3 / zeta4 - (p : ℝ) / q| := by
  obtain ⟨hB7, ⟨c, N, wA, wB, a0, AA, d⟩, Shat, hS, hR⟩ := h
  have hD := lai_ratio_decay d
  have hDS := lai_ratio_decay_scaled_cert hB7 Shat hS hR hD
  have hC := lai_ratio_hasScaledContent_cert hB7
  have hη : (3344019129 / 10 ^ 8 - 2868723663 / 10 ^ 8 - 0 : ℝ) = laiEta := by
    unfold laiEta; ring
  have hmass := windowOK_of_fields ratioTiedS (fun i => by fin_cases i <;> rfl)
    (fun i => by fin_cases i <;> rfl) (fun i => by fin_cases i <;> rfl) ratio_unionWindowOK
  have hys := ystar_bounds
  have key := measure_of_family_tiedNV_index ratioTiedS (Λ := 0)
    (D := 3344019129 / 10 ^ 8 - 2868723663 / 10 ^ 8) (ρ := 4294856306 / 10 ^ 8) (κ := 3)
    (β := 661 / 1000) (Kh := 3) (μ := 55.499) hC hDS (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun n _ => by
      have hn : ∀ m : ℕ, ((3 * m : ℕ) : ℝ) ≤ 3 * ((id m : ℕ) : ℝ) := fun m => by simp
      exact hn n)
    (ratioW_hW (x := zeta3 / zeta4) hys.1 (by linarith [hys.2])) (by rw [hη]; exact hmass)
    (by norm_num)
  exact key

/-- **LR11, ratio root, plain form**, `μ = 55.50`, for `ζ(3)/π⁴`. -/
theorem lai_ratio_of (h : LaiInputs) :
    ∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(55.50 : ℝ)) < |zeta3 / Real.pi ^ 4 - (p : ℝ) / q| := by
  refine plain_measure_smul (x := zeta3 / Real.pi ^ 4) (r := 90) (by norm_num)
    (μ' := 55.499) (by norm_num) ?_
  have e : (((90 : ℚ) : ℝ)) * (zeta3 / Real.pi ^ 4) = zeta3 / zeta4 := by
    rw [zeta4_eq_pi]
    have : Real.pi ^ 4 ≠ 0 := by positivity
    push_cast
    field_simp
  rw [e]
  exact lai_ratio_family_of h

/-- Both roots from the three inputs. -/
theorem lai_roots_of (h : LaiInputs) :
    (∀ a b : ℤ, b ≠ 0 → ∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(34.14 : ℝ)) < |((a : ℝ) * zeta3 + (b : ℝ) * zeta4) - (p : ℝ) / q|) ∧
    (∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(55.50 : ℝ)) < |zeta3 / Real.pi ^ 4 - (p : ℝ) / q|) :=
  ⟨fun a b hb => lai_plane_of h a b hb, lai_ratio_of h⟩

end CatalanCore.Lai

#print axioms CatalanCore.Lai.lai_plane_of
#print axioms CatalanCore.Lai.lai_ratio_of
#print axioms CatalanCore.Lai.lai_roots_of
