module

public import CatalanCore.Star.Leonard.KSStep

/-!
# The K-step ratio is good (package H7, (B2) in the `GoodF` interface)

Generic building blocks: `cauFac_good`, `chainD_good`, `chainU_good`: Cauchy factors and chain
products of the diagonal/K-steps are `ℓ`-units times integer powers of `θ + c`, `0 ≤ c < B`, provided
the integer shifts stay in `[0, B)` and the constant parts (`dnC`, `upC`, `cnum`) are `ℓ`-units.
-/

@[expose] public section

open Finset Matrix CatalanCore.ThmA

namespace CatalanCore.Star.Leonard

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma GoodF0.lin_int {B : ℕ} (z : ℤ) (h0 : 0 ≤ z) (hB : z < B) (k : ℤ) :
    GoodF0 ℓ B (fun θ => (θ + (z : ℚ)) ^ k) := by
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, z = c := ⟨z.toNat, by omega⟩
  simpa using GoodF0.lin (ℓ := ℓ) c (by omega) k

lemma GoodF0.prod2 {ι κ : Type*} [Fintype ι] [Fintype κ] {B : ℕ} (z : ι → κ → ℤ)
    (h : ∀ i j, 0 ≤ z i j ∧ z i j < B) :
    GoodF0 ℓ B (fun θ => ∏ i, ∏ j, (θ + ((z i j : ℤ) : ℚ))) := by
  refine GoodF0.prod _ _ fun i _ => GoodF0.prod _ _ fun j _ => ?_
  have := GoodF0.lin_int (ℓ := ℓ) (B := B) (z i j) (h i j).1 (h i j).2 1
  simpa using this

/-- Cauchy factors at `θ + e` -/
theorem cauFac_good {m n : ℕ} (a : Fin m → ℤ) (b : Fin n → ℤ) (e : ℤ) (B : ℕ)
    (hc : LU ℓ (cnum (Fin.addCases (fun i => ((a i : ℤ) : ℚ)) (fun j => ((b j : ℤ) : ℚ)) :
      Fin (m + n) → ℚ)))
    (hA : ∀ (i : Fin (m + n)) (l : Fin m), 0 ≤ ((i : ℕ) : ℤ) + a l + e ∧ ((i : ℕ) : ℤ) + a l + e < B)
    (hB : ∀ (i : Fin (m + n)) (j : Fin n), 0 ≤ ((i : ℕ) : ℤ) + b j + e ∧ ((i : ℕ) : ℤ) + b j + e < B) :
    GoodF0 ℓ B (fun θ => cauFac (θ + (e : ℚ))
      (Fin.addCases (fun i => ((a i : ℤ) : ℚ)) (fun j => ((b j : ℤ) : ℚ)) : Fin (m + n) → ℚ)) := by
  have hP1 := GoodF0.prod2 (ℓ := ℓ) (B := B) (fun (i : Fin (m + n)) (l : Fin m) =>
    ((i : ℕ) : ℤ) + a l + e) hA
  have hP2 := GoodF0.prod2 (ℓ := ℓ) (B := B) (fun (i : Fin (m + n)) (j : Fin n) =>
    ((i : ℕ) : ℤ) + b j + e) hB
  refine ((GoodF0.const (B := B) hc).div (hP1.mul hP2)).congr fun θ h0 hg => ?_
  rw [cauFac_split]
  congr 1
  congr 1
  · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun l _ => ?_
    push_cast; ring
  · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring

theorem dnT_good (K n : ℕ) (y0 e : ℤ) (B : ℕ)
    (h1 : ∀ j : ℕ, j + 1 < n → 0 ≤ y0 - j - 1 + e ∧ y0 - j - 1 + e < B)
    (h2 : ∀ j : ℕ, j + 1 < n → 0 ≤ (K : ℤ) - 1 + y0 - j + e ∧ (K : ℤ) - 1 + y0 - j + e < B) :
    GoodF0 ℓ B (fun θ => dnT K n (θ + (e : ℚ)) y0) := by
  unfold dnT
  refine GoodF0.prod _ _ fun k hk => GoodF0.prod _ _ fun j hj => ?_
  have hk' := Finset.mem_range.1 hk; have hj' := Finset.mem_range.1 hj
  have a1 := GoodF0.lin_int (ℓ := ℓ) (B := B) (y0 - j - 1 + e) (h1 j (by omega)).1 (h1 j (by omega)).2 1
  have a2 := GoodF0.lin_int (ℓ := ℓ) (B := B) ((K : ℤ) - 1 + y0 - j + e) (h2 j (by omega)).1
    (h2 j (by omega)).2 1
  refine (a1.mul a2).congr fun θ h0 hg => ?_
  simp only [zpow_one]; push_cast; ring

theorem upT_good (K n : ℕ) (y1 e : ℤ) (B : ℕ)
    (h1 : ∀ j : ℕ, j + 1 < n → 0 ≤ y1 + j + e ∧ y1 + j + e < B)
    (h2 : ∀ j : ℕ, j + 1 < n → 0 ≤ (K : ℤ) + y1 + j + e ∧ (K : ℤ) + y1 + j + e < B) :
    GoodF0 ℓ B (fun θ => upT K n (θ + (e : ℚ)) y1) := by
  unfold upT
  refine GoodF0.prod _ _ fun k hk => GoodF0.prod _ _ fun j hj => ?_
  have hk' := Finset.mem_range.1 hk; have hj' := Finset.mem_range.1 hj
  have a1 := GoodF0.lin_int (ℓ := ℓ) (B := B) (y1 + j + e) (h1 j (by omega)).1 (h1 j (by omega)).2 1
  have a2 := GoodF0.lin_int (ℓ := ℓ) (B := B) ((K : ℤ) + y1 + j + e) (h2 j (by omega)).1
    (h2 j (by omega)).2 1
  refine (a1.mul a2).congr fun θ h0 hg => ?_
  simp only [zpow_one]; push_cast; ring

/-- the downward chain value `lprodDown · cauFac` at `θ + e` -/
theorem chainD_good (m n S : ℕ) (y0 e : ℤ) (B : ℕ)
    (hC1 : LU ℓ (dnC m S (m + n) n y0))
    (hC2 : LU ℓ (cnum (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => (((y0 - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ)))
    (hlo : 0 ≤ y0 - (n : ℤ) + 1 + e) (hup1 : ((m + n : ℕ) : ℤ) - 1 + y0 + e < B)
    (hup2 : ((m + n : ℕ) : ℤ) + S + 2 * m - 2 + e < B) (hY : 0 ≤ (S : ℤ) + 1 + e) (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    GoodF0 ℓ B (fun θ => lprodDown m n S (θ + (e : ℚ)) y0 *
      cauFac (θ + (e : ℚ)) (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
        (fun j : Fin n => (((y0 - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ)) := by
  have hT := dnT_good (ℓ := ℓ) (m + n) n y0 e B (fun j hj => ⟨by omega, by omega⟩)
    (fun j hj => ⟨by push_cast; omega, by push_cast; omega⟩)
  have hCau := cauFac_good (ℓ := ℓ) (fun i : Fin m => bY m (S : ℤ) i)
    (fun j : Fin n => y0 - ((j : ℕ) : ℤ)) e B hC2
    (fun i l => by have := i.2; have := bY_bounds m (S : ℤ) l; push_cast at *; omega)
    (fun i j => by have := i.2; have := j.2; push_cast at *; omega)
  refine ((GoodF0.const (B := B) hC1).mul (hT.mul hCau)).congr fun θ h0 hg => ?_
  rw [lprodDown_eq]; ring

/-- the upward chain value `lprodUp · cauFac` at `θ + e` -/
theorem chainU_good (m n S : ℕ) (y1 e : ℤ) (B : ℕ)
    (hC1 : LU ℓ (upC m S (m + n) n y1))
    (hC2 : LU ℓ (cnum (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => (((y1 + ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ)))
    (hlo : 0 ≤ y1 + e) (hup1 : ((m + n : ℕ) : ℤ) + y1 + n + e < B)
    (hup2 : ((m + n : ℕ) : ℤ) + S + 2 * m - 2 + e < B) (hY : 0 ≤ (S : ℤ) + 1 + e) (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    GoodF0 ℓ B (fun θ => lprodUp m n S (θ + (e : ℚ)) y1 *
      cauFac (θ + (e : ℚ)) (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
        (fun j : Fin n => (((y1 + ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ)) := by
  have hT := upT_good (ℓ := ℓ) (m + n) n y1 e B (fun j hj => ⟨by omega, by omega⟩)
    (fun j hj => ⟨by push_cast; omega, by push_cast; omega⟩)
  have hCau := cauFac_good (ℓ := ℓ) (fun i : Fin m => bY m (S : ℤ) i)
    (fun j : Fin n => y1 + ((j : ℕ) : ℤ)) e B hC2
    (fun i l => by have := i.2; have := bY_bounds m (S : ℤ) l; push_cast at *; omega)
    (fun i j => by have := i.2; have := j.2; push_cast at *; omega)
  refine ((GoodF0.const (B := B) hC1).mul (hT.mul hCau)).congr fun θ h0 hg => ?_
  rw [lprodUp_eq]; ring

/-- `Lp · G`: the product of the leading coefficients of the y-space chain and the Gram scalar -/
noncomputable def LpG (m n' : ℕ) (θ : ℚ) : ℚ :=
  (∏ k : Fin n', ∏ j ∈ range k, (-tau (m + (n' + 1)) m n' θ (-θ - (((-(j : ℤ)) : ℤ) : ℚ)))) *
    (CatalanCore.colMat fun j => zvec m (n' + 1) n' θ j).det

theorem ksratio_good (m n' : ℕ) (hm : 1 ≤ m) (hn' : 1 ≤ n') (ℓ' : ℕ) [Fact ℓ'.Prime]
    (hl : 2 * (n' + 1) + 3 * m ≤ ℓ')
    (hLpG : GoodF0 ℓ' (2 * n' + 3 * m + 1) (fun θ => LpG m n' θ)) :
    GoodF0 ℓ' (2 * n' + 3 * m + 1) (fun θ => KSratio m n' θ) := by
  set B := 2 * n' + 3 * m + 1 with hB
  set L := 2 * n' + 3 * m + 1 with hLdef
  have hL : L < ℓ' := by omega
  -- constants
  have cCF : LU ℓ' (cnum (Fin.addCases (fun i : Fin m => ((bY m (n' : ℤ) i : ℤ) : ℚ))
      (fun j : Fin (n' + 1) => (((j : ℕ) : ℤ) : ℚ)) : Fin (m + (n' + 1)) → ℚ)) := by
    refine LU_cnum_add (fun i : Fin m => bY m (n' : ℤ) i) (fun j : Fin (n' + 1) => ((j : ℕ) : ℤ))
      L hL (by omega) 0 ((n' : ℤ) + 2 * m) (fun i => ?_) (fun j => ?_) (by omega)
      (bY_inj m _) (fun i j h => Fin.ext (by simpa using h)) (fun i j => ?_)
    · have := bY_bounds m (n' : ℤ) i; omega
    · have := j.2; omega
    · have := bY_bounds m (n' : ℤ) i; have := j.2; omega
  have cLD : LU ℓ' (cnum (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
      (fun j : Fin (n' + 1) => (((((n' + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) :
        Fin (m + (n' + 1)) → ℚ)) := by
    refine LU_cnum_add (fun i : Fin m => bY m ((n' + 1 : ℕ) : ℤ) i)
      (fun j : Fin (n' + 1) => ((n' + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ))
      L hL (by omega) 1 ((n' : ℤ) + 2 * m) (fun i => ?_) (fun j => ?_) (by omega)
      (bY_inj m _) (fun i j h => Fin.ext (by simp at h; omega)) (fun i j => ?_)
    · have := bY_bounds m ((n' + 1 : ℕ) : ℤ) i; push_cast at this ⊢; omega
    · have := j.2; push_cast; omega
    · have := bY_bounds m ((n' + 1 : ℕ) : ℤ) i; have := j.2; push_cast at *; omega
  have cUT : LU ℓ' (cnum (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n' => (((((n' + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n') → ℚ)) := by
    refine LU_cnum_add (fun i : Fin m => bY m ((n' + 1 : ℕ) : ℤ) i)
      (fun j : Fin n' => ((n' + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ))
      L hL (by omega) 2 ((n' : ℤ) + 2 * m) (fun i => ?_) (fun j => ?_) (by omega)
      (bY_inj m _) (fun i j h => Fin.ext (by simp at h; omega)) (fun i j => ?_)
    · have := bY_bounds m ((n' + 1 : ℕ) : ℤ) i; push_cast at this ⊢; omega
    · have := j.2; push_cast; omega
    · have := bY_bounds m ((n' + 1 : ℕ) : ℤ) i; have := j.2; push_cast at *; omega
  have cLU : LU ℓ' (cnum (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
      (fun j : Fin (n' + 1) => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : ℚ)) :
        Fin (m + (n' + 1)) → ℚ)) := by
    refine LU_cnum_add (fun i : Fin m => bY m ((n' + 1 : ℕ) : ℤ) i)
      (fun j : Fin (n' + 1) => (1 : ℤ) + ((j : ℕ) : ℤ))
      L hL (by omega) 1 ((n' : ℤ) + 2 * m) (fun i => ?_) (fun j => ?_) (by omega)
      (bY_inj m _) (fun i j h => Fin.ext (by simp at h; omega)) (fun i j => ?_)
    · have := bY_bounds m ((n' + 1 : ℕ) : ℤ) i; push_cast at this ⊢; omega
    · have := j.2; omega
    · have := bY_bounds m ((n' + 1 : ℕ) : ℤ) i; have := j.2; push_cast at *; omega
  have dLD : LU ℓ' (dnC m (n' + 1) (m + (n' + 1)) (n' + 1) ((n' + 1 : ℕ) : ℤ)) := by
    refine LU_dnC m (n' + 1) (m + (n' + 1)) (n' + 1) _ L hL fun j hj => ⟨⟨by push_cast; omega, by push_cast; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩⟩
  have dUT : LU ℓ' (dnC m (n' + 1) (m + n') n' ((n' + 1 : ℕ) : ℤ)) := by
    refine LU_dnC m (n' + 1) (m + n') n' _ L hL fun j hj => ⟨⟨by push_cast; omega, by push_cast; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩⟩
  have dLU : LU ℓ' (upC m (n' + 1) (m + (n' + 1)) (n' + 1) 1) := by
    refine LU_upC m (n' + 1) (m + (n' + 1)) (n' + 1) 1 L hL fun j hj => ⟨⟨by omega, by omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩⟩
  have e1 : ∀ θ : ℚ, θ + (((-1 : ℤ)) : ℚ) = θ - 1 := fun θ => by push_cast; ring
  have gCF : GoodF0 ℓ' B (fun θ => cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (n' : ℤ) i : ℤ) : ℚ))
      (fun j : Fin (n' + 1) => (((j : ℕ) : ℤ) : ℚ)) : Fin (m + (n' + 1)) → ℚ)) := by
    refine (cauFac_good (ℓ := ℓ') (fun i : Fin m => bY m (n' : ℤ) i)
      (fun j : Fin (n' + 1) => ((j : ℕ) : ℤ)) 0 B cCF
      (fun i l => by have := i.2; have := bY_bounds m (n' : ℤ) l; push_cast at *; omega)
      (fun i j => by have := i.2; have := j.2; push_cast at *; omega)).congr fun θ _ _ => by simp
  have gLD : GoodF0 ℓ' B (fun θ => lprodDown m (n' + 1) (n' + 1) (θ - 1) ((n' + 1 : ℕ) : ℤ) *
      cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
        (fun j : Fin (n' + 1) => (((((n' + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) :
          Fin (m + (n' + 1)) → ℚ)) := by
    refine (chainD_good (ℓ := ℓ') m (n' + 1) (n' + 1) ((n' + 1 : ℕ) : ℤ) (-1) B dLD cLD
      (by push_cast <;> omega) (by push_cast <;> omega) (by push_cast <;> omega) (by push_cast <;> omega)
      (by omega) hm).congr fun θ _ _ => by rw [e1]
  have gUT : GoodF0 ℓ' B (fun θ => lprodDown m n' (n' + 1) θ ((n' + 1 : ℕ) : ℤ) *
      cauFac θ (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
        (fun j : Fin n' => (((((n' + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) :
          Fin (m + n') → ℚ)) := by
    refine (chainD_good (ℓ := ℓ') m n' (n' + 1) ((n' + 1 : ℕ) : ℤ) 0 B dUT cUT
      (by push_cast <;> omega) (by push_cast <;> omega) (by push_cast <;> omega) (by push_cast <;> omega)
      hn' hm).congr fun θ _ _ => by simp
  have gLU : GoodF0 ℓ' B (fun θ => lprodUp m (n' + 1) (n' + 1) (θ - 1) 1 *
      cauFac (θ - 1) (Fin.addCases (fun i : Fin m => ((bY m ((n' + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
        (fun j : Fin (n' + 1) => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : ℚ)) :
          Fin (m + (n' + 1)) → ℚ)) := by
    refine (chainU_good (ℓ := ℓ') m (n' + 1) (n' + 1) 1 (-1) B dLU cLU
      (by push_cast <;> omega) (by push_cast <;> omega) (by push_cast <;> omega) (by push_cast <;> omega)
      (by omega) hm).congr fun θ _ _ => by rw [e1]
  exact (((gCF.mul hLpG).mul gLD).div (gUT.mul gLU))

theorem ks_transfer_of_LpG (m : ℕ) (hm : 1 ≤ m)
    (hLpG : ∀ n' : ℕ, 1 ≤ n' → 2 * (n' + 1) + 3 * m ≤ ℓ →
      GoodF0 ℓ (2 * n' + 3 * m + 1) (fun θ => LpG m n' θ)) : KSTransfer ℓ m := by
  intro n' hn' hl h1
  have hl' : 2 * (n' + 1) + 3 * m ≤ ℓ := by omega
  have h2 := (ksratio_good m n' hm hn' ℓ hl' (hLpG n' hn' hl')).shift1
  have h3 := (h1.shift1.mono (by omega : _ ≤ 2 * n' + 3 * m + 1)).mul h2
  refine (h3.mono (by omega)).congr fun θ h0 hg => ?_
  have := ks_eq m n' hm hn' (θ + 1) (by linarith) (gen_add_one hg)
  rw [add_sub_cancel_right] at this
  exact this.symm

end CatalanCore.Star.Leonard
