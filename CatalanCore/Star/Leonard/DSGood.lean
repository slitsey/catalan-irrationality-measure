module

public import CatalanCore.Star.Leonard.DSStep

/-!
# The diagonal step is good (package H7, (B1) in the `GoodF` interface)

`dsK m n S` is an `ℓ`-unit when `S + n + 2m + 2 ≤ ℓ`, and `Tp1 (m+n) θ n` has support `0 ≤ c < m + n`,
so `GoodF ℓ B (uu m n S) → GoodF ℓ B' (uu m n (S+1))` (descending orientation).
-/

@[expose] public section

open Finset Matrix CatalanCore.ThmA

namespace CatalanCore.Star.Leonard

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma cast_addCases {m n : ℕ} (a : Fin m → ℤ) (b : Fin n → ℤ) :
    (Fin.addCases (fun i => ((a i : ℤ) : ℚ)) (fun j => ((b j : ℤ) : ℚ)) : Fin (m + n) → ℚ) =
      fun x => ((Fin.addCases (motive := fun _ => ℤ) a b x : ℤ) : ℚ) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x <;> simp

lemma LU_int' {z : ℤ} {L : ℕ} (hL : L < ℓ) (h0 : z ≠ 0) (hz : z.natAbs ≤ L) : LU ℓ (z : ℚ) :=
  LU_intCast_lt h0 (by omega)

/-- `cnum` of an injective integer vector with bounded differences is an `ℓ`-unit -/
lemma LU_cnum {N : ℕ} (v : Fin N → ℤ) (hinj : Function.Injective v) (L : ℕ) (hL : L < ℓ)
    (hN : N ≤ L) (hd : ∀ i j, (v j - v i).natAbs ≤ L) :
    LU ℓ (cnum (fun j => ((v j : ℤ) : ℚ))) := by
  unfold cnum
  refine LU.prod _ _ fun i _ => LU.prod _ _ fun j hj => ?_
  have hlt : i < j := Finset.mem_Ioi.1 hj
  have hlt' : (i : ℕ) < j := hlt
  have h1 : LU ℓ ((((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) := by
    have := LU_int' (ℓ := ℓ) (z := ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) hL (by omega)
      (by have := j.2; omega)
    simpa using this
  have h2 : LU ℓ (((v j : ℤ) : ℚ) - ((v i : ℤ) : ℚ)) := by
    have hne : v j - v i ≠ 0 := sub_ne_zero.2 (fun h => by
      have := hinj h; rw [this] at hlt; exact lt_irrefl _ hlt)
    have := LU_int' (ℓ := ℓ) (z := v j - v i) hL hne (hd i j)
    simpa using this
  exact h1.mul h2

lemma LU_prod_int {ι : Type*} (s : Finset ι) (z : ι → ℤ) (L : ℕ) (hL : L < ℓ)
    (hz : ∀ i ∈ s, z i ≠ 0 ∧ (z i).natAbs ≤ L) : LU ℓ (∏ i ∈ s, ((z i : ℤ) : ℚ)) :=
  LU.prod _ _ fun i hi => LU_int' hL (hz i hi).1 (hz i hi).2

lemma LU_clc (m S K : ℕ) (y : ℤ) (L : ℕ) (hL : L < ℓ)
    (h1 : 1 - y ≠ 0 ∧ (1 - y).natAbs ≤ L)
    (hA : ∀ i ∈ range (m + 1), ((S : ℤ) + 2 * i + 1 - y) ≠ 0 ∧ ((S : ℤ) + 2 * i + 1 - y).natAbs ≤ L)
    (hB : ∀ i ∈ range m, ((S : ℤ) + 2 * (i + 1) - y) ≠ 0 ∧ ((S : ℤ) + 2 * (i + 1) - y).natAbs ≤ L) :
    LU ℓ (clc m S K y) := by
  unfold clc
  have e1 : (1 - (y : ℚ)) = (((1 - y : ℤ)) : ℚ) := by push_cast; ring
  have e2 : (∏ i ∈ range (m + 1), ((S : ℚ) + 2 * (i : ℚ) + 1 - (y : ℚ))) =
      ∏ i ∈ range (m + 1), ((((S : ℤ) + 2 * i + 1 - y : ℤ)) : ℚ) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  have e3 : (∏ i ∈ range m, ((S : ℚ) + 2 * ((i : ℚ) + 1) - (y : ℚ))) =
      ∏ i ∈ range m, ((((S : ℤ) + 2 * (i + 1) - y : ℤ)) : ℚ) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  rw [e1, e2, e3]
  exact (LU_int' hL h1.1 h1.2).mul (LU_prod_int _ _ L hL hA) |>.div (LU_prod_int _ _ L hL hB)

lemma LU_crc (m S K : ℕ) (y : ℤ) (L : ℕ) (hL : L < ℓ)
    (h1 : y ≠ 0 ∧ y.natAbs ≤ L)
    (hA : ∀ i ∈ range m, ((S : ℤ) + 2 * (i + 1) - y - 1) ≠ 0 ∧ ((S : ℤ) + 2 * (i + 1) - y - 1).natAbs ≤ L)
    (hB : ∀ i ∈ range (m - 1), ((S : ℤ) + 2 * (i + 1) - y) ≠ 0 ∧ ((S : ℤ) + 2 * (i + 1) - y).natAbs ≤ L) :
    LU ℓ (crc m S K y) := by
  unfold crc
  have e2 : (∏ i ∈ range m, ((S : ℚ) + 2 * ((i : ℚ) + 1) - (y : ℚ) - 1)) =
      ∏ i ∈ range m, ((((S : ℤ) + 2 * (i + 1) - y - 1 : ℤ)) : ℚ) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  have e3 : (∏ i ∈ range (m - 1), ((S : ℚ) + 2 * ((i : ℚ) + 1) - (y : ℚ))) =
      ∏ i ∈ range (m - 1), ((((S : ℤ) + 2 * (i + 1) - y : ℤ)) : ℚ) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  rw [e2, e3]
  have := (LU_int' hL h1.1 h1.2)
  exact (this.neg.mul (LU_prod_int _ _ L hL hA)).div (LU_prod_int _ _ L hL hB)

lemma LU_dnC (m S K n : ℕ) (y0 : ℤ) (L : ℕ) (hL : L < ℓ)
    (h : ∀ j, j + 1 < n →
      (1 - (y0 - j) ≠ 0 ∧ (1 - (y0 - j)).natAbs ≤ L) ∧
      (∀ i ∈ range (m + 1), ((S : ℤ) + 2 * i + 1 - (y0 - j)) ≠ 0 ∧
        ((S : ℤ) + 2 * i + 1 - (y0 - j)).natAbs ≤ L) ∧
      (∀ i ∈ range m, ((S : ℤ) + 2 * (i + 1) - (y0 - j)) ≠ 0 ∧
        ((S : ℤ) + 2 * (i + 1) - (y0 - j)).natAbs ≤ L)) :
    LU ℓ (dnC m S K n y0) := by
  unfold dnC
  refine LU.prod _ _ fun k hk => LU.prod _ _ fun j hj => ?_
  have := Finset.mem_range.1 hk; have := Finset.mem_range.1 hj
  obtain ⟨a, b, c⟩ := h j (by omega)
  exact LU_clc m S K _ L hL a b c

lemma LU_upC (m S K n : ℕ) (y1 : ℤ) (L : ℕ) (hL : L < ℓ)
    (h : ∀ j, j + 1 < n →
      (y1 + j ≠ 0 ∧ (y1 + j).natAbs ≤ L) ∧
      (∀ i ∈ range m, ((S : ℤ) + 2 * (i + 1) - (y1 + j) - 1) ≠ 0 ∧
        ((S : ℤ) + 2 * (i + 1) - (y1 + j) - 1).natAbs ≤ L) ∧
      (∀ i ∈ range (m - 1), ((S : ℤ) + 2 * (i + 1) - (y1 + j)) ≠ 0 ∧
        ((S : ℤ) + 2 * (i + 1) - (y1 + j)).natAbs ≤ L)) :
    LU ℓ (upC m S K n y1) := by
  unfold upC
  refine LU.prod _ _ fun k hk => LU.prod _ _ fun j hj => ?_
  have := Finset.mem_range.1 hk; have := Finset.mem_range.1 hj
  obtain ⟨a, b, c⟩ := h j (by omega)
  exact LU_crc m S K _ L hL a b c

lemma LU_cnum_add {m n : ℕ} (a : Fin m → ℤ) (b : Fin n → ℤ) (L : ℕ) (hL : L < ℓ) (hN : m + n ≤ L)
    (lo hi : ℤ) (ha : ∀ i, lo ≤ a i ∧ a i ≤ hi) (hb : ∀ j, lo ≤ b j ∧ b j ≤ hi)
    (hlh : hi - lo ≤ L) (hai : Function.Injective a) (hbi : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j) :
    LU ℓ (cnum (Fin.addCases (fun i => ((a i : ℤ) : ℚ)) (fun j => ((b j : ℤ) : ℚ)) :
      Fin (m + n) → ℚ)) := by
  rw [cast_addCases a b]
  refine LU_cnum _ ?_ L hL hN ?_
  · intro x y hxy
    induction x using Fin.addCases with
    | left i =>
      induction y using Fin.addCases with
      | left i' =>
        simp only [Fin.addCases_left] at hxy
        rw [hai hxy]
      | right j' =>
        simp only [Fin.addCases_left, Fin.addCases_right] at hxy
        exact absurd hxy (hab _ _)
    | right j =>
      induction y using Fin.addCases with
      | left i' =>
        simp only [Fin.addCases_left, Fin.addCases_right] at hxy
        exact absurd hxy.symm (hab _ _)
      | right j' =>
        simp only [Fin.addCases_right] at hxy
        rw [hbi hxy]
  · intro x y
    have hv : ∀ z : Fin (m + n), lo ≤ (Fin.addCases (motive := fun _ => ℤ) a b z : ℤ) ∧
        (Fin.addCases (motive := fun _ => ℤ) a b z : ℤ) ≤ hi := by
      intro z
      refine Fin.addCases (fun i => ?_) (fun j => ?_) z <;> simp only [Fin.addCases_left, Fin.addCases_right]
      · exact ha i
      · exact hb j
    have := hv x; have := hv y
    omega

lemma bY_inj (m : ℕ) (S : ℤ) : Function.Injective (bY m S) := by
  intro i j h; simp only [bY] at h; exact Fin.ext (by omega)

lemma bY_bounds (m : ℕ) (S : ℤ) (i : Fin m) : S + 1 ≤ bY m S i ∧ bY m S i ≤ S + 2 * (m : ℤ) := by
  have := i.2; simp only [bY]; omega

/-- the diagonal-step constant is an `ℓ`-unit -/
theorem dsK_LU (m n S : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hS : n ≤ S) (hl : S + n + 2 * m + 3 ≤ ℓ) :
    LU ℓ (dsK m n S) := by
  set L := S + n + 2 * m + 2 with hLdef
  have hL : L < ℓ := by omega
  unfold dsK
  have c1 : LU ℓ (dnC m S (m + n) n 0) := by
    refine LU_dnC m S (m + n) n 0 L hL fun j hj => ⟨⟨by omega, by omega⟩, fun i hi => ⟨by
      have := Finset.mem_range.1 hi; omega, by have := Finset.mem_range.1 hi; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; omega, by have := Finset.mem_range.1 hi; omega⟩⟩
  have c2 : LU ℓ (dnC m (S + 1) (m + n) n ((S + 1 : ℕ) : ℤ)) := by
    refine LU_dnC m (S + 1) (m + n) n _ L hL fun j hj => ⟨⟨by push_cast; omega, by push_cast; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩⟩
  have c3 : LU ℓ (dnC m S (m + n) n (S : ℤ)) := by
    refine LU_dnC m S (m + n) n _ L hL fun j hj => ⟨⟨by omega, by omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; omega, by have := Finset.mem_range.1 hi; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; omega, by have := Finset.mem_range.1 hi; omega⟩⟩
  have c4 : LU ℓ (upC m (S + 1) (m + n) n 1) := by
    refine LU_upC m (S + 1) (m + n) n 1 L hL fun j hj => ⟨⟨by omega, by omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩,
      fun i hi => ⟨by have := Finset.mem_range.1 hi; push_cast; omega,
        by have := Finset.mem_range.1 hi; push_cast; omega⟩⟩
  have d1 : LU ℓ (cnum (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => ((((0 : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ)) := by
    refine LU_cnum_add (fun i : Fin m => bY m (S : ℤ) i) (fun j : Fin n => (0 : ℤ) - ((j : ℕ) : ℤ))
      L hL (by omega) (-(n : ℤ)) ((S : ℤ) + 2 * m) (fun i => ?_) (fun j => ?_) (by omega)
      (bY_inj m _) (fun i j h => Fin.ext (by simp at h; omega)) (fun i j => ?_)
    · have := bY_bounds m (S : ℤ) i; omega
    · have := j.2; omega
    · have := bY_bounds m (S : ℤ) i; omega
  have d2 : LU ℓ (cnum (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => (((((S + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ)) := by
    refine LU_cnum_add (fun i : Fin m => bY m ((S + 1 : ℕ) : ℤ) i)
      (fun j : Fin n => ((S + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ))
      L hL (by omega) ((S : ℤ) + 1 - n) ((S : ℤ) + 1 + 2 * m) (fun i => ?_) (fun j => ?_) (by omega)
      (bY_inj m _) (fun i j h => Fin.ext (by simp at h; omega)) (fun i j => ?_)
    · have := bY_bounds m ((S + 1 : ℕ) : ℤ) i; push_cast at this ⊢; omega
    · have := j.2; push_cast; omega
    · have := bY_bounds m ((S + 1 : ℕ) : ℤ) i; have := j.2; push_cast at *; omega
  have d3 : LU ℓ (cnum (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => ((((S : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ)) := by
    refine LU_cnum_add (fun i : Fin m => bY m (S : ℤ) i) (fun j : Fin n => (S : ℤ) - ((j : ℕ) : ℤ))
      L hL (by omega) ((S : ℤ) - n) ((S : ℤ) + 2 * m) (fun i => ?_) (fun j => ?_) (by omega)
      (bY_inj m _) (fun i j h => Fin.ext (by simp at h; omega)) (fun i j => ?_)
    · have := bY_bounds m (S : ℤ) i; omega
    · have := j.2; omega
    · have := bY_bounds m (S : ℤ) i; omega
  have d4 : LU ℓ (cnum (Fin.addCases (fun i : Fin m => ((bY m ((S + 1 : ℕ) : ℤ) i : ℤ) : ℚ))
      (fun j : Fin n => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : ℚ)) : Fin (m + n) → ℚ)) := by
    refine LU_cnum_add (fun i : Fin m => bY m ((S + 1 : ℕ) : ℤ) i)
      (fun j : Fin n => (1 : ℤ) + ((j : ℕ) : ℤ))
      L hL (by omega) 0 ((S : ℤ) + 1 + 2 * m) (fun i => ?_) (fun j => ?_) (by omega)
      (bY_inj m _) (fun i j h => Fin.ext (by simp at h; omega)) (fun i j => ?_)
    · have := bY_bounds m ((S + 1 : ℕ) : ℤ) i; push_cast at this ⊢; omega
    · have := j.2; omega
    · have := bY_bounds m ((S + 1 : ℕ) : ℤ) i; have := j.2; push_cast at *; omega
  exact (((c1.mul c2).mul d1).mul d2).div (((c3.mul c4).mul d3).mul d4)

lemma Tp1_good (K n : ℕ) (hn : n ≤ K) : GoodF0 ℓ K (fun θ => Tp1 K θ n) := by
  unfold Tp1
  refine GoodF0.prod _ _ fun j hj => ?_
  have hjn := Finset.mem_range.1 hj
  have hK : K - 1 - j < K := by omega
  have hj' : j < K := by omega
  refine GoodF0.congr ((GoodF0.lin (K - 1 - j) hK ((2 * (n - 1 - j) : ℕ) : ℤ)).mul
    (GoodF0.lin j hj' (-((2 * (n - 1 - j) : ℕ) : ℤ)))) fun θ h0 hg => ?_
  have hx : θ + ((K - 1 - j : ℕ) : ℚ) = θ + K - 1 - j := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  simp only [zpow_natCast, zpow_neg]
  rw [hx, div_pow, div_eq_mul_inv]

lemma gen_add_one {θ : ℚ} (h : Gen θ) : Gen (θ + 1) := by
  intro z; have := h (z + 1); push_cast at this; intro h'; apply this; linear_combination h'

/-- one descending diagonal step preserves the good form -/
theorem uu_good_succ (m n S B : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hS : n ≤ S)
    (hl : S + n + 2 * m + 3 ≤ ℓ) (h : GoodF ℓ B (uu m n S)) :
    GoodF ℓ (max (B + 1) (m + n)) (uu m n (S + 1)) := by
  have h1 := h.shift1
  have h2 : GoodF ℓ (m + n) (fun θ => dsK m n S * Tp1 (m + n) (θ + 1) n) :=
    ((GoodF0.const (B := m + n) (dsK_LU m n S hm hn hS hl)).mul (Tp1_good (m + n) n (by omega))).shift1
  have h3 := (h1.mono (le_max_left _ _)).mul (h2.mono (le_max_right _ _))
  refine h3.congr fun θ h0 hg => ?_
  have := ds_step m n S hm hn hS (θ + 1) (by linarith) (gen_add_one hg)
  rw [add_sub_cancel_right] at this
  exact this.symm

end CatalanCore.Star.Leonard
