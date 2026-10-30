module

public import CatalanCore.Star.Leonard.KSGood
public import CatalanCore.Star.Leonard.GFinal

/-!
# `Lp · G` is good: the negative-shift factors cancel (package H7, (B2) core)

`Lneg = ∏_{k<n'} ∏_{j<k} (θ-j-1)` (from the y-space chain `Lp`) is exactly the negative-`c` part of the
Pochhammer denominator `∏_{b<K} ∏_{i<2N} (θ - n' + 1 + b + i)` of `G`; the rest has support `c ≥ 0`.
-/

@[expose] public section

open Finset Matrix CatalanCore.ThmA

namespace CatalanCore.Star.Leonard

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- the triangular product, reflected -/
lemma Gneg_eq_Lneg (θ : ℚ) (n' : ℕ) (hn' : 1 ≤ n') :
    ∏ b ∈ range (n' - 1), ∏ i ∈ range (n' - 1 - b), (θ - n' + 1 + b + i) =
      ∏ k ∈ range n', ∏ j ∈ range k, (θ - j - 1) := by
  set P : ℕ → ℚ := fun M => ∏ j ∈ range M, (θ - j - 1) with hP
  have h1 : ∀ b ∈ range (n' - 1), ∏ i ∈ range (n' - 1 - b), (θ - n' + 1 + b + i) = P (n' - 1 - b) := by
    intro b hb
    have hb' := Finset.mem_range.1 hb
    rw [hP]; simp only []
    rw [← Finset.prod_range_reflect (fun j => θ - j - 1) (n' - 1 - b)]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have e1 : ((n' - 1 - b - 1 - i : ℕ) : ℚ) = (n' : ℚ) - 2 - b - i := by
      rw [show n' - 1 - b - 1 - i = n' - (2 + b + i) by omega, Nat.cast_sub (by omega)]
      push_cast; ring
    show _ = θ - ((n' - 1 - b - 1 - i : ℕ) : ℚ) - 1
    rw [e1]; ring
  rw [Finset.prod_congr rfl h1]
  have h2 : ∏ b ∈ range (n' - 1), P (n' - 1 - b) = ∏ b ∈ range (n' - 1), P (b + 1) := by
    rw [← Finset.prod_range_reflect (fun b => P (b + 1)) (n' - 1)]
    refine Finset.prod_congr rfl fun b hb => ?_
    have := Finset.mem_range.1 hb
    congr 1; omega
  rw [h2]
  obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
  rw [Finset.prod_range_succ' (fun k => P k)]
  simp [hP]

lemma Gden_split (θ : ℚ) (n' K N : ℕ) (hn' : 1 ≤ n') (hK : n' - 1 ≤ K) (hN : n' - 1 ≤ 2 * N) :
    ∏ b ∈ range K, ∏ i ∈ range (2 * N), (θ - n' + 1 + b + i) =
      (∏ k ∈ range n', ∏ j ∈ range k, (θ - j - 1)) *
        ∏ b ∈ range K, ∏ i ∈ Ico (n' - 1 - b) (2 * N), (θ - n' + 1 + b + i) := by
  rw [← Gneg_eq_Lneg θ n' hn']
  have h1 : ∀ b ∈ range K, ∏ i ∈ range (2 * N), (θ - n' + 1 + b + i) =
      (∏ i ∈ range (n' - 1 - b), (θ - n' + 1 + b + i)) *
        ∏ i ∈ Ico (n' - 1 - b) (2 * N), (θ - n' + 1 + b + i) := by
    intro b hb
    rw [Finset.prod_range_mul_prod_Ico _ (by omega : n' - 1 - b ≤ 2 * N)]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  congr 1
  refine (Finset.prod_subset (Finset.range_subset_range.2 hK) ?_).symm
  intro b hb hb'
  have : n' - 1 - b = 0 := by
    have := Finset.mem_range.1 hb; have := (Finset.mem_range.not).1 hb'; omega
  rw [this]; simp

lemma Gpos_good (n' K N B : ℕ) (hn' : 1 ≤ n') (hB : K + 2 * N ≤ B + n') :
    GoodF0 ℓ B (fun θ => ∏ b ∈ range K, ∏ i ∈ Ico (n' - 1 - b) (2 * N), (θ - n' + 1 + b + i)) := by
  refine GoodF0.prod _ _ fun b hb => GoodF0.prod _ _ fun i hi => ?_
  have hb' := Finset.mem_range.1 hb
  have hi' := Finset.mem_Ico.1 hi
  have hc : n' ≤ b + i + 1 := by omega
  have := GoodF0.lin (ℓ := ℓ) (B := B) (b + i + 1 - n') (by omega) 1
  refine this.congr fun θ _ _ => ?_
  simp only [zpow_one]
  rw [Nat.cast_sub hc]; push_cast; ring

/-! ### `Lp` = constant · `Lneg` · `Lpos` -/

noncomputable def Lc (m n' : ℕ) : ℚ :=
  ∏ k ∈ range n', ∏ j ∈ range k, clc m n' (m + (n' + 1)) (-(j : ℤ))

noncomputable def Lneg (n' : ℕ) (θ : ℚ) : ℚ := ∏ k ∈ range n', ∏ j ∈ range k, (θ - j - 1)

noncomputable def Lpos (m n' : ℕ) (θ : ℚ) : ℚ :=
  ∏ k ∈ range n', ∏ j ∈ range k, (θ + ((m + (n' + 1) : ℕ) : ℚ) - 1 - j)

lemma Lp_split (m n' : ℕ) (θ : ℚ) :
    (∏ k : Fin n', ∏ j ∈ range k, (-tau (m + (n' + 1)) m n' θ (-θ - (((-(j : ℤ)) : ℤ) : ℚ)))) =
      Lc m n' * Lneg n' θ * Lpos m n' θ := by
  rw [Fin.prod_univ_eq_prod_range (fun k => ∏ j ∈ range k,
    (-tau (m + (n' + 1)) m n' θ (-θ - (((-(j : ℤ)) : ℤ) : ℚ)))) n']
  unfold Lc Lneg Lpos
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [neg_tau_at (m + (n' + 1)) m n' θ (-(j : ℤ))]
  push_cast; ring

lemma Lpos_good (m n' B : ℕ) (hB : m + (n' + 1) ≤ B) :
    GoodF0 ℓ B (fun θ => Lpos m n' θ) := by
  unfold Lpos
  refine GoodF0.prod _ _ fun k hk => GoodF0.prod _ _ fun j hj => ?_
  have hk' := Finset.mem_range.1 hk; have hj' := Finset.mem_range.1 hj
  have := GoodF0.lin (ℓ := ℓ) (B := B) (m + (n' + 1) - 1 - j) (by omega) 1
  refine this.congr fun θ _ _ => ?_
  simp only [zpow_one]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

lemma Lc_LU (m n' : ℕ) (hm : 1 ≤ m) (L : ℕ) (hL : L < ℓ) (hLn : 2 * n' + 2 * m + 2 ≤ L) :
    LU ℓ (Lc m n') := by
  unfold Lc
  refine LU.prod _ _ fun k hk => LU.prod _ _ fun j hj => ?_
  have hk' := Finset.mem_range.1 hk; have hj' := Finset.mem_range.1 hj
  refine LU_clc m n' (m + (n' + 1)) _ L hL ⟨by omega, by omega⟩ (fun i hi => ⟨by
    have := Finset.mem_range.1 hi; omega, by have := Finset.mem_range.1 hi; omega⟩)
    (fun i hi => ⟨by have := Finset.mem_range.1 hi; omega, by have := Finset.mem_range.1 hi; omega⟩)

/-! ### `G`: the constants are `θ`-free -/

lemma Vprod_shift {N : ℕ} (v : Fin N → ℚ) (c : ℚ) : Vprod (fun x => c + v x) = Vprod v := by
  unfold Vprod
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  ring

lemma asv_shift (m S : ℕ) (θ : ℚ) : asv m S θ = fun x => θ + asv m S 0 x := by
  funext x
  refine Fin.addCases (fun j => ?_) (fun i => ?_) x <;> simp [asv]

lemma bsv_shift (m S : ℕ) (θ : ℚ) : bsv m S θ = fun x => θ + bsv m S 0 x := by
  funext x
  refine Fin.addCases (fun j => ?_) (fun i => ?_) x <;> simp [bsv]

lemma LU_Vprod_int {N : ℕ} (v : Fin N → ℤ) (hinj : Function.Injective v) (L : ℕ) (hL : L < ℓ)
    (hd : ∀ i j, (v j - v i).natAbs ≤ L) : LU ℓ (Vprod (fun x => ((v x : ℤ) : ℚ))) := by
  unfold Vprod
  refine LU.prod _ _ fun i _ => LU.prod _ _ fun j hj => ?_
  have hlt : i < j := Finset.mem_Ioi.1 hj
  have hne : v j - v i ≠ 0 := sub_ne_zero.2 (fun h => by
    have := hinj h; rw [this] at hlt; exact lt_irrefl _ hlt)
  have := LU_int' (ℓ := ℓ) (z := v j - v i) hL hne (hd i j)
  simpa using this

lemma LU_Vprod_asv (m S L : ℕ) (hL : L < ℓ) (hLS : S + 2 * m + 2 ≤ L) :
    LU ℓ (Vprod (asv m S (0 : ℚ))) := by
  have e : asv m S (0 : ℚ) = fun x => ((Fin.addCases (motive := fun _ => ℤ)
      (fun j' : Fin S => (((j' : ℕ) + 1 : ℕ) : ℤ)) (fun i : Fin m => bX m (S : ℤ) i) x : ℤ) : ℚ) := by
    funext x
    refine Fin.addCases (fun j => ?_) (fun i => ?_) x <;> simp [asv]
  rw [e]
  refine LU_Vprod_int _ ?_ L hL ?_
  · intro x y hxy
    induction x using Fin.addCases with
    | left i =>
      induction y using Fin.addCases with
      | left i' => simp only [Fin.addCases_left] at hxy; congr 1; apply Fin.ext; omega
      | right j' =>
        simp only [Fin.addCases_left, Fin.addCases_right, bX] at hxy
        have := i.2; omega
    | right j =>
      induction y using Fin.addCases with
      | left i' =>
        simp only [Fin.addCases_left, Fin.addCases_right, bX] at hxy
        have := i'.2; omega
      | right j' => simp only [Fin.addCases_right, bX] at hxy; congr 1; apply Fin.ext; omega
  · intro x y
    have hv : ∀ z : Fin (S + m), 1 ≤ (Fin.addCases (motive := fun _ => ℤ)
        (fun j' : Fin S => (((j' : ℕ) + 1 : ℕ) : ℤ)) (fun i : Fin m => bX m (S : ℤ) i) z : ℤ) ∧
        (Fin.addCases (motive := fun _ => ℤ)
        (fun j' : Fin S => (((j' : ℕ) + 1 : ℕ) : ℤ)) (fun i : Fin m => bX m (S : ℤ) i) z : ℤ) ≤
          (S : ℤ) + 2 * m := by
      intro z
      refine Fin.addCases (fun j => ?_) (fun i => ?_) z <;> simp only [Fin.addCases_left, Fin.addCases_right, bX]
      · have := j.2; omega
      · have := i.2; omega
    have := hv x; have := hv y
    omega

lemma LU_Vprod_bsv (m S L : ℕ) (hL : L < ℓ) (hLS : 2 * S + 2 * m ≤ L) :
    LU ℓ (Vprod (bsv m S (0 : ℚ))) := by
  have e : bsv m S (0 : ℚ) = fun x => ((Fin.addCases (motive := fun _ => ℤ)
      (fun j' : Fin S => -((j' : ℕ) : ℤ)) (fun i : Fin m => bY m (S : ℤ) i) x : ℤ) : ℚ) := by
    funext x
    refine Fin.addCases (fun j => ?_) (fun i => ?_) x <;> simp [bsv]
  rw [e]
  refine LU_Vprod_int _ ?_ L hL ?_
  · intro x y hxy
    induction x using Fin.addCases with
    | left i =>
      induction y using Fin.addCases with
      | left i' => simp only [Fin.addCases_left] at hxy; congr 1; apply Fin.ext; omega
      | right j' =>
        simp only [Fin.addCases_left, Fin.addCases_right, bY] at hxy
        have := i.2; omega
    | right j =>
      induction y using Fin.addCases with
      | left i' =>
        simp only [Fin.addCases_left, Fin.addCases_right, bY] at hxy
        have := i'.2; omega
      | right j' => simp only [Fin.addCases_right, bY] at hxy; congr 1; apply Fin.ext; omega
  · intro x y
    have hv : ∀ z : Fin (S + m), -(S : ℤ) ≤ (Fin.addCases (motive := fun _ => ℤ)
        (fun j' : Fin S => -((j' : ℕ) : ℤ)) (fun i : Fin m => bY m (S : ℤ) i) z : ℤ) ∧
        (Fin.addCases (motive := fun _ => ℤ)
        (fun j' : Fin S => -((j' : ℕ) : ℤ)) (fun i : Fin m => bY m (S : ℤ) i) z : ℤ) ≤
          (S : ℤ) + 2 * m := by
      intro z
      refine Fin.addCases (fun j => ?_) (fun i => ?_) z <;> simp only [Fin.addCases_left, Fin.addCases_right, bY]
      · have := j.2; omega
      · have := i.2; omega
    have := hv x; have := hv y
    omega

noncomputable def Cg (m n' : ℕ) : ℚ :=
  (Vprod (asv m n' (0 : ℚ)) * Vprod (bsv m n' (0 : ℚ)) *
      Vprod (fun i : Fin (m + (n' + 1)) => ((i : ℕ) : ℚ)) ^ 2 *
      (((2 * (n' + m)).choose (n' + m) : ℕ) : ℚ) / (((n' + m).factorial : ℕ) : ℚ) ^ 2) /
    (Vprod (xsθ (n' : ℚ) m) * Vprod (ysθ (n' : ℚ) m) * Hunif ℚ (m + (n' + 1)) m)

noncomputable def Gden (m n' : ℕ) (θ : ℚ) : ℚ :=
  ∏ b ∈ range (m + (n' + 1)), ∏ i ∈ range (2 * (n' + m)), (θ - n' + 1 + b + i)

noncomputable def Gnum2 (m n' : ℕ) (θ : ℚ) : ℚ :=
  (∏ i ∈ range (n' + m), (θ - n' + 1 + ((n' + m : ℕ) : ℚ) + i)) ^ 2

lemma xsθ_shift (S m : ℕ) (θ : ℚ) : xsθ (θ + (S : ℚ)) m = fun x => θ + xsθ (S : ℚ) m x := by
  funext x; simp only [xsθ]; ring

lemma ysθ_shift (S m : ℕ) (θ : ℚ) : ysθ (θ + (S : ℚ)) m = fun x => θ + ysθ (S : ℚ) m x := by
  funext x; simp only [ysθ]; ring

theorem G_param (m n' : ℕ) (hm : 1 ≤ m) (θ : ℚ) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + (n' + 1)) θ (bX m (n' : ℤ)))ᵀ *
      Wb (m + (n' + 1)) θ (bY m (n' : ℤ))).det) :
    (CatalanCore.colMat fun j => zvec m (n' + 1) n' θ j).det =
      Cg m n' * ((Gden m n' θ)⁻¹ * Gnum2 m n' θ * Dpair (θ + (n' : ℚ)) (m + (n' + 1)) m) := by
  have h := G_closed m n' hm (n' + 1) rfl θ hθ hΔ
  rw [h, asv_shift m n' θ, bsv_shift m n' θ, Vprod_shift, Vprod_shift, xsθ_shift, ysθ_shift,
    Vprod_shift, Vprod_shift]
  have hFin : (∏ b : Fin (m + (n' + 1)), (∏ i ∈ range (2 * (n' + m)),
      ((θ - (n' : ℚ) + 1) + ((b : ℕ) : ℚ) + (i : ℚ)))⁻¹) = (Gden m n' θ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    congr 1
    unfold Gden
    exact Fin.prod_univ_eq_prod_range (fun b => ∏ i ∈ range (2 * (n' + m)), (θ - n' + 1 + b + i))
      (m + (n' + 1))
  rw [hFin]
  unfold Cg Gnum2
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

theorem Cg_LU (m n' : ℕ) (hm : 1 ≤ m) (L : ℕ) (hL : L < ℓ) (hLn : 2 * n' + 3 * m + 1 ≤ L) :
    LU ℓ (Cg m n') := by
  unfold Cg
  have hVa := LU_Vprod_asv (ℓ := ℓ) m n' L hL (by omega)
  have hVb := LU_Vprod_bsv (ℓ := ℓ) m n' L hL (by omega)
  have hVK : LU ℓ (Vprod (fun i : Fin (m + (n' + 1)) => ((i : ℕ) : ℚ))) := by
    have := LU_Vprod_int (ℓ := ℓ) (fun i : Fin (m + (n' + 1)) => ((i : ℕ) : ℤ))
      (fun i j h => Fin.ext (by simpa using h)) L hL (fun i j => by
        have := i.2; have := j.2; omega)
    simpa using this
  have hch : LU ℓ (((2 * (n' + m)).choose (n' + m) : ℕ) : ℚ) := by
    have := CatalanCore.Bordered.Hankel.LU_choose (l := ℓ) (N := n' + m) (M := n' + m) (by omega)
    rwa [← two_mul] at this
  have hfac : LU ℓ (((n' + m).factorial : ℕ) : ℚ) := CatalanCore.Bordered.Hankel.LU_factorial (l := ℓ) (by omega)
  have hVx : LU ℓ (Vprod (xsθ (n' : ℚ) m)) :=
    LU_Vprod ((n' : ℚ) + 2) m (by omega) _ (fun j => by simp only [xsθ])
  have hVy : LU ℓ (Vprod (ysθ (n' : ℚ) m)) :=
    LU_Vprod ((n' : ℚ) + 1) m (by omega) _ (fun j => by simp only [ysθ])
  have hH : LU ℓ (Hunif ℚ (m + (n' + 1)) m) := by
    rw [Hunif_eq_hkH _ m (by omega)]
    exact CatalanCore.Bordered.Hankel.LU_hkH ℓ m 0 0 (m + (n' + 1) - 1) (by omega) (by omega)
  exact (((hVa.mul hVb).mul (hVK.pow 2)).mul hch |>.div (hfac.pow 2)).div
    ((hVx.mul hVy).mul hH)

lemma Gnum2_good (m n' B : ℕ) (hB : 2 * m + n' < B) : GoodF0 ℓ B (fun θ => Gnum2 m n' θ) := by
  have h1 : GoodF0 ℓ B (fun θ => ∏ i ∈ range (n' + m), (θ - n' + 1 + ((n' + m : ℕ) : ℚ) + i)) := by
    refine GoodF0.prod _ _ fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have := GoodF0.lin (ℓ := ℓ) (B := B) (m + 1 + i) (by omega) 1
    refine this.congr fun θ _ _ => ?_
    simp only [zpow_one]; push_cast; ring
  unfold Gnum2
  simpa [sq] using h1.mul h1

lemma Dp_good (m n' B : ℕ) (hB : 2 * n' + 3 * m < B) :
    GoodF0 ℓ B (fun θ => Dpair (θ + (n' : ℚ)) (m + (n' + 1)) m) := by
  unfold Dpair
  refine GoodF0.prod _ _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  refine GoodF0.mul ?_ ?_ <;> unfold pochr <;>
    refine GoodF0.prod _ _ fun t ht => ?_ <;> have ht' := Finset.mem_range.1 ht
  · have := GoodF0.lin (ℓ := ℓ) (B := B) (n' + 1 + i + t) (by omega) 1
    refine this.congr fun θ _ _ => ?_
    simp only [zpow_one]; push_cast; ring
  · have := GoodF0.lin (ℓ := ℓ) (B := B) (n' + (m + (n' + 1)) + 1 + i + t) (by omega) 1
    refine this.congr fun θ _ _ => ?_
    simp only [zpow_one]; push_cast; ring

theorem LpG_good (m n' : ℕ) (hm : 1 ≤ m) (hn' : 1 ≤ n') (hl : 2 * (n' + 1) + 3 * m ≤ ℓ) :
    GoodF0 ℓ (2 * n' + 3 * m + 1) (fun θ => LpG m n' θ) := by
  set B := 2 * n' + 3 * m + 1 with hB
  have hL : B < ℓ := by omega
  have hc : LU ℓ (Lc m n' * Cg m n') :=
    (Lc_LU m n' hm B hL (by omega)).mul (Cg_LU m n' hm B hL le_rfl)
  have hGpos := Gpos_good (ℓ := ℓ) n' (m + (n' + 1)) (n' + m) B hn' (by omega)
  refine ((((((GoodF0.const (B := B) hc).mul (Lpos_good m n' B (by omega))).mul
    (Gnum2_good m n' B (by omega))).mul (Dp_good m n' B (by omega))).mul hGpos.inv)).congr
    fun θ h0 hg => ?_
  have hΔ : IsUnit ((Wb (m + (n' + 1)) θ (bX m (n' : ℤ)))ᵀ *
      Wb (m + (n' + 1)) θ (bY m (n' : ℤ))).det :=
    isUnit_iff_ne_zero.2 (Delta_ne_pos (m + (n' + 1)) m n' (by omega) θ h0)
  unfold LpG
  rw [Lp_split, G_param m n' hm θ hg hΔ]
  have hsplit := Gden_split θ n' (m + (n' + 1)) (n' + m) hn' (by omega) (by omega)
  have hGd : Gden m n' θ = Lneg n' θ * ∏ b ∈ range (m + (n' + 1)),
      ∏ i ∈ Ico (n' - 1 - b) (2 * (n' + m)), (θ - n' + 1 + b + i) := hsplit
  have hLneg : Lneg n' θ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun k _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    have := hg (-((j : ℤ) + 1)); push_cast at this
    intro h; apply this; linear_combination h
  rw [hGd, mul_inv]
  field_simp

end CatalanCore.Star.Leonard
