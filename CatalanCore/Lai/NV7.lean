module

public import CatalanCore.Lai.NV7Inst
public import CatalanCore.Lai.NV7Dual
public import CatalanCore.Lai.NV
public import CatalanCore.Content.HalfIntDet
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-! # `CatalanCore.Lai.NV7`: Theorem NV7 and its corollaries (ledger LN06-LN08). -/

section
/-!
# The two diagonal blocks of `Z̄`: nonsingularity

`detAA_ne`: the `A × A` block is block diagonal with blocks `b̄ W(r) · M₀`, `det M₀ = 1095/2`.
`detBB_ne`: the `B × B` block is `[[D, C], [Cᵀ, E]]`; its Schur complement is
`b̄ K (779689/6234) · [∑_{T4} D_α(s) (-s)^{i+j}]`, nonsingular by Hankel duality (`top_hankel_ne_zero`).
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {α A d : ℕ}

theorem zmod_cast_ne {s t : ℕ} (hs : s < ℓ) (ht : t < ℓ) (h : s ≠ t) : (s : ZMod ℓ) ≠ (t : ZMod ℓ) :=
  fun h' => h (cast_inj_lt hs ht h')

theorem PcoreR_ne_zero (α A s : ℕ) (hAl : A + 1 < ℓ) (hs : s < ℓ) : PcoreR ℓ α A s ≠ 0 := by
  unfold PcoreR
  split_ifs with h
  · refine Finset.prod_ne_zero_iff.2 fun t ht => pow_ne_zero _ ?_
    have ht' := Finset.mem_erase.1 ht
    refine sub_ne_zero.2 (zmod_cast_ne (by have := mem_range.1 ht'.2; omega) hs ht'.1)
  · refine Finset.prod_ne_zero_iff.2 fun t ht => pow_ne_zero _ ?_
    refine sub_ne_zero.2 (zmod_cast_ne (by have := mem_range.1 ht; omega) hs (by have := mem_range.1 ht; omega))

theorem chatc_T1_ne_zero (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hα1 : 1 ≤ α) (hαA : α ≤ A)
    (hAl : A + 1 < ℓ) (hs : s < α) : chatc ℓ n α A s ≠ 0 := by
  unfold chatc chat
  rw [if_neg (by omega), if_neg (by omega)]
  have f1 : fz ℓ A ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have f2 : fz ℓ s ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have f3 : fz ℓ (A + 0 * ℓ - s) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have f4 : fz ℓ (2 * n + s - 0 * ℓ) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have f5 : fz ℓ (2 * n) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  exact mul_ne_zero (pow_ne_zero _ (div_ne_zero f1 (mul_ne_zero f2 f3)))
    (pow_ne_zero _ (div_ne_zero f4 (mul_ne_zero f5 f2)))

theorem Wt_eq_K (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hα1 : 1 ≤ α)
    (hαA : α ≤ A) (hAl : A + 1 < ℓ) (hs1 : α ≤ s) (hs2 : s < ℓ) :
    Wt ℓ n α A s = Kc ℓ n A * Dal ℓ α (s : ZMod ℓ) := by
  unfold Wt chatc Dal
  by_cases h : s ≤ A
  · rw [if_neg (by omega), if_pos hs1]
    exact unit_T2 n α A s hα hA hα1 hs1 h
  · rw [if_pos (by omega), if_pos hs1]
    exact unit_T4 n α A s hα hA hα1 (by omega) (by omega) hs2

theorem Dal_ne_zero (α s : ℕ) (hs : α ≤ s) (hsl : s < ℓ) : Dal ℓ α (s : ZMod ℓ) ≠ 0 := by
  unfold Dal
  refine Finset.prod_ne_zero_iff.2 fun t ht => sub_ne_zero.2 (zmod_cast_ne hsl (by
    have := mem_range.1 ht; omega) (by have := mem_range.1 ht; omega))

theorem Kc_ne_zero (n A : ℕ) (hA : A < ℓ) (h2n : 2 * n < ℓ) : Kc ℓ n A ≠ 0 := by
  unfold Kc
  exact div_ne_zero (pow_ne_zero _ (fz_ne_zero (p := ℓ) hA)) (pow_ne_zero _ (fz_ne_zero (p := ℓ) h2n))

theorem sum_Ico_top_nat (A : ℕ) (hA : A + 1 ≤ ℓ) (f : ZMod ℓ → ZMod ℓ) :
    ∑ s ∈ Ico (A + 1) ℓ, f (s : ZMod ℓ) = ∑ z ∈ topS ℓ A, f z := by
  rw [topS, Finset.sum_image]
  intro s hs t ht h
  exact cast_inj_lt (mem_Ico.1 hs).2 (mem_Ico.1 ht).2 h

end CatalanCore.Lai.NV7

end

section
open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {α A d : ℕ}

section Blocks

variable (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
  (hv : NodeVals ℓ n α A b w0 U E) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hα1 : 1 ≤ α)
  (hαA : α ≤ A) (hAl : A + 1 < ℓ)
  (Z : Matrix (Ix α A d) (Ix α A d) (LocRing ℓ))
  (hZ : ∀ x y, redQ ℓ (Z x y) = ∑ k ∈ range (6 * n + 1),
    if omg α A (k % ℓ) + mm α A d x y (k % ℓ) = exV α A d x + eyV α A d y then
      Tk α A d w0 U E x y k else 0)

include hv hα hA hα1 hαA hAl hZ in
theorem detAA_ne (hb : b ≠ 0) (h2 : (2 : ZMod ℓ) ≠ 0) (h1095 : (1095 : ZMod ℓ) ≠ 0) :
    (Matrix.of fun x x' : IA α => redQ ℓ (Z (Sum.inl x) (Sum.inl x'))).det ≠ 0 := by
  have hmat : (Matrix.of fun x x' : IA α => redQ ℓ (Z (Sum.inl x) (Sum.inl x'))) =
      Matrix.of fun (x y : Fin α × Fin 3) => if x.1 = y.1 then (b * Wt ℓ n α A x.1) *
        (Matrix.of fun i i' : Fin 3 => hh ℓ ((i : ℕ) + i')) x.2 y.2 else 0 := by
    ext ⟨r, i⟩ ⟨r', i'⟩
    simp only [Matrix.of_apply]
    rw [hZ, Zbar_AA n b w0 U E hv hα hA hαA hAl r r' i i']
    by_cases h : r = r' <;> simp [h, hh]
  rw [hmat]
  refine det_AA_ne_zero _ (fun r => mul_ne_zero hb (mul_ne_zero
    (chatc_T1_ne_zero n α A r hα hα1 hαA hAl r.2) (PcoreR_ne_zero α A r hAl (by have := r.2; omega)))) _ ?_
  show (Matrix.of fun i i' : Fin 3 => hh ℓ ((i : ℕ) + i')).det ≠ 0
  rw [detH h2]
  exact div_ne_zero h1095 h2

include hv hα hA hα1 hαA hAl hZ in
theorem detBB_ne (hb : b ≠ 0) (h2 : (2 : ZMod ℓ) ≠ 0) (h3 : (3 : ZMod ℓ) ≠ 0)
    (h1039 : (1039 : ZMod ℓ) ≠ 0) (h779689 : (779689 : ZMod ℓ) ≠ 0)
    (hd : 2 * d + α ≤ ℓ)
    (hTop : (Matrix.of fun i j : Fin d => ∑ s ∈ topS ℓ A, Dal ℓ α s * s ^ ((i : ℕ) + j)).det ≠ 0) :
    (Matrix.of fun y y' : IB α A d => redQ ℓ (Z (Sum.inr y) (Sum.inr y'))).det ≠ 0 := by
  classical
  obtain ⟨h4, h8⟩ := ne48 h2
  have h2n : 2 * n < ℓ := by omega
  have h3117 : (3117 : ZMod ℓ) ≠ 0 := by
    have : (3117 : ZMod ℓ) = 3 * 1039 := by norm_num
    rw [this]; exact mul_ne_zero h3 h1039
  have h6234 : (6234 : ZMod ℓ) ≠ 0 := by
    have : (6234 : ZMod ℓ) = 2 * 3 * 1039 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h3) h1039
  have hDc : Dc ℓ ≠ 0 := by
    rw [Dc_val h2]; exact div_ne_zero h3117 h8
  set DD : Fin (A + 1 - α) → ZMod ℓ := fun u => b * Wt ℓ n α A (α + u) * Dc ℓ with hDD
  set CC : Fin (A + 1 - α) → Fin d → ZMod ℓ := fun u m =>
    b * Wt ℓ n α A (α + u) * (-((α + (u : ℕ) : ℕ) : ZMod ℓ)) ^ (m : ℕ) * Cc ℓ with hCC
  set EE : Matrix (Fin d) (Fin d) (ZMod ℓ) := Matrix.of fun m m' => b * (G2c ℓ *
      ∑ s ∈ Ico α (A + 1), Wt ℓ n α A s * (-(s : ZMod ℓ)) ^ ((m : ℕ) + m') +
      G4c ℓ * ∑ s ∈ Ico (A + 1) ℓ, Wt ℓ n α A s * (-(s : ZMod ℓ)) ^ ((m : ℕ) + m')) with hEE
  have hWt : ∀ s, α ≤ s → s < ℓ → Wt ℓ n α A s = Kc ℓ n A * Dal ℓ α (s : ZMod ℓ) :=
    fun s h1 h2' => Wt_eq_K n α A s hα hA hα1 hαA hAl h1 h2'
  have hWne : ∀ s, α ≤ s → s < ℓ → Wt ℓ n α A s ≠ 0 := fun s h1 h2' => by
    rw [hWt s h1 h2']
    exact mul_ne_zero (Kc_ne_zero n A (by omega) h2n) (Dal_ne_zero α s h1 h2')
  have hmat : (Matrix.of fun y y' : IB α A d => redQ ℓ (Z (Sum.inr y) (Sum.inr y'))) =
      fromBlocks (diagonal DD) (Matrix.of CC) (Matrix.of CC)ᵀ EE := by
    ext (u | m) (u' | m')
    · simp only [Matrix.of_apply, fromBlocks_apply₁₁, diagonal_apply]
      rw [hZ, Zbar_EE n b w0 U E hv hα hA hαA hAl u u']
      by_cases h : u = u' <;> simp [h, hDD, Dc]
    · simp only [Matrix.of_apply, fromBlocks_apply₁₂]
      rw [hZ, Zbar_EG n b w0 U E hv hα hA hαA hAl u m']
      simp [hCC, Cc]
    · simp only [Matrix.of_apply, fromBlocks_apply₂₁, Matrix.transpose_apply]
      rw [hZ, Zbar_GE n b w0 U E hv hα hA hαA hAl u' m]
      simp [hCC, Cc]
    · simp only [Matrix.of_apply, fromBlocks_apply₂₂]
      rw [hZ, Zbar_GG n b w0 U E hv hα hA hαA hAl m m']
      simp [hEE, G2c, G4c]
  rw [hmat]
  refine det_BB_ne_zero DD (fun u => ?_) CC EE ?_
  · exact mul_ne_zero (mul_ne_zero hb (hWne _ (by omega) (by have := u.2; omega))) hDc
  · have hsv := schur_val h2 h3 h1039
    have hK := Kc_ne_zero (ℓ := ℓ) n A (by omega) h2n
    have h6234' : (779689 / 6234 : ZMod ℓ) ≠ 0 := div_ne_zero h779689 h6234
    set cc : ZMod ℓ := b * Kc ℓ n A * (779689 / 6234) with hcc
    have hcc0 : cc ≠ 0 := mul_ne_zero (mul_ne_zero hb hK) h6234'
    have hT : ∀ m m' : Fin d, (EE - Matrix.of fun m m' => ∑ u, CC u m * (DD u)⁻¹ * CC u m') m m' =
        cc * ∑ z ∈ topS ℓ A, Dal ℓ α z * (-z) ^ ((m : ℕ) + m') := by
      intro m m'
      have hm := m.2; have hm' := m'.2
      set e : ℕ := (m : ℕ) + m' with he
      have e1 : ∑ u : Fin (A + 1 - α), CC u m * (DD u)⁻¹ * CC u m' =
          b * (Cc ℓ ^ 2 / Dc ℓ) * ∑ s ∈ Ico α (A + 1), Wt ℓ n α A s * (-(s : ZMod ℓ)) ^ e := by
        rw [Finset.mul_sum, Finset.sum_Ico_eq_sum_range,
          ← Fin.sum_univ_eq_sum_range (fun k => b * (Cc ℓ ^ 2 / Dc ℓ) *
            (Wt ℓ n α A (α + k) * (-((α + k : ℕ) : ZMod ℓ)) ^ e)) (A + 1 - α)]
        refine Finset.sum_congr rfl fun u _ => ?_
        have hW := hWne (α + (u : ℕ)) (by omega) (by have := u.2; omega)
        simp only [hCC, hDD, he]
        rw [pow_add]
        field_simp
      have e2 : ∑ s ∈ Ico α (A + 1), Wt ℓ n α A s * (-(s : ZMod ℓ)) ^ e =
          Kc ℓ n A * ∑ s ∈ Ico α (A + 1), Dal ℓ α (s : ZMod ℓ) * (-(s : ZMod ℓ)) ^ e := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs' := mem_Ico.1 hs
        rw [hWt s hs'.1 (by omega)]; ring
      have e3 : ∑ s ∈ Ico (A + 1) ℓ, Wt ℓ n α A s * (-(s : ZMod ℓ)) ^ e =
          Kc ℓ n A * ∑ z ∈ topS ℓ A, Dal ℓ α z * (-z) ^ e := by
        rw [← sum_Ico_top_nat A (by omega) (fun z => Dal ℓ α z * (-z) ^ e), Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs' := mem_Ico.1 hs
        rw [hWt s (by omega) hs'.2]; ring
      have e4 := sum_Ico_top (ℓ := ℓ) α A e (by omega) hAl (by omega)
      set T : ZMod ℓ := ∑ z ∈ topS ℓ A, Dal ℓ α z * (-z) ^ e with hTdef
      have e5 : ∑ s ∈ Ico α (A + 1), Dal ℓ α (s : ZMod ℓ) * (-(s : ZMod ℓ)) ^ e = -T := by
        rw [hTdef]; linear_combination e4
      simp only [Matrix.sub_apply, hEE, Matrix.of_apply]
      rw [e1, e2, e3, e5]
      rw [hcc]
      linear_combination (b * Kc ℓ n A * T) * hsv
    have hmat2 : (EE - Matrix.of fun m m' => ∑ u, CC u m * (DD u)⁻¹ * CC u m') =
        cc • (Matrix.of fun i j : Fin d => (-1 : ZMod ℓ) ^ ((i : ℕ) + j) *
          ∑ z ∈ topS ℓ A, Dal ℓ α z * z ^ ((i : ℕ) + j)) := by
      ext m m'
      rw [hT]
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [neg_pow]; ring
    have hs := det_signed (Matrix.of fun i j : Fin d => ∑ z ∈ topS ℓ A, Dal ℓ α z * z ^ ((i : ℕ) + j))
    simp only [Matrix.of_apply] at hs
    rw [hmat2, det_smul, hs]
    exact mul_ne_zero (pow_ne_zero _ hcc0) hTop

end Blocks

end CatalanCore.Lai.NV7

end

section
/-!
# Theorem NV7 (core): `J_n(a, b, X'/ℓ³) ≠ 0` on the lines `3ℓ = 7n + 1, 7n + 2`
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem natDegree_Pd_le (a w : ℕ) (ν : Fin a → ℕ) : (Pd a w ν).natDegree ≤ w + ∑ r, ν r := by
  unfold Pd
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  refine Nat.add_le_add_left ?_ w
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine natDegree_pow_le.trans ?_
  rw [natDegree_X_add_C]; omega

theorem sum_nu0 (α A : ℕ) (h : α ≤ A + 1) : ∑ t : Fin (A + 1), nu0 α t = 3 * α + (A + 1 - α) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => nu0 α t) (A + 1), ← Finset.sum_range_add_sum_Ico _ h]
  have e1 : ∑ t ∈ range α, nu0 α t = 3 * α := by
    rw [Finset.sum_congr rfl (fun t ht => by simp [nu0, mem_range.1 ht] :
      ∀ t ∈ range α, nu0 α t = 3)]
    simp; ring
  have e2 : ∑ t ∈ Ico α (A + 1), nu0 α t = A + 1 - α := by
    rw [Finset.sum_congr rfl (fun t ht => by simp [nu0, (mem_Ico.1 ht).1] :
      ∀ t ∈ Ico α (A + 1), nu0 α t = 1)]
    simp
  omega

theorem nuV_le {α A d : ℕ} (x : Ix α A d) (t : Fin (A + 1)) : nuV α A d x t ≤ nu0 α t := by
  rcases x with ⟨r, i⟩ | u | m
  · have hi := i.2; have hr := r.2
    simp only [nuV, nu0]
    split_ifs <;> omega
  · simp only [nuV]; split_ifs <;> omega
  · simp only [nuV]; omega

theorem vec_natDegree_lt {α A d n : ℕ} (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n)
    (hαA : α ≤ A) (hd : d + 1 = n) (hn : 2 ≤ n) (x : Ix α A d) :
    (vecV α A d x).natDegree < 3 * n := by
  have h1 := natDegree_Pd_le (A + 1) (wV α A d x) (nuV α A d x)
  have h2 : ∑ r, nuV α A d x r ≤ ∑ r : Fin (A + 1), nu0 α r :=
    Finset.sum_le_sum fun r _ => nuV_le x r
  rw [sum_nu0 α A (by omega)] at h2
  have h3 : wV α A d x + 1 ≤ d + 1 := by
    rcases x with ⟨r, i⟩ | u | m
    · simp [wV]
    · simp [wV]
    · simp only [wV]; have := m.2; omega
  have h4 : wV α A d x ≤ d := by omega
  have h5 : (wV α A d x = 0) ∨ (∃ m : Fin d, x = Sum.inr (Sum.inr m) ∧ wV α A d x = m) := by
    rcases x with ⟨r, i⟩ | u | m
    · left; simp [wV]
    · left; simp [wV]
    · right; exact ⟨m, rfl, rfl⟩
  unfold vecV
  rcases h5 with h5 | ⟨m, _, h5⟩
  · omega
  · have := m.2; omega

theorem card_Ix (α A d : ℕ) : Fintype.card (Ix α A d) = 3 * α + (A + 1 - α) + d := by
  simp only [Ix, IA, IB, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

end CatalanCore.Lai.NV7

end

section
/-!
# Theorem NV7 (core form)
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `H₁ ≠ 0` on the line `3ℓ = 7n + 1`: `18 E₁ = 31n² - 7n - 2 ≡ -18/49`. -/
theorem E1_ne_zero (n α A : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hl : 3 * ℓ = 7 * n + 1)
    (hα1 : 1 ≤ α) (hαA : α ≤ A) (h2 : (2 : ZMod ℓ) ≠ 0) (h3 : (3 : ZMod ℓ) ≠ 0) :
    (∑ i ∈ range (A + 1), (i : ZMod ℓ) + ∑ i ∈ Ico α (A + 1), (i : ZMod ℓ)) ≠ 0 := by
  have hS12 : ∑ i ∈ range (A + 1), i = ∑ i ∈ range α, i + ∑ i ∈ Ico α (A + 1), i :=
    (Finset.sum_range_add_sum_Ico _ (show α ≤ A + 1 by omega)).symm
  have h1 : (∑ i ∈ range (A + 1), i) * 2 = (A + 1) * A := by
    have := Finset.sum_range_id_mul_two (A + 1)
    simpa using this
  have h2' : (∑ i ∈ range α, i) * 2 = α * (α - 1) := Finset.sum_range_id_mul_two α
  obtain ⟨α', rfl⟩ : ∃ α', α = α' + 1 := ⟨α - 1, by omega⟩
  have h2'' : (∑ i ∈ range (α' + 1), i) * 2 = (α' + 1) * α' := by simpa using h2'
  set S1 : ℕ := ∑ i ∈ range (A + 1), i with hS1
  set S2 : ℕ := ∑ i ∈ range (α' + 1), i with hS2
  set S3 : ℕ := ∑ i ∈ Ico (α' + 1) (A + 1), i with hS3
  have hA3 : 3 * A + 2 = 4 * n := by omega
  have hα3 : 3 * (α' + 1) = n + 1 := by omega
  have hcast : (∑ i ∈ range (A + 1), (i : ZMod ℓ) + ∑ i ∈ Ico (α' + 1) (A + 1), (i : ZMod ℓ)) =
      ((S1 + S3 : ℕ) : ZMod ℓ) := by
    push_cast [hS1, hS3]; rfl
  rw [hcast]
  have hy : (7 : ZMod ℓ) * n = -1 := by
    have : ((3 * ℓ : ℕ) : ZMod ℓ) = 0 := by simp
    rw [hl] at this
    push_cast at this
    linear_combination this
  have k1 : (2 * (S1 : ZMod ℓ)) = (A + 1) * A := by
    have := congrArg (fun z : ℕ => (z : ZMod ℓ)) (show 2 * S1 = (A + 1) * A by omega)
    push_cast at this; exact this
  have k2 : (2 * (S2 : ZMod ℓ)) = (α' + 1) * α' := by
    have := congrArg (fun z : ℕ => (z : ZMod ℓ)) (show 2 * S2 = (α' + 1) * α' by omega)
    push_cast at this; exact this
  have k3 : (S1 : ZMod ℓ) = S2 + S3 := by
    have := congrArg (fun z : ℕ => (z : ZMod ℓ)) hS12
    push_cast at this; exact this
  have kA : 3 * (A : ZMod ℓ) = 4 * n - 2 := by
    have := congrArg (fun z : ℕ => (z : ZMod ℓ)) hA3
    push_cast at this
    linear_combination this
  have kα : 3 * ((α' : ZMod ℓ) + 1) = n + 1 := by
    have := congrArg (fun z : ℕ => (z : ZMod ℓ)) hα3
    push_cast at this
    linear_combination this
  have h18 : 18 * ((S1 : ZMod ℓ) + S3) = 31 * (n : ZMod ℓ) ^ 2 - 7 * n - 2 := by
    have : (S3 : ZMod ℓ) = S1 - S2 := by linear_combination -k3
    rw [this]
    linear_combination 18 * k1 - 9 * k2 + 2 * (3 * (A : ZMod ℓ) + 4 * n + 1) * kA -
      (3 * ((α' : ZMod ℓ) + 1) + n - 2) * kα
  intro h0
  rw [Nat.cast_add] at h0
  rw [h0, mul_zero] at h18
  have h18z : (18 : ZMod ℓ) = 0 := by
    linear_combination (-49) * (-h18) + (31 * (7 * (n : ZMod ℓ)) - 80) * hy
  have : (18 : ZMod ℓ) = 2 * 3 ^ 2 := by norm_num
  rw [this] at h18z
  exact mul_ne_zero h2 (pow_ne_zero _ h3) h18z

end CatalanCore.Lai.NV7

end

section
open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- **Theorem NV7 (normalised form).**  `ℓ` prime with `3ℓ = 7n + 1` or `7n + 2`, `n ≥ 7`,
`a, b, X' ∈ ℤ_(ℓ)`, `b` a unit: `J_n(a, b, X'/ℓ³) ≠ 0`. -/
theorem nv7_core (n : ℕ) (hn : 7 ≤ n) (hline : 3 * ℓ = 7 * n + 1 ∨ 3 * ℓ = 7 * n + 2)
    (h2 : (2 : ZMod ℓ) ≠ 0) (h3 : (3 : ZMod ℓ) ≠ 0)
    (h1095 : (1095 : ZMod ℓ) ≠ 0) (h1039 : (1039 : ZMod ℓ) ≠ 0)
    (h779689 : (779689 : ZMod ℓ) ≠ 0)
    (a b X' : LocRing ℓ) (hb : redQ ℓ b ≠ 0) :
    MvPolynomial.eval ![(a : ℚ), (b : ℚ), (X' : ℚ) / (ℓ : ℚ) ^ 3] (laiJ n) ≠ 0 := by
  classical
  obtain ⟨α, hα⟩ : ∃ α, α + 2 * n = ℓ := ⟨ℓ - 2 * n, by omega⟩
  obtain ⟨A, hA⟩ : ∃ A, A + 2 * ℓ = 6 * n := ⟨6 * n - 2 * ℓ, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, d + 1 = n := ⟨n - 1, by omega⟩
  have hα1 : 1 ≤ α := by omega
  have hαA : α ≤ A := by omega
  have hAl : A + 1 < ℓ := by omega
  have h8 : 8 * n < ℓ ^ 2 := by nlinarith
  have h17 : 17 ≤ ℓ := by omega
  obtain ⟨w0, U, E, hw, hU, hE, hv⟩ := exists_nodeVals n α A hα hA hα1 hαA hAl h2 h8 a b X'
  obtain ⟨Z, hZ1, hZ2⟩ := gram_Z (ℓ := ℓ) (α := α) (A := A) (d := d) n hαA w0 hw
    (fun k => -3 * (a : ℚ) * Hq 2 k - 2 * (b : ℚ) * Hq 3 k)
    (fun k => laiH n k * (3 * (a : ℚ) * Hq 2 k + 2 * (b : ℚ) * Hq 3 k) +
      6 * ((X' : ℚ) / (ℓ : ℚ) ^ 3 - (a : ℚ) * Hq 3 k - (b : ℚ) * Hq 4 k)) U E hU hE
  have hZ : ∀ x y, redQ ℓ (Z x y) = ∑ k ∈ range (6 * n + 1),
      if omg α A (k % ℓ) + mm α A d x y (k % ℓ) = exV α A d x + eyV α A d y then
        Tk α A d w0 U E x y k else 0 := fun x y => hZ2 x y
  -- the Hankel duality input
  have hTop : (Matrix.of fun i j : Fin d => ∑ s ∈ topS ℓ A, Dal ℓ α s * s ^ ((i : ℕ) + j)).det ≠ 0 := by
    rcases hline with hl | hl
    · refine top_hankel_ne_zero A α d 1 hAl (by omega) (by omega) (by omega) ?_
      refine Or.inl ⟨rfl, by omega, ?_⟩
      exact E1_ne_zero n α A hα hA hl hα1 hαA h2 h3
    · refine top_hankel_ne_zero A α d 2 hAl (by omega) (by omega) (by omega) ?_
      exact Or.inr ⟨rfl, by omega⟩
  have hAA := detAA_ne n (redQ ℓ b) w0 U E hv hα hA hα1 hαA hAl Z hZ hb h2 h1095
  have hBB := detBB_ne n (redQ ℓ b) w0 U E hv hα hA hα1 hαA hAl Z hZ hb h2 h3 h1039 h779689
    (by omega) hTop
  have hBA : ∀ (y : IB α A d) (x : IA α), redQ ℓ (Z (Sum.inr y) (Sum.inl x)) = 0 := by
    intro y x
    rw [hZ]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := bound (d := d) hαA (Sum.inr y) (Sum.inl x) (k % ℓ)
    have hc : corr α A d (Sum.inr y) (Sum.inl x) = 1 := rfl
    rw [hc] at this
    rw [if_neg (by omega)]
  -- Gram criterion
  have hcard : Fintype.card (Ix α A d) = 3 * n := by
    rw [card_Ix]; omega
  let e : Ix α A d ≃ Fin (3 * n) := Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin])
  rw [CatalanCore.Lai.NV.eval_laiJ]
  refine mul_ne_zero (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero 2 (by positivity))) ?_
  refine CatalanCore.Lai.NV.hankel_det_ne_zero_of_gram _ e (vecV α A d) (fun x => ?_) ?_
  · exact lt_of_le_of_lt degree_le_natDegree
      (by exact_mod_cast vec_natDegree_lt hα hA hαA hd (by omega) x)
  · exact det_ne_zero_of_block _ Z 4 (exV α A d) (eyV α A d)
      (fun x y => by simpa [Matrix.of_apply] using hZ1 x y) hBA hAA hBB

end CatalanCore.Lai.NV7

end

section
/-!
# Theorem NV7: corollaries (plane `e = 4`, ratio `e = 1`) and the `TiedNV` instances (ledger LN08)
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai
  CatalanCore.Content

namespace CatalanCore.Lai.NV7

section Consts

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem zmod_ne_zero_of_not_dvd (m : ℕ) (h : ¬ ℓ ∣ m) : (m : ZMod ℓ) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact h

/-- the nonvanishing of the seven constants (and `2, 3`) for `ℓ ≥ 17`, `ℓ ∉ {73, 1039}`, `ℓ ≢ 1 (7)`. -/
theorem consts_ne (h17 : 17 ≤ ℓ) (h73 : ℓ ≠ 73) (h1039 : ℓ ≠ 1039) (h7 : ℓ % 7 ≠ 1) :
    (2 : ZMod ℓ) ≠ 0 ∧ (3 : ZMod ℓ) ≠ 0 ∧ (1095 : ZMod ℓ) ≠ 0 ∧ (1039 : ZMod ℓ) ≠ 0 ∧
      (779689 : ZMod ℓ) ≠ 0 := by
  have hp := hℓ.out
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := zmod_ne_zero_of_not_dvd (ℓ := ℓ) 2 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  · have := zmod_ne_zero_of_not_dvd (ℓ := ℓ) 3 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  · have := zmod_ne_zero_of_not_dvd (ℓ := ℓ) 1095 (fun h => by
      have e : (1095 : ℕ) = 3 * 5 * 73 := by norm_num
      rw [e] at h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · have := Nat.le_of_dvd (by norm_num) h; omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      · exact h73 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
    simpa using this
  · have := zmod_ne_zero_of_not_dvd (ℓ := ℓ) 1039 (fun h =>
      h1039 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
    simpa using this
  · have := zmod_ne_zero_of_not_dvd (ℓ := ℓ) 779689 (fun h => by
      have e : (779689 : ℕ) = 883 * 883 := by norm_num
      rw [e] at h
      have h2 : ℓ ∣ 883 := by
        rcases (Nat.Prime.dvd_mul hp).1 h with h | h <;> exact h
      have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2
      omega)
    simpa using this

end Consts

section Cor

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem mem_locRing_scaled' {j : ℕ} (z : ℤ) {q : ℕ} (hq : 0 < q) (h : ¬ ℓ ^ (j + 1) ∣ q) :
    (((ℓ : ℚ) ^ j * z) / (q : ℚ)) ∈ LocRing ℓ :=
  CatalanCore.Lai.NV.mem_locRing_scaled z hq h

theorem nv7_pt (n : ℕ) (hn : 7 ≤ n) (hline : 3 * ℓ = 7 * n + 1 ∨ 3 * ℓ = 7 * n + 2)
    (h73 : ℓ ≠ 73) (h1039 : ℓ ≠ 1039) (a b : ℤ) (hb : ¬ (ℓ : ℤ) ∣ b) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hq4 : ¬ ℓ ^ 4 ∣ q) :
    MvPolynomial.eval ![(a : ℚ), (b : ℚ), (p : ℚ) / (q : ℚ)] (laiJ n) ≠ 0 := by
  have h17 : 17 ≤ ℓ := by omega
  obtain ⟨h2, h3, h1095, h1039', h779689⟩ := consts_ne (ℓ := ℓ) h17 h73 h1039 (by omega)
  have hmem : ((ℓ : ℚ) ^ 3 * (p : ℤ) / (q : ℚ)) ∈ LocRing ℓ := mem_locRing_scaled' p hq hq4
  have hb' : redQ ℓ (b : LocRing ℓ) ≠ 0 := by
    rw [map_intCast]
    intro h0
    exact hb ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0)
  have key := nv7_core n hn hline h2 h3 h1095 h1039' h779689 ((a : ℤ) : LocRing ℓ) (b : LocRing ℓ)
    ⟨_, hmem⟩ hb'
  have hl := CatalanCore.Lai.NV.l_ne_zero ℓ
  have hv : (![(((a : ℤ) : LocRing ℓ) : ℚ), ((b : LocRing ℓ) : ℚ),
      ((⟨_, hmem⟩ : LocRing ℓ) : ℚ) / (ℓ : ℚ) ^ 3] : Fin 3 → ℚ) = ![(a : ℚ), (b : ℚ), (p : ℚ) / (q : ℚ)] := by
    funext i
    fin_cases i
    · simp
    · simp
    · simp; field_simp
  rw [hv] at key
  exact key

theorem nv7_plane (n : ℕ) (hn : 7 ≤ n) (hline : 3 * ℓ = 7 * n + 1 ∨ 3 * ℓ = 7 * n + 2)
    (h73 : ℓ ≠ 73) (h1039 : ℓ ≠ 1039) (a b p : ℤ) (q : ℕ) (hb : ¬ (ℓ : ℤ) ∣ b) (hq : 0 < q)
    (hq4 : ¬ ℓ ^ 4 ∣ q) : (laiPlaneFam a b).evalQ n ((p : ℚ) / (q : ℚ)) ≠ 0 := by
  rw [plane_evalQ]
  exact nv7_pt n hn hline h73 h1039 a b hb p q hq hq4

theorem nv7_ratio (n : ℕ) (hn : 7 ≤ n) (hline : 3 * ℓ = 7 * n + 1 ∨ 3 * ℓ = 7 * n + 2)
    (h73 : ℓ ≠ 73) (h1039 : ℓ ≠ 1039) (p q : ℤ) (hq : q ≠ 0) (hp : ¬ (ℓ : ℤ) ∣ p) :
    laiRatioFam.evalQ n ((p : ℚ) / (q : ℚ)) ≠ 0 := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  intro h0
  have hs := ratio_scaled n p q hq'
  have h17 : 17 ≤ ℓ := by omega
  obtain ⟨h2, h3, h1095, h1039', h779689⟩ := consts_ne (ℓ := ℓ) h17 h73 h1039 (by omega)
  have hb' : redQ ℓ (((-p : ℤ)) : LocRing ℓ) ≠ 0 := by
    rw [map_intCast]
    intro h0
    apply hp
    have : ((-p : ℤ) : ZMod ℓ) = 0 := h0
    rw [Int.cast_neg, neg_eq_zero] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have key := nv7_core n hn hline h2 h3 h1095 h1039' h779689 ((q : ℤ) : LocRing ℓ)
    ((-p : ℤ) : LocRing ℓ) 0 hb'
  have hv : (![(((q : ℤ) : LocRing ℓ) : ℚ), (((-p : ℤ) : LocRing ℓ) : ℚ),
      ((0 : LocRing ℓ) : ℚ) / (ℓ : ℚ) ^ 3] : Fin 3 → ℚ) = ![(q : ℚ), -(p : ℚ), 0] := by
    funext i
    fin_cases i
    · simp
    · simp
    · simp
  rw [hv] at key
  exact key (hs.symm.trans (mul_eq_zero_of_right _ h0))

end Cor

end CatalanCore.Lai.NV7

end
