module

public import CatalanCore.Star.Leonard.DeltaFinal
public import CatalanCore.Bordered.Hankel.HahnUnit
public import CatalanCore.Bordered.Hankel.Basis

/-!
# Prop hDelta over `ℚ`: `Hunif = H_m(W_{0,0,K-1})` and `ℓ`-units

`Hunif ℚ K m` (the Hankel determinant of the uniform weight on `{0..K-1}`) is the Hahn Hankel
determinant `hkH 0 0 (K-1) m`, hence an `ℓ`-unit when `K - 1 + m < ℓ` (`LU_hkH`).
-/

@[expose] public section

open Finset Matrix CatalanCore.ThmA CatalanCore.Bordered.Hankel

namespace CatalanCore.Star.Leonard

theorem Hunif_eq_hkH (K m : ℕ) (hK : 1 ≤ K) : Hunif ℚ K m = hkH 0 0 (K - 1) m := by
  obtain ⟨N, rfl⟩ : ∃ N, K = N + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold hkH gramH Hunif
  have h1 := gram_monic (range (N + 1)) (fun _ => (1 : ℚ)) (fun x => (x : ℚ))
    (fun i => descPochhammer ℚ i) (fun i => monic_descPochhammer ℚ i)
    (fun i => descPochhammer_natDegree ℚ i) m
  have e1 : (Matrix.of fun (p q : Fin m) => ∑ a : Fin (N + 1), ((a : ℕ) : ℚ) ^ ((p : ℕ) + (q : ℕ))) =
      Matrix.of fun (p q : Fin m) => ∑ x ∈ range (N + 1), (fun _ => (1 : ℚ)) x * (fun x : ℕ => (x : ℚ)) x ^ ((p : ℕ) + (q : ℕ)) := by
    ext p q
    simp only [Matrix.of_apply, one_mul]
    exact Fin.sum_univ_eq_sum_range (fun x => (x : ℚ) ^ ((p : ℕ) + (q : ℕ))) (N + 1)
  have e2 : (Matrix.of fun a b : Fin m => ipH 0 0 N (ff a) (ff b)) =
      Matrix.of fun (a b : Fin m) => ∑ x ∈ range (N + 1), (fun _ => (1 : ℚ)) x *
        (descPochhammer ℚ a).eval ((fun x : ℕ => (x : ℚ)) x) * (descPochhammer ℚ b).eval ((fun x : ℕ => (x : ℚ)) x) := by
    ext a b
    simp only [Matrix.of_apply, ipH, WtH, ff, Nat.zero_add]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp
  rw [e1, e2, h1]
  rfl

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma LU_pochr_nat (a L : ℕ) (ha : 1 ≤ a) (h : a + L ≤ ℓ) :
    LU ℓ (pochr ((a : ℕ) : ℚ) L) := by
  unfold pochr
  refine LU.prod _ _ fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have := LU_natCast_lt (l := ℓ) (n := a + t) (by omega) (by omega)
  simpa using this

lemma LU_Vprod (θ : ℚ) (m : ℕ) (hm : 2 * m ≤ ℓ) (v : Fin m → ℚ)
    (hv : ∀ j : Fin m, v j = θ + 2 * ((j : ℕ) : ℚ)) : LU ℓ (Vprod v) := by
  unfold Vprod
  refine LU.prod _ _ fun i _ => LU.prod _ _ fun j hj => ?_
  have hij : (i : ℕ) < (j : ℕ) := Fin.lt_def.1 (Finset.mem_Ioi.1 hj)
  have : v j - v i = ((2 * ((j : ℕ) - (i : ℕ)) : ℕ) : ℚ) := by
    rw [hv, hv, Nat.cast_mul, Nat.cast_sub hij.le]; push_cast; ring
  rw [this]
  exact LU_natCast_lt (by omega) (by have := j.2; omega)

/-- The `ℓ`-unit property of `Δ = det(W_Xᵀ W_Y)` at `θ = 0`, all nodes below `ℓ`. -/
theorem Delta_LU (K m S : ℕ) (hmK : m ≤ K) (hK : 1 ≤ K) (hb : S + K + 2 * m ≤ ℓ) :
    LU ℓ ((Wb K (0 : ℚ) (bX m (S : ℤ)))ᵀ * Wb K (0 : ℚ) (bY m (S : ℤ))).det := by
  have hGen : GenP (0 : ℚ) := fun z hz => by
    simp only [zero_add]; exact_mod_cast (by omega : z ≠ 0)
  rw [Delta_closed K m S 0 hGen hmK]
  have hx : LU ℓ (Vprod (xsθ ((0 : ℚ) + (S : ℚ)) m)) :=
    LU_Vprod ((0 : ℚ) + (S : ℚ) + 2) m (by omega) _ (fun j => by simp only [xsθ])
  have hy : LU ℓ (Vprod (ysθ ((0 : ℚ) + (S : ℚ)) m)) :=
    LU_Vprod ((0 : ℚ) + (S : ℚ) + 1) m (by omega) _ (fun j => by simp only [ysθ])
  have hH : LU ℓ (Hunif ℚ K m) := by
    rw [Hunif_eq_hkH K m hK]
    exact LU_hkH ℓ m 0 0 (K - 1) (by omega) (by omega)
  have hD : LU ℓ (Dpair ((0 : ℚ) + (S : ℚ)) K m) := by
    unfold Dpair
    refine LU.prod _ _ fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    refine LU.mul ?_ ?_
    · have := LU_pochr_nat (ℓ := ℓ) (S + 1 + i) m (by omega) (by omega)
      have e : ((0 : ℚ) + (S : ℚ) + 1 + (i : ℚ)) = ((S + 1 + i : ℕ) : ℚ) := by push_cast; ring
      rw [e]; exact this
    · have := LU_pochr_nat (ℓ := ℓ) (S + K + 1 + i) m (by omega) (by omega)
      have e : ((0 : ℚ) + (S : ℚ) + (K : ℚ) + 1 + (i : ℚ)) = ((S + K + 1 + i : ℕ) : ℚ) := by
        push_cast; ring
      rw [e]; exact this
  exact (hx.mul hy).mul (hH.div hD)

end CatalanCore.Star.Leonard
