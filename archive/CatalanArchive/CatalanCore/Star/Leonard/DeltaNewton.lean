module

public import CatalanCore.Star.Leonard.DeltaDD

/-!
# Prop hDelta, step (4): the two-variable Newton expansion of `f[u_p, v_q]`

With `u_p = x - p`, `v_q = x + 1 + q` (so that `U_i ∪ V_j` is the window `{x-i, …, x+1+j}`):
`f[u_p, v_q] = ∑_{i,j} N_i(u_p) N_j(v_q) · C(K,i+j+1) (x+j+1)_{K-i-j-1}` for `f = (z)_K`.
-/

@[expose] public section

open Finset

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- upper nodes `x - p` -/
def uN (x : F) : ℕ → F := fun p => x - (p : F)

/-- lower nodes `x + 1 + q` -/
def vN (x : F) : ℕ → F := fun q => x + 1 + (q : F)

lemma uN_inj (x : F) : Function.Injective (uN x) := fun a b h => by
  have : (a : F) = (b : F) := by simp only [uN] at h; linear_combination -h
  exact Nat.cast_injective this

lemma vN_inj (x : F) : Function.Injective (vN x) := fun a b h => by
  have : (a : F) = (b : F) := by simp only [vN] at h; linear_combination h
  exact Nat.cast_injective this

lemma vN_ne_uN (x : F) (q i : ℕ) : vN x q ≠ uN x i := fun h => by
  have h2 : ((q + 1 + i : ℕ) : F) = 0 := by simp only [vN, uN] at h; push_cast; linear_combination h
  exact absurd (Nat.cast_eq_zero.1 h2) (by omega)

lemma union_Vs_eq_Win (x : F) (i j : ℕ) :
    Vs (uN x) (i + 1) ∪ Vs (vN x) (j + 1) = Win (x - (i : F)) (i + j + 1) := by
  ext z
  simp only [Vs, Win, Finset.mem_union, Finset.mem_image, Finset.mem_range, uN, vN]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · refine ⟨i - k, by omega, ?_⟩
      rw [Nat.cast_sub (by omega)]; ring
    · refine ⟨i + 1 + k, by omega, ?_⟩
      push_cast; ring
  · rintro ⟨t, ht, rfl⟩
    by_cases h : t ≤ i
    · left; refine ⟨i - t, by omega, ?_⟩
      rw [Nat.cast_sub h]; ring
    · right; refine ⟨t - i - 1, by omega, ?_⟩
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

/-- **Two-variable Newton expansion.** -/
theorem dd_pair_expand (x : F) (K p q : ℕ) :
    dd (fun z => pochr z K) (insert (uN x p) {vN x q}) =
      ∑ i ∈ range (p + 1), ∑ j ∈ range (q + 1), Nn (uN x) (uN x p) i * Nn (vN x) (vN x q) j *
        ((K.choose (i + j + 1) : F) * pochr (x + (j : F) + 1) (K - (i + j + 1))) := by
  rw [newton _ (uN x) (uN_inj x) {vN x q} (by
    intro z hz i; rw [Finset.mem_singleton] at hz; subst hz; exact vN_ne_uN x q i) p]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : {vN x q} ∪ Vs (uN x) (i + 1) = insert (vN x q) (Vs (uN x) (i + 1)) := by
    rw [Finset.insert_eq]
  rw [e, newton _ (vN x) (vN_inj x) (Vs (uN x) (i + 1)) (by
    intro z hz j
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
    exact fun h => vN_ne_uN x j k h.symm) q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [union_Vs_eq_Win, dd_Win_pochr]
  have : x - (i : F) + ((i + j + 1 : ℕ) : F) = x + (j : F) + 1 := by push_cast; ring
  rw [this]; ring

end CatalanCore.Star.Leonard
