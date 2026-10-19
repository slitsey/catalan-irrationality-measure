module

public import CatalanFrames.LambdaHybrid.NV.Members
public import CatalanFrames.LambdaHybrid.NV.LamData

/-!
# WP-H7 deliverable (frame-generic, then λ)

`nv_hyb_pair_gen`: for any `ModData Fr ℓ K` and `K = s' + 1 + m`, `2K + m ≤ ℓ`:
if `x ∈ ℤ_(ℓ)` and both `det Full(after r m)(x)` and `det Full(afterTop r m)(x)` vanish
(`r = ℓ - K - m`), then `k_R = 0 ∨ k_L = 0` in `𝔽_ℓ`, where `k_R, k_L` are the Krylov
determinants of `T = (Γ̂⁻¹)_{GG}`, `Γ̂ = [G X]ᵀ [G Y]`, with the Cauchy columns
`G = (1/(a - (ℓ-1-i)))`, `X = (1/(a - (r+2j)))`, `Y = (1/(a - (r+2j+1)))`.

Nothing here uses `ℓ + 1 = 4K`: only `2K + m ≤ ℓ` and the `ModData` fields.
`nv_hyb_pair_lam` is the λ instance.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime]

/-- absent nodes of member 1 -/
def ndAbs (ℓ s' : ℕ) : Fin (s' + 1) → ℕ := fun i => ℓ - 1 - (i : ℕ)

theorem nv_hyb_pair_gen {Fr : Frame} (D : ModData Fr ℓ K) (m s' : ℕ) (hs : s' + 1 + m = K)
    (h3 : 2 * K + m ≤ ℓ) {x : ℚ} (hx : x ∈ S ℓ)
    (h1 : ((after (ℓ - K - m) m).Full Fr x).det = 0)
    (h2 : ((afterTop (ℓ - K - m) m).Full Fr x).det = 0) :
    kR (gramHat (Gcols ℓ K (ndAbs ℓ s')) (WX ℓ K (after (ℓ - K - m) m))
        (WY ℓ K (after (ℓ - K - m) m))) (Fin.last s') = 0 ∨
    kL (gramHat (Gcols ℓ K (ndAbs ℓ s')) (WX ℓ K (after (ℓ - K - m) m))
        (WY ℓ K (after (ℓ - K - m) m))) (Fin.last s') = 0 := by
  set r := ℓ - K - m with hr
  have h2K : 2 * K ≤ ℓ := by omega
  have hrK : K ≤ r := by omega
  have hk : (after r m).k = m := after_k r m
  have hmem := memXY r m
  -- geometry hypotheses
  have hlow1 : ∀ n, n < K → n ∈ (after r m).C := fun n hn => by simp [after]; omega
  have hlow2 : ∀ n, n < K → n ∈ (afterTop r m).C := fun n hn => by simp [afterTop]; omega
  have hlt1 : ∀ n, n ∈ (after r m).C ∨ n ∈ (after r m).X' ∨ n ∈ (after r m).Y' → n < ℓ := by
    intro n hn
    rcases hn with hn | hn
    · simp [after] at hn; omega
    · have := (hmem n).1 hn; omega
  have hlt2 : ∀ n, n ∈ (afterTop r m).C ∨ n ∈ (afterTop r m).X' ∨ n ∈ (afterTop r m).Y' →
      n < ℓ := by
    intro n hn
    rcases hn with hn | hn
    · simp [afterTop] at hn; omega
    · have := (hmem n).1 hn; omega
  have hhi : ∀ n, n ∈ (after r m).X' ∨ n ∈ (after r m).Y' → K ≤ n := by
    intro n hn; have := (hmem n).1 hn; omega
  have hnd : Function.Injective (ndAbs ℓ s') := by
    intro i j hij; simp only [ndAbs] at hij; exact Fin.ext (by omega)
  have hab1 := hab_after ℓ K m s' h2K hs
  have hab2 := hab_afterTop ℓ K m s' h2K hs
  have hnd2 : Function.Injective (ndAbs ℓ s' ∘ Fin.castSucc) := hnd.comp (Fin.castSucc_injective _)
  -- the two bordered determinants vanish at Y₀
  have b1 := reduction_G D (after r m) hlow1 hlt1 hhi (ndAbs ℓ s') hnd hab1 hx h1
  have b2 := reduction_G D (afterTop r m) hlow2 hlt2 hhi (ndAbs ℓ s' ∘ Fin.castSucc) hnd2 hab2 hx h2
  -- Cauchy hypotheses
  let e : Fin (s' + 1) ⊕ Fin (after r m).k ≃ Fin K :=
    finSumFinEquiv.trans (finCongr (by rw [hk]; omega))
  have hys : ∀ j : Fin (after r m).k, (after r m).ys j = r + 2 * (j : ℕ) + 1 := after_ys r m
  have hxs : ∀ j : Fin (after r m).k, (after r m).xs j = r + 2 * (j : ℕ) := after_xs r m
  have hnd_ge : ∀ i : Fin (s' + 1), r + 2 * m ≤ ndAbs ℓ s' i := by
    intro i; have := i.2; simp only [ndAbs]; omega
  have hnd_lt : ∀ i : Fin (s' + 1), ndAbs ℓ s' i < ℓ := by
    intro i; simp only [ndAbs]; omega
  have hCauchy : ∀ (w : Fin (after r m).k → ℕ), Function.Injective w →
      (∀ j, r ≤ w j ∧ w j < r + 2 * m) →
      ((fromCols (Gcols ℓ K (ndAbs ℓ s')) (Matrix.of fun a j => Wnode ℓ K (w j) a)).submatrix
        e id).det ≠ 0 := by
    intro w hw hwr
    have hM : (fromCols (Gcols ℓ K (ndAbs ℓ s'))
        (Matrix.of fun a j => Wnode ℓ K (w j) a)).submatrix e id =
        Matrix.of fun (k j : Fin (s' + 1) ⊕ Fin (after r m).k) =>
          1 / ((((e k : Fin K) : ℕ) : ZMod ℓ) - ((Sum.elim (ndAbs ℓ s') w j : ℕ) : ZMod ℓ)) := by
      ext k (j | j) <;> simp [Gcols, Wnode]
    rw [hM]
    refine cauchy_ne_zero _ _ ?_ ?_ (K := K) (by omega) (fun k => (e k).2) ?_
    · intro k k' h; exact e.injective (Fin.ext h)
    · rintro (i | i) (j | j) h
      · simp only [Sum.elim_inl] at h; exact congrArg Sum.inl (hnd h)
      · simp only [Sum.elim_inl, Sum.elim_inr] at h
        have := hnd_ge i; have := (hwr j).2; omega
      · simp only [Sum.elim_inl, Sum.elim_inr] at h
        have := hnd_ge j; have := (hwr i).2; omega
      · simp only [Sum.elim_inr] at h; exact congrArg Sum.inr (hw h)
    · rintro (i | i)
      · simp only [Sum.elim_inl]; exact ⟨by have := hnd_ge i; omega, hnd_lt i⟩
      · simp only [Sum.elim_inr]; exact ⟨by have := (hwr i).1; omega, by have := (hwr i).2; omega⟩
  have hY := hCauchy (after r m).ys (ys_family (after r m)).1
    (fun j => by have := j.2; rw [hys]; omega)
  have hX := hCauchy (after r m).xs (xs_family (after r m)).1
    (fun j => by have := j.2; rw [hxs]; omega)
  exact pair_krylov _ _ _ e hY hX _ b1 b2

/-- **The WP-H7 deliverable for λ.**  `ℓ ≡ 3 (mod 4)`, `K = (ℓ+1)/4`, `0 ≤ m ≤ K-1`, `s' + 1 = K - m`. -/
theorem nv_hyb_pair_lam (hlK : ℓ + 1 = 4 * K) (m s' : ℕ) (hs : s' + 1 + m = K) {x : ℚ}
    (hx : x ∈ S ℓ) (h1 : ((after (ℓ - K - m) m).Full lamFrame x).det = 0)
    (h2 : ((afterTop (ℓ - K - m) m).Full lamFrame x).det = 0) :
    kR (gramHat (Gcols ℓ K (ndAbs ℓ s')) (WX ℓ K (after (ℓ - K - m) m))
        (WY ℓ K (after (ℓ - K - m) m))) (Fin.last s') = 0 ∨
    kL (gramHat (Gcols ℓ K (ndAbs ℓ s')) (WX ℓ K (after (ℓ - K - m) m))
        (WY ℓ K (after (ℓ - K - m) m))) (Fin.last s') = 0 :=
  nv_hyb_pair_gen (lamData hlK) m s' hs (by omega) hx h1 h2

end CatalanFrames.LambdaHybrid.NV

