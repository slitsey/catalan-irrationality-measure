module

public import CatalanFrames.LambdaHybrid.NV.Split
public import CatalanFrames.LambdaHybrid.NV.Main

/-!
# Frame-generic discharge of `ReductionHyp` (DO Prop 1.3, instance level)

`reduction_G`: for a `Frame` `Fr`, prime `ℓ`, threshold `K` with `ModData Fr ℓ K`, and a
geometry `G` with `[0,K) ⊆ C`, all nodes `< ℓ`, `X', Y'` above `K`: if `x ∈ ℤ_(ℓ)` and
`det Full(x) = 0` then `det B(h + x̄/κ) = 0`, where `B` is built from the Cauchy columns of the
absent high nodes (`nd : g → ℕ`, injective with range `absS`) and of `X'`, `Y'`.
`Y₀ = h + x̄/κ` does not depend on `G`.

(Sign convention: `Full` here uses `+Mn`; DO's uses `R = -M0`, so `X_DO = -x`.)
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime] {Fr : Frame}

theorem hA_ident (D : ModData Fr ℓ K) (G : Geometry)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < ℓ)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {g : Type} [Fintype g] [DecidableEq g] (nd : g → ℕ) (hnd : Function.Injective nd)
    (hab : ∀ n, (∃ i, nd i = n) ↔ n ∈ absS K ℓ G.C G.X' G.Y') :
    D.A = D.κ • (WC ℓ K G * (WC ℓ K G)ᵀ + Gcols ℓ K nd * (Gcols ℓ K nd)ᵀ +
      WX ℓ K G * (WX ℓ K G)ᵀ + WY ℓ K G * (WY ℓ K G)ᵀ + D.h • 1) := by
  ext a a'
  have hsp := sum_split K ℓ G.C G.X' G.Y' G.disjCX G.disjCY G.disjXY
    (fun n hn => hlt n (Or.inl hn)) (fun n hn => ⟨hhi n (Or.inl hn), hlt n (Or.inr (Or.inl hn))⟩)
    (fun n hn => ⟨hhi n (Or.inr hn), hlt n (Or.inr (Or.inr hn))⟩)
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  obtain ⟨hxi, hxr⟩ := xs_family G
  obtain ⟨hyi, hyr⟩ := ys_family G
  obtain ⟨hci, hcr⟩ := hic_family K G
  have s1 := sum_family (fun b : HiC K G => ((b.1 : G.C) : ℕ)) hci _ hcr
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  have s2 := sum_family nd hnd _ hab
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  have s3 := sum_family G.xs hxi _ hxr
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  have s4 := sum_family G.ys hyi _ hyr
    (fun n => (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))
  rw [D.harm a a', hsp, ← s1, ← s2, ← s3, ← s4]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, WC, WX, WY, Gcols, Wnode, smul_eq_mul, Matrix.one_apply,
    Matrix.of_apply]
  split_ifs <;> ring

/-- **DO Proposition 1.3 (instance, frame-generic).** -/
theorem reduction_G (D : ModData Fr ℓ K) (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < ℓ)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {g : Type} [Fintype g] [DecidableEq g] (nd : g → ℕ) (hnd : Function.Injective nd)
    (hab : ∀ n, (∃ i, nd i = n) ↔ n ∈ absS K ℓ G.C G.X' G.Y')
    {x : ℚ} (hx : x ∈ S ℓ) (hdet : (G.Full Fr x).det = 0) :
    (bordered (D.h + red ℓ x / D.κ) (Gcols ℓ K nd) (WX ℓ K G) (WY ℓ K G)).det = 0 := by
  have hx' : Good ℓ x (red ℓ x) := ⟨hx, rfl⟩
  have h0 : (Ncell Fr ℓ K G x).det = 0 := by
    have : Ncell Fr ℓ K G x = -(Matrix.diagonal (fun i => Dq ℓ K (rn G i)) *
        G.Full Fr x * Matrix.diagonal (fun j => Dq ℓ K (cn G j))) := by
      ext i j
      simp [Ncell, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc, mul_comm, mul_left_comm]
    rw [this, Matrix.det_neg, Matrix.det_mul, Matrix.det_mul, hdet]
    simp
  have hy := det_eq_zero_of_good (eIdx K G hlow) (Ncell Fr ℓ K G x)
    (Zmat (-red ℓ x) D.t D.d D.A (WC ℓ K G) (WX ℓ K G) (WY ℓ K G))
    (fun i j => y_good D G hlow hlt hhi hx' i j) h0
  rw [det_Zmat (-red ℓ x) D.t D.d D.κ D.h D.ht D.hd D.hκ D.htk D.A (WC ℓ K G) (WX ℓ K G)
    (WY ℓ K G) (Gcols ℓ K nd) (hA_ident D G hlt hhi nd hnd hab)] at hy
  have e : D.h - -red ℓ x / D.κ = D.h + red ℓ x / D.κ := by ring
  rw [e] at hy
  have hne : D.d ^ (Fintype.card (HiC K G) + Fintype.card (Fin G.k)) *
      (-D.κ) ^ Fintype.card (Fin K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ D.hd) (pow_ne_zero _ (neg_ne_zero.2 D.hκ))
  exact (mul_eq_zero.1 hy).resolve_left hne

end CatalanFrames.LambdaHybrid.NV
