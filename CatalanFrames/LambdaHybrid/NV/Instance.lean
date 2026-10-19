module

public import CatalanFrames.LambdaHybrid.NV.Split
public import CatalanFrames.LambdaHybrid.NV.Main

/-!
# Discharging `ReductionHyp` for a hybrid geometry on the λ frame

`reduction_G`: for a geometry `G` with `[0,K) ⊆ C`, all nodes `< ℓ`, `X', Y'` above `K`,
`ℓ + 1 = 4K`, and `x ∈ ℤ_(ℓ)`: if `det Full(x) = 0` then
`det B(cc + 16 x̄) = 0` where `B` is built from the Cauchy columns of the absent high nodes
(`nd : g → ℕ`, injective with range `absS`) and of `X'`, `Y'`.  `Y₀ = cc + 16 x̄` does not depend on
`G`.  (`cc = H2_{K-1}` mod `ℓ`; sign convention: `Full` here uses `+M0`, DO's uses `R = -M0`, so
`X_DO = -x`.)
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

open CatalanFrames.Lambda

variable {ℓ K : ℕ} [Fact ℓ.Prime]

/-- Cauchy columns of the absent nodes -/
noncomputable def Gcols (ℓ K : ℕ) [Fact ℓ.Prime] {g : Type} (nd : g → ℕ) :
    Matrix (Fin K) g (ZMod ℓ) :=
  Matrix.of fun a i => Wnode ℓ K (nd i) a

theorem hA_ident (hlK : ℓ + 1 = 4 * K) (G : Geometry)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < ℓ)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {g : Type} [Fintype g] [DecidableEq g] (nd : g → ℕ) (hnd : Function.Injective nd)
    (hab : ∀ n, (∃ i, nd i = n) ↔ n ∈ absS K ℓ G.C G.X' G.Y') :
    (16 : ZMod ℓ) • Alow ℓ K = WC ℓ K G * (WC ℓ K G)ᵀ + Gcols ℓ K nd * (Gcols ℓ K nd)ᵀ +
      WX ℓ K G * (WX ℓ K G)ᵀ + WY ℓ K G * (WY ℓ K G)ᵀ + CatalanLambda.cc ℓ K • 1 := by
  have hKl : K ≤ ℓ := by omega
  have h4 := CatalanLambda.four_ne (ℓ := ℓ) hlK
  have h16 : (16 : ZMod ℓ) ≠ 0 := by
    have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  ext a a'
  have hG := Gleg_eq_sum hKl a a'
  have hsp := sum_split K ℓ G.C G.X' G.Y' G.disjCX G.disjCY G.disjXY
    (fun n hn => hlt n (Or.inl hn)) (fun n hn => ⟨hhi n (Or.inl hn), hlt n (Or.inr (Or.inl hn))⟩)
    (fun n hn => ⟨hhi n (Or.inr hn), hlt n (Or.inr (Or.inr hn))⟩)
    (fun n => (1 / ((a : ZMod ℓ) - n)) * (1 / ((a' : ZMod ℓ) - n)))
  obtain ⟨hxi, hxr⟩ := xs_family G
  obtain ⟨hyi, hyr⟩ := ys_family G
  obtain ⟨hci, hcr⟩ := hic_family K G
  have s1 := sum_family (fun b : HiC K G => ((b.1 : G.C) : ℕ)) hci _ hcr
    (fun n => (1 / ((a : ZMod ℓ) - n)) * (1 / ((a' : ZMod ℓ) - n)))
  have s2 := sum_family nd hnd _ hab
    (fun n => (1 / ((a : ZMod ℓ) - n)) * (1 / ((a' : ZMod ℓ) - n)))
  have s3 := sum_family G.xs hxi _ hxr
    (fun n => (1 / ((a : ZMod ℓ) - n)) * (1 / ((a' : ZMod ℓ) - n)))
  have s4 := sum_family G.ys hyi _ hyr
    (fun n => (1 / ((a : ZMod ℓ) - n)) * (1 / ((a' : ZMod ℓ) - n)))
  rw [hsp, ← s1, ← s2, ← s3, ← s4] at hG
  simp only [Matrix.smul_apply, Alow, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, WC, WX, WY, Gcols, Wnode, smul_eq_mul, Matrix.one_apply]
  rw [hG]
  by_cases haa : a = a'
  · subst haa; simp; field_simp; ring
  · simp [haa]; field_simp

/-- **DO Proposition 1.3 (instance).** -/
theorem reduction_G (hlK : ℓ + 1 = 4 * K) (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < ℓ)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {g : Type} [Fintype g] [DecidableEq g] (nd : g → ℕ) (hnd : Function.Injective nd)
    (hab : ∀ n, (∃ i, nd i = n) ↔ n ∈ absS K ℓ G.C G.X' G.Y')
    {x : ℚ} (hx : x ∈ S ℓ) (hdet : (G.Full lamFrame x).det = 0) :
    (bordered (CatalanLambda.cc ℓ K + 16 * red ℓ x) (Gcols ℓ K nd) (WX ℓ K G) (WY ℓ K G)).det
      = 0 := by
  have h4 := CatalanLambda.four_ne (ℓ := ℓ) hlK
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    apply h4
    have : (4 : ZMod ℓ) = 2 * 2 := by norm_num
    rw [this, h, zero_mul]
  have h16 : (16 : ZMod ℓ) ≠ 0 := by
    have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  have hx' : Good ℓ x (red ℓ x) := ⟨hx, rfl⟩
  have h0 : (Ncell ℓ K G x).det = 0 := by
    have : Ncell ℓ K G x = -(Matrix.diagonal (fun i => CatalanLambda.Dq ℓ K (rn G i)) *
        G.Full lamFrame x * Matrix.diagonal (fun j => CatalanLambda.Dq ℓ K (cn G j))) := by
      ext i j
      simp [Ncell, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc, mul_comm, mul_left_comm]
    rw [this, Matrix.det_neg, Matrix.det_mul, Matrix.det_mul, hdet]
    simp
  have hy := det_eq_zero_of_good (eIdx K G hlow) (Ncell ℓ K G x)
    (Zmat (-red ℓ x) (Alow ℓ K) (WC ℓ K G) (WX ℓ K G) (WY ℓ K G))
    (fun i j => y_good hlK G hlow hlt hhi hx' i j) h0
  rw [det_Zmat h2 (-red ℓ x) (CatalanLambda.cc ℓ K) (Alow ℓ K) (WC ℓ K G) (WX ℓ K G) (WY ℓ K G)
    (Gcols ℓ K nd) (hA_ident hlK G hlt hhi nd hnd hab)] at hy
  have e : CatalanLambda.cc ℓ K - 16 * -red ℓ x = CatalanLambda.cc ℓ K + 16 * red ℓ x := by ring
  rw [e] at hy
  have hne1 : ((-1 : ZMod ℓ) ^ (Fintype.card (HiC K G) + Fintype.card (Fin G.k))) ≠ 0 :=
    pow_ne_zero _ (by simp)
  have hne2 : (((-16 : ZMod ℓ) ^ Fintype.card (Fin K))⁻¹) ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 h16))
  exact (mul_eq_zero.1 hy).resolve_left (mul_ne_zero hne1 hne2)

end CatalanFrames.LambdaHybrid.NV
