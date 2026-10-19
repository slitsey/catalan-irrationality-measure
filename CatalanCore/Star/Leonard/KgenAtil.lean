module

public import CatalanCore.Star.Leonard.KgenBridge
public import CatalanCore.Star.Leonard.KStepKS

/-!
# `k^gen` and `u(Ã, Π c_S)` (package H7 glue)

For `S ≥ 1`, `K = m + n`: the legacy `kgen K m S θ` (with `N = ∑_{j=1}^{S-1} w_j w_jᵀ`) and the bordered
Krylov determinant `bkdet W_Y (Ã_S) (Π w_S)` of the Darboux route (`Ã_S = Π N_S Π`, `N_S = ∑_{y=1}^S`)
agree up to the explicit nonzero constant of `kgenN_bridge` (`kgen_bridge`).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma Nmat_Icc_eq_Nsum (K : ℕ) (θ : F) (s : ℕ) :
    CatalanCore.Star.Nmat K θ (Finset.Icc (1 : ℤ) (s : ℤ)) =
      Nsum (fun y : ℕ => wcol K θ (y : ℤ)) s := by
  have hmap : (Finset.Icc 1 s).map ⟨Nat.cast, Nat.cast_injective⟩ = Finset.Icc (1 : ℤ) (s : ℤ) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩; omega
    · intro h; exact ⟨x.toNat, ⟨by omega, by omega⟩, by omega⟩
  unfold CatalanCore.Star.Nmat Nsum
  rw [← hmap, Finset.sum_map]
  rfl

lemma krylov_PNP_eq {K : ℕ} (Pj N : Matrix (Fin K) (Fin K) F) (hidem : Pj * Pj = Pj)
    (v : Fin K → F) (hv : Pj *ᵥ v = v) (k : ℕ) :
    (Pj * N * Pj) ^ k *ᵥ v = (Pj * N) ^ k *ᵥ v ∧ Pj *ᵥ ((Pj * N) ^ k *ᵥ v) = (Pj * N) ^ k *ᵥ v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hPP : ∀ x, Pj *ᵥ (Pj *ᵥ x) = Pj *ᵥ x := fun x => by
      rw [Matrix.mulVec_mulVec, hidem]
    refine ⟨?_, ?_⟩
    · rw [pow_succ', ← Matrix.mulVec_mulVec, h1, pow_succ', ← Matrix.mulVec_mulVec]
      simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      rw [h2]
    · rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hidem]

section KB

variable [CharZero F] (m n S : ℕ) (θ : F) (hθ : Gen θ)
  (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)

include hΔ in
/-- `u(Π N_{S-1}, Π w_S) = u(Ã_S, Π w_S)` for `S ≥ 1`. -/
theorem bkdet_PN_eq_Atil (hS : 1 ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ)))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *
          Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) (S - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) =
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) := by
  obtain ⟨hPW, -⟩ := projB_props m n S θ hΔ
  have hidem := projB_idem m n S θ hΔ
  set Pj := projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) with hPj
  set N' := Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) (S - 1) with hN'
  set v := Pj *ᵥ wcol (m + n) θ (S : ℤ) with hv
  have hPv : Pj *ᵥ v = v := by rw [hv, Matrix.mulVec_mulVec, hidem]
  -- Atil_S = Π N' Π + (Π w_S)(Πᵀ w_S)ᵀ
  have hA : Atil m n S θ = Pj * N' * Pj +
      Matrix.vecMulVec v (Pjᵀ *ᵥ wcol (m + n) θ (S : ℤ)) := by
    unfold Atil
    have hNs : Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) S =
        N' + Matrix.vecMulVec (wcol (m + n) θ (S : ℤ)) (wcol (m + n) θ (S : ℤ)) := by
      have := Nsum_succ (fun y : ℕ => wcol (m + n) θ (y : ℤ)) (S - 1)
      rw [show S - 1 + 1 = S by omega] at this
      rw [this]
    rw [hNs, Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.mulVec_transpose]
  have hB : ∀ x ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))), (Pj * N' * Pj) *ᵥ x ∈
      CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))) := by
    intro x hx
    rw [← Matrix.mulVec_mulVec, hPW x hx, Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  have h1 := CatalanCore.bkdet_add_vecMulVec hB (Pjᵀ *ᵥ wcol (m + n) θ (S : ℤ)) v
  rw [hA, h1]
  unfold CatalanCore.bkdet
  congr 2
  ext i k
  simp only [CatalanCore.krylovE, Matrix.of_apply]
  rw [(krylov_PNP_eq Pj N' hidem v hPv k).1]


include hθ hΔ in
/-- **The bridge `kgen` ↔ `u(Ã, Π w_S)`.**  With `c_X = Π_X(S)/∏_a(θ+a+S)`, `c_Y = Π_Y(S)/∏_a(θ+a+S)`,
`U = ubasis_X`, `H = Hn`:
`c_Y^n · det[W_Y | U] · kgen = c_X^n · det H · u(Ã_S, Π w_S)`. -/
theorem kgen_bridge (hS : 1 ≤ S) (hH : IsUnit (Hn (m + n) m S n θ).det) :
    (piB (bY m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ^ n *
        (CatalanCore.bmat (Wb (m + n) θ (bY m (S : ℤ)))
          (ubasis (m + n) n θ (bX m (S : ℤ)))).det *
        kgen (m + n) m S θ =
      (piB (bX m (S : ℤ)) (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ^ n *
        (Hn (m + n) m S n θ).det *
        CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
          (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) := by
  have key : ∀ (a : Fin (m + n)) (z : ℤ), θ + ((a : ℕ) : F) + (z : F) ≠ 0 := fun a z =>
    gen_add hθ a z
  have hJ : Finset.Icc (1 : ℤ) ((S : ℤ) - 1) = Finset.Icc (1 : ℤ) (((S - 1 : ℕ)) : ℤ) := by
    congr 1; omega
  unfold CatalanCore.Star.kgen CatalanCore.Star.kgenR
  rw [kgenCore_eq_kgenN m n θ _ (S : ℤ) (bX m (S : ℤ)) (bY m (S : ℤ))]
  have := kgenN_bridge (m := m) (n := n) θ (Finset.Icc (1 : ℤ) ((S : ℤ) - 1)) S (bX m (S : ℤ))
    (bY m (S : ℤ))
    (fun a b h => Fin.ext (Nat.cast_injective h))
    (piB_bX_bY_eq m S)
    (fun j _ a => key a j)
    (fun a => by simpa using key a (S : ℤ))
    (fun i a => key a _) (fun i a => key a _) hΔ hH
  rw [hJ, Nmat_Icc_eq_Nsum, bkdet_PN_eq_Atil m n S θ hΔ hS] at this
  rw [hJ]
  exact this

end KB

end CatalanCore.Star.Leonard
