module

public import CatalanCore.Uniform.Content.Hybrid.Compression
public import CatalanCore.Uniform.Content.ClearMin

@[expose] public section

/-!
# The hybrid rank-layer price at one prime

Assembly of UC4 (`Leading`), the compression to loads (`Compression`) and the free + pair lower
bound (`LoadKernel`):

  `denexp_p(det Φ) ≤ h + R0 - (F + E_pair(V))`

for every constant subspace `V ⊆ 𝔽_p(X)²`, where `F` is the free sector (at least the number of
load-zero right kernel vectors, `card_zeroLoad_le_finrank_ker_lam`) and `E_pair(V)` is the
constant-map Euler value of the pair conditions.  The certificate form
(`gle_det_hybrid_of_bounds`) needs only upper bounds on the restricted ranks.

Everything is stated for an arbitrary finite index type, so it applies verbatim to members and
submatrices (H5).  Competing prices at one prime combine by minimum (`ClearMin.gle_min`).
-/

open Polynomial CatalanCore.Basic CatalanCore.Arith.Hybrid Finset Module

namespace CatalanCore.Uniform.Content.Hybrid

section Free

variable {K : Type*} [Field K] [DecidableEq K] {S : Type*} [Fintype S] [DecidableEq S]
  (β : S → K) (y : S → K × K)

/-- Extension by zero from the load-zero columns. -/
noncomputable def zeroExt : ({c // y c = 0} → K) →ₗ[K] (S → K) :=
  LinearMap.pi fun c => if h : y c = 0 then LinearMap.proj (⟨c, h⟩ : {c // y c = 0}) else 0

lemma zeroExt_apply (z : {c // y c = 0} → K) (c : S) :
    zeroExt y z c = if h : y c = 0 then z ⟨c, h⟩ else 0 := by
  unfold zeroExt; split_ifs <;> simp [*]

/-- **Free sector.** Load-zero columns are free: `#{c : y_c = 0} ≤ F`. -/
theorem card_zeroLoad_le_finrank_ker_lam :
    Fintype.card {c // y c = 0} ≤ finrank K (LinearMap.ker (lam β y)) := by
  have hker : ∀ z, zeroExt y z ∈ LinearMap.ker (lam β y) := by
    intro z
    rw [LinearMap.mem_ker]
    funext b
    rw [lam_apply, Pi.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [zeroExt_apply]
    split_ifs with h
    · simp [colVec, h]
    · simp
  let J := (zeroExt y).codRestrict _ hker
  have hJ : Function.Injective J := by
    intro z z' h
    funext c
    have := congrFun (congrArg (fun w : LinearMap.ker (lam β y) => (w : S → K)) h) c
    have e1 : (J z : S → K) c = z c := by
      change zeroExt y z c = z c
      rw [zeroExt_apply, dif_pos c.2]
    have e2 : (J z' : S → K) c = z' c := by
      change zeroExt y z' c = z' c
      rw [zeroExt_apply, dif_pos c.2]
    rw [← e1, ← e2]; exact this
  have := LinearMap.finrank_le_finrank_of_injective hJ
  rwa [Module.finrank_fintype_fun_eq_card] at this

end Free

variable {p : ℕ} [Fact p.Prime]

/-- Componentwise image of a pair. -/
noncomputable def mapPair {F F' : Type*} [Field F] [Field F'] (f : F →+* F') (z : F × F) : F' × F' :=
  (f z.1, f z.2)

open LeadingData in
open scoped Classical in
/-- **Hybrid rank-layer price at one prime (exact form).** -/
theorem gle_det_hybrid {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Matrix ι ι ℚ[X]}
    (D : LeadingData p Φ) (α β Lr Lc : ι → ZMod p)
    (hCr : ∀ i j, phiP p (D.Cr i j) = rfC p ((Lc j - Lr i) / (β j - α i)))
    (ρ σ : D.s → ZMod p)
    (hu : ∀ (i : D.s) k, redQ p (D.L i k) ≠ 0 → α k = ρ i)
    (hv : ∀ (j : D.s) l, redQ p (D.P l j) ≠ 0 → β l = σ j)
    (horth : ∀ i j, ρ i = σ j → omegaL (D.rowLoad Lr i) (D.colLoad Lc j) = 0)
    (R0 : ℕ) (hR : R0 + D.s.card = Fintype.card ι)
    (Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p))) :
    GLE p (Fintype.card ι + R0 -
      (finrank (RatFunc (ZMod p)) (LinearMap.ker (lam (fun j => rfH p (σ j))
          (fun j => mapPair (rfH p) (D.colLoad Lc j)))) +
        ((colRes (fun j => rfH p (σ j))).card * finrank (RatFunc (ZMod p)) Vs -
          ∑ c, finrank (RatFunc (ZMod p)) (LinearMap.range (condMap (fun i => rfH p (ρ i))
            (fun i => mapPair (rfH p) (D.rowLoad Lr i)) (fun j => rfH p (σ j))
            (fun j => mapPair (rfH p) (D.colLoad Lc j)) Vs c))))) Φ.det := by
  apply D.gle_det_R0 R0 _ hR
  have hmat := D.nextRed_eq_loadMat α β Lr Lc hCr ρ σ hu hv
  rw [loadMat_map] at hmat
  rw [hmat]
  have horth' : ∀ r c, rfH p (ρ r) = rfH p (σ c) →
      omegaL (mapPair (rfH p) (D.rowLoad Lr r)) (mapPair (rfH p) (D.colLoad Lc c)) = 0 := by
    intro r c h
    have h0 := horth r c (rfH_injective h)
    have : omegaL (mapPair (rfH p) (D.rowLoad Lr r)) (mapPair (rfH p) (D.colLoad Lc c)) =
        rfH p (omegaL (D.rowLoad Lr r) (D.colLoad Lc c)) := by
      simp only [omegaL_apply, mapPair, map_sub, map_mul]
    rw [this, h0, map_zero]
  have h := loadMat_rank_add_le (fun i => rfH p (ρ i))
    (fun i => mapPair (rfH p) (D.rowLoad Lr i)) (fun j => rfH p (σ j))
    (fun j => mapPair (rfH p) (D.colLoad Lc j)) Vs horth'
  rw [Fintype.card_coe] at h
  have e : (fun r => ((rfH p (D.rowLoad Lr r).1, rfH p (D.rowLoad Lr r).2) :
      RatFunc (ZMod p) × RatFunc (ZMod p))) = fun i => mapPair (rfH p) (D.rowLoad Lr i) := rfl
  have e' : (fun c => ((rfH p (D.colLoad Lc c).1, rfH p (D.colLoad Lc c).2) :
      RatFunc (ZMod p) × RatFunc (ZMod p))) = fun j => mapPair (rfH p) (D.colLoad Lc j) := rfl
  rw [e, e']
  omega

lemma mapPair_eq_zero_iff (z : ZMod p × ZMod p) : mapPair (rfH p) z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [mapPair, Prod.fst_zero, Prod.snd_zero] at h1 h2
    exact Prod.ext (rfH_injective (h1.trans (map_zero _).symm))
      (rfH_injective (h2.trans (map_zero _).symm))
  · rintro rfl; simp [mapPair]

open LeadingData in
open scoped Classical in
/-- **Hybrid rank-layer price at one prime (certificate form).** The free sector is charged by
the number of load-zero right kernel vectors and the pair conditions by certified upper bounds on
their restricted ranks; `V` is any explicit constant subspace. -/
theorem gle_det_hybrid_of_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Matrix ι ι ℚ[X]}
    (D : LeadingData p Φ) (α β Lr Lc : ι → ZMod p)
    (hCr : ∀ i j, phiP p (D.Cr i j) = rfC p ((Lc j - Lr i) / (β j - α i)))
    (ρ σ : D.s → ZMod p)
    (hu : ∀ (i : D.s) k, redQ p (D.L i k) ≠ 0 → α k = ρ i)
    (hv : ∀ (j : D.s) l, redQ p (D.P l j) ≠ 0 → β l = σ j)
    (horth : ∀ i j, ρ i = σ j → omegaL (D.rowLoad Lr i) (D.colLoad Lc j) = 0)
    (R0 : ℕ) (hR : R0 + D.s.card = Fintype.card ι)
    (Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)))
    (cost : Cond (fun i => rfH p (ρ i)) (fun j => rfH p (σ j)) → ℕ)
    (hcost : ∀ c, finrank (RatFunc (ZMod p)) (LinearMap.range (condMap (fun i => rfH p (ρ i))
            (fun i => mapPair (rfH p) (D.rowLoad Lr i)) (fun j => rfH p (σ j))
            (fun j => mapPair (rfH p) (D.colLoad Lc j)) Vs c)) ≤ cost c) :
    GLE p (Fintype.card ι + R0 -
      (Fintype.card {j : D.s // D.colLoad Lc j = 0} +
        ((colRes (fun j => rfH p (σ j))).card * finrank (RatFunc (ZMod p)) Vs -
          ∑ c, cost c))) Φ.det := by
  refine (gle_det_hybrid D α β Lr Lc hCr ρ σ hu hv horth R0 hR Vs).mono ?_
  have hF := card_zeroLoad_le_finrank_ker_lam (fun j => rfH p (σ j))
    (fun j => mapPair (rfH p) (D.colLoad Lc j))
  have hcard : Fintype.card {j : D.s // D.colLoad Lc j = 0} =
      Fintype.card {j : D.s // mapPair (rfH p) (D.colLoad Lc j) = 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun j => (mapPair_eq_zero_iff _).symm)
  have hc : ∑ c, finrank (RatFunc (ZMod p)) (LinearMap.range (condMap (fun i => rfH p (ρ i))
            (fun i => mapPair (rfH p) (D.rowLoad Lr i)) (fun j => rfH p (σ j))
            (fun j => mapPair (rfH p) (D.colLoad Lc j)) Vs c)) ≤ ∑ c, cost c :=
    Finset.sum_le_sum fun c _ => hcost c
  omega

/-- Competing certified prices at one prime combine by minimum. -/
theorem gle_det_min {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Matrix ι ι ℚ[X]} {a b : ℕ}
    (ha : GLE p a Φ.det) (hb : GLE p b Φ.det) : GLE p (min a b) Φ.det :=
  CatalanCore.Uniform.Content.gle_min ha hb

end CatalanCore.Uniform.Content.Hybrid
