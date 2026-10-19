module

public import CatalanCore.Arith.Hybrid.DefGKDelta1

@[expose] public section

/-!
# GK, class `p ≡ 1 (mod 4)`: `v_p(den_F) ≤ 2r` and the `DefHypT` family

`gleAt_GK1`: `GLE p (2 r) (Fr.fullPoly r m)` for `GKS1 o p r m k` (`13 ≤ p`, `4k = 3p+1`, `2p < r`,
`4(r+2m) ≤ 11p+1`, `p ≠ 1009`), for a `λ`-like frame.  `defHypT_GK1`: the deficit `m` against any
`T ≥ 2r + m` on a window `W` of such primes.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid.GK1

open CatalanCore.Arith.Hybrid

section Gle1

variable {o p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

/-- **GK, class 1.** -/
theorem gleAt_GK1 (hL : LamData Fr o) (S : GKS1 o p r m k) : GLE p (2 * r) (Fr.fullPoly r m) := by
  have := tcore_vec (Full := Matrix.of (fullEntry Fr r m)) (Atil_int hL S) (Atil_prim hL S)
    (alphaM Fr p r m) (betaM Fr p r m) (hL_bound hL S) (hL'_bound hL S) (hDelta_bound hL S)
  rw [Fintype.card_fin] at this
  exact this

end Gle1

open Classical in
/-- **GK (class 1) as a `DefHypT` family.** -/
theorem defHypT_GK1 {Fr : Frame} (I : HybInst Fr) {o : ℕ} (hL : LamData Fr o) (r m : ℕ) [I.DiagOK r m] (T : ℕ → ℕ)
    (W : ℕ → Prop) (hSet : ∀ p : ℕ, p.Prime → W p → ∃ k, GKS1 o p r m k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → 2 * r + m ≤ T p) :
    DefHypT I r m T (fun p => if W p then m else 0) := by
  refine defHypT_of_local I r m T _ hT W (fun p hp => by simp [hp]) ?_
  intro p hp hb hWp
  obtain ⟨k, S⟩ := hSet p hp hWp
  haveI : Fact p.Prime := ⟨hp⟩
  have hd := hTd p hp hWp
  have hg := gleAt_GK1 hL S
  simp only [if_pos hWp]
  exact ⟨by omega, fun [Fact p.Prime] => hg.mono (by omega)⟩

end CatalanCore.Arith.Hybrid.GK1
