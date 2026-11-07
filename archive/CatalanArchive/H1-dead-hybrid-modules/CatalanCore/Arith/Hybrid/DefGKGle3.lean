module

public import CatalanCore.Arith.Hybrid.GKUniform

@[expose] public section

/-!
# GK, class `p ≡ 3 (mod 4)`: `v_p(den_F) ≤ 2r` and the `DefHypT` family

`gleAt_GK3`: `GLE p (2 r) (Fr.fullPoly r m)` for `GKS3 o p r m k` (`13 ≤ p`, `4k = p+1`, `2p+k < r`,
`r + 2m ≤ 3p`, `p ≠ 139`), for a `λ`-like frame.  `defHypT_GK3`: the deficit `m` against any
`T ≥ 2r + m` on a window `W` of such primes.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid

section Gle3

variable {o p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

/-- **GK, class 3.** -/
theorem gleAt_GK3 (hL : LamData Fr o) (S : GKS3 o p r m k) : GLE p (2 * r) (Fr.fullPoly r m) := S.uniform_gle hL

end Gle3

open Classical in
/-- **GK (class 3) as a `DefHypT` family.** -/
theorem defHypT_GK3 {Fr : Frame} (I : HybInst Fr) {o : ℕ} (hL : LamData Fr o) (r m : ℕ) [I.DiagOK r m] (T : ℕ → ℕ)
    (W : ℕ → Prop) (hSet : ∀ p : ℕ, p.Prime → W p → ∃ k, GKS3 o p r m k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → 2 * r + m ≤ T p) :
    DefHypT I r m T (fun p => if W p then m else 0) := by
  refine defHypT_of_local I r m T _ hT W (fun p hp => by simp [hp]) ?_
  intro p hp hb hWp
  obtain ⟨k, S⟩ := hSet p hp hWp
  haveI : Fact p.Prime := ⟨hp⟩
  have hd := hTd p hp hWp
  have hg := gleAt_GK3 hL S
  simp only [if_pos hWp]
  exact ⟨by omega, fun [Fact p.Prime] => hg.mono (by omega)⟩

end CatalanCore.Arith.Hybrid
