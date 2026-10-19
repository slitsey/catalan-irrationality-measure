module

public import CatalanCore.Arith.Hybrid.DefBFinal
public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# Bordered Theorem B (MEM2C): `defHypTop_B`

Bordered Theorem B from the rank witness `gleAt_B_lam_wit` (`HasRankWit.border`).
`gle_full_of_rank` replaced by `gle_fullTop_of_rank'` (conclusions for `afterTop r m`, extra cost
`topC`).  All internal lemmas are reused from `DefBC5`, `DefBFinal`.
-/

open Finset Polynomial CatalanCore CatalanCore.Rect CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {r m j k : ℕ}

/-- **Bordered Theorem B at a prime** (member 2, cost `topC`), from the rank witness. -/
theorem gleAt_Btop_lam {Fr : Frame} (I : HybInst Fr) {o : ℕ} (hL : LamData Fr o)
    (S : BSetup o p r m j k) (hpm : p < r + m) :
    GLE p (∑ a, uPot p r k (Frame.hybRow r m a) + ∑ b, uPot p r k (Frame.hybCol r m b) -
      (m - (p - r)) + topC I r m p) ((afterTop r m).fullPolyG Fr) :=
  (gleAt_B_lam_wit hL S hpm).border I

end

open Classical in
/-- **Bordered Theorem B as a `DefHypTop` family** (twin of `defHypT_B`, same hypotheses). -/
theorem defHypTop_B {Fr : Frame} (I : HybInst Fr) {o : ℕ} (hL : LamData Fr o) (r m : ℕ) (T : ℕ → ℕ)
    (W : ℕ → Prop) (hW : ∀ p, W p → p < r + m)
    (hSet : ∀ p : ℕ, p.Prime → W p → ∃ j k, BSetup o p r m j k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → ∀ j k, BSetup o p r m j k →
      ∑ a, uPot p r k (Frame.hybRow r m a) + ∑ b, uPot p r k (Frame.hybCol r m b) ≤ T p) :
    DefHypTop I r m T (fun p => if W p then m - (p - r) else 0) := by
  refine defHypTop_of_local T _ hT W (fun p hp => by simp [hp]) ?_
  intro p hp hb hWp
  obtain ⟨j, k, S⟩ := hSet p hp hWp
  haveI : Fact p.Prime := ⟨hp⟩
  have hd := hTd p hp hWp j k S
  have h1 := uPot_sum_ge (p := p) (r := r) (m := m) (k := k) S.hrp
  have hg := gleAt_Btop_lam I hL S (hW p hWp)
  simp only [if_pos hWp]
  exact fun [Fact p.Prime] => hg.mono (show _ ≤ T p - (m - (p - r)) + topC I r m p by omega)

end CatalanCore.Arith.Hybrid
