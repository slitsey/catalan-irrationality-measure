module

public import CatalanCore.Rect.PairBridge
public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# `Mem2Content` from a bordered deficit family (MEM2C)

`Mem2Content Fr Λ` (the content of `det Full(afterTop r m)`, `m = r/8`) is discharged from the
member-1 content machinery plus the bordering lemma:

* `DhybTop I r m T δ = ∏_{p<Bnd} p^{T p - δ p + topC p}` clears the denominators of
  `det Full(afterTop r m)` when `DefHypTop I r m T δ` (`DhybTop_integral`);
* `log DhybTop = log DhybT + ∑ topC log p` (`log_DhybTop`);
* `mem2Content_of_top`: "for every `ε`, eventually a bordered deficit family with
  `log DhybTop ≤ (Λ + ε) r²`" gives `Mem2Content Fr Λ` (diagonal argument `exists_diag`).
-/

open Filter Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Rect

variable {Fr : Frame} (I : HybInst Fr) (r m : ℕ)

/-- The denominator of the bordered determinant. -/
noncomputable def DhybTop (T δ : ℕ → ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, p ^ (T p - δ p + topC I r m p)

theorem DhybTop_pos (T δ : ℕ → ℕ) : 0 < DhybTop I r m T δ :=
  Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _

/-- Integrality of `DhybTop · det Full(afterTop r m)`. -/
theorem DhybTop_integral {T δ : ℕ → ℕ} (hδ : DefHypTop I r m T δ) (i : ℕ) :
    ∃ z : ℤ, (DhybTop I r m T δ : ℚ) * ((afterTop r m).fullPolyG Fr).coeff i = z := by
  apply int_of_forall_locRing
  intro p hp
  by_cases hb : p < Bnd I r m
  · have hmem : p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hp.out⟩
    have hgle := hδ p hp.out hb i
    have hD : (DhybTop I r m T δ : ℚ) = (p : ℚ) ^ (T p - δ p + topC I r m p) *
        ((∏ q ∈ ((Finset.range (Bnd I r m)).filter Nat.Prime).erase p,
          q ^ (T q - δ q + topC I r m q) : ℕ) : ℚ) := by
      unfold DhybTop
      rw [← Nat.cast_pow, ← Nat.cast_mul,
        Finset.mul_prod_erase _ (fun q => q ^ (T q - δ q + topC I r m q)) hmem]
    rw [hD]
    have hR := int_mem_locRing (ℓ := p)
      ((∏ q ∈ ((Finset.range (Bnd I r m)).filter Nat.Prime).erase p,
          q ^ (T q - δ q + topC I r m q) : ℕ) : ℤ)
    have := (LocRing p).mul_mem hgle (by simpa using hR)
    convert this using 1; push_cast; ring
  · have h0 := tropExp_eq_zero I r m p hp.out (by omega)
    have h1 := topW_eq_zero_of_ge I r m p hp.out (by omega)
    have hgle := fullTop_gle' I r m p i
    rw [h0, h1] at hgle
    simp only [pow_zero, one_mul, add_zero] at hgle
    rw [mul_comm]
    exact (LocRing p).mul_mem hgle
      (by exact_mod_cast int_mem_locRing (ℓ := p) (DhybTop I r m T δ : ℤ))

theorem log_DhybTop {T δ : ℕ → ℕ} (h : DefHypT I r m T δ) :
    Real.log (DhybTop I r m T δ) =
      Real.log (DhybT I r m T δ) +
        ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (topC I r m p : ℝ) * Real.log p := by
  rw [log_DhybT I r m h]
  unfold DhybTop
  rw [Nat.cast_prod, Real.log_prod, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  · apply Finset.sum_congr rfl
    intro p hp
    have hh := h p (Finset.mem_filter.mp hp).2 (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_sub hh.1]; ring
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity

open Classical in
/-- **`Mem2ContentA` from bordered deficit families** (G3): any admissible relation `A`. -/
theorem mem2ContentA_of_top (I : HybInst Fr) {Λ : ℝ} (A : ℕ → ℕ → Prop)
    (h : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, A r m → ∃ T δ : ℕ → ℕ, DefHypTop I r m T δ ∧
      Real.log (DhybTop I r m T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    Mem2ContentA Fr A Λ := by
  haveI : Nonempty (ℕ → (ℕ → ℕ) × (ℕ → ℕ)) := ⟨fun _ => (fun _ => 0, fun _ => 0)⟩
  obtain ⟨f, hf⟩ := exists_diag (β := ℕ → (ℕ → ℕ) × (ℕ → ℕ))
    (fun ε r b => ∀ m, A r m → DefHypTop I r m (b m).1 (b m).2 ∧
      Real.log (DhybTop I r m (b m).1 (b m).2) ≤ (Λ + ε) * (r : ℝ) ^ 2)
    (fun ε ε' r b hε hb m hA =>
      ⟨(hb m hA).1, (hb m hA).2.trans (by nlinarith [sq_nonneg (r : ℝ)])⟩)
    (fun ε hε => (h ε hε).mono fun r hr => by
      have : ∀ m, ∃ b : (ℕ → ℕ) × (ℕ → ℕ), A r m → DefHypTop I r m b.1 b.2 ∧
          Real.log (DhybTop I r m b.1 b.2) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
        intro m
        by_cases hA : A r m
        · obtain ⟨T, δ, h1, h2⟩ := hr m hA
          exact ⟨(T, δ), fun _ => ⟨h1, h2⟩⟩
        · exact ⟨(fun _ => 0, fun _ => 0), fun h => absurd h hA⟩
      choose b hb using this
      exact ⟨b, hb⟩)
  have hdef0 : ∀ r m, DefHypTop I r m (tropExp I r m) (fun _ => 0) := fun r m =>
    defHypTop_of_local (I := I) (r := r) (m := m) _ _ (fun p _ _ => le_rfl) (fun _ => False)
      (fun _ _ => rfl) (fun p _ _ hS => absurd hS id)
  refine ⟨fun r m => if DefHypTop I r m (f r m).1 (f r m).2 then
      DhybTop I r m (f r m).1 (f r m).2
      else DhybTop I r m (tropExp I r m) (fun _ => 0), ?_, ?_, ?_⟩
  · intro r m
    dsimp only
    split_ifs <;> exact DhybTop_pos I r m _ _
  · intro r m _ i
    dsimp only
    split_ifs with hd
    · exact DhybTop_integral I r m hd i
    · exact DhybTop_integral I r m (hdef0 r m) i
  · intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.1 (hf ε hε)
    refine ⟨R, fun r m hA hr => ?_⟩
    obtain ⟨hd, hlog⟩ := hR r hr m hA
    dsimp only
    rw [if_pos hd]
    exact hlog

/-- **`Mem2Content` from bordered deficit families** (slope `1/8`, `m = r / 8`). -/
theorem mem2Content_of_top (I : HybInst Fr) {Λ : ℝ}
    (h : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefHypTop I r (r / 8) T δ ∧
      Real.log (DhybTop I r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    Mem2Content Fr Λ := by
  obtain ⟨D2, h1, h2, h3⟩ := mem2ContentA_of_top I (Λ := Λ) (fun r m => m = r / 8)
    (fun ε hε => (h ε hε).mono fun r ⟨T, δ, a, b⟩ m hm => ⟨T, δ, by subst hm; exact a,
      by subst hm; exact b⟩)
  refine ⟨fun r => D2 r (r / 8), fun r => h1 r _, fun r _ i => h2 r _ rfl i, fun ε hε => ?_⟩
  obtain ⟨N₀, H⟩ := h3 ε hε
  exact ⟨N₀, fun r _ hr => H r _ rfl hr⟩


end CatalanCore.Rect

namespace CatalanCore.Arith.Hybrid

/-- Replace the deficit by `δ₂` on the set `S` (bordered twin of `DefHypT.glue`). -/
lemma DefHypTop.glue {Fr : Frame} {I : HybInst Fr} {r m : ℕ} {T δ₁ δ₂ : ℕ → ℕ}
    (S : ℕ → Prop) [DecidablePred S]
    (h1 : DefHypTop I r m T δ₁) (h2 : DefHypTop I r m T δ₂) :
    DefHypTop I r m T (fun p => if S p then δ₂ p else δ₁ p) := by
  intro p hp hb _
  by_cases hS : S p
  · simpa only [if_pos hS] using h2 p hp hb
  · simpa only [if_neg hS] using h1 p hp hb

end CatalanCore.Arith.Hybrid
