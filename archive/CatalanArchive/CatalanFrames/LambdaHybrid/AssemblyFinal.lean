module

public import CatalanFrames.Lambda.HybContent
public import CatalanArchive.CatalanFrames.LambdaHybrid.AssemblyDecayAll
public import CatalanFrames.LambdaHybrid.PairG

@[expose] public section

/-!
# λ hybrid measure theorem, unconditional (LAMFINAL)

`lam_hyb_measure_of_both`: the decay of both members is proved (`lam_hyb_decay_member1`,
`lam_mem2_decay`, `D = 3.9028`, `c = 7.6444`); the only input is a `DefBoth` content family
(simultaneous member-1/member-2 deficit family) at a constant `Λ`.
`lam_hyb_measure_final` instantiates it with `Λ₁ = 3.70343 ≥ 3.7034204…` (deficits E, B, C5, C7, GK,
all bordered).  Exponent `c/(D - Λ₁) = 38.3419… ≤ 38.35`.  `lam_hyb_measure_final_nogk` is the earlier
GK-free form (`Λ₂ = 3.708`, exponent `39.2423…`).
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

/-- **λ hybrid measure theorem from a `DefBoth` content family at constant `Λ`**; decay of both
members is built in (`D = 3.9028`, `c = 7.6444`). -/
theorem lam_hyb_measure_of_both {Λ E : ℚ}
    (hboth : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ ((Λ : ℝ) + ε) * (r : ℝ) ^ 2)
    (hΛ0 : 0 ≤ Λ) (hη : Λ < 39028 / 10000) (hη2 : 2 * (39028 / 10000 - Λ) < 23 / 10)
    (hE : (76444 / 10000 : ℚ) / (39028 / 10000 - Λ) ≤ E) (hE0 : 0 ≤ E) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (E : ℝ) :=
  lam_pairMeasure_G hE0
    (lam_hyb_measure_of_content_eps
      (fun ε hε => (hboth ε hε).mono fun r ⟨T, δ, hδ, hlog⟩ => ⟨T, δ, hδ.1, hlog⟩) hΛ0
      lam_hyb_decay_member1 (lam_mem2Content_of_both le_rfl hboth) lam_mem2_decay hη
      (by norm_num) hη2 hE)

/-- **λ hybrid measure theorem (final, no `Mem2*`/decay hypotheses)**:
`μ(G - 5π²/48) ≤ 38.35` (true exponent `38.3419…`), all seven deficits (E, B, C5, C7, GK) bordered:
content constant `Λ₁ = 3.7034204… ≤ 3.70343`. -/
theorem lam_hyb_measure_final :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (((3835 / 100 : ℚ)) : ℝ) :=
  lam_hyb_measure_of_both (Λ := 370343 / 100000) (E := 3835 / 100)
    (lam_both_eps4 (by push_cast; norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The previous form (GK not bordered): `μ(G - 5π²/48) ≤ 39.25`. -/
theorem lam_hyb_measure_final_nogk :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (((3925 / 100 : ℚ)) : ℝ) :=
  lam_hyb_measure_of_both (Λ := 3708 / 1000) (E := 3925 / 100)
    (lam_both_eps3 (by push_cast; norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

#print axioms lam_hyb_measure_final
#print axioms lam_hyb_measure_final_nogk

end CatalanFrames.LambdaHybrid
