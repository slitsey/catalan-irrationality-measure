module

public import CatalanFrames.LambdaMirrorHybrid.MirNV
public import CatalanFrames.LambdaMirror.Const
public import CatalanCore.Rect.PairNV
public import CatalanCore.Rect.PairBridge
public import CatalanCore.Measure.Scaling

@[expose] public section

/-!
# λ′: the hybrid measure theorem from content, decay and nonvanishing (LAMASM)

Mirror of `CatalanFrames/LambdaHybrid/Assembly.lean` for `λ′ = G/2 + 5π²/96`, the prime class
`ℓ ≡ 1 (mod 4)`, `K = (ℓ + 3)/4`.  The mirror hybrid content theorem (a `HybInst mirFrame` and
its deficit bounds) does not exist yet, so the content `HasContent (hybPairFam mirFrame 8) Λ` is a
hypothesis (it follows from `hasContent_hybPair` once the mirror content is built).
-/

open Filter CatalanCore CatalanCore.Rect CatalanFrames.LambdaMirror

namespace CatalanFrames.LambdaMirrorHybrid

theorem mir_hybPairNV : HybPairNV mirFrame (fun l => l % 4 = 1) (fun l => (l + 3) / 4) := by
  intro ℓ hℓ hcls m s' r hm hmK hrK hr hS x hx h1 h2
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hc : ℓ % 4 = 1 := hcls
  have hlK : ℓ + 3 = 4 * ((ℓ + 3) / 4) := by omega
  exact mir_hyb_nonvanishing hlK m s' r hm hmK hrK hr hS (CatalanCore.mem_S.2 hx) h1 h2

theorem mir_hK : ∀ l : ℕ, l.Prime → l % 4 = 1 → l ≤ 4 * ((l + 3) / 4) ∧
    4 * ((l + 3) / 4) ≤ l + 3 := by
  intro l _ h
  omega

theorem mir_hyb_measure_of_decay {Λ D C E : ℚ}
    (hΛ : HasContent (hybPairFam mirFrame 8) (Λ : ℝ))
    (hD : HasDecay (hybridFamUp mirFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2d : Mem2Decay mirFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E) :
    (hybPairFam mirFrame 8).MeasureLB (E : ℝ) :=
  measure_hybPair mirFrame (c := 1) (by norm_num) (by simpa using isUnit_mod4_one)
    mir_hK mir_hybPairNV hΛ (hasDecay_hybPair (by exact_mod_cast hC.le) hD M2d) hη hC hη2 hE

/-- The statement in the project's form `G + 5π²/48`. -/
theorem mir_hyb_measure_G {Λ D C E : ℚ}
    (hΛ : HasContent (hybPairFam mirFrame 8) (Λ : ℝ))
    (hD : HasDecay (hybridFamUp mirFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2d : Mem2Decay mirFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E)
    (hE0 : 0 ≤ E) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      + 5 * Real.pi ^ 2 / 48) (E : ℝ) := by
  have h := mir_hyb_measure_of_decay hΛ hD M2d hη hC hη2 hE
  have h' : Measure.MeasureLBAt mirFrame.const (E : ℝ) := h
  rw [const_eq] at h'
  have := h'.affine (by exact_mod_cast hE0) 2 0 (by norm_num)
  convert this using 1
  push_cast
  ring

#print axioms mir_hyb_measure_G

end CatalanFrames.LambdaMirrorHybrid
