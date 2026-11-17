module

public import CatalanCore.Lai.ContentFinal
public import CatalanCore.Lai.ContentBridge
public import CatalanCore.Lai.ContentL2Main

@[expose] public section

/-!
# `CatalanCore.Lai.ContentCert`: discharge of the content hypotheses

`ContentFinal` states the assembly under `L2Stmt`, `Band7Stmt`, `BridgeStmt` and the C01 prefix datum.
Here `L2Stmt` is `lai_L2` (`Lai.ContentL2Main`) and `BridgeStmt` is `bridge_proof` (`Lai.ContentBridge`).
What is left, for a complete unconditional `lai_content`, is exactly `Band7Stmt` (Lai Lemma 4.4 for
`7n/2 < p ≤ 6n`) and the W2 datum `(Ŝ, hS, hR)`.
-/

open CatalanCore.Content

namespace CatalanCore.Lai

/-- Theorem L2 (LC21) as `L2Stmt`. -/
theorem l2Stmt : L2Stmt := fun _ _ _ h => lai_L2 h

/-- **LC30 with `L2Stmt` and `BridgeStmt` discharged.** -/
theorem lai_content_cert (hB7 : Band7Stmt) (Shat : ℚ)
    (hS : CatalanCore.Content.PartialSums.partialS e23 d23 1000 ≤ Shat)
    (hR : Shat + CatalanCore.Content.PartialSums.Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ n : ℕ, R₀ ≤ n →
      0 < signedDen n laiW ∧
      (∀ q : ℕ, ∀ [Fact q.Prime], GV q 0 (MvPolynomial.C (signedDen n laiW) * laiJ n)) ∧
      Real.log ((signedDen n laiW : ℚ) : ℝ) ≤ (2868723663 / 10 ^ 8 + ε) * (n : ℝ) ^ 2 :=
  lai_content l2Stmt hB7 bridge_proof Shat hS hR hε

/-- **LC40 (plane), `L2Stmt` discharged.** -/
theorem lai_plane_hasScaledContent_cert (hB7 : Band7Stmt) (a b : ℤ) :
    CatalanCore.Uniform.HasScaledContent (laiPlaneFamS a b) id 0 :=
  lai_plane_hasScaledContent l2Stmt hB7 a b

/-- **LC40 (ratio), `L2Stmt` discharged.** -/
theorem lai_ratio_hasScaledContent_cert (hB7 : Band7Stmt) :
    CatalanCore.Uniform.HasScaledContent laiRatioFamS id 0 :=
  lai_ratio_hasScaledContent l2Stmt hB7

/-- Decay of the rescaled plane family. -/
theorem lai_plane_decay_scaled_cert (hB7 : Band7Stmt) (Shat : ℚ)
    (hS : CatalanCore.Content.PartialSums.partialS e23 d23 1000 ≤ Shat)
    (hR : Shat + CatalanCore.Content.PartialSums.Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000)
    (a b : ℤ) {D c : ℝ} (hD : CatalanCore.Uniform.HasScaledDecay (laiPlaneFam a b) id D c) :
    CatalanCore.Uniform.HasScaledDecay (laiPlaneFamS a b) id (D - 2868723663 / 10 ^ 8) c :=
  lai_plane_decay_scaled l2Stmt hB7 bridge_proof Shat hS hR a b hD

/-- Decay of the rescaled ratio family. -/
theorem lai_ratio_decay_scaled_cert (hB7 : Band7Stmt) (Shat : ℚ)
    (hS : CatalanCore.Content.PartialSums.partialS e23 d23 1000 ≤ Shat)
    (hR : Shat + CatalanCore.Content.PartialSums.Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000)
    {D c : ℝ} (hD : CatalanCore.Uniform.HasScaledDecay laiRatioFam id D c) :
    CatalanCore.Uniform.HasScaledDecay laiRatioFamS id (D - 2868723663 / 10 ^ 8) c :=
  lai_ratio_decay_scaled l2Stmt hB7 bridge_proof Shat hS hR hD

end CatalanCore.Lai

#print axioms CatalanCore.Lai.lai_content_cert
#print axioms CatalanCore.Lai.lai_plane_hasScaledContent_cert
#print axioms CatalanCore.Lai.lai_ratio_hasScaledContent_cert
#print axioms CatalanCore.Lai.lai_plane_decay_scaled_cert
#print axioms CatalanCore.Lai.lai_ratio_decay_scaled_cert
