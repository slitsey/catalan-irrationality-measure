module
public import CatalanMeasure.GenD.RankU
@[expose] public section

/-!
Parity check of Theorem U at the design `(20,3,1,2,1)`: window `8N ≤ p ≤ 9N` gives `18N - 2p - 1`.
-/

namespace CatalanMeasure.GenD
open CatalanMeasure.Parametric

def designP20 : Parameters := ⟨20, 3, 1, 2, 1⟩

theorem designP20_window {N p : ℕ} (h8 : 8 * N ≤ p) (h9 : p ≤ 9 * N) :
    UWindow designP20 N p := by
  unfold designP20
  constructor <;>
    simp only [Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] <;> omega

theorem designP20_uStar {N p : ℕ} (h8 : 8 * N ≤ p) :
    uStar designP20 N p - designP20.g N - 2 * p - 1 = 18 * N - 2 * p - 1 := by
  unfold uStar designP20
  simp only [Parameters.n, Parameters.g]
  omega

theorem designP20_nullity {N p : ℕ} [Fact p.Prime] (hN : 0 < N) (hp2 : p ≠ 2)
    (h8 : 8 * N ≤ p) (h9 : p ≤ 9 * N) (hH : designP20.H N < p ^ 2) :
    18 * N - 2 * p - 1 ≤ designP20.n N -
      (scaledResidueMatrix (p := p)
        (Matrix.of fun r k : Fin (designP20.n N) => filteredEntryRat designP20 0 N r.val k.val)).rank := by
  have h := u_nullity (P := designP20) (by unfold designP20 Admissible; decide) hN hp2 hH
    (designP20_window h8 h9)
  rwa [designP20_uStar h8] at h

#print axioms u_rank
#print axioms designP20_nullity

end CatalanMeasure.GenD
