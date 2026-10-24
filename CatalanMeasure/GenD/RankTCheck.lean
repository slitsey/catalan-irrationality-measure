module
public import CatalanMeasure.GenD.RankT
public import CatalanMeasure.GenD.RankUCheck
@[expose] public section

/-!
Parity check of Theorem T at the design `(20,3,1,2,1)`.

For `22N ≤ 3p` and `3p < 26N` (the paper's sparse-bank region `[22/3, 26/3] N` of the tent
`gamma`, area `4/3`), Theorem T gives nullity at least `min (3p - 22N) (26N - 3p) (2N - 1)`:
the tent of height `2N`, with the single unit loss at the plateau coming from `n - 1`.
-/

namespace CatalanMeasure.GenD
open CatalanMeasure.Parametric

theorem designP20_tentD {N p : ℕ} :
    tentD designP20 N p = min (2 * N) (min (18 * N - 1 - 2 * p) (26 * N - 3 * p)) := by
  unfold tentD designP20
  simp only [Parameters.n, Parameters.g, Parameters.C, Parameters.L, Parameters.b,
    Parameters.q]
  omega

theorem designP20_T_nullity {N p : ℕ} [Fact p.Prime] (hN : 0 < N) (hp2 : p ≠ 2)
    (h1 : 22 * N ≤ 3 * p) (h2 : 3 * p + 1 ≤ 26 * N) (h3 : p + 1 ≤ 9 * N)
    (hH : designP20.H N < p ^ 2) :
    min (3 * p - 22 * N) (min (26 * N - 3 * p) (2 * N - 1)) ≤ designP20.n N -
      (scaledResidueMatrix (p := p)
        (Matrix.of fun r k : Fin (designP20.n N) => filteredEntryRat designP20 0 N r.val k.val)).rank := by
  have hD := designP20_tentD (N := N) (p := p)
  have hHd : designP20.H N = 27 * N := by
    unfold designP20
    simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
      Parameters.q, Parameters.g, Parameters.h]
    omega
  have hg : designP20.g N = 2 * N := rfl
  have hn : designP20.n N = 20 * N := rfl
  have hcost : designP20.n N + designP20.q N + designP20.g N + designP20.h N = 24 * N := by
    unfold designP20
    simp only [Parameters.n, Parameters.q, Parameters.g, Parameters.h]
    omega
  have h := t_rank (P := designP20) (p := p) (by unfold designP20 Admissible; decide) hN hp2 hH
    (by omega) (by omega) (by rw [hD]; omega)
  rw [hcost, hD] at h
  omega

#print axioms t_rank
#print axioms designP20_T_nullity

end CatalanMeasure.GenD
