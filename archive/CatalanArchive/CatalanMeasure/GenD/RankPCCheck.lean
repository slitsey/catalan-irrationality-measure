module
public import CatalanMeasure.GenD.RankU6
@[expose] public section

/-!
Parity checks of Theorems U6g and S at the design `(20,3,1,2,1)`.

* U6g: for `4N ≤ p`, `2p ≤ 9N` the nullity is at least `(p-1)/2 - 2N` (the banked region).
* S: for `5N ≤ p ≤ 7N` the nullity is at least `min((9p-1)/2 - 26N, 22N - (7p+1)/2)`, the
  window law `(52N/9, 44N/7)`.
-/

namespace CatalanMeasure.GenD
open CatalanMeasure.Parametric

def designPC20 : Parameters := ⟨20, 3, 1, 2, 1⟩

theorem designPC20_adm : Admissible designPC20 := by unfold designPC20 Admissible; decide

theorem designPC20_vals (N : ℕ) :
    designPC20.n N = 20 * N ∧ designPC20.b N = 3 * N ∧ designPC20.q N = N ∧
    designPC20.g N = 2 * N ∧ designPC20.h N = N ∧ designPC20.L N = 24 * N ∧
    designPC20.C N = 26 * N ∧ designPC20.H N = 27 * N := by
  have hn : designPC20.n N = 20 * N := rfl
  have hb : designPC20.b N = 3 * N := rfl
  have hq : designPC20.q N = N := by unfold designPC20 Parameters.q; simp
  have hg : designPC20.g N = 2 * N := rfl
  have hh : designPC20.h N = N := by unfold designPC20 Parameters.h; simp
  have hL : designPC20.L N = 24 * N := by
    unfold Parameters.L; rw [hn, hb, hq]; omega
  have hC : designPC20.C N = 26 * N := by
    unfold Parameters.C; rw [hL, hg]; omega
  have hH : designPC20.H N = 27 * N := by
    unfold Parameters.H; rw [hC, hh]; omega
  exact ⟨hn, hb, hq, hg, hh, hL, hC, hH⟩

theorem designPC20_u6 {N p : ℕ} [Fact p.Prime] (hN : 0 < N) (hp2 : p ≠ 2)
    (h4 : 4 * N ≤ p) (h9 : 2 * p ≤ 9 * N) (hH : designPC20.H N < p ^ 2) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (designPC20.n N) =>
        filteredEntryRat designPC20 0 N r.val k.val)).rank + ((p - 1) / 2 - 2 * N) ≤ 20 * N := by
  have hodd := odd_of_ne_two hp2
  obtain ⟨hn, hb, hq, hg, hh, hL, hC, hHv⟩ := designPC20_vals N
  have h0 : uM0 designPC20 N p = max (designPC20.q N) (designPC20.H N + designPC20.q N - 6 * p) :=
    rfl
  have h := u6_rank_closed (P := designPC20) designPC20_adm hN hp2 hH
    (by omega) (by omega) (by omega) (by omega)
  omega

theorem designPC20_s {N p : ℕ} [Fact p.Prime] (hN : 0 < N) (hp2 : p ≠ 2)
    (h5 : 5 * N ≤ p) (h7 : p ≤ 7 * N) (hH : designPC20.H N < p ^ 2) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (designPC20.n N) =>
        filteredEntryRat designPC20 0 N r.val k.val)).rank +
      min ((9 * p - 1) / 2 - 26 * N) (22 * N - (7 * p + 1) / 2) ≤ 20 * N := by
  have hodd := odd_of_ne_two hp2
  obtain ⟨hn, hb, hq, hg, hh, hL, hC, hHv⟩ := designPC20_vals N
  have h := s_rank (P := designPC20) designPC20_adm hN hp2 hH (by omega) (by omega)
  unfold sM0 sM1 sE at h
  omega

#print axioms u6_rank
#print axioms s_rank
#print axioms designPC20_u6
#print axioms designPC20_s

end CatalanMeasure.GenD
