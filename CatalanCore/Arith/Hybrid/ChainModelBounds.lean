module
public import CatalanCore.Arith.Hybrid.ChainModel
public import CatalanCore.Arith.Hybrid.LemmaE.ProjectedBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}
lemma Q_eq_shift : Q Fr p r xs ys =
    ((p:ℚ)^2 • (Matrix.of (fun i j : Fin r=>Fr.Mn i.val j.val))).map (C : ℚ →+* ℚ[X])+(X : ℚ[X]) • 1 := by
  change Atil p (fun _ : Fin r=>1)
    (((Matrix.of (fun i j : Fin r=>Fr.Mn i.val j.val)).map (C : ℚ →+* ℚ[X])+(X : ℚ[X]) • 1).map (rescaleHom p 2)) = _
  simpa using Atil_rescale_shift (p:=p) (Matrix.of (fun i j : Fin r=>Fr.Mn i.val j.val)) 1
lemma Q_apply (i j : Fin r) : Q Fr p r xs ys i j =
    C ((p:ℚ)^2 * Fr.Mn i.val j.val)+X*(if i=j then 1 else 0) := by
  rw [Q_eq_shift]
  simp [Matrix.smul_apply, Matrix.one_apply]
lemma Q0_apply_same (i j : Fin r) (hij : i.val%p=j.val%p) :
    Q0 Fr p r xs ys i j = Q Fr p r xs ys i j := by
  simp [Q0, blockProject, blockRect, hij]
lemma Q_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ i j,Int1 p (Q Fr p r xs ys i j) := by
  rw [Q_eq_shift]
  intro i j
  apply Int1.add
  · change Int1 p (C ((p:ℚ)^2 * Fr.Mn i.val j.val))
    rw [Int1, gn_C]
    exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp (Mn_square_mem hL hp hN (i.isLt.trans_le hr) (j.isLt.trans_le hr))
  · by_cases hi : i=j
    · subst j; simpa using (show Int1 p (X:ℚ[X]) from by
        unfold Int1; exact (gle_iff_gn p 0 X).mp GLE.X)
    · simp [Matrix.smul_apply, Matrix.one_apply, hi, Int1.zero]
lemma Q0_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ i j,Int1 p (Q0 Fr p r xs ys i j) :=
  blockRect_int1 _ _ _ (Q_int1 hL hp hN hr)
lemma h_primitive (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    gn p (h Fr p r xs ys)=1 := by
  unfold h Q0
  rw [Q_eq_shift]
  apply prim_blockProject_shift
  intro i j
  exact Mn_square_mem hL hp hN (i.isLt.trans_le hr) (j.isLt.trans_le hr)
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.h_primitive
