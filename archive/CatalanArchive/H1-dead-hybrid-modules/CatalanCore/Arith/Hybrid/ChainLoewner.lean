module
public import CatalanCore.Arith.Hybrid.ChainAlgebra
public import CatalanCore.Arith.Hybrid.ChainBlocks
public import CatalanCore.Arith.Hybrid.ClearedCancellation
@[expose] public section
open Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainClasses
open LemmaE
variable {p : ℕ} [Fact p.Prime]




/-- Uniform first-order entry congruence in integral rational lifts of finite-field data. -/
lemma loewner_entry_cng {Fr : Frame} {o N k A B : ℕ}
    (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hk4 : (4 : ZMod p)*k=o) (hA : A<N) (hB : B<N)
    {d a b : ZMod p} (hd : d≠0) (hdisp : (B : ZMod p)-A=d)
    (ha : Lv (singularNodes p o N) (deltaResidue p o) A=a)
    (hb : Lv (singularNodes p o N) (deltaResidue p o) B=b) :
    Cng p (C ((p:ℚ)*Fr.Mn A B))
      (C (residueLift ((16*d)⁻¹)) * (C (residueLift b)-C (residueLift a))) := by
  have g := good_Mn_cross_uniform hL hp5 hN hk4 hA hB (by rwa [hdisp])
  rw [hdisp,ha,hb] at g
  have gm := (good_residueLift ((16*d)⁻¹)).mul
    ((good_residueLift b).sub (good_residueLift a))
  have H := good_constants_cng g gm
  simpa only [C_mul,C_sub] using H
end CatalanCore.Arith.Hybrid.ChainClasses
#print axioms CatalanCore.Arith.Hybrid.ChainClasses.loewner_entry_cng
