module
public import CatalanCore.Li2.NVMod.ResRec
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

theorem RFValue.rational_Q (φ : ℤ[X]→+*ℚ) (q : ℚ) : RFValue φ (q:RatFunc ℚ) q := by
  have hd : (q.den:ℚ)≠0 := by exact_mod_cast q.den_ne_zero
  have hh := (RFValue.int φ q.num).div (RFValue.nat φ q.den) hd
  have he : (q:RatFunc ℚ)=(q.num:RatFunc ℚ)/(q.den:RatFunc ℚ) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using
      congrArg (fun x : ℚ=>(x:RatFunc ℚ)) (Rat.num_div_den q).symm
  rw [←he,Rat.num_div_den] at hh
  exact hh

theorem omega_value_Q (φ : ℤ[X]→+*ℚ) (z : ℚ) (hX : RFValue φ rfX z) (hz : z≠0) (m : ℕ) :
    RFValue φ (omegaRF m) (omega z m) := by
  unfold omegaRF omega
  apply RFValue.sum
  intro b hb
  have hbp := (Finset.mem_Icc.mp hb).1
  have hb0 : (b:ℚ)≠0 := by exact_mod_cast (show b≠0 by omega)
  have hh := (hX.zpow hz ((b:ℤ)-m)).div ((RFValue.nat φ b).pow 2) (pow_ne_zero _ hb0)
  simpa only [rfPoly_C_rat,Rat.cast_pow,Rat.cast_natCast] using hh

theorem moment_value_Q (φ : ℤ[X]→+*ℚ) (z : ℚ) (hX : RFValue φ rfX z)
    (hz : z≠0) (h1 : z≠1) (A : TypeKey) (g : ℚ[X]) :
    RFValue φ (momentRF A g) (L A z g) := by
  rw [momentRF_partial_fractions,moment_partial_fractions A g z hz h1]
  apply RFValue.add
  · apply RFValue.sum
    intro m hm
    have hc := RFValue.rational_Q φ (residue A m*g.eval (-(m:ℚ)))
    simpa only [eq_ratCast] using hc.mul (omega_value_Q φ z hX hz m)
  · apply RFValue.sum
    intro k hk
    have hc := RFValue.rational_Q φ ((polyPart A g).coeff k)
    simpa only [eq_ratCast] using ((RFValue.nat φ k).mul hc).mul (hX.polylog h1 (k-1))

theorem EndpointInput.eval_clear (I : EndpointInput) (z : ℚ) (hz : z≠0) (h1 : z≠1) :
    (I.F.map (Int.castRingHom ℚ)).eval z=
      ((I.D:ℚ)*z^I.clearZ*(1-z)^I.clearOne)^I.key.size*K I.key z := by
  let φ : ℤ[X]→+*ℚ := Polynomial.eval₂RingHom (Int.castRingHom ℚ) z
  let s : ℚ := (I.D:ℚ)*z^I.clearZ*(1-z)^I.clearOne
  have hx : RFValue φ rfX z := by
    simpa only [φ,intPolyRF,Polynomial.map_X,rfX,Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X] using RFValue.intPoly φ X
  have hone : RFValue φ (1:RatFunc ℚ) (1:ℚ) := by simpa using RFValue.nat φ 1
  have hD : RFValue φ (rfPoly (C (I.D:ℚ))) (I.D:ℚ) := by
    simpa only [rfPoly_C_rat,Rat.cast_natCast] using RFValue.nat φ I.D
  have hmat : φ.mapMatrix (Matrix.of fun i j : Fin I.key.size=>I.mz (i.val+j.val))=
      s • (Matrix.of fun i j : Fin I.key.size=>L I.key z (X^(i.val+j.val))) := by
    apply Matrix.ext
    intro i j
    have hm := moment_value_Q φ z hx hz h1 I.key (X^(i.val+j.val))
    have hv := ((hD.mul (hx.pow I.clearZ)).mul ((hone.sub hx).pow I.clearOne)).mul hm
    have hp := RFValue.intPoly φ (I.mz (i.val+j.val))
    rw [I.moment_clear] at hp
    exact hp.unique hv
  rw [Polynomial.eval_map]
  change φ I.F=_
  rw [EndpointInput.F,RingHom.map_det,hmat,Matrix.det_smul,Fintype.card_fin]
  rfl

#print axioms moment_value_Q
#print axioms EndpointInput.eval_clear
end
end CatalanCore.Li2.NVMod
