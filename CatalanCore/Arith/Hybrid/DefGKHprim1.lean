module

public import CatalanCore.Arith.Hybrid.DefGKInj1
public import CatalanCore.Arith.Hybrid.DefGKHprim
public import CatalanCore.Arith.Hybrid.LemmaE.Model
public import CatalanCore.Arith.Hybrid.LemmaE.Bridge

@[expose] public section

/-!
# GK, class 1: `Atil = p² A` is integral with unit determinant (`hI`, `hprim` of `tcore_vec`)

`A = Full₁₁ = X·I + (Mn c c')`.  `Atil_int`: `p² A` is integral.  `Atil_cng`: `p² A ≡ (Qz1/56448)`.
`Atil_prim`: `gn (det (p² A)) = 1`, from `Qm1_inj`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid.GK1

open CatalanCore.Arith.Hybrid

section Hprim

variable {p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame}

variable {r m : ℕ}

theorem Atil_int (hL : LamData Fr) (S : GKS1 p r m k) (c c' : Fin r) :
    Int1 p (Atil p (fun _ : Fin r => 1) (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ c c') := by
  have hN := S.hN
  have hc := c.2; have hc' := c'.2
  have g := good_Qz1 hL S (A := (c : ℕ)) (B := (c' : ℕ)) (by omega) (by omega)
    (fun _ => hc)
  rw [Atil_entry]
  refine Int1.add ?_ ?_
  · exact int1_C_of_good (g.congr' (by ring))
  · split_ifs
    · exact gn_Cp2_X.le
    · exact Int1.zero

/-- The model matrix `Qz1 / 56448` (constants). -/
noncomputable def Mq1 (p k r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  Matrix.of fun c c' => C (((Qz1 p k (c : ℕ) (c' : ℕ) : ℤ) : ℚ) / 56448)

lemma good_Qq1 (h13 : 13 ≤ p) (z : ℤ) :
    Good p ((z : ℚ) / 56448) ((z : ZMod p) * 56448⁻¹) := by
  have := (Good.intCast (ℓ := p) z).div (Good.ofNat (ℓ := p) 56448) (n56448 h13)
  simpa [div_eq_mul_inv] using this

theorem Atil_cng (hL : LamData Fr) (S : GKS1 p r m k) (c c' : Fin r) :
    Cng p (Atil p (fun _ : Fin r => 1) (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ c c')
      (Mq1 p k r c c') := by
  have hN := S.hN
  have h13 := S.p13
  have hc := c.2; have hc' := c'.2
  have g := good_Qz1 hL S (A := (c : ℕ)) (B := (c' : ℕ)) (by omega) (by omega)
    (fun _ => hc)
  have g' := good_Qq1 (p := p) h13 (Qz1 p k (c : ℕ) (c' : ℕ))
  unfold Cng
  rw [Atil_entry]
  have e : C ((p : ℚ) ^ 1 * (p : ℚ) ^ 1 * Fr.Mn (c : ℕ) (c' : ℕ)) +
      (if c = c' then C ((p : ℚ) ^ 1 * (p : ℚ) ^ 1) * X else 0) - Mq1 p k r c c' =
      (C ((p : ℚ) ^ 1 * (p : ℚ) ^ 1 * Fr.Mn (c : ℕ) (c' : ℕ)) -
        C (((Qz1 p k (c : ℕ) (c' : ℕ) : ℤ) : ℚ) / 56448)) +
      (if c = c' then C ((p : ℚ) ^ 1 * (p : ℚ) ^ 1) * X else 0) := by
    simp only [Mq1, Matrix.of_apply]; ring
  rw [e]
  refine lt_of_le_of_lt (gn_add_le _ _) (max_lt ?_ ?_)
  · have hx : Good p ((p : ℚ) ^ 1 * (p : ℚ) ^ 1 * Fr.Mn (c : ℕ) (c' : ℕ))
        ((Qz1 p k (c : ℕ) (c' : ℕ) : ZMod p) * 56448⁻¹) := g.congr' (by ring)
    exact (cng_C_iff hx.1 g'.1).2 (hx.2.trans g'.2.symm)
  · split_ifs
    · exact gn_Cp2_X
    · rw [gn_zero]; exact one_pos

/-- `Mq1` is integral. -/
lemma Mq1_int (h13 : 13 ≤ p) (c c' : Fin r) : Int1 p (Mq1 p k r c c') :=
  int1_C_of_good (good_Qq1 h13 _)

theorem Mq1_det (S : GKS1 p r m k) : gn p (Mq1 p k r).det = 1 := by
  have h13 := S.p13
  set Z : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun c c' => Qz1 p k (c : ℕ) (c' : ℕ) with hZ
  set Q0 : Matrix (Fin r) (Fin r) ℚ := Matrix.of fun c c' : Fin r =>
    (((Qz1 p k (c : ℕ) (c' : ℕ) : ℤ) : ℚ) / 56448) with hQ0
  have hM : Mq1 p k r = Q0.map Polynomial.C := by ext c c'; simp [Mq1, hQ0]
  have hdet : (Mq1 p k r).det = C Q0.det := by
    rw [hM]; exact (RingHom.map_det (Polynomial.C : ℚ →+* ℚ[X]) Q0).symm
  rw [hdet, gn_C]
  have h1 : Q0 = ((56448 : ℚ)⁻¹) • (Z.map (Int.cast : ℤ → ℚ)) := by
    ext c c'; simp [hZ, hQ0, div_eq_inv_mul]
  have hZd : (Z.map (Int.cast : ℤ → ℚ)).det = ((Z.det : ℤ) : ℚ) := by
    have := (RingHom.map_det (Int.castRingHom ℚ) Z).symm
    simpa using this
  rw [h1, Matrix.det_smul, Fintype.card_fin, hZd]
  have hdet0 : (Z.map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    exact hv0 (Qm1_inj S v hv)
  have hZp : ((Z.det : ℤ) : ZMod p) ≠ 0 := by
    have := (RingHom.map_det (Int.castRingHom (ZMod p)) Z).symm
    simp only [eq_intCast, RingHom.mapMatrix_apply] at this
    rw [← this]; exact hdet0
  have hnd : ¬ (p : ℤ) ∣ Z.det := by
    intro h; exact hZp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h)
  have hn1 : padicNorm p ((Z.det : ℤ) : ℚ) = 1 := (padicNorm.int_eq_one_iff _).2 hnd
  have hn0 : padicNorm p (56448 : ℚ) = 1 := by
    have := (padicNorm.nat_eq_one_iff (p := p) 56448).2 (by
      intro hd
      exact n56448 (p := p) h13 (by exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).2 hd))
    simpa using this
  have hn3 : padicNorm p ((56448 : ℚ) ^ r) = 1 := by
    have h129 : ¬ p ∣ 56448 ^ r := by
      intro hd
      have h2 := (Fact.out : p.Prime).dvd_of_dvd_pow hd
      have h3 : ((56448 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
      exact n56448 (p := p) h13 (by exact_mod_cast h3)
    have := (padicNorm.nat_eq_one_iff (p := p) (56448 ^ r)).2 h129
    simpa using this
  have hn2 : padicNorm p ((56448 : ℚ)⁻¹ ^ r) = 1 := by
    have h := padicNorm.mul (p := p) ((56448 : ℚ)⁻¹ ^ r) ((56448 : ℚ) ^ r)
    rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow, padicNorm.one, hn3, mul_one] at h
    exact h.symm
  have hn : padicNorm p ((56448 : ℚ)⁻¹ ^ r * ((Z.det : ℤ) : ℚ)) = 1 := by
    rw [padicNorm.mul, hn2, hn1]; norm_num
  rw [hn]; norm_num

theorem Atil_prim (hL : LamData Fr) (S : GKS1 p r m k) :
    gn p (Atil p (fun _ : Fin r => 1) (Matrix.of (fullEntry Fr r m)).toBlocks₁₁).det = 1 :=
  prim_det_Atil p (fun _ : Fin r => 1) _ (Mq1 p k r) (Atil_int hL S)
    (Mq1_int S.p13) (Atil_cng hL S) (Mq1_det S)

end Hprim

end CatalanCore.Arith.Hybrid.GK1
