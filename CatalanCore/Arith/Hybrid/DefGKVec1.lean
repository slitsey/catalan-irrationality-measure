module

public import CatalanCore.Arith.Hybrid.DefGKHprim1
public import CatalanCore.Arith.Hybrid.DefGKVec3

@[expose] public section

/-!
# GK, class 1: the vector partners `α, β` and the entry algebra

For a zone label `u` the class in `C` is `{u - 2p, u - p}` (the `2×2` block `(B1, B3)`).  With
`a₁ = N1/D`, `a₂ = N2/D` (`D = 16415622000`, `N1 = 130388940`, `N2 = 56643300`; the solution of
`ā Q_Z = ρ`) the vector `avec u` is `a₁` at `c = u - 2p`, `a₂` at `c = u - p`, `0` elsewhere.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid.GK1

open CatalanCore.Arith.Hybrid

section Vec3

variable {o p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

/-- The two partner coefficients (the solution of `ā Q_Z = ρ`, `Z` of type `(B0, B2)`). -/
noncomputable def a1q : ℚ := 137 / 84
noncomputable def a2q : ℚ := 17 / 28

/-- The partner vector of the label `u`: `a₁` at `u - 2p`, `a₂` at `u - p`. -/
noncomputable def avec (p r u : ℕ) (c : Fin r) : ℚ :=
  if (c : ℕ) + 2 * p = u then a1q else if (c : ℕ) + p = u then a2q else 0

lemma good_a1 (h13 : 13 ≤ p) (hp : p ≠ 1009) :
    Good p a1q ((137 : ZMod p) * (84 : ZMod p)⁻¹) := by
  have := (Good.ofNat (ℓ := p) 137).div (Good.ofNat (ℓ := p) 84) (n84 (p := p) h13)
  simpa [a1q, div_eq_mul_inv] using this

lemma good_a2 (h13 : 13 ≤ p) (hp : p ≠ 1009) :
    Good p a2q ((17 : ZMod p) * (28 : ZMod p)⁻¹) := by
  have := (Good.ofNat (ℓ := p) 17).div (Good.ofNat (ℓ := p) 28) (n28 (p := p) h13)
  simpa [a2q, div_eq_mul_inv] using this

/-- The residue of `avec`. -/
noncomputable def ave (p r u : ℕ) (c : Fin r) : ZMod p :=
  if (c : ℕ) + 2 * p = u then (137 : ZMod p) * (84 : ZMod p)⁻¹
  else if (c : ℕ) + p = u then (17 : ZMod p) * (28 : ZMod p)⁻¹ else 0

lemma good_avec (h13 : 13 ≤ p) (hp : p ≠ 1009) (u : ℕ) (c : Fin r) :
    Good p (avec p r u c) (ave p r u c) := by
  unfold avec ave
  split_ifs
  · exact good_a1 h13 hp
  · exact good_a2 h13 hp
  · exact Good.zero

lemma sum_avec (u : ℕ) (hu : 2 * p ≤ u) (hur : u - p < r) (hp0 : 0 < p) (f : ℕ → ℚ) :
    ∑ c : Fin r, avec p r u c * f c = a1q * f (u - 2 * p) + a2q * f (u - p) :=
  GKGen.sum_avecG a1q a2q u hu hur hp0 f

/-- The Qz1 values at the zone class `u - 2p, u - p, u`. -/
lemma zone_vals {r m : ℕ} (S : GKS1 o p r m k) {u : ℕ} (hu1 : r ≤ u) (hu2 : u < r + 2 * m) :
    Qz1 p k (u - 2 * p) (u - 2 * p) = 0 ∧ Qz1 p k (u - p) (u - p) = 2744 ∧
    Qz1 p k (u - 2 * p) (u - p) = -1176 ∧ Qz1 p k (u - 2 * p) u = -714 ∧
    Qz1 p k (u - p) u = -252 := by
  have h13 := S.p13; have hk := S.hk; have hkp := S.kp; have hr := S.hr; have hN := S.hN; have hkk := S.hk
  have hp0 : 0 < p := by omega
  obtain ⟨v00, v11, v22, v01, v02, v12⟩ := chain1_vals (k := k) (u - 2 * p) hp0 0 (-28)
    (-34) 0 (-1372) (-1507) (Lz_B0 h13 hk (by omega)) (Lz_B2 h13 hk (by omega) (by omega))
    (Lz_B4 h13 hk (by omega)) (Pz_B0 h13 hk (by omega))
    (Pz_B2 h13 hk (by omega) (by omega)) (Pz_B4 h13 hk (by omega))
  rw [show u - 2 * p + p = u - p by omega] at v11 v01 v12
  rw [show u - 2 * p + 2 * p = u by omega] at v22 v02 v12
  refine ⟨by rw [v00]; norm_num, by rw [v11]; norm_num, by rw [v01]; norm_num,
    by rw [v02]; norm_num, by rw [v12]; norm_num⟩

lemma Qz_zero_c1 {r m : ℕ} (S : GKS1 o p r m k) {u : ℕ} (hu1 : r ≤ u) (hu2 : u < r + 2 * m)
    (c : ℕ) (hc : c < r) (h1 : c ≠ u - 2 * p) (h2 : c ≠ u - p) :
    Qz1 p k u c = 0 ∧ Qz1 p k (u - 2 * p) c = 0 ∧ Qz1 p k (u - p) c = 0 := by
  have h13 := S.p13; have hk := S.hk; have hkp := S.kp; have hr := S.hr; have hN := S.hN; have hkk := S.hk
  refine ⟨?_, ?_, ?_⟩ <;> apply Qz1_zero <;> omega

theorem lbnd (hL : LamData Fr o) (S : GKS1 o p r m k) {u : ℕ} (hu1 : r ≤ u) (hu2 : u < r + 2 * m)
    (c : Fin r) :
    gn p (C (Fr.Mn u (c : ℕ) - ∑ c' : Fin r, avec p r u c' * Fr.Mn (c' : ℕ) (c : ℕ))) ≤ p := by
  have h13 := S.p13; have hk := S.hk; have hkp := S.kp; have hr := S.hr; have hN := S.hN; have hkk := S.hk
  have hp139 := S.h1009
  have hp0 : 0 < p := by omega
  have hc := c.2
  rw [sum_avec u (by omega) (by omega) hp0 (fun n => Fr.Mn n (c : ℕ))]
  apply gnC_le_of_good0
  have g0 := good_Qz1 hL S (A := u) (B := (c : ℕ)) (by omega) (by omega) (fun h => by omega)
  have g1 := good_Qz1 hL S (A := u - 2 * p) (B := (c : ℕ)) (by omega) (by omega) (fun h => by omega)
  have g2 := good_Qz1 hL S (A := u - p) (B := (c : ℕ)) (by omega) (by omega) (fun h => by omega)
  have := g0.sub (((good_a1 h13 hp139).mul g1).add ((good_a2 h13 hp139).mul g2))
  refine (this.congr' (by ring)).congr ?_
  have n56448' := n56448 (p := p) h13
  have n84' := n84 (p := p) h13
  have n28' := n28 (p := p) h13
  obtain ⟨q11, q22, q12, q1u, q2u⟩ := zone_vals S hu1 hu2
  by_cases e1 : (c : ℕ) = u - 2 * p
  · rw [e1, Qz1_symm p k u, Qz1_symm p k (u - p), q1u, q11, q12]
    push_cast
    field_simp
    ring
  by_cases e2 : (c : ℕ) = u - p
  · rw [e2, Qz1_symm p k u, q2u, q12, q22]
    push_cast
    field_simp
    ring
  · obtain ⟨z0, z1, z2⟩ := Qz_zero_c1 S hu1 hu2 (c : ℕ) hc e1 e2
    rw [z0, z1, z2]; simp

end Vec3

end CatalanCore.Arith.Hybrid.GK1
