module

public import CatalanCore.Arith.Hybrid.DefGKHprim

@[expose] public section

/-!
# GK, class 3: the vector partners `α, β` and the entry algebra

For a zone label `u` the class in `C` is `{u - 2p, u - p}` (the `2×2` block `(B1, B3)`).  With
`a₁ = N1/D`, `a₂ = N2/D` (`D = 16415622000`, `N1 = 130388940`, `N2 = 56643300`; the solution of
`ā Q_Z = ρ`) the vector `avec u` is `a₁` at `c = u - 2p`, `a₂` at `c = u - p`, `0` elsewhere.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid

section Vec3

variable {p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

lemma gnC_le_of_good0 {x : ℚ} (h : Good p ((p : ℚ) ^ 2 * x) 0) : gn p (C x) ≤ p := by
  have hlt : padicNorm p ((p : ℚ) ^ 2 * x) < 1 := (padicNorm_lt_one_iff h.1).2 h.2
  have h1 : gn p (C ((p : ℚ) ^ 2 * x)) < 1 := by rw [gn_C]; exact_mod_cast hlt
  have h2 := gn_le_inv_of_lt_one p h1
  rw [C_mul, gn_mul, gn_C] at h2
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h3 : ((padicNorm p ((p : ℚ) ^ 2) : ℚ) : ℝ) = ((p : ℝ)⁻¹) ^ 2 := by
    have h := map_pow (Rat.AbsoluteValue.padic p) (p : ℚ) 2
    simp only [Rat.AbsoluteValue.padic_eq_padicNorm] at h
    have h4 : ((padicNorm p (p : ℚ) : ℚ) : ℝ) = (p : ℝ)⁻¹ := by
      rw [padicNorm.padicNorm_p_of_prime]; push_cast; simp
    rw [h]; push_cast; rw [h4]
  rw [h3] at h2
  have hg : 0 ≤ gn p (C x) := gn_nonneg p _
  have hp0 : (0 : ℝ) < p := by linarith
  have : gn p (C x) ≤ p := by
    have h5 : ((p : ℝ)⁻¹) ^ 2 * gn p (C x) * (p : ℝ) ^ 2 ≤ (p : ℝ)⁻¹ * (p : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have h6 : ((p : ℝ)⁻¹) ^ 2 * gn p (C x) * (p : ℝ) ^ 2 = gn p (C x) := by
      field_simp
    have h7 : (p : ℝ)⁻¹ * (p : ℝ) ^ 2 = p := by field_simp
    linarith
  exact this

lemma int1_of_good0 {x : ℚ} (h : Good p ((p : ℚ) * x) 0) : Int1 p (C x) := by
  have hlt : padicNorm p ((p : ℚ) * x) < 1 := (padicNorm_lt_one_iff h.1).2 h.2
  have h1 : gn p (C ((p : ℚ) * x)) < 1 := by rw [gn_C]; exact_mod_cast hlt
  have h2 := gn_le_inv_of_lt_one p h1
  rw [C_mul, gn_mul, gn_C] at h2
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h4 : ((padicNorm p (p : ℚ) : ℚ) : ℝ) = (p : ℝ)⁻¹ := by
    rw [padicNorm.padicNorm_p_of_prime]; push_cast; simp
  rw [h4] at h2
  have hp0 : (0 : ℝ) < p := by linarith
  have hg : 0 ≤ gn p (C x) := gn_nonneg p _
  unfold Int1
  have h5 : (p : ℝ)⁻¹ * gn p (C x) * (p : ℝ) ≤ (p : ℝ)⁻¹ * (p : ℝ) :=
    mul_le_mul_of_nonneg_right h2 hp0.le
  have h6 : (p : ℝ)⁻¹ * gn p (C x) * (p : ℝ) = gn p (C x) := by field_simp
  have h7 : (p : ℝ)⁻¹ * (p : ℝ) = 1 := by field_simp
  linarith

/-- The two partner coefficients (rational lifts of the solution of `ā Q_Z = ρ`). -/
noncomputable def a1q : ℚ := 130388940 / 16415622000
noncomputable def a2q : ℚ := 56643300 / 16415622000

/-- The partner vector of the label `u`: `a₁` at `u - 2p`, `a₂` at `u - p`. -/
noncomputable def avec (p r u : ℕ) (c : Fin r) : ℚ :=
  if (c : ℕ) + 2 * p = u then a1q else if (c : ℕ) + p = u then a2q else 0

lemma good_a1 (h13 : 13 ≤ p) (hp : p ≠ 139) :
    Good p a1q ((130388940 : ZMod p) * (16415622000 : ZMod p)⁻¹) := by
  have hD : (16415622000 : ZMod p) ≠ 0 := by
    have := nz_III (p := p) h13 hp
    simpa using this
  have := (Good.ofNat (ℓ := p) 130388940).div (Good.ofNat (ℓ := p) 16415622000) hD
  simpa [a1q, div_eq_mul_inv] using this

lemma good_a2 (h13 : 13 ≤ p) (hp : p ≠ 139) :
    Good p a2q ((56643300 : ZMod p) * (16415622000 : ZMod p)⁻¹) := by
  have hD : (16415622000 : ZMod p) ≠ 0 := by
    have := nz_III (p := p) h13 hp
    simpa using this
  have := (Good.ofNat (ℓ := p) 56643300).div (Good.ofNat (ℓ := p) 16415622000) hD
  simpa [a2q, div_eq_mul_inv] using this

/-- The residue of `avec`. -/
noncomputable def ave (p r u : ℕ) (c : Fin r) : ZMod p :=
  if (c : ℕ) + 2 * p = u then (130388940 : ZMod p) * (16415622000 : ZMod p)⁻¹
  else if (c : ℕ) + p = u then (56643300 : ZMod p) * (16415622000 : ZMod p)⁻¹ else 0

lemma good_avec (h13 : 13 ≤ p) (hp : p ≠ 139) (u : ℕ) (c : Fin r) :
    Good p (avec p r u c) (ave p r u c) := by
  unfold avec ave
  split_ifs
  · exact good_a1 h13 hp
  · exact good_a2 h13 hp
  · exact Good.zero

lemma sum_avec (u : ℕ) (hu : 2 * p ≤ u) (hur : u - p < r) (hp0 : 0 < p) (f : ℕ → ℚ) :
    ∑ c : Fin r, avec p r u c * f c = a1q * f (u - 2 * p) + a2q * f (u - p) := by
  classical
  have h1 : u - 2 * p < r := by omega
  have hne : (⟨u - 2 * p, h1⟩ : Fin r) ≠ ⟨u - p, hur⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [Finset.sum_eq_add (⟨u - 2 * p, h1⟩ : Fin r) ⟨u - p, hur⟩ hne]
  · have e1 : avec p r u ⟨u - 2 * p, h1⟩ = a1q := by
      unfold avec; simp only; rw [if_pos (by omega)]
    have e2 : avec p r u ⟨u - p, hur⟩ = a2q := by
      unfold avec; simp only; rw [if_neg (by omega), if_pos (by omega)]
    rw [e1, e2]
  · intro c _ hc
    have h2 : (c : ℕ) + 2 * p ≠ u := by
      intro h; apply hc.1; apply Fin.ext; simp; omega
    have h3 : (c : ℕ) + p ≠ u := by
      intro h; apply hc.2; apply Fin.ext; simp; omega
    unfold avec; rw [if_neg h2, if_neg h3]; simp
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The Qz3 values at the zone class `u - 2p, u - p, u`. -/
lemma zone_vals {r m : ℕ} (S : GKS3 p r m k) {u : ℕ} (hu1 : r ≤ u) (hu2 : u < r + 2 * m) :
    Qz3 p k (u - 2 * p) (u - 2 * p) = 129600 ∧ Qz3 p k (u - p) (u - p) = 126684 ∧
    Qz3 p k (u - 2 * p) (u - p) = 1620 ∧ Qz3 p k (u - 2 * p) u = 1035 ∧
    Qz3 p k (u - p) u = 450 := by
  have h13 := S.p13; have hk := S.hk; have hkp := S.kp; have hr := S.hr; have hN := S.hN
  have hp0 : 0 < p := by omega
  obtain ⟨v00, v11, v22, v01, v02, v12⟩ := chain_vals (k := k) (u - 2 * p) hp0 (-360) (-342)
    (-337) (-129600) (-126684) (-126259) (Lz_B1 h13 hk (by omega) (by omega))
    (Lz_B3 h13 hk (by omega) (by omega)) (Lz_B5 h13 hk (by omega))
    (Pz_B1 h13 hk (by omega) (by omega)) (Pz_B3 h13 hk (by omega) (by omega))
    (Pz_B5 h13 hk (by omega))
  rw [show u - 2 * p + p = u - p by omega] at v11 v01 v12
  rw [show u - 2 * p + 2 * p = u by omega] at v22 v02 v12
  refine ⟨by rw [v00]; norm_num, by rw [v11]; norm_num, by rw [v01]; norm_num,
    by rw [v02]; norm_num, by rw [v12]; norm_num⟩

lemma Qz_zero_c1 {r m : ℕ} (S : GKS3 p r m k) {u : ℕ} (hu1 : r ≤ u) (hu2 : u < r + 2 * m)
    (c : ℕ) (hc : c < r) (h1 : c ≠ u - 2 * p) (h2 : c ≠ u - p) :
    Qz3 p k u c = 0 ∧ Qz3 p k (u - 2 * p) c = 0 ∧ Qz3 p k (u - p) c = 0 := by
  have h13 := S.p13; have hr := S.hr; have hN := S.hN
  refine ⟨?_, ?_, ?_⟩ <;> apply Qz3_zero <;> omega

theorem lbnd (hL : LamData Fr 1) (S : GKS3 p r m k) {u : ℕ} (hu1 : r ≤ u) (hu2 : u < r + 2 * m)
    (c : Fin r) :
    gn p (C (Fr.Mn u (c : ℕ) - ∑ c' : Fin r, avec p r u c' * Fr.Mn (c' : ℕ) (c : ℕ))) ≤ p := by
  have h13 := S.p13; have hk := S.hk; have hkp := S.kp; have hr := S.hr; have hN := S.hN
  have hp139 := S.h139
  have hp0 : 0 < p := by omega
  have hc := c.2
  rw [sum_avec u (by omega) (by omega) hp0 (fun n => Fr.Mn n (c : ℕ))]
  apply gnC_le_of_good0
  have g0 := good_Qz3 hL S (A := u) (B := (c : ℕ)) (by omega) (by omega) (fun h => by omega)
  have g1 := good_Qz3 hL S (A := u - 2 * p) (B := (c : ℕ)) (by omega) (by omega) (fun h => by omega)
  have g2 := good_Qz3 hL S (A := u - p) (B := (c : ℕ)) (by omega) (by omega) (fun h => by omega)
  have := g0.sub (((good_a1 h13 hp139).mul g1).add ((good_a2 h13 hp139).mul g2))
  refine (this.congr' (by ring)).congr ?_
  have n129600' := n129600 (p := p) h13
  have hD : (16415622000 : ZMod p) ≠ 0 := by
    have := nz_III (p := p) h13 hp139
    simpa using this
  obtain ⟨q11, q22, q12, q1u, q2u⟩ := zone_vals S hu1 hu2
  by_cases e1 : (c : ℕ) = u - 2 * p
  · rw [e1, Qz3_symm p k u, Qz3_symm p k (u - p), q1u, q11, q12]
    push_cast
    field_simp
    ring
  by_cases e2 : (c : ℕ) = u - p
  · rw [e2, Qz3_symm p k u, q2u, q12, q22]
    push_cast
    field_simp
    ring
  · obtain ⟨z0, z1, z2⟩ := Qz_zero_c1 S hu1 hu2 (c : ℕ) hc e1 e2
    rw [z0, z1, z2]; simp

end Vec3

end CatalanCore.Arith.Hybrid
