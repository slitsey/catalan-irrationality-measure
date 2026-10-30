module

public import CatalanCore.Uniform.Decay.Nodes.Limit
public import CatalanCore.Uniform.Decay.PolyFull.CapNodes
public import CatalanLambda.Cert.LogBounds

@[expose] public section
set_option Elab.async false

/-!
# A Boolean lower-bound check for node energies (lane D2)

For rational constant-density pieces the self energy is a finite sum of terms `c * Hfun s`
(`pairInteraction`, `pairEnergy`), so a certified lower bound `Inu ≤ nodeEnergy` reduces to one
rational computation: each `log |s|` is enclosed by the atanh series after the exact reduction
`|s| = u * 2 ^ k`, and each term takes the side of the enclosure that its coefficient requires.

* `energyCheck N R Q Inu` : the Boolean check;
* `energyCheck_sound` : `energyCheck N R Q Inu = true → Inu ≤ nodeEnergy (R.map ratPiece) (Q.map ratPiece)`.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open CatalanCore.Uniform.Decay.PolyFull CatalanLambda.Cert

/-! ### The energy as a finite sum of `Hfun` terms -/

/-- The four signed `Hfun` terms of one ordered pair of rational pieces `(w, lo, hi)`. -/
def pairTerms (P Q : ℚ × ℚ × ℚ) : List (ℚ × ℚ) :=
  [(P.1 * Q.1, P.2.2 - Q.2.2), (P.1 * Q.1, P.2.1 - Q.2.1), (-(P.1 * Q.1), P.2.2 - Q.2.1),
    (-(P.1 * Q.1), P.2.1 - Q.2.2)]

/-- The value `c * Hfun s` of one term. -/
noncomputable def hval (t : ℚ × ℚ) : ℝ := (t.1 : ℝ) * Hfun (t.2 : ℝ)

theorem pairInteraction_ratPiece (P Q : ℚ × ℚ × ℚ) :
    pairInteraction (ratPiece P) (ratPiece Q) = ((pairTerms P Q).map hval).sum := by
  simp only [pairInteraction, pairEnergy, ratPiece, pairTerms, hval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- All terms of the bilinear energy of two rational piece lists. -/
def energyTerms (A B : List (ℚ × ℚ × ℚ)) : List (ℚ × ℚ) :=
  A.flatMap fun P => B.flatMap fun Q => pairTerms P Q

theorem row_ratPiece (P : ℚ × ℚ × ℚ) (B : List (ℚ × ℚ × ℚ)) :
    ((B.map ratPiece).map fun Q => pairInteraction (ratPiece P) Q).sum =
      ((B.flatMap fun Q => pairTerms P Q).map hval).sum := by
  induction B with
  | nil => simp
  | cons Q B ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append,
      ih, pairInteraction_ratPiece]

theorem mutE_ratPiece (A B : List (ℚ × ℚ × ℚ)) :
    mutE (A.map ratPiece) (B.map ratPiece) = ((energyTerms A B).map hval).sum := by
  induction A with
  | nil => simp [mutE, energyTerms]
  | cons P A ih =>
    rw [List.map_cons, mutE_cons_left, ih, row_ratPiece]
    simp only [energyTerms, List.flatMap_cons, List.map_append, List.sum_append]

/-! ### Certified enclosures of `log` -/

/-- Exact reduction `t = u * 2 ^ k` with `u` moved towards `[1/2, 2]` (fuel `f`). -/
def redE : ℕ → ℚ → ℤ × ℚ
  | 0, t => (0, t)
  | f + 1, t =>
    if 2 < t then Prod.map (· + 1) id (redE f (t / 2))
    else if t < 1 / 2 then Prod.map (· - 1) id (redE f (t * 2)) else (0, t)

theorem redE_spec : ∀ (f : ℕ) (t : ℚ), (redE f t).2 * (2 : ℚ) ^ (redE f t).1 = t
  | 0, t => by simp [redE]
  | f + 1, t => by
    unfold redE
    split_ifs with h1 h2
    · have ih := redE_spec f (t / 2)
      simp only [Prod.map_fst, Prod.map_snd, id]
      rw [zpow_add_one₀ (by norm_num), ← mul_assoc, ih]
      ring
    · have ih := redE_spec f (t * 2)
      simp only [Prod.map_fst, Prod.map_snd, id]
      rw [zpow_sub_one₀ (by norm_num), ← mul_assoc, ih]
      ring
    · simp

/-- Lower and upper bounds of `log u` for `u > 0` (atanh series, `N` terms). -/
def uLo (N : ℕ) (u : ℚ) : ℚ :=
  if 1 ≤ u then atS ((u - 1) / (u + 1)) N
  else -(atS ((1 - u) / (1 + u)) N + atT ((1 - u) / (1 + u)) N)

def uHi (N : ℕ) (u : ℚ) : ℚ :=
  if 1 ≤ u then atS ((u - 1) / (u + 1)) N + atT ((u - 1) / (u + 1)) N
  else -atS ((1 - u) / (1 + u)) N

/-- The atanh bounds in the form `log ((1 + y) / (1 - y))`. -/
theorem log_ratio_bounds {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) (N : ℕ) :
    atS y N ≤ Real.log ((1 + y) / (1 - y)) ∧
      Real.log ((1 + y) / (1 - y)) ≤ atS y N + atT y N := by
  rw [Real.log_div (by linarith) (by linarith)]
  exact log_atanh_bounds h0 h1 N

theorem uLo_le {u : ℚ} (hu : 0 < u) (N : ℕ) : (uLo N u : ℝ) ≤ Real.log (u : ℝ) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  unfold uLo
  split_ifs with h
  · have h' : (1 : ℝ) ≤ u := by exact_mod_cast h
    have hb := (log_ratio_bounds (y := ((u : ℝ) - 1) / ((u : ℝ) + 1))
      (div_nonneg (by linarith) (by linarith)) ((div_lt_one (by linarith)).2 (by linarith)) N).1
    have e : (1 + ((u : ℝ) - 1) / ((u : ℝ) + 1)) / (1 - ((u : ℝ) - 1) / ((u : ℝ) + 1)) = u := by
      field_simp; ring
    rw [e] at hb
    rw [atS_cast]; push_cast; exact hb
  · have h' : (u : ℝ) < 1 := by exact_mod_cast not_le.1 h
    have hb := (log_ratio_bounds (y := (1 - (u : ℝ)) / (1 + (u : ℝ)))
      (div_nonneg (by linarith) (by linarith)) ((div_lt_one (by linarith)).2 (by linarith)) N).2
    have hu0 : (u : ℝ) ≠ 0 := hu'.ne'
    have e : (1 + (1 - (u : ℝ)) / (1 + (u : ℝ))) / (1 - (1 - (u : ℝ)) / (1 + (u : ℝ))) =
        (u : ℝ)⁻¹ := by
      field_simp
      ring_nf
      exact mul_inv_cancel₀ hu0
    rw [e, Real.log_inv] at hb
    push_cast [atS_cast, atT_cast]
    linarith

theorem le_uHi {u : ℚ} (hu : 0 < u) (N : ℕ) : Real.log (u : ℝ) ≤ (uHi N u : ℝ) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  unfold uHi
  split_ifs with h
  · have h' : (1 : ℝ) ≤ u := by exact_mod_cast h
    have hb := (log_ratio_bounds (y := ((u : ℝ) - 1) / ((u : ℝ) + 1))
      (div_nonneg (by linarith) (by linarith)) ((div_lt_one (by linarith)).2 (by linarith)) N).2
    have e : (1 + ((u : ℝ) - 1) / ((u : ℝ) + 1)) / (1 - ((u : ℝ) - 1) / ((u : ℝ) + 1)) = u := by
      field_simp; ring
    rw [e] at hb
    push_cast [atS_cast, atT_cast]; exact hb
  · have h' : (u : ℝ) < 1 := by exact_mod_cast not_le.1 h
    have hb := (log_ratio_bounds (y := (1 - (u : ℝ)) / (1 + (u : ℝ)))
      (div_nonneg (by linarith) (by linarith)) ((div_lt_one (by linarith)).2 (by linarith)) N).1
    have hu0 : (u : ℝ) ≠ 0 := hu'.ne'
    have e : (1 + (1 - (u : ℝ)) / (1 + (u : ℝ))) / (1 - (1 - (u : ℝ)) / (1 + (u : ℝ))) =
        (u : ℝ)⁻¹ := by
      field_simp
      ring_nf
      exact mul_inv_cancel₀ hu0
    rw [e, Real.log_inv] at hb
    push_cast [atS_cast]
    linarith

/-- `log 2` from the atanh series at `1/3`. -/
def l2Lo (N : ℕ) : ℚ := atS (1 / 3 : ℚ) N
def l2Hi (N : ℕ) : ℚ := atS (1 / 3 : ℚ) N + atT (1 / 3 : ℚ) N

theorem log2_enc (N : ℕ) : (l2Lo N : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (l2Hi N : ℝ) := by
  have hb := log_ratio_bounds (y := (1 : ℝ) / 3) (by norm_num) (by norm_num) N
  have e : (1 + (1 : ℝ) / 3) / (1 - 1 / 3) = 2 := by norm_num
  rw [e] at hb
  unfold l2Lo l2Hi
  push_cast [atS_cast, atT_cast]
  exact hb

/-- Enclosure of `log t` for `t > 0`: reduction `t = u * 2 ^ k`, then the two series. -/
def logLoQ (N : ℕ) (t : ℚ) : ℚ :=
  let r := redE 64 t
  r.1 * (if 0 ≤ r.1 then l2Lo N else l2Hi N) + uLo N r.2

def logHiQ (N : ℕ) (t : ℚ) : ℚ :=
  let r := redE 64 t
  r.1 * (if 0 ≤ r.1 then l2Hi N else l2Lo N) + uHi N r.2

theorem log_redE {t : ℚ} (ht : 0 < t) :
    0 < (redE 64 t).2 ∧
      Real.log (t : ℝ) = (redE 64 t).1 * Real.log 2 + Real.log ((redE 64 t).2 : ℝ) := by
  have hs := redE_spec 64 t
  have hp : (0 : ℚ) < (2 : ℚ) ^ (redE 64 t).1 := zpow_pos (by norm_num) _
  have hu : 0 < (redE 64 t).2 := by
    by_contra h
    push_neg at h
    have : (redE 64 t).2 * (2 : ℚ) ^ (redE 64 t).1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hp.le
    linarith
  refine ⟨hu, ?_⟩
  have hu' : (0 : ℝ) < ((redE 64 t).2 : ℝ) := by exact_mod_cast hu
  have hcast : (t : ℝ) = ((redE 64 t).2 : ℝ) * (2 : ℝ) ^ (redE 64 t).1 := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) hs
    simp only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat] at h
    exact h.symm
  rw [hcast, Real.log_mul hu'.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  ring

theorem logLoQ_le {t : ℚ} (ht : 0 < t) (N : ℕ) : (logLoQ N t : ℝ) ≤ Real.log (t : ℝ) := by
  obtain ⟨hu, he⟩ := log_redE ht
  obtain ⟨l1, l2⟩ := log2_enc N
  have hU := uLo_le hu N
  unfold logLoQ
  simp only
  rw [he]
  push_cast
  split_ifs with hk
  · have hk' : (0 : ℝ) ≤ ((redE 64 t).1 : ℝ) := by exact_mod_cast hk
    nlinarith [mul_le_mul_of_nonneg_left l1 hk']
  · have hk' : ((redE 64 t).1 : ℝ) < 0 := by exact_mod_cast not_le.1 hk
    nlinarith [mul_le_mul_of_nonpos_left l2 hk'.le]

theorem le_logHiQ {t : ℚ} (ht : 0 < t) (N : ℕ) : Real.log (t : ℝ) ≤ (logHiQ N t : ℝ) := by
  obtain ⟨hu, he⟩ := log_redE ht
  obtain ⟨l1, l2⟩ := log2_enc N
  have hU := le_uHi hu N
  unfold logHiQ
  simp only
  rw [he]
  push_cast
  split_ifs with hk
  · have hk' : (0 : ℝ) ≤ ((redE 64 t).1 : ℝ) := by exact_mod_cast hk
    nlinarith [mul_le_mul_of_nonneg_left l2 hk']
  · have hk' : ((redE 64 t).1 : ℝ) < 0 := by exact_mod_cast not_le.1 hk
    nlinarith [mul_le_mul_of_nonpos_left l1 hk'.le]

/-! ### Termwise lower bounds and the check -/

/-- Certified lower bound of `c * Hfun s`. -/
def lowTerm (N : ℕ) (t : ℚ × ℚ) : ℚ :=
  if t.2 = 0 then 0 else
    let A := t.1 * t.2 ^ 2 / 2
    (if 0 ≤ A then A * logLoQ N |t.2| else A * logHiQ N |t.2|) - 3 / 4 * t.1 * t.2 ^ 2

theorem lowTerm_le (N : ℕ) (t : ℚ × ℚ) : (lowTerm N t : ℝ) ≤ hval t := by
  obtain ⟨c, s⟩ := t
  unfold lowTerm hval Hfun
  simp only
  split_ifs with h0 hA
  · subst h0; simp
  · have hs : (0 : ℚ) < |s| := abs_pos.2 h0
    have hlo := logLoQ_le hs N
    have hA' : (0 : ℝ) ≤ (c : ℝ) * (s : ℝ) ^ 2 / 2 := by exact_mod_cast hA
    rw [Rat.cast_abs, Real.log_abs] at hlo
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlo hA']
  · have hs : (0 : ℚ) < |s| := abs_pos.2 h0
    have hhi := le_logHiQ hs N
    have hA' : (c : ℝ) * (s : ℝ) ^ 2 / 2 < 0 := by exact_mod_cast not_le.1 hA
    rw [Rat.cast_abs, Real.log_abs] at hhi
    push_cast
    nlinarith [mul_le_mul_of_nonpos_left hhi hA'.le]

theorem sum_lowTerm_le (N : ℕ) : ∀ l : List (ℚ × ℚ),
    (((l.map (lowTerm N)).sum : ℚ) : ℝ) ≤ (l.map hval).sum
  | [] => by simp
  | t :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [Rat.cast_add]
    exact add_le_add (lowTerm_le N t) (sum_lowTerm_le N l)

/-- Certified rational lower bound of `nodeEnergy` for rational piece lists. -/
def energyLowQ (N : ℕ) (R Q : List (ℚ × ℚ × ℚ)) : ℚ :=
  (((energyTerms R R).map (lowTerm N)).sum + ((energyTerms Q Q).map (lowTerm N)).sum) / 2

/-- **The Boolean check.** -/
def energyCheck (N : ℕ) (R Q : List (ℚ × ℚ × ℚ)) (Inu : ℚ) : Bool :=
  decide (Inu ≤ energyLowQ N R Q)

theorem energyLowQ_le (N : ℕ) (R Q : List (ℚ × ℚ × ℚ)) :
    (energyLowQ N R Q : ℝ) ≤ nodeEnergy (R.map ratPiece) (Q.map ratPiece) := by
  unfold energyLowQ nodeEnergy selfEnergy
  rw [mutE_ratPiece, mutE_ratPiece]
  push_cast
  have h1 := sum_lowTerm_le N (energyTerms R R)
  have h2 := sum_lowTerm_le N (energyTerms Q Q)
  push_cast at h1 h2
  linarith

/-- **Soundness**: a passing check certifies `Inu ≤ nodeEnergy`. -/
theorem energyCheck_sound {N : ℕ} {R Q : List (ℚ × ℚ × ℚ)} {Inu : ℚ}
    (h : energyCheck N R Q Inu = true) :
    (Inu : ℝ) ≤ nodeEnergy (R.map ratPiece) (Q.map ratPiece) := by
  have h' : Inu ≤ energyLowQ N R Q := by simpa [energyCheck] using h
  have hc : (Inu : ℝ) ≤ (energyLowQ N R Q : ℝ) := by exact_mod_cast h'
  exact hc.trans (energyLowQ_le N R Q)

/-- The `BlockGeom` form: for a geometry whose row and column pieces are rational lists. -/
theorem inu_le_nodeEnergy_of_check {G : BlockGeom} {RP CP : List (ℚ × ℚ × ℚ)} {N : ℕ} {Inu : ℚ}
    (hR : G.rowPieces = RP.map ratPiece) (hC : G.colPieces = CP.map ratPiece)
    (h : energyCheck N RP CP Inu = true) : (Inu : ℝ) ≤ G.nodeEnergy := by
  unfold BlockGeom.nodeEnergy
  rw [hR, hC]
  exact energyCheck_sound h


/-! Regression: the certified `Inu` of the thirds and chi3 tables on their actual node pieces. -/
example : energyCheck 30 [(1, 0, 1), (1 / 2, 1, 13 / 10)] [(1, 0, 1), (1 / 2, 1, 13 / 10)]
    (867481404213 / 500000000000) = true := by decide +kernel

example : energyCheck 30 [(1, 0, 1), (1 / 2, 1, 3 / 2)] [(1, 0, 1), (1 / 2, 1, 3 / 2)]
    (28816875853 / 15625000000) = true := by decide +kernel

end CatalanCore.Uniform.Decay.Nodes
