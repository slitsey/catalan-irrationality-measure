module

public import CatalanCore.Cert.SigmaHybS.IChunk0
public import CatalanCore.Cert.SigmaHybS.IChunk1
public import CatalanCore.Cert.SigmaHybS.IChunk2
public import CatalanCore.Cert.SigmaHybS.IChunk3
public import CatalanCore.Cert.SigmaHybS.IChunk4
public import CatalanCore.Cert.SigmaHybS.IChunk5
public import CatalanCore.Cert.SigmaHybS.IChunk6
public import CatalanCore.Cert.SigmaHybS.IChunk7
public import CatalanCore.Cert.SigmaHybS.IChunk8
public import CatalanCore.Cert.SigmaHybS.IChunk9
public import CatalanCore.Cert.SigmaHybS.IChunk10
public import CatalanCore.Cert.SigmaHybS.IChunk11
public import CatalanCore.Cert.SigmaHybS.IChunk12
public import CatalanCore.Cert.SigmaHybS.IChunk13
public import CatalanCore.Cert.SigmaHybS.IChunk14
public import CatalanCore.Cert.SigmaHybS.IChunk15
public import CatalanCore.Cert.SigmaHybS.IChunk16
public import CatalanCore.Cert.SigmaHybS.IChunk17
public import CatalanCore.Cert.SigmaHybS.IChunk18
public import CatalanCore.Cert.SigmaHybS.IChunk19
public import CatalanCore.Cert.SigmaHybS.IChunk20
public import CatalanCore.Cert.SigmaHybS.IChunk21
public import CatalanCore.Cert.SigmaHybS.IChunk22
public import CatalanCore.Cert.SigmaHybS.IChunk23
public import CatalanCore.Cert.SigmaHybS.IChunk24
public import CatalanCore.Cert.SigmaHybS.IChunk25
public import CatalanCore.Cert.SigmaHybS.IChunk26
public import CatalanCore.Cert.SigmaHybS.IChunk27
public import CatalanCore.Cert.SigmaHybS.IChunk28
public import CatalanCore.Cert.SigmaHybS.IChunk29
public import CatalanCore.Cert.SigmaHybS.IChunk30
public import CatalanCore.Cert.SigmaHybS.IChunk31
public import CatalanCore.Cert.SigmaHybS.IChunk32
public import CatalanCore.Cert.SigmaHybS.IChunk33
public import CatalanCore.Cert.SigmaHybS.IChunk34
public import CatalanCore.Cert.SigmaHybS.IChunk35
public import CatalanCore.Cert.SigmaHybS.IChunk36
public import CatalanCore.Cert.SigmaHybS.IChunk37
public import CatalanCore.Cert.SigmaHybS.IChunk38
public import CatalanCore.Cert.SigmaHybS.IChunk39
public import CatalanCore.Cert.SigmaHybS.IChunk40
public import CatalanCore.Cert.SigmaHybS.IChunk41
public import CatalanCore.Cert.SigmaHybS.IChunk42
public import CatalanCore.Cert.SigmaHybS.IChunk43
public import CatalanCore.Cert.SigmaHybS.IChunk44
public import CatalanCore.Cert.SigmaHybS.IChunk45
public import CatalanCore.Cert.SigmaHybS.IChunk46
public import CatalanCore.Cert.SigmaHybS.IChunk47
public import CatalanCore.Cert.SigmaHybS.IChunk48
public import CatalanCore.Cert.SigmaHybS.IChunk49
public import CatalanCore.Cert.SigmaHybS.IBoundDef
public import CatalanCore.Cert.SigmaHybS.Bridge

@[expose] public section

/-!
# `I_ρ(σ_h) ≤ IBOUNDS` from the scaled-integer lower log bounds (`logLoS`), triangular row sums

`Irho (1/4096) cH wtH = (64/81) Irho (1/4096) cH mH` and `Irho cH mH ≤ ∑ₖ∑ₗ Jr pₖ pₗ = -iTri/2^129`;
`iTri` is the triangular sum (`Jr` is symmetric), cut into `NCH` chunks computed by the kernel (`IChunk*`).
-/

open Real

namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000

lemma rowsSum_add (a n m : ℕ) : rowsSum a (n + m) = rowsSum a n + rowsSum (a + n) m := by
  unfold rowsSum
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  congr 2
  funext i
  simp [Function.comp, add_assoc]

theorem chunk_ok : ∀ k < NCH, rowsSum (chunkStart k) (chunkLen k) = chunkVal k := by
  intro k hk
  unfold NCH at hk
  interval_cases k
  exacts [iChunk_0, iChunk_1, iChunk_2, iChunk_3, iChunk_4, iChunk_5, iChunk_6, iChunk_7, iChunk_8, iChunk_9, iChunk_10, iChunk_11, iChunk_12, iChunk_13, iChunk_14, iChunk_15, iChunk_16, iChunk_17, iChunk_18, iChunk_19, iChunk_20, iChunk_21, iChunk_22, iChunk_23, iChunk_24, iChunk_25, iChunk_26, iChunk_27, iChunk_28, iChunk_29, iChunk_30, iChunk_31, iChunk_32, iChunk_33, iChunk_34, iChunk_35, iChunk_36, iChunk_37, iChunk_38, iChunk_39, iChunk_40, iChunk_41, iChunk_42, iChunk_43, iChunk_44, iChunk_45, iChunk_46, iChunk_47, iChunk_48, iChunk_49]

lemma rows_prefix : ∀ k, k ≤ NCH → rowsSum 0 (chunkStart k) = cumVal k := by
  intro k
  induction k with
  | zero => intro _; simp [rowsSum, chunkStart, cumVal]
  | succ k ih =>
    intro hk
    have h := chunk_ok k (by omega)
    show rowsSum 0 (chunkStart k + chunkLen k) = cumVal k + chunkVal k
    rw [rowsSum_add, ih (by omega), zero_add, h]

theorem chunkStart_NCH : chunkStart NCH = 1650 := by decide +kernel
theorem cumVal_NCH : cumVal NCH = ITOT := by decide +kernel

theorem rows_total : rowsSum 0 1650 = ITOT := by
  have h := rows_prefix NCH le_rfl
  rw [chunkStart_NCH, cumVal_NCH] at h
  exact h

def iTri : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * ((p.2.2 : ℤ) * CatalanLambda.Cert.logLoS (qII p p) + 2 * iRow p ps) + iTri ps

lemma iTri_eq (L : List Pt) : iTri L = ((List.range L.length).map (rowT L)).sum := by
  induction L with
  | nil => simp [iTri]
  | cons p ps ih =>
    have h0 : rowT (p :: ps) 0 = (p.2.2 : ℤ) * ((p.2.2 : ℤ) * CatalanLambda.Cert.logLoS (qII p p) + 2 * iRow p ps) := by
      simp [rowT]
    have h1 : ∀ r, rowT (p :: ps) (r + 1) = rowT ps r := by
      intro r; simp [rowT]
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have e : (rowT (p :: ps) ∘ Nat.succ) = rowT ps := by
      funext r; simp [Function.comp, h1]
    rw [e, h0, ← ih]
    simp only [iTri]

theorem iTri_sigH : iTri sigH = ITOT := by
  rw [iTri_eq, sigH_len]
  have : ((List.range 1650).map (rowT sigH)).sum = rowsSum 0 1650 := by
    unfold rowsSum; simp
  rw [this, rows_total]

noncomputable def Jr (p q : Pt) : ℝ :=
  -(1 / 2) * ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) * ((CatalanLambda.Cert.logLoS (qII p q) : ℝ) / 2 ^ 64)

lemma qII_symm (p q : Pt) : qII p q = qII q p := by
  unfold qII
  rw [← Int.natAbs_neg (p.1 - q.1), ← Int.natAbs_neg (p.2.1 - q.2.1), neg_sub, neg_sub]

lemma Jr_symm (p q : Pt) : Jr p q = Jr q p := by
  unfold Jr; rw [qII_symm]; ring

lemma row_eq (p : Pt) : ∀ l : List Pt,
    (l.map (Jr p)).sum = -((p.2.2 : ℝ) * (iRow p l : ℝ)) / 2 ^ 129 := by
  intro l
  induction l with
  | nil => simp [iRow]
  | cons q qs ih =>
    simp only [List.map_cons, List.sum_cons, ih, iRow, Jr]
    push_cast
    ring

theorem S_eq : ∀ L : List Pt, (L.map (fun p => (L.map (Jr p)).sum)).sum = -(iTri L : ℝ) / 2 ^ 129 := by
  intro L
  induction L with
  | nil => simp [iTri]
  | cons p ps ih =>
    have e1 : ((p :: ps).map (fun p' => ((p :: ps).map (Jr p')).sum)).sum
        = ((p :: ps).map (Jr p)).sum + (ps.map (fun p' => Jr p' p + (ps.map (Jr p')).sum)).sum := by
      simp only [List.map_cons, List.sum_cons]
    have e2 : (ps.map (fun p' => Jr p' p + (ps.map (Jr p')).sum)).sum
        = (ps.map (Jr p)).sum + (ps.map (fun p' => (ps.map (Jr p')).sum)).sum := by
      rw [List.sum_map_add]
      congr 1
      exact congrArg List.sum (List.map_congr_left (fun q _ => Jr_symm q p))
    rw [e1, e2, ih]
    simp only [List.map_cons, List.sum_cons, row_eq, iTri]
    have hJ : Jr p p = -(((p.2.2 : ℝ)) * ((p.2.2 : ℝ) * (CatalanLambda.Cert.logLoS (qII p p) : ℝ))) / 2 ^ 129 := by
      unfold Jr; ring
    rw [hJ]
    push_cast
    ring

noncomputable def cpt (p : Pt) : ℂ := ⟨(p.1 : ℝ) / 2 ^ 40, (p.2.1 : ℝ) / 2 ^ 40⟩

lemma qII_cast (p q : Pt) :
    (qII p q : ℝ) = ((p.1 : ℝ) - q.1) ^ 2 + ((p.2.1 : ℝ) - q.2.1) ^ 2 + 2 ^ 56 := by
  unfold qII
  push_cast [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  ring

lemma pair_le (p q : Pt) :
    ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) * CatalanLambda.Decay.krho (1 / 4096 : ℝ) (cpt p) (cpt q)
      ≤ Jr p q := by
  unfold CatalanLambda.Decay.krho cpt
  rw [norm_sq_mk]
  have hN : 0 < qII p q := by unfold qII; positivity
  have hq : ((p.1 : ℝ) / 2 ^ 40 - (q.1 : ℝ) / 2 ^ 40) ^ 2 + ((p.2.1 : ℝ) / 2 ^ 40 - (q.2.1 : ℝ) / 2 ^ 40) ^ 2
      + (1 / 4096 : ℝ) ^ 2 = (qII p q : ℝ) / 2 ^ 80 := by
    rw [qII_cast]; field_simp; ring
  rw [hq]
  have h1 := CatalanLambda.Cert.logLoS_spec hN
  have hn : (0 : ℝ) ≤ ((p.2.2 : ℝ) / 2 ^ 32) * ((q.2.2 : ℝ) / 2 ^ 32) := by positivity
  have h2 : -(1 / 2 : ℝ) * Real.log ((qII p q : ℝ) / 2 ^ 80) ≤ -(1 / 2) * ((CatalanLambda.Cert.logLoS (qII p q) : ℝ) / 2 ^ 64) := by
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn
  unfold Jr
  linarith

theorem Im_le : CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH mH ≤ -(ITOT : ℝ) / 2 ^ 129 := by
  have h1 : CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH mH ≤ ∑ k : Fin 1650, ∑ l : Fin 1650, Jr (ptAt k) (ptAt l) := by
    unfold CatalanLambda.Decay.Irho
    refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
    have := pair_le (ptAt k) (ptAt l)
    unfold mH cH
    exact this
  have h2 : ∑ k : Fin 1650, ∑ l : Fin 1650, Jr (ptAt k) (ptAt l) = -(iTri sigH : ℝ) / 2 ^ 129 := by
    have e1 : ∀ k : Fin 1650, ∑ l : Fin 1650, Jr (ptAt k) (ptAt l) = (sigH.map (Jr (ptAt k))).sum :=
      fun k => sum_sigma (Jr (ptAt k))
    simp_rw [e1]
    rw [sum_sigma (fun p => (sigH.map (Jr p)).sum), S_eq]
  rw [iTri_sigH] at h2
  exact h1.trans h2.le

theorem Irho_wt : CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH wtH
    = (64 / 81) * CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH mH := by
  unfold CatalanLambda.Decay.Irho
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold wtH
  ring

theorem I_ok_S : CatalanLambda.Decay.Irho (1 / 4096 : ℝ) cH wtH ≤ (IBOUNDS : ℝ) := by
  rw [Irho_wt]
  have h := Im_le
  have hX : (64 / 81 : ℝ) * (-(ITOT : ℝ) / 2 ^ 129) ≤ (IBOUNDS : ℝ) := by
    unfold ITOT IBOUNDS
    push_cast
    norm_num
  have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 64 / 81)
  exact this.trans hX

end CatalanCore.Cert.SigmaHybS
