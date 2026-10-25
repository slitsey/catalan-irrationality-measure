module

public import CatalanCore.Cert.SigmaThirds.IChunk0
public import CatalanCore.Cert.SigmaThirds.IChunk1
public import CatalanCore.Cert.SigmaThirds.IChunk2
public import CatalanCore.Cert.SigmaThirds.IChunk3
public import CatalanCore.Cert.SigmaThirds.IChunk4
public import CatalanCore.Cert.SigmaThirds.IChunk5
public import CatalanCore.Cert.SigmaThirds.IChunk6
public import CatalanCore.Cert.SigmaThirds.IChunk7
public import CatalanCore.Cert.SigmaThirds.IChunk8
public import CatalanCore.Cert.SigmaThirds.IChunk9
public import CatalanCore.Cert.SigmaThirds.IChunk10
public import CatalanCore.Cert.SigmaThirds.IChunk11
public import CatalanCore.Cert.SigmaThirds.IChunk12
public import CatalanCore.Cert.SigmaThirds.IChunk13
public import CatalanCore.Cert.SigmaThirds.IChunk14
public import CatalanCore.Cert.SigmaThirds.IChunk15
public import CatalanCore.Cert.SigmaThirds.IChunk16
public import CatalanCore.Cert.SigmaThirds.IChunk17
public import CatalanCore.Cert.SigmaThirds.IChunk18
public import CatalanCore.Cert.SigmaThirds.IChunk19
public import CatalanCore.Cert.SigmaThirds.IChunk20
public import CatalanCore.Cert.SigmaThirds.IChunk21
public import CatalanCore.Cert.SigmaThirds.IChunk22
public import CatalanCore.Cert.SigmaThirds.IChunk23
public import CatalanCore.Cert.SigmaThirds.IChunk24
public import CatalanCore.Cert.SigmaThirds.IChunk25
public import CatalanCore.Cert.SigmaThirds.IChunk26
public import CatalanCore.Cert.SigmaThirds.IChunk27
public import CatalanCore.Cert.SigmaThirds.IChunk28
public import CatalanCore.Cert.SigmaThirds.IChunk29
public import CatalanCore.Cert.SigmaThirds.IChunk30
public import CatalanCore.Cert.SigmaThirds.IChunk31
public import CatalanCore.Cert.SigmaThirds.IChunk32
public import CatalanCore.Cert.SigmaThirds.IChunk33
public import CatalanCore.Cert.SigmaThirds.IChunk34
public import CatalanCore.Cert.SigmaThirds.IChunk35
public import CatalanCore.Cert.SigmaThirds.IChunk36
public import CatalanCore.Cert.SigmaThirds.IChunk37
public import CatalanCore.Cert.SigmaThirds.IChunk38
public import CatalanCore.Cert.SigmaThirds.IChunk39
public import CatalanCore.Cert.SigmaThirds.IChunk40
public import CatalanCore.Cert.SigmaThirds.IChunk41
public import CatalanCore.Cert.SigmaThirds.IChunk42
public import CatalanCore.Cert.SigmaThirds.IChunk43
public import CatalanCore.Cert.SigmaThirds.IChunk44
public import CatalanCore.Cert.SigmaThirds.IChunk45
public import CatalanCore.Cert.SigmaThirds.IChunk46
public import CatalanCore.Cert.SigmaThirds.IChunk47
public import CatalanCore.Cert.SigmaThirds.IChunk48
public import CatalanCore.Cert.SigmaThirds.IChunk49
public import CatalanCore.Cert.SigmaThirds.IChunk50
public import CatalanCore.Cert.SigmaThirds.IChunk51
public import CatalanCore.Cert.SigmaThirds.IBoundDef

@[expose] public section

/-!
# `I_ρ(σ_h) ≤ IBOUNDS` from the scaled-integer lower log bounds (`logLoS`), triangular row sums

`Irho (1/4096) cH wtH = (64/81) Irho (1/4096) cH mH` and `Irho cH mH ≤ ∑ₖ∑ₗ Jr pₖ pₗ = -iTri/2^129`;
`iTri` is the triangular sum (`Jr` is symmetric), cut into `NCH` chunks computed by the kernel (`IChunk*`).
-/

open Real

namespace CatalanCore.Cert.SigmaThirds

open _root_.CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

lemma sum_range_add (f : ℕ → ℤ) (n m : ℕ) :
    ((List.range (n + m)).map f).sum
      = ((List.range n).map f).sum + ((List.range m).map (fun i => f (n + i))).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl

lemma rowsSum_add (a n m : ℕ) : rowsSum a (n + m) = rowsSum a n + rowsSum (a + n) m := by
  unfold rowsSum
  rw [sum_range_add (fun i => rowT sigH (a + i)) n m]
  congr 2
  exact List.map_congr_left (fun i _ => by rw [add_assoc])

theorem chunk_ok : ∀ k < NCH, rowsSum (chunkStart k) (chunkLen k) = chunkVal k := by
  intro k hk
  unfold NCH at hk
  interval_cases k
  exacts [iChunk_0, iChunk_1, iChunk_2, iChunk_3, iChunk_4, iChunk_5, iChunk_6, iChunk_7, iChunk_8, iChunk_9, iChunk_10, iChunk_11, iChunk_12, iChunk_13, iChunk_14, iChunk_15, iChunk_16, iChunk_17, iChunk_18, iChunk_19, iChunk_20, iChunk_21, iChunk_22, iChunk_23, iChunk_24, iChunk_25, iChunk_26, iChunk_27, iChunk_28, iChunk_29, iChunk_30, iChunk_31, iChunk_32, iChunk_33, iChunk_34, iChunk_35, iChunk_36, iChunk_37, iChunk_38, iChunk_39, iChunk_40, iChunk_41, iChunk_42, iChunk_43, iChunk_44, iChunk_45, iChunk_46, iChunk_47, iChunk_48, iChunk_49, iChunk_50, iChunk_51, iChunk_52, iChunk_53, iChunk_54, iChunk_55, iChunk_56, iChunk_57, iChunk_58, iChunk_59, iChunk_60, iChunk_61, iChunk_62, iChunk_63, iChunk_64, iChunk_65, iChunk_66, iChunk_67, iChunk_68, iChunk_69, iChunk_70, iChunk_71, iChunk_72, iChunk_73, iChunk_74, iChunk_75, iChunk_76, iChunk_77, iChunk_78, iChunk_79, iChunk_80, iChunk_81, iChunk_82, iChunk_83, iChunk_84, iChunk_85, iChunk_86, iChunk_87, iChunk_88, iChunk_89, iChunk_90, iChunk_91, iChunk_92, iChunk_93, iChunk_94, iChunk_95, iChunk_96, iChunk_97, iChunk_98, iChunk_99, iChunk_100, iChunk_101, iChunk_102, iChunk_103, iChunk_104, iChunk_105, iChunk_106, iChunk_107, iChunk_108, iChunk_109, iChunk_110, iChunk_111, iChunk_112, iChunk_113, iChunk_114, iChunk_115, iChunk_116, iChunk_117, iChunk_118, iChunk_119, iChunk_120, iChunk_121, iChunk_122, iChunk_123, iChunk_124, iChunk_125, iChunk_126, iChunk_127, iChunk_128, iChunk_129, iChunk_130, iChunk_131, iChunk_132, iChunk_133, iChunk_134, iChunk_135, iChunk_136, iChunk_137, iChunk_138, iChunk_139, iChunk_140, iChunk_141, iChunk_142, iChunk_143, iChunk_144, iChunk_145, iChunk_146, iChunk_147, iChunk_148, iChunk_149, iChunk_150, iChunk_151, iChunk_152, iChunk_153, iChunk_154, iChunk_155]

lemma rows_prefix : ∀ k, k ≤ NCH → rowsSum 0 (chunkStart k) = cumVal k := by
  intro k
  induction k with
  | zero => intro _; simp [rowsSum, chunkStart, cumVal]
  | succ k ih =>
    intro hk
    have h := chunk_ok k (by omega)
    show rowsSum 0 (chunkStart k + chunkLen k) = cumVal k + chunkVal k
    rw [rowsSum_add, ih (by omega), zero_add, h]

theorem chunkStart_NCH : chunkStart NCH = 2950 := by decide +kernel
theorem cumVal_NCH : cumVal NCH = ITOT := by decide +kernel

theorem rows_total : rowsSum 0 2950 = ITOT := by
  have h := rows_prefix NCH le_rfl
  rw [chunkStart_NCH, cumVal_NCH] at h
  exact h

def iTri : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * ((p.2.2 : ℤ) * CatalanLambda.Cert.logLoS (qII p p) + 2 * iRow p ps) + iTri ps

lemma rowT_cons_zero (p : Pt) (ps : List Pt) : rowT (p :: ps) 0 =
    (p.2.2 : ℤ) * ((p.2.2 : ℤ) * CatalanLambda.Cert.logLoS (qII p p) + 2 * iRow p ps) := by
  simp only [rowT, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]

lemma rowT_cons_succ (p : Pt) (ps : List Pt) (r : ℕ) : rowT (p :: ps) (r + 1) = rowT ps r := by
  simp only [rowT, List.getD_cons_succ, List.drop_succ_cons]

lemma sum_range_succ_cons (f : ℕ → ℤ) (n : ℕ) :
    ((List.range (n + 1)).map f).sum = f 0 + ((List.range n).map (fun r => f (r + 1))).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  rfl

lemma iTri_eq (L : List Pt) : iTri L = ((List.range L.length).map (rowT L)).sum := by
  induction L with
  | nil => simp only [iTri, List.length_nil, List.range_zero, List.map_nil, List.sum_nil]
  | cons p ps ih =>
    rw [List.length_cons, sum_range_succ_cons (rowT (p :: ps)) ps.length]
    simp only [rowT_cons_succ]
    rw [rowT_cons_zero, ← ih]
    simp only [iTri]

lemma rowsSum_from_zero (n : ℕ) : rowsSum 0 n = ((List.range n).map (rowT sigH)).sum := by
  unfold rowsSum
  simp only [zero_add]

theorem sigH_len' : sigH.length = 2950 := by decide +kernel

theorem iTri_sigH : iTri sigH = ITOT := by
  rw [iTri_eq, sigH_len', ← rowsSum_from_zero, rows_total]

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


end CatalanCore.Cert.SigmaThirds
