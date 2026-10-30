module

public import CatalanCore.Cert.SigmaThirds.SegM0
public import CatalanCore.Cert.SigmaThirds.SegM1
public import CatalanCore.Cert.SigmaThirds.SegM2
public import CatalanCore.Cert.SigmaThirds.SegM3
public import CatalanCore.Cert.SigmaThirds.SegM4
public import CatalanCore.Cert.SigmaThirds.SegM5
public import CatalanCore.Cert.SigmaThirds.SegM6
public import CatalanCore.Cert.SigmaThirds.SegM7
public import CatalanCore.Cert.SigmaThirds.SegM8
public import CatalanCore.Cert.SigmaThirds.SegM9
public import CatalanCore.Cert.SigmaThirds.SegM10
public import CatalanCore.Cert.SigmaThirds.SegM11
public import CatalanCore.Cert.SigmaThirds.SegM12
public import CatalanCore.Cert.SigmaThirds.SegM13
public import CatalanCore.Cert.SigmaThirds.SegM14
public import CatalanCore.Cert.SigmaThirds.SegM15
public import CatalanCore.Cert.SigmaThirds.SegM16
public import CatalanCore.Cert.SigmaThirds.SegM17
public import CatalanCore.Cert.SigmaThirds.SegM18
public import CatalanCore.Cert.SigmaThirds.SegM19
public import CatalanCore.Cert.SigmaThirds.SegM20
public import CatalanCore.Cert.SigmaThirds.SegM21
public import CatalanCore.Cert.SigmaThirds.SegM22
public import CatalanCore.Cert.SigmaThirds.SegM23
public import CatalanCore.Cert.SigmaThirds.LineM0
public import CatalanCore.Cert.SigmaThirds.LineM1
public import CatalanCore.Cert.SigmaThirds.LineM2
public import CatalanCore.Cert.SigmaThirds.LineM3
public import CatalanCore.Cert.SigmaThirds.LineM4
public import CatalanCore.Cert.SigmaThirds.LineM5
public import CatalanCore.Cert.SigmaThirds.LineM6
public import CatalanCore.Cert.SigmaThirds.LineM7
public import CatalanCore.Cert.SigmaThirds.LineM8
public import CatalanCore.Cert.SigmaThirds.LineM9
public import CatalanCore.Cert.SigmaThirds.LineM10
public import CatalanCore.Cert.SigmaThirds.LineM11
public import CatalanCore.Cert.SigmaThirds.LineM12
public import CatalanCore.Cert.SigmaThirds.LineM13
public import CatalanCore.Cert.SigmaThirds.LineM14
public import CatalanCore.Cert.SigmaThirds.LineM15
public import CatalanCore.Cert.SigmaThirds.Bridge

@[expose] public section

/-!
# Glue for the real-axis cells: global indexing, chain/cover checks, the sum `S_cert`
-/

open Real

namespace CatalanCore.Cert.SigmaThirds

open _root_.CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 1000000

/-- cover lemma for a chain of closed intervals. -/
    lemma cover_chain (n : ℕ) (a b : ℕ → ℝ) (lo hi : ℝ) (hn0 : 0 < n) (h0 : a 0 ≤ lo)
        (hn : hi ≤ b (n - 1)) (hab : ∀ i, i + 1 < n → a (i + 1) ≤ b i) :
        ∀ x, lo ≤ x → x ≤ hi → ∃ i < n, a i ≤ x ∧ x ≤ b i := by
      have key : ∀ k, k < n → ∀ x, a 0 ≤ x → x ≤ b k → ∃ i < n, a i ≤ x ∧ x ≤ b i := by
        intro k
        induction k with
        | zero => intro hk x h1 h2; exact ⟨0, hk, h1, h2⟩
        | succ k ih =>
          intro hk x h1 h2
          by_cases hx : x ≤ b k
          · exact ih (by omega) x h1 hx
          · exact ⟨k + 1, hk, le_trans (hab k hk) (le_of_lt (not_le.mp hx)), h2⟩
      intro x hx1 hx2
      exact key (n - 1) (by omega) x (h0.trans hx1) (hx2.trans hn)

    def segM : ℕ → ℕ
  | 0 => 64
  | 1 => 64
  | 2 => 64
  | 3 => 64
  | 4 => 64
  | 5 => 64
  | 6 => 64
  | 7 => 64
  | 8 => 64
  | 9 => 64
  | 10 => 64
  | 11 => 64
  | 12 => 64
  | 13 => 64
  | 14 => 64
  | 15 => 64
  | 16 => 64
  | 17 => 64
  | 18 => 64
  | 19 => 64
  | 20 => 64
  | 21 => 64
  | 22 => 64
  | 23 => 64
  | _ => 1

def segP : ℕ → ℕ
  | 0 => SegM0P
  | 1 => SegM1P
  | 2 => SegM2P
  | 3 => SegM3P
  | 4 => SegM4P
  | 5 => SegM5P
  | 6 => SegM6P
  | 7 => SegM7P
  | 8 => SegM8P
  | 9 => SegM9P
  | 10 => SegM10P
  | 11 => SegM11P
  | 12 => SegM12P
  | 13 => SegM13P
  | 14 => SegM14P
  | 15 => SegM15P
  | 16 => SegM16P
  | 17 => SegM17P
  | 18 => SegM18P
  | 19 => SegM19P
  | 20 => SegM20P
  | 21 => SegM21P
  | 22 => SegM22P
  | 23 => SegM23P
  | _ => 0

theorem segAll_ok : ∀ m < 24, ∀ j < 1024 / segM m, realMacroOKH sigH true 0 (segM m) (segP m) j = true := by
  intro m hm
  interval_cases m
  exacts [SegM0_ok, SegM1_ok, SegM2_ok, SegM3_ok, SegM4_ok, SegM5_ok, SegM6_ok, SegM7_ok, SegM8_ok, SegM9_ok, SegM10_ok, SegM11_ok, SegM12_ok, SegM13_ok, SegM14_ok, SegM15_ok, SegM16_ok, SegM17_ok, SegM18_ok, SegM19_ok, SegM20_ok, SegM21_ok, SegM22_ok, SegM23_ok]

theorem segM_pos (m : ℕ) : 0 < segM m := by
  unfold segM; split <;> norm_num

theorem segM_dvd (m : ℕ) (hm : m < 24) : segM m ∣ 1024 := by
  interval_cases m <;> decide

def segCellG (i : ℕ) : ℤ × ℤ × ℤ :=
  realCell (segM (i / 1024)) (segP (i / 1024)) ((i % 1024) / segM (i / 1024)) (i % segM (i / 1024))

theorem seg_sound (i : ℕ) (hi : i < 24576) (x : ℝ) (h1 : ((segCellG i).1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ ((segCellG i).2.1 : ℝ) / 2 ^ 40) :
    ((((segCellG i).2.2 : ℚ) / 2 ^ 32 : ℚ) : ℝ) ≤ gHR sigH x 0 := by
  have := realMacroH_sound sigH true 0 (segM (i / 1024)) (segP (i / 1024)) ((i % 1024) / segM (i / 1024))
    (segAll_ok (i / 1024) (by omega) _ (Nat.div_lt_div_of_lt_of_dvd (segM_dvd _ (by omega)) (Nat.mod_lt _ (by omega))))
    (i % segM (i / 1024)) (Nat.mod_lt _ (segM_pos _)) x h1 h2
  simpa [realThr, segCellG] using this

def segGeomCell (i : ℕ) : Bool :=
  decide ((segCellG i).1 ≤ (segCellG i).2.1 ∧ (segCellG i).2.1 ≤ 0)

def segChainCell (i : ℕ) : Bool :=
  decide (24576 ≤ i + 1 ∨ (segCellG (i + 1)).1 ≤ (segCellG i).2.1)

theorem seg_geom_0 : (List.range 1024).all (fun i => segGeomCell (1024 * 0 + i)) = true := by
  decide +kernel

theorem seg_geom_1 : (List.range 1024).all (fun i => segGeomCell (1024 * 1 + i)) = true := by
  decide +kernel

theorem seg_geom_2 : (List.range 1024).all (fun i => segGeomCell (1024 * 2 + i)) = true := by
  decide +kernel

theorem seg_geom_3 : (List.range 1024).all (fun i => segGeomCell (1024 * 3 + i)) = true := by
  decide +kernel

theorem seg_geom_4 : (List.range 1024).all (fun i => segGeomCell (1024 * 4 + i)) = true := by
  decide +kernel

theorem seg_geom_5 : (List.range 1024).all (fun i => segGeomCell (1024 * 5 + i)) = true := by
  decide +kernel

theorem seg_geom_6 : (List.range 1024).all (fun i => segGeomCell (1024 * 6 + i)) = true := by
  decide +kernel

theorem seg_geom_7 : (List.range 1024).all (fun i => segGeomCell (1024 * 7 + i)) = true := by
  decide +kernel

theorem seg_geom_8 : (List.range 1024).all (fun i => segGeomCell (1024 * 8 + i)) = true := by
  decide +kernel

theorem seg_geom_9 : (List.range 1024).all (fun i => segGeomCell (1024 * 9 + i)) = true := by
  decide +kernel

theorem seg_geom_10 : (List.range 1024).all (fun i => segGeomCell (1024 * 10 + i)) = true := by
  decide +kernel

theorem seg_geom_11 : (List.range 1024).all (fun i => segGeomCell (1024 * 11 + i)) = true := by
  decide +kernel

theorem seg_geom_12 : (List.range 1024).all (fun i => segGeomCell (1024 * 12 + i)) = true := by
  decide +kernel

theorem seg_geom_13 : (List.range 1024).all (fun i => segGeomCell (1024 * 13 + i)) = true := by
  decide +kernel

theorem seg_geom_14 : (List.range 1024).all (fun i => segGeomCell (1024 * 14 + i)) = true := by
  decide +kernel

theorem seg_geom_15 : (List.range 1024).all (fun i => segGeomCell (1024 * 15 + i)) = true := by
  decide +kernel

theorem seg_geom_16 : (List.range 1024).all (fun i => segGeomCell (1024 * 16 + i)) = true := by
  decide +kernel

theorem seg_geom_17 : (List.range 1024).all (fun i => segGeomCell (1024 * 17 + i)) = true := by
  decide +kernel

theorem seg_geom_18 : (List.range 1024).all (fun i => segGeomCell (1024 * 18 + i)) = true := by
  decide +kernel

theorem seg_geom_19 : (List.range 1024).all (fun i => segGeomCell (1024 * 19 + i)) = true := by
  decide +kernel

theorem seg_geom_20 : (List.range 1024).all (fun i => segGeomCell (1024 * 20 + i)) = true := by
  decide +kernel

theorem seg_geom_21 : (List.range 1024).all (fun i => segGeomCell (1024 * 21 + i)) = true := by
  decide +kernel

theorem seg_geom_22 : (List.range 1024).all (fun i => segGeomCell (1024 * 22 + i)) = true := by
  decide +kernel

theorem seg_geom_23 : (List.range 1024).all (fun i => segGeomCell (1024 * 23 + i)) = true := by
  decide +kernel

theorem seg_chain_0 : (List.range 1024).all (fun i => segChainCell (1024 * 0 + i)) = true := by
  decide +kernel

theorem seg_chain_1 : (List.range 1024).all (fun i => segChainCell (1024 * 1 + i)) = true := by
  decide +kernel

theorem seg_chain_2 : (List.range 1024).all (fun i => segChainCell (1024 * 2 + i)) = true := by
  decide +kernel

theorem seg_chain_3 : (List.range 1024).all (fun i => segChainCell (1024 * 3 + i)) = true := by
  decide +kernel

theorem seg_chain_4 : (List.range 1024).all (fun i => segChainCell (1024 * 4 + i)) = true := by
  decide +kernel

theorem seg_chain_5 : (List.range 1024).all (fun i => segChainCell (1024 * 5 + i)) = true := by
  decide +kernel

theorem seg_chain_6 : (List.range 1024).all (fun i => segChainCell (1024 * 6 + i)) = true := by
  decide +kernel

theorem seg_chain_7 : (List.range 1024).all (fun i => segChainCell (1024 * 7 + i)) = true := by
  decide +kernel

theorem seg_chain_8 : (List.range 1024).all (fun i => segChainCell (1024 * 8 + i)) = true := by
  decide +kernel

theorem seg_chain_9 : (List.range 1024).all (fun i => segChainCell (1024 * 9 + i)) = true := by
  decide +kernel

theorem seg_chain_10 : (List.range 1024).all (fun i => segChainCell (1024 * 10 + i)) = true := by
  decide +kernel

theorem seg_chain_11 : (List.range 1024).all (fun i => segChainCell (1024 * 11 + i)) = true := by
  decide +kernel

theorem seg_chain_12 : (List.range 1024).all (fun i => segChainCell (1024 * 12 + i)) = true := by
  decide +kernel

theorem seg_chain_13 : (List.range 1024).all (fun i => segChainCell (1024 * 13 + i)) = true := by
  decide +kernel

theorem seg_chain_14 : (List.range 1024).all (fun i => segChainCell (1024 * 14 + i)) = true := by
  decide +kernel

theorem seg_chain_15 : (List.range 1024).all (fun i => segChainCell (1024 * 15 + i)) = true := by
  decide +kernel

theorem seg_chain_16 : (List.range 1024).all (fun i => segChainCell (1024 * 16 + i)) = true := by
  decide +kernel

theorem seg_chain_17 : (List.range 1024).all (fun i => segChainCell (1024 * 17 + i)) = true := by
  decide +kernel

theorem seg_chain_18 : (List.range 1024).all (fun i => segChainCell (1024 * 18 + i)) = true := by
  decide +kernel

theorem seg_chain_19 : (List.range 1024).all (fun i => segChainCell (1024 * 19 + i)) = true := by
  decide +kernel

theorem seg_chain_20 : (List.range 1024).all (fun i => segChainCell (1024 * 20 + i)) = true := by
  decide +kernel

theorem seg_chain_21 : (List.range 1024).all (fun i => segChainCell (1024 * 21 + i)) = true := by
  decide +kernel

theorem seg_chain_22 : (List.range 1024).all (fun i => segChainCell (1024 * 22 + i)) = true := by
  decide +kernel

theorem seg_chain_23 : (List.range 1024).all (fun i => segChainCell (1024 * 23 + i)) = true := by
  decide +kernel

theorem seg_geom : ∀ m < 24, (List.range 1024).all (fun i => segGeomCell (1024 * m + i)) = true := by
  intro m hm
  interval_cases m
  exacts [seg_geom_0, seg_geom_1, seg_geom_2, seg_geom_3, seg_geom_4, seg_geom_5, seg_geom_6, seg_geom_7, seg_geom_8, seg_geom_9, seg_geom_10, seg_geom_11, seg_geom_12, seg_geom_13, seg_geom_14, seg_geom_15, seg_geom_16, seg_geom_17, seg_geom_18, seg_geom_19, seg_geom_20, seg_geom_21, seg_geom_22, seg_geom_23]

theorem seg_chain : ∀ m < 24, (List.range 1024).all (fun i => segChainCell (1024 * m + i)) = true := by
  intro m hm
  interval_cases m
  exacts [seg_chain_0, seg_chain_1, seg_chain_2, seg_chain_3, seg_chain_4, seg_chain_5, seg_chain_6, seg_chain_7, seg_chain_8, seg_chain_9, seg_chain_10, seg_chain_11, seg_chain_12, seg_chain_13, seg_chain_14, seg_chain_15, seg_chain_16, seg_chain_17, seg_chain_18, seg_chain_19, seg_chain_20, seg_chain_21, seg_chain_22, seg_chain_23]

theorem seg_ends : 50 * (segCellG 0).1 ≤ -7 * 2 ^ 40 ∧ 0 ≤ (segCellG 24575).2.1 := by
  decide +kernel

lemma seg_geom' (i : ℕ) (hi : i < 24576) : (segCellG i).1 ≤ (segCellG i).2.1 ∧ (segCellG i).2.1 ≤ 0 := by
  have h := List.all_eq_true.mp (seg_geom (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simpa [segGeomCell] using h

lemma seg_chain' (i : ℕ) (hi : i + 1 < 24576) : (segCellG (i + 1)).1 ≤ (segCellG i).2.1 := by
  have h := List.all_eq_true.mp (seg_chain (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simp only [segChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

def fSeg (i : ℕ) : ℤ :=
  ((segCellG i).2.1 - (segCellG i).1) *
    (if (segCellG i).2.2 * 50000 ≤ 103161 * 2 ^ 32 then (segCellG i).2.2 * 50000 - 103161 * 2 ^ 32 else 0)

def sacc : ℕ → ℤ
  | 0 => 0
  | n + 1 => sacc n + fSeg n

theorem sacc_add (a n : ℕ) : sacc (a + n) = sacc a + ((List.range n).map (fun i => fSeg (a + i))).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 from rfl, sacc, ih, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring

def segSum (k : ℕ) : ℤ := ((List.range 1024).map (fun i => fSeg (1024 * k + i))).sum

theorem segSum_0 : segSum 0 = (-9992785966842386160880 : ℤ) := by decide +kernel

theorem segSum_1 : segSum 1 = (-40437071404716598133824 : ℤ) := by decide +kernel

theorem segSum_2 : segSum 2 = (-76273696773514288583824 : ℤ) := by decide +kernel

theorem segSum_3 : segSum 3 = (-114986836745977297211168 : ℤ) := by decide +kernel

theorem segSum_4 : segSum 4 = (-155933786296093417583824 : ℤ) := by decide +kernel

theorem segSum_5 : segSum 5 = (-198815880946692048833824 : ℤ) := by decide +kernel

theorem segSum_6 : segSum 6 = (-243518952022324354061168 : ℤ) := by decide +kernel

theorem segSum_7 : segSum 7 = (-289997100954681513683824 : ℤ) := by decide +kernel

theorem segSum_8 : segSum 8 = (-338241728714025220133824 : ℤ) := by decide +kernel

theorem segSum_9 : segSum 9 = (-388309732385516080183824 : ℤ) := by decide +kernel

theorem segSum_10 : segSum 10 = (-440245639315292053311168 : ℤ) := by decide +kernel

theorem segSum_11 : segSum 11 = (-494160680513853023133824 : ℤ) := by decide +kernel

theorem segSum_12 : segSum 12 = (-550163474120610565533824 : ℤ) := by decide +kernel

theorem segSum_13 : segSum 13 = (-608404063012035174961168 : ℤ) := by decide +kernel

theorem segSum_14 : segSum 14 = (-669079756571375281383824 : ℤ) := by decide +kernel

theorem segSum_15 : segSum 15 = (-732403221893013439483824 : ℤ) := by decide +kernel

theorem segSum_16 : segSum 16 = (-798688038970526184783824 : ℤ) := by decide +kernel

theorem segSum_17 : segSum 17 = (-868289834411369728811168 : ℤ) := by decide +kernel

theorem segSum_18 : segSum 18 = (-941715510256350598283824 : ℤ) := by decide +kernel

theorem segSum_19 : segSum 19 = (-1019648203933475310983824 : ℤ) := by decide +kernel

theorem segSum_20 : segSum 20 = (-1103077388075389968761168 : ℤ) := by decide +kernel

theorem segSum_21 : segSum 21 = (-1193628588758083674333824 : ℤ) := by decide +kernel

theorem segSum_22 : segSum 22 = (-1294313330171587878083824 : ℤ) := by decide +kernel

theorem segSum_23 : segSum 23 = (-1413939183915105600833824 : ℤ) := by decide +kernel

def segV : ℕ → ℤ
  | 0 => (-9992785966842386160880 : ℤ)
  | 1 => (-40437071404716598133824 : ℤ)
  | 2 => (-76273696773514288583824 : ℤ)
  | 3 => (-114986836745977297211168 : ℤ)
  | 4 => (-155933786296093417583824 : ℤ)
  | 5 => (-198815880946692048833824 : ℤ)
  | 6 => (-243518952022324354061168 : ℤ)
  | 7 => (-289997100954681513683824 : ℤ)
  | 8 => (-338241728714025220133824 : ℤ)
  | 9 => (-388309732385516080183824 : ℤ)
  | 10 => (-440245639315292053311168 : ℤ)
  | 11 => (-494160680513853023133824 : ℤ)
  | 12 => (-550163474120610565533824 : ℤ)
  | 13 => (-608404063012035174961168 : ℤ)
  | 14 => (-669079756571375281383824 : ℤ)
  | 15 => (-732403221893013439483824 : ℤ)
  | 16 => (-798688038970526184783824 : ℤ)
  | 17 => (-868289834411369728811168 : ℤ)
  | 18 => (-941715510256350598283824 : ℤ)
  | 19 => (-1019648203933475310983824 : ℤ)
  | 20 => (-1103077388075389968761168 : ℤ)
  | 21 => (-1193628588758083674333824 : ℤ)
  | 22 => (-1294313330171587878083824 : ℤ)
  | 23 => (-1413939183915105600833824 : ℤ)
  | _ => 0

theorem segSum_eq : ∀ k < 24, segSum k = segV k := by
  intro k hk
  interval_cases k
  exacts [segSum_0, segSum_1, segSum_2, segSum_3, segSum_4, segSum_5, segSum_6, segSum_7, segSum_8, segSum_9, segSum_10, segSum_11, segSum_12, segSum_13, segSum_14, segSum_15, segSum_16, segSum_17, segSum_18, segSum_19, segSum_20, segSum_21, segSum_22, segSum_23]

def cumSeg : ℕ → ℤ
  | 0 => 0
  | k + 1 => cumSeg k + segV k

theorem sacc_chunks : ∀ k, k ≤ 24 → sacc (1024 * k) = cumSeg k := by
  intro k
  induction k with
  | zero => intro _; simp [sacc, cumSeg]
  | succ k ih =>
    intro hk
    rw [show 1024 * (k + 1) = 1024 * k + 1024 by ring, sacc_add, ih (by omega), cumSeg]
    have := segSum_eq k (by omega)
    unfold segSum at this
    rw [this]

def SVAL : ℤ := -13984264486128451687252896

theorem sacc_val : sacc 24576 = SVAL := by
  have h := sacc_chunks 24 le_rfl
  rw [show 24576 = 1024 * 24 by norm_num] at *
  rw [h]
  decide +kernel

def lineM : ℕ → ℕ
  | 0 => 64
  | 1 => 64
  | 2 => 64
  | 3 => 64
  | 4 => 64
  | 5 => 64
  | 6 => 64
  | 7 => 64
  | 8 => 64
  | 9 => 64
  | 10 => 64
  | 11 => 64
  | 12 => 64
  | 13 => 64
  | 14 => 64
  | 15 => 64
  | _ => 1

def lineP : ℕ → ℕ
  | 0 => LineM0P
  | 1 => LineM1P
  | 2 => LineM2P
  | 3 => LineM3P
  | 4 => LineM4P
  | 5 => LineM5P
  | 6 => LineM6P
  | 7 => LineM7P
  | 8 => LineM8P
  | 9 => LineM9P
  | 10 => LineM10P
  | 11 => LineM11P
  | 12 => LineM12P
  | 13 => LineM13P
  | 14 => LineM14P
  | 15 => LineM15P
  | _ => 0

theorem lineAll_ok : ∀ m < 16, ∀ j < 1024 / lineM m, realMacroOKH sigH false GMINS (lineM m) (lineP m) j = true := by
  intro m hm
  interval_cases m
  exacts [LineM0_ok, LineM1_ok, LineM2_ok, LineM3_ok, LineM4_ok, LineM5_ok, LineM6_ok, LineM7_ok, LineM8_ok, LineM9_ok, LineM10_ok, LineM11_ok, LineM12_ok, LineM13_ok, LineM14_ok, LineM15_ok]

theorem lineM_pos (m : ℕ) : 0 < lineM m := by
  unfold lineM; split <;> norm_num

theorem lineM_dvd (m : ℕ) (hm : m < 16) : lineM m ∣ 1024 := by
  interval_cases m <;> decide

def lineCellG (i : ℕ) : ℤ × ℤ × ℤ :=
  realCell (lineM (i / 1024)) (lineP (i / 1024)) ((i % 1024) / lineM (i / 1024)) (i % lineM (i / 1024))

theorem line_sound (i : ℕ) (hi : i < 16384) (x : ℝ) (h1 : ((lineCellG i).1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ ((lineCellG i).2.1 : ℝ) / 2 ^ 40) :
    ((GMINS : ℚ) : ℝ) ≤ gHR sigH x 0 := by
  have := realMacroH_sound sigH false GMINS (lineM (i / 1024)) (lineP (i / 1024)) ((i % 1024) / lineM (i / 1024))
    (lineAll_ok (i / 1024) (by omega) _ (Nat.div_lt_div_of_lt_of_dvd (lineM_dvd _ (by omega)) (Nat.mod_lt _ (by omega))))
    (i % lineM (i / 1024)) (Nat.mod_lt _ (lineM_pos _)) x h1 h2
  simpa [realThr, lineCellG] using this

def lineGeomCell (i : ℕ) : Bool :=
  decide (0 ≤ (lineCellG i).1 ∧ (lineCellG i).1 ≤ (lineCellG i).2.1 ∧ (lineCellG i).2.1 ≤ 2 ^ 40)

def lineChainCell (i : ℕ) : Bool :=
  decide (16384 ≤ i + 1 ∨ (lineCellG (i + 1)).1 ≤ (lineCellG i).2.1)

theorem line_geom_0 : (List.range 1024).all (fun i => lineGeomCell (1024 * 0 + i)) = true := by
  decide +kernel

theorem line_geom_1 : (List.range 1024).all (fun i => lineGeomCell (1024 * 1 + i)) = true := by
  decide +kernel

theorem line_geom_2 : (List.range 1024).all (fun i => lineGeomCell (1024 * 2 + i)) = true := by
  decide +kernel

theorem line_geom_3 : (List.range 1024).all (fun i => lineGeomCell (1024 * 3 + i)) = true := by
  decide +kernel

theorem line_geom_4 : (List.range 1024).all (fun i => lineGeomCell (1024 * 4 + i)) = true := by
  decide +kernel

theorem line_geom_5 : (List.range 1024).all (fun i => lineGeomCell (1024 * 5 + i)) = true := by
  decide +kernel

theorem line_geom_6 : (List.range 1024).all (fun i => lineGeomCell (1024 * 6 + i)) = true := by
  decide +kernel

theorem line_geom_7 : (List.range 1024).all (fun i => lineGeomCell (1024 * 7 + i)) = true := by
  decide +kernel

theorem line_geom_8 : (List.range 1024).all (fun i => lineGeomCell (1024 * 8 + i)) = true := by
  decide +kernel

theorem line_geom_9 : (List.range 1024).all (fun i => lineGeomCell (1024 * 9 + i)) = true := by
  decide +kernel

theorem line_geom_10 : (List.range 1024).all (fun i => lineGeomCell (1024 * 10 + i)) = true := by
  decide +kernel

theorem line_geom_11 : (List.range 1024).all (fun i => lineGeomCell (1024 * 11 + i)) = true := by
  decide +kernel

theorem line_geom_12 : (List.range 1024).all (fun i => lineGeomCell (1024 * 12 + i)) = true := by
  decide +kernel

theorem line_geom_13 : (List.range 1024).all (fun i => lineGeomCell (1024 * 13 + i)) = true := by
  decide +kernel

theorem line_geom_14 : (List.range 1024).all (fun i => lineGeomCell (1024 * 14 + i)) = true := by
  decide +kernel

theorem line_geom_15 : (List.range 1024).all (fun i => lineGeomCell (1024 * 15 + i)) = true := by
  decide +kernel

theorem line_chain_0 : (List.range 1024).all (fun i => lineChainCell (1024 * 0 + i)) = true := by
  decide +kernel

theorem line_chain_1 : (List.range 1024).all (fun i => lineChainCell (1024 * 1 + i)) = true := by
  decide +kernel

theorem line_chain_2 : (List.range 1024).all (fun i => lineChainCell (1024 * 2 + i)) = true := by
  decide +kernel

theorem line_chain_3 : (List.range 1024).all (fun i => lineChainCell (1024 * 3 + i)) = true := by
  decide +kernel

theorem line_chain_4 : (List.range 1024).all (fun i => lineChainCell (1024 * 4 + i)) = true := by
  decide +kernel

theorem line_chain_5 : (List.range 1024).all (fun i => lineChainCell (1024 * 5 + i)) = true := by
  decide +kernel

theorem line_chain_6 : (List.range 1024).all (fun i => lineChainCell (1024 * 6 + i)) = true := by
  decide +kernel

theorem line_chain_7 : (List.range 1024).all (fun i => lineChainCell (1024 * 7 + i)) = true := by
  decide +kernel

theorem line_chain_8 : (List.range 1024).all (fun i => lineChainCell (1024 * 8 + i)) = true := by
  decide +kernel

theorem line_chain_9 : (List.range 1024).all (fun i => lineChainCell (1024 * 9 + i)) = true := by
  decide +kernel

theorem line_chain_10 : (List.range 1024).all (fun i => lineChainCell (1024 * 10 + i)) = true := by
  decide +kernel

theorem line_chain_11 : (List.range 1024).all (fun i => lineChainCell (1024 * 11 + i)) = true := by
  decide +kernel

theorem line_chain_12 : (List.range 1024).all (fun i => lineChainCell (1024 * 12 + i)) = true := by
  decide +kernel

theorem line_chain_13 : (List.range 1024).all (fun i => lineChainCell (1024 * 13 + i)) = true := by
  decide +kernel

theorem line_chain_14 : (List.range 1024).all (fun i => lineChainCell (1024 * 14 + i)) = true := by
  decide +kernel

theorem line_chain_15 : (List.range 1024).all (fun i => lineChainCell (1024 * 15 + i)) = true := by
  decide +kernel

theorem line_geom : ∀ m < 16, (List.range 1024).all (fun i => lineGeomCell (1024 * m + i)) = true := by
  intro m hm
  interval_cases m
  exacts [line_geom_0, line_geom_1, line_geom_2, line_geom_3, line_geom_4, line_geom_5, line_geom_6, line_geom_7, line_geom_8, line_geom_9, line_geom_10, line_geom_11, line_geom_12, line_geom_13, line_geom_14, line_geom_15]

theorem line_chain : ∀ m < 16, (List.range 1024).all (fun i => lineChainCell (1024 * m + i)) = true := by
  intro m hm
  interval_cases m
  exacts [line_chain_0, line_chain_1, line_chain_2, line_chain_3, line_chain_4, line_chain_5, line_chain_6, line_chain_7, line_chain_8, line_chain_9, line_chain_10, line_chain_11, line_chain_12, line_chain_13, line_chain_14, line_chain_15]

theorem line_ends : (lineCellG 0).1 ≤ 0 ∧ 2 ^ 40 ≤ (lineCellG 16383).2.1 := by
  decide +kernel

lemma line_geom' (i : ℕ) (hi : i < 16384) : 0 ≤ (lineCellG i).1 ∧ (lineCellG i).1 ≤ (lineCellG i).2.1 ∧ (lineCellG i).2.1 ≤ 2 ^ 40 := by
  have h := List.all_eq_true.mp (line_geom (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simpa [lineGeomCell] using h

lemma line_chain' (i : ℕ) (hi : i + 1 < 16384) : (lineCellG (i + 1)).1 ≤ (lineCellG i).2.1 := by
  have h := List.all_eq_true.mp (line_chain (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simp only [lineChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

end CatalanCore.Cert.SigmaThirds
