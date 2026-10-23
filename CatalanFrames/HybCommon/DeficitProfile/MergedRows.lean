module
public import CatalanFrames.HybCommon.DeficitProfile.Content
public import CatalanFrames.HybCommon.DeficitProfile.Kind3
public import CatalanFrames.HybCommon.DeficitProfile.K3Cov0
public import CatalanFrames.HybCommon.DeficitProfile.K3Cov1
public import CatalanFrames.HybCommon.DeficitProfile.K3Cov2
public import CatalanFrames.HybCommon.DeficitProfile.K3Cov3
public import CatalanFrames.HybCommon.DeficitProfile.K3Cov4
@[expose] public section
set_option maxRecDepth 100000
open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon
open ChainClasses
variable {Fr : Frame}

/-! # The merged profile (non-clean two-level rows, capped at m)

`mergedProfile` = the banked rows of kinds 0 and 2, the banked kind-1 rows with `lo >= 1/2`, and the
26 kind-3 rows below (both pole classes, `u` in `(1/4, 3/5)`), the exact upper envelope (offline,
`Fraction`) of the banked rows and `min(1/8, max(sigma, 2 sigma - b))` for the non-clean overfull long
cells.  The cap `1/8` is the Lean bound `min m (sigma + (sigma - B'))`. -/

def newK3Raw : List DeficitRow := [
  ⟨3, 1, (1 / 4), (9 / 34), (9 / 4), (-17 / 2), 17, 20, 3⟩,
  ⟨3, 1, (9 / 32), (5 / 17), (-9 / 4), (8), 13, 16, 3⟩,
  ⟨3, 1, (5 / 17), (3 / 10), (-1), (15 / 4), 13, 16, 3⟩,
  ⟨3, 1, (3 / 10), (4 / 13), (1 / 8), (0), 13, 16, 3⟩,
  ⟨3, 1, (4 / 13), (5 / 16), (1 / 8), (0), 13, 16, 3⟩,
  ⟨3, 1, (5 / 16), (9 / 28), (1 / 8), (0), 13, 16, 3⟩,
  ⟨3, 1, (9 / 28), (1 / 3), (5 / 4), (-7 / 2), 13, 16, 3⟩,
  ⟨3, 1, (1 / 3), (9 / 26), (9 / 4), (-13 / 2), 13, 16, 2⟩,
  ⟨3, 1, (3 / 8), (5 / 13), (-9 / 4), (6), 9, 12, 2⟩,
  ⟨3, 1, (5 / 13), (9 / 22), (-1), (11 / 4), 9, 12, 2⟩,
  ⟨3, 1, (9 / 22), (5 / 12), (1 / 8), (0), 9, 12, 2⟩,
  ⟨3, 1, (4 / 9), (9 / 20), (1 / 8), (0), 9, 12, 2⟩,
  ⟨3, 1, (9 / 20), (1 / 2), (5 / 4), (-5 / 2), 9, 12, 2⟩,
  ⟨3, 3, (1 / 4), (5 / 19), (1 / 8), (0), 16, 19, 3⟩,
  ⟨3, 3, (5 / 19), (9 / 34), (1 / 8), (0), 16, 19, 3⟩,
  ⟨3, 3, (9 / 34), (4 / 15), (5 / 4), (-17 / 4), 16, 19, 3⟩,
  ⟨3, 3, (4 / 15), (9 / 32), (9 / 4), (-8), 16, 19, 3⟩,
  ⟨3, 3, (3 / 10), (5 / 16), (-9 / 4), (15 / 2), 12, 15, 3⟩,
  ⟨3, 3, (5 / 16), (9 / 28), (-1), (7 / 2), 12, 15, 3⟩,
  ⟨3, 3, (9 / 28), (1 / 3), (1 / 8), (0), 12, 15, 3⟩,
  ⟨3, 3, (1 / 3), (9 / 26), (1 / 8), (0), 12, 15, 2⟩,
  ⟨3, 3, (9 / 26), (4 / 11), (5 / 4), (-13 / 4), 12, 15, 2⟩,
  ⟨3, 3, (4 / 11), (3 / 8), (9 / 4), (-6), 12, 15, 2⟩,
  ⟨3, 3, (9 / 22), (5 / 12), (-9 / 4), (11 / 2), 8, 11, 2⟩,
  ⟨3, 3, (5 / 12), (9 / 20), (-1), (5 / 2), 8, 11, 2⟩,
  ⟨3, 3, (9 / 20), (5 / 11), (1 / 8), (0), 8, 11, 2⟩
  ]

def newK3 : List DeficitRow := newK3Raw.map DeficitRow.trim

def mergedOld : List DeficitRow :=
  newProfile.filter (fun P => decide (P.kind ≠ 1 ∨ (1/2 : ℚ) ≤ P.lo))

def mergedProfile : List DeficitRow := mergedOld ++ newK3

/-- Exact merged content constant. -/
def mergedLambda : ℚ := 2015079667893797 / 547747200000000

lemma mergedOld_mem {P : DeficitRow} (h : P ∈ mergedOld) : P ∈ newProfile := List.mem_of_mem_filter h

set_option maxHeartbeats 4000000 in
theorem newK3_shape : ∀ P ∈ newK3, Kind3Shape P := by
  intro P hP
  simp only [newK3, newK3Raw, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    DeficitRow.trim] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨rfl, by decide, rfl, ⟨by decide, by decide, by decide, fun j hj => by
    dsimp only at hj ⊢; simp only [Finset.mem_Ioo] at hj; omega⟩, by norm_num [profileTrim], by norm_num [profileTrim]⟩

set_option maxHeartbeats 4000000 in
theorem newK3_safe : ∀ P ∈ newK3, P.oldSafe := by
  norm_num [newK3, newK3Raw, DeficitRow.trim, profileTrim, DeficitRow.oldSafe]

set_option maxHeartbeats 4000000 in
theorem newK3_basic : ∀ P ∈ newK3, (P.poleClass=1 ∨ P.poleClass=3) ∧ 0<P.lo ∧ P.lo<P.hi := by
  norm_num [newK3, newK3Raw, DeficitRow.trim, profileTrim]

set_option maxHeartbeats 4000000 in
theorem newK3_hi_le_one : ∀ P ∈ newK3, P.hi ≤ 1 := by
  norm_num [newK3, newK3Raw, DeficitRow.trim, profileTrim]

set_option maxHeartbeats 4000000 in
theorem newK3_lift : ∀ P ∈ newK3, (1/8 : ℚ) ≤ P.lo ∧
    (if P.kind=0 then P.hi≤1/4 else
      1/4≤P.lo ∧ P.hi≤(if P.poleClass=1 then 9/10 else 9/14)) := by
  norm_num [newK3, newK3Raw, DeficitRow.trim, profileTrim]

set_option maxHeartbeats 8000000 in
theorem mergedProfile_pairwise : mergedProfile.Pairwise DeficitRow.disjoint := by
  norm_num (config := {maxSteps := 4000000}) [mergedProfile, mergedOld, newK3, newK3Raw, newProfile, rawProfile,
    DeficitRow.trim, profileTrim, List.pairwise_append, List.pairwise_cons, DeficitRow.disjoint, List.filter]

set_option maxHeartbeats 8000000 in
theorem mergedProfile_nodup : mergedProfile.Nodup := by
  norm_num (config := {maxSteps := 4000000}) [mergedProfile, mergedOld, newK3, newK3Raw, newProfile, rawProfile,
    DeficitRow.trim, profileTrim, List.nodup_append, List.nodup_cons, DeficitRow.mk.injEq, List.filter]

theorem mergedProfile_rowData : RowData mergedProfile where
  basic P hP := by
    rcases List.mem_append.1 hP with h | h
    · have hc := newProfile_cert P (mergedOld_mem h); exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
    · exact newK3_basic P h
  hi_le_one P hP := by
    rcases List.mem_append.1 hP with h | h
    · exact newProfile_hi_le_one P (mergedOld_mem h)
    · exact newK3_hi_le_one P h
  pairwise := mergedProfile_pairwise
  nodup := mergedProfile_nodup
  lift P hP := by
    rcases List.mem_append.1 hP with h | h
    · exact profile_lift_support P (mergedOld_mem h)
    · exact newK3_lift P h

set_option maxHeartbeats 8000000 in
theorem mergedProfile_integral : baseLambda - profileIntegralL mergedProfile ≤ mergedLambda := by
  unfold profileIntegralL
  norm_num (config := {maxSteps := 4000000}) [mergedProfile, mergedOld, newK3, newK3Raw, newProfile, rawProfile,
    DeficitRow.trim, profileTrim, DeficitRow.area, List.filter, baseLambda, mergedLambda]

/-- The cover of a kind-3 row from an integer inequality. -/
lemma k3_cover_link {P : DeficitRow} {nl dl nh dh D : ℕ} {A Bn : ℤ} {r p δ : ℕ}
    (hdl : 0<dl) (hdh : 0<dh) (hD : 0<D)
    (hlo : P.lo = (nl:ℚ)/dl) (hhi : P.hi = (nh:ℚ)/dh) (ha : P.a = (A:ℚ)/D) (hb : P.b = (Bn:ℚ)/D)
    (hact : ⌊(P.lo:ℝ)*r⌋₊ < p ∧ p ≤ ⌊(P.hi:ℝ)*r⌋₊)
    (H : nl*r < dl*p → dh*p ≤ nh*r → A*(r:ℤ) + Bn*(p:ℤ) - 8*(D:ℤ) ≤ (D:ℤ)*(δ:ℤ)) :
    (P.a:ℝ)*r + (P.b:ℝ)*p - 8 ≤ δ := by
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hdlR : (0:ℝ) < dl := by exact_mod_cast hdl
  have hdhR : (0:ℝ) < dh := by exact_mod_cast hdh
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hloR : (P.lo:ℝ) = (nl:ℝ)/dl := by rw [hlo]; push_cast; ring
  have hhiR : (P.hi:ℝ) = (nh:ℝ)/dh := by rw [hhi]; push_cast; ring
  have haR : (P.a:ℝ) = (A:ℝ)/D := by rw [ha]; push_cast; ring
  have hbR : (P.b:ℝ) = (Bn:ℝ)/D := by rw [hb]; push_cast; ring
  have h1 : (P.lo:ℝ)*r < p :=
    (Nat.floor_lt (mul_nonneg (by rw [hloR]; positivity) hr0)).mp hact.1
  have h2 : (p:ℝ) ≤ (P.hi:ℝ)*r :=
    (Nat.le_floor_iff (mul_nonneg (by rw [hhiR]; positivity) hr0)).mp hact.2
  rw [hloR, div_mul_eq_mul_div, div_lt_iff₀ hdlR] at h1
  rw [hhiR, div_mul_eq_mul_div, le_div_iff₀ hdhR] at h2
  have hl : nl*r < dl*p := by
    have : (nl:ℝ)*r < dl*p := by linarith
    exact_mod_cast this
  have hh : dh*p ≤ nh*r := by
    have : (dh:ℝ)*p ≤ nh*r := by linarith
    exact_mod_cast this
  have hH := H hl hh
  have hHR : (A:ℝ)*r + Bn*p - 8*D ≤ D*δ := by exact_mod_cast hH
  rw [haR, hbR]
  have : (A:ℝ)/D*r + Bn/D*p - 8 = ((A:ℝ)*r + Bn*p - 8*D)/D := by field_simp
  rw [this, div_le_iff₀ hDR]
  linarith

lemma k3_deficit_eq {o r p : ℕ} {P : DeficitRow} (h : P.kind=3) :
    profileRowDeficit o r p P = profileKind3Deficit o r p P := if_pos h

set_option maxHeartbeats 8000000 in
theorem newK3_cover {o : ℕ} (ho : o=1 ∨ o=3) {r p : ℕ} (hr : 1000000000 ≤ r) {P : DeficitRow} (hP : P ∈ newK3)
    (ha : profileRowActive o r p P) :
    (P.a:ℝ)*r + (P.b:ℝ)*p - 8 ≤ (profileRowDeficit o r p P : ℝ) := by
  have ha := ha.2
  simp only [newK3, newK3Raw, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    DeficitRow.trim] at hP
  rcases hP with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact k3_cover_link (nl:=2500001) (dl:=10000000) (nh:=44999983) (dh:=170000000) (D:=4) (A:=9) (Bn:=-34)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_0 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=2812501) (dl:=10000000) (nh:=49999983) (dh:=170000000) (D:=4) (A:=-9) (Bn:=32)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_1 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=50000017) (dl:=170000000) (nh:=2999999) (dh:=10000000) (D:=4) (A:=-4) (Bn:=15)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_2 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=3000001) (dl:=10000000) (nh:=39999987) (dh:=130000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_3 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=40000013) (dl:=130000000) (nh:=3124999) (dh:=10000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_4 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=3125001) (dl:=10000000) (nh:=22499993) (dh:=70000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_5 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=22500007) (dl:=70000000) (nh:=9999997) (dh:=30000000) (D:=4) (A:=5) (Bn:=-14)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_6 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=10000003) (dl:=30000000) (nh:=44999987) (dh:=130000000) (D:=4) (A:=9) (Bn:=-26)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_7 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=3750001) (dl:=10000000) (nh:=49999987) (dh:=130000000) (D:=4) (A:=-9) (Bn:=24)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_8 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=50000013) (dl:=130000000) (nh:=44999989) (dh:=110000000) (D:=4) (A:=-4) (Bn:=11)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_9 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=45000011) (dl:=110000000) (nh:=12499997) (dh:=30000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_10 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=40000009) (dl:=90000000) (nh:=4499999) (dh:=10000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_11 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=4500001) (dl:=10000000) (nh:=4999999) (dh:=10000000) (D:=4) (A:=5) (Bn:=-10)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_12 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=2500001) (dl:=10000000) (nh:=49999981) (dh:=190000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_13 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=50000019) (dl:=190000000) (nh:=44999983) (dh:=170000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_14 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=45000017) (dl:=170000000) (nh:=7999997) (dh:=30000000) (D:=4) (A:=5) (Bn:=-17)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_15 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=8000003) (dl:=30000000) (nh:=2812499) (dh:=10000000) (D:=4) (A:=9) (Bn:=-32)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_16 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=3000001) (dl:=10000000) (nh:=3124999) (dh:=10000000) (D:=4) (A:=-9) (Bn:=30)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_17 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=3125001) (dl:=10000000) (nh:=22499993) (dh:=70000000) (D:=2) (A:=-2) (Bn:=7)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_18 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=22500007) (dl:=70000000) (nh:=9999997) (dh:=30000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_19 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=10000003) (dl:=30000000) (nh:=44999987) (dh:=130000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_20 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=45000013) (dl:=130000000) (nh:=39999989) (dh:=110000000) (D:=4) (A:=5) (Bn:=-13)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_21 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=40000011) (dl:=110000000) (nh:=3749999) (dh:=10000000) (D:=4) (A:=9) (Bn:=-24)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_22 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=45000011) (dl:=110000000) (nh:=12499997) (dh:=30000000) (D:=4) (A:=-9) (Bn:=22)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_23 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=12500003) (dl:=30000000) (nh:=4499999) (dh:=10000000) (D:=2) (A:=-2) (Bn:=5)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_24 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)
  · exact k3_cover_link (nl:=4500001) (dl:=10000000) (nh:=49999989) (dh:=110000000) (D:=8) (A:=1) (Bn:=0)
      (by norm_num) (by norm_num) (by norm_num) (by subst h; norm_num [profileTrim]) (by subst h; norm_num [profileTrim])
      (by subst h; norm_num) (by subst h; norm_num) ha (fun hl hh => by
        rw [k3_deficit_eq (by subst h; rfl)]
        have h := k3cov_25 (o:=o) (r:=r) (p:=p) P ho (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) (by subst h; rfl) hr hl hh
        push_cast at h ⊢
        linarith)

theorem mergedProfile_cover {o : ℕ} (ho : o=1 ∨ o=3) :
    ProfileCoverL mergedProfile o (profileDeficitL mergedProfile o) 8 := by
  filter_upwards [eventually_ge_atTop 1000000000] with r hr
  intro P hP p hpL hpH hp hc
  have ha : profileRowActive o r p P := ⟨hc, hpL, hpH⟩
  have hgood : profilePrimeGood o r p := by
    rcases List.mem_append.1 hP with h | h
    · exact profile_active_good ho hr P (mergedOld_mem h) ha
    · exact profile_active_good_of ho hr P (newK3_safe P h) (newK3_basic P h) ha
  have hh : (P.a:ℝ)*r + (P.b:ℝ)*p - 8 ≤ (profileRowDeficit o r p P : ℝ) := by
    rcases List.mem_append.1 hP with h | h
    · exact profileRowDeficit_real_cover ho (by omega) P (mergedOld_mem h) ha
    · exact newK3_cover ho hr h ha
  have hle : (profileRowDeficit o r p P : ℝ) ≤ profileDeficitL mergedProfile o r p := by
    exact_mod_cast profileDeficit_ge_row o r p P hP hgood ha
  exact hh.trans hle

theorem mergedProfile_rowLocal {I : HybInst Fr} {o : ℕ} (hL : LamData Fr o) (ho : o=1 ∨ o=3) :
    ProfileRowLocal I o mergedProfile := by
  intro r p _ _ hr P hP ha hg hpos
  rcases List.mem_append.1 hP with h | h
  · exact profileRowLocal_new I hL ho r p hr P (mergedOld_mem h) ha hg hpos
  · exact kind3_rowLocal I hL ho (newK3_shape P h) hr ha hg hpos

/-- **The merged two-member content bound** (generic over the frame; both offsets). -/
theorem merged_both_eps (I : HybInst Fr) [∀r, I.DiagOK r (r/8)]
    {o Lc cm : ℕ} (hL : LamData Fr o) (ho : o=1 ∨ o=3)
    (T : TropFacts I o) (B : BadInfo I Lc cm) :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r/8) T δ)≤(((mergedLambda : ℚ) : ℝ)+ε)*(r : ℝ)^2 := by
  refine profile_both_eps_of_rows I hL ho T B mergedProfile_rowData (mergedProfile_rowLocal hL ho)
    (mergedProfile_cover ho) ?_
  have := (Rat.cast_le (K := ℝ)).2 mergedProfile_integral
  unfold baseLambda at this
  push_cast at this ⊢
  linarith

#print axioms merged_both_eps
end CatalanFrames.HybCommon
