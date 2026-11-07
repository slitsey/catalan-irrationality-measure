module
public import CatalanFrames.HybGen.TropGood
public import CatalanFrames.HybGen.D1Prefix
public import CatalanFrames.Fifths.Tables
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen
namespace CatalanFrames.Fifths
/-- The correct first-root band on primes of a unit class, with the actual good-prime floor. -/
def BandP7 {Fr : Frame} (I : HybInst Fr) (j p : ℕ) : Prop :=
  7 ≤ p ∧ j*p+1 ≤ 5*I.cd.kq p ∧ 5*I.cd.kq p ≤ j*p+4
def Band7 {Fr : Frame} (I : HybInst Fr) (M : ℕ) (c : ZMod M) (j : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ZMod M) = c → BandP7 I j p
variable {Fr : Frame} {I : HybInst Fr}
  (T : LevelFacts I (fun p => 7 ≤ p) (fun q c => c < I.cd.kq q))
  {M : ℕ} {c : ZMod M} {r m : ℕ}
  (hm1 : r ≤ 8*m) (hm2 : 8*m ≤ r+9) (hr : 400 ≤ r)

section Class1
variable (hband : Band7 I M c 1)
include T hband hm1 hm2 hr
/-- Tail class1, piece1, D1; all-r admissible-window proof, no sampled replay. -/
theorem tail1_1 : Covers c (WGm I r m) r (mkPiece 1 4 15 16 17 (0) 48 8) :=
  covers_mkM c (BandP7 I 1) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hb1 := XGm_D1x I r m p hp (by omega)
    have hd := dist_ge p m 0 hp.pos (by omega)
    generalize m % p = s0 at hb1 hd
    omega)
/-- Tail class1, piece2, D2; all-r admissible-window proof, no sampled replay. -/
theorem tail1_2 : Covers c (WGm I r m) r (mkPiece 15 16 1 1 65 (-24) 120 20) :=
  covers_mkM c (BandP7 I 1) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hkr : I.cd.kq p ≤ r := by omega
    obtain ⟨u,L,h1,h2,h3,h4,h6⟩ :=
      XGm_D2_good T r m p hp h7 (by omega) (by omega) hkr
    omega)
/-- Tail class1, piece3, D45; all-r admissible-window proof, no sampled replay. -/
theorem tail1_3 : Covers c (WGm I r m) r (mkPiece 1 1 5 4 35 (-14) 60 10) :=
  covers_mkM c (BandP7 I 1) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D45_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class1, piece4, D45; all-r admissible-window proof, no sampled replay. -/
theorem tail1_4 : Covers c (WGm I r m) r (mkPiece 5 4 5 1 45 (-8) 120 20) :=
  covers_mkM c (BandP7 I 1) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D45_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class1, piece5, D6; all-r admissible-window proof, no sampled replay. -/
theorem tail1_5 : Covers c (WGm I r m) r (mkPiece 5 1 25 4 25 (-4) 120 20) :=
  covers_mkM c (BandP7 I 1) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D6_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class1, piece6, D6; all-r admissible-window proof, no sampled replay. -/
theorem tail1_6 : Covers c (WGm I r m) r (mkPiece 25 4 7 1 0 (0) 6 1) :=
  covers_mkM c (BandP7 I 1) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D6_good T r m p hp h7 (by omega) (by omega)
    omega)
theorem tail1_covers : ∀ P ∈ tail1, Covers c (WGm I r m) r P := by
  intro P hP
  simp only [tail1,List.mem_cons,List.not_mem_nil,or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
  · exact tail1_1 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail1_2 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail1_3 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail1_4 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail1_5 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail1_6 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
theorem table1_covers : ∀ P ∈ table1, Covers c (WGm I r m) r P := by
  intro P hP
  unfold table1 at hP
  rcases List.mem_append.mp hP with hP | hP
  · exact ld1_covers (I := I) (hm1 := hm1) (hm2 := hm2)
      (hc2 := fun p hp hc => by have h := (hband p hp hc).1; omega) P hP
  · exact tail1_covers (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr) P hP
end Class1

section Class2
variable (hband : Band7 I M c 2)
include T hband hm1 hm2 hr
/-- Tail class2, piece1, D1; all-r admissible-window proof, no sampled replay. -/
theorem tail2_1 : Covers c (WGm I r m) r (mkPiece 1 4 45 56 17 (0) 48 8) :=
  covers_mkM c (BandP7 I 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hb1 := XGm_D1x I r m p hp (by omega)
    have hd := dist_ge p m 0 hp.pos (by omega)
    generalize m % p = s0 at hb1 hd
    omega)
/-- Tail class2, piece2, D2; all-r admissible-window proof, no sampled replay. -/
theorem tail2_2 : Covers c (WGm I r m) r (mkPiece 45 56 25 28 65 (-28) 120 20) :=
  covers_mkM c (BandP7 I 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hkr : I.cd.kq p ≤ r := by omega
    obtain ⟨u,L,h1,h2,h3,h4,h6⟩ :=
      XGm_D2_good T r m p hp h7 (by omega) (by omega) hkr
    omega)
/-- Tail class2, piece3, D2; all-r admissible-window proof, no sampled replay. -/
theorem tail2_3 : Covers c (WGm I r m) r (mkPiece 25 28 1 1 45 (-28) 60 10) :=
  covers_mkM c (BandP7 I 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hkr : I.cd.kq p ≤ r := by omega
    obtain ⟨u,L,h1,h2,h3,h4,h6⟩ :=
      XGm_D2_good T r m p hp h7 (by omega) (by omega) hkr
    omega)
/-- Tail class2, piece4, D45; all-r admissible-window proof, no sampled replay. -/
theorem tail2_4 : Covers c (WGm I r m) r (mkPiece 1 1 5 4 35 (-18) 60 10) :=
  covers_mkM c (BandP7 I 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D45_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class2, piece5, D45; all-r admissible-window proof, no sampled replay. -/
theorem tail2_5 : Covers c (WGm I r m) r (mkPiece 5 4 5 2 45 (-16) 120 20) :=
  covers_mkM c (BandP7 I 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D45_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class2, piece6, D6; all-r admissible-window proof, no sampled replay. -/
theorem tail2_6 : Covers c (WGm I r m) r (mkPiece 5 2 25 8 25 (-8) 120 20) :=
  covers_mkM c (BandP7 I 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D6_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class2, piece7, D6; all-r admissible-window proof, no sampled replay. -/
theorem tail2_7 : Covers c (WGm I r m) r (mkPiece 25 8 7 1 0 (0) 6 1) :=
  covers_mkM c (BandP7 I 2) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D6_good T r m p hp h7 (by omega) (by omega)
    omega)
theorem tail2_covers : ∀ P ∈ tail2, Covers c (WGm I r m) r P := by
  intro P hP
  simp only [tail2,List.mem_cons,List.not_mem_nil,or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tail2_1 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail2_2 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail2_3 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail2_4 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail2_5 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail2_6 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail2_7 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
theorem table2_covers : ∀ P ∈ table2, Covers c (WGm I r m) r P := by
  intro P hP
  unfold table2 at hP
  rcases List.mem_append.mp hP with hP | hP
  · exact ld1_covers (I := I) (hm1 := hm1) (hm2 := hm2)
      (hc2 := fun p hp hc => by have h := (hband p hp hc).1; omega) P hP
  · exact tail2_covers (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr) P hP
end Class2

section Class3
variable (hband : Band7 I M c 3)
include T hband hm1 hm2 hr
/-- Tail class3, piece1, D1; all-r admissible-window proof, no sampled replay. -/
theorem tail3_1 : Covers c (WGm I r m) r (mkPiece 1 4 45 64 17 (0) 48 8) :=
  covers_mkM c (BandP7 I 3) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hb1 := XGm_D1x I r m p hp (by omega)
    have hd := dist_ge p m 0 hp.pos (by omega)
    generalize m % p = s0 at hb1 hd
    omega)
/-- Tail class3, piece2, D2; all-r admissible-window proof, no sampled replay. -/
theorem tail3_2 : Covers c (WGm I r m) r (mkPiece 45 64 25 32 65 (-32) 120 20) :=
  covers_mkM c (BandP7 I 3) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hkr : I.cd.kq p ≤ r := by omega
    obtain ⟨u,L,h1,h2,h3,h4,h6⟩ :=
      XGm_D2_good T r m p hp h7 (by omega) (by omega) hkr
    omega)
/-- Tail class3, piece3, D2; all-r admissible-window proof, no sampled replay. -/
theorem tail3_3 : Covers c (WGm I r m) r (mkPiece 25 32 1 1 45 (-32) 60 10) :=
  covers_mkM c (BandP7 I 3) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hkr : I.cd.kq p ≤ r := by omega
    obtain ⟨u,L,h1,h2,h3,h4,h6⟩ :=
      XGm_D2_good T r m p hp h7 (by omega) (by omega) hkr
    omega)
/-- Tail class3, piece4, D45; all-r admissible-window proof, no sampled replay. -/
theorem tail3_4 : Covers c (WGm I r m) r (mkPiece 1 1 5 4 35 (-22) 60 10) :=
  covers_mkM c (BandP7 I 3) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D45_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class3, piece5, D45; all-r admissible-window proof, no sampled replay. -/
theorem tail3_5 : Covers c (WGm I r m) r (mkPiece 5 4 5 3 45 (-24) 120 20) :=
  covers_mkM c (BandP7 I 3) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D45_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class3, piece6, D6; all-r admissible-window proof, no sampled replay. -/
theorem tail3_6 : Covers c (WGm I r m) r (mkPiece 5 3 25 12 25 (-12) 120 20) :=
  covers_mkM c (BandP7 I 3) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D6_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class3, piece7, D6; all-r admissible-window proof, no sampled replay. -/
theorem tail3_7 : Covers c (WGm I r m) r (mkPiece 25 12 7 1 0 (0) 6 1) :=
  covers_mkM c (BandP7 I 3) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D6_good T r m p hp h7 (by omega) (by omega)
    omega)
theorem tail3_covers : ∀ P ∈ tail3, Covers c (WGm I r m) r P := by
  intro P hP
  simp only [tail3,List.mem_cons,List.not_mem_nil,or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tail3_1 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail3_2 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail3_3 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail3_4 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail3_5 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail3_6 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail3_7 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
theorem table3_covers : ∀ P ∈ table3, Covers c (WGm I r m) r P := by
  intro P hP
  unfold table3 at hP
  rcases List.mem_append.mp hP with hP | hP
  · exact ld1_covers (I := I) (hm1 := hm1) (hm2 := hm2)
      (hc2 := fun p hp hc => by have h := (hband p hp hc).1; omega) P hP
  · exact tail3_covers (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr) P hP
end Class3

section Class4
variable (hband : Band7 I M c 4)
include T hband hm1 hm2 hr
/-- Tail class4, piece1, D1; all-r admissible-window proof, no sampled replay. -/
theorem tail4_1 : Covers c (WGm I r m) r (mkPiece 1 4 5 8 17 (0) 48 8) :=
  covers_mkM c (BandP7 I 4) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hb1 := XGm_D1x I r m p hp (by omega)
    have hd := dist_ge p m 0 hp.pos (by omega)
    generalize m % p = s0 at hb1 hd
    omega)
/-- Tail class4, piece2, D2; all-r admissible-window proof, no sampled replay. -/
theorem tail4_2 : Covers c (WGm I r m) r (mkPiece 5 8 25 36 65 (-36) 120 20) :=
  covers_mkM c (BandP7 I 4) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hkr : I.cd.kq p ≤ r := by omega
    obtain ⟨u,L,h1,h2,h3,h4,h6⟩ :=
      XGm_D2_good T r m p hp h7 (by omega) (by omega) hkr
    omega)
/-- Tail class4, piece3, D2; all-r admissible-window proof, no sampled replay. -/
theorem tail4_3 : Covers c (WGm I r m) r (mkPiece 25 36 1 1 45 (-36) 60 10) :=
  covers_mkM c (BandP7 I 4) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have hkr : I.cd.kq p ≤ r := by omega
    obtain ⟨u,L,h1,h2,h3,h4,h6⟩ :=
      XGm_D2_good T r m p hp h7 (by omega) (by omega) hkr
    omega)
/-- Tail class4, piece4, D45; all-r admissible-window proof, no sampled replay. -/
theorem tail4_4 : Covers c (WGm I r m) r (mkPiece 1 1 5 4 35 (-26) 60 10) :=
  covers_mkM c (BandP7 I 4) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D45_good T r m p hp h7 (by omega) (by omega)
    omega)
/-- Tail class4, piece5, D6fallback; all-r admissible-window proof, no sampled replay. -/
theorem tail4_5 : Covers c (WGm I r m) r (mkPiece 5 4 25 16 25 (-16) 120 20) :=
  covers_mkM c (BandP7 I 4) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    by_cases hN : r+2*m ≤ p
    · have h6 := XGm_D6_good T r m p hp h7 hN (by omega)
      omega
    · have h6 := XGm_D45_good T r m p hp h7 (by omega) (by omega)
      omega)
/-- Tail class4, piece6, D6; all-r admissible-window proof, no sampled replay. -/
theorem tail4_6 : Covers c (WGm I r m) r (mkPiece 25 16 7 1 0 (0) 6 1) :=
  covers_mkM c (BandP7 I 4) hband (XGm I r m) r _ _ _ _ _ _ _ _ (by norm_num) (by
    intro p hs ht hp hb
    obtain ⟨h7,hk1,hk2⟩ := hb
    have h6 := XGm_D6_good T r m p hp h7 (by omega) (by omega)
    omega)
theorem tail4_covers : ∀ P ∈ tail4, Covers c (WGm I r m) r P := by
  intro P hP
  simp only [tail4,List.mem_cons,List.not_mem_nil,or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
  · exact tail4_1 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail4_2 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail4_3 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail4_4 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail4_5 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · exact tail4_6 (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr)
theorem table4_covers : ∀ P ∈ table4, Covers c (WGm I r m) r P := by
  intro P hP
  unfold table4 at hP
  rcases List.mem_append.mp hP with hP | hP
  · exact ld1_covers (I := I) (hm1 := hm1) (hm2 := hm2)
      (hc2 := fun p hp hc => by have h := (hband p hp hc).1; omega) P hP
  · exact tail4_covers (T := T) (hband := hband) (hm1 := hm1) (hm2 := hm2) (hr := hr) P hP
end Class4
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.table1_covers
#print axioms CatalanFrames.Fifths.table2_covers
#print axioms CatalanFrames.Fifths.table3_covers
#print axioms CatalanFrames.Fifths.table4_covers
