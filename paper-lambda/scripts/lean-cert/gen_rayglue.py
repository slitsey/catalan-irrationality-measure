R='./CatalanLambda/Cert/'
N=27
imports="".join("import CatalanLambda.Cert.RayM%d\n"%i for i in range(N))
rayP="".join("  | %d => RayM%dP\n"%(i,i) for i in range(N))
oks=", ".join("RayM%d_ok"%i for i in range(N))
txt=imports+"""import CatalanLambda.Cert.Bridge

/-!
# Glue for the ray cells: global indexing of the 27 modules (27648 = 864 macros x 32 cells),
geometry (the cell box contains the CertFacts box of its `u`-interval), chain (cover of `[0,3/2]`).
-/

open Real

namespace CatalanLambda.Cert

set_option maxRecDepth 100000

def rayP : ℕ → ℕ
"""+rayP+"""  | _ => 0

theorem rayAll_ok : ∀ m < 27, ∀ j < 32, rayMacroOK MPRAY 32 (rayP m) j = true := by
  intro m hm
  interval_cases m
  exacts ["""+oks+"""]

def rayCellG (i : ℕ) : ℤ × ℤ × ℤ × ℤ := cellBox 32 (rayP (i / 1024)) ((i % 1024) / 32) (i % 32)

theorem ray_sound (i : ℕ) (hi : i < 27648) (x y : ℝ)
    (h1 : ((rayCellG i).1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ ((rayCellG i).2.1 : ℝ) / 2 ^ 40)
    (h3 : ((rayCellG i).2.2.1 : ℝ) / 2 ^ 40 ≤ y) (h4 : y ≤ ((rayCellG i).2.2.2 : ℝ) / 2 ^ 40) :
    (MPRAY : ℝ) ≤ gfun sigmaS x y :=
  rayMod_sound MPRAY 32 (rayP (i / 1024)) 32 (rayAll_ok (i / 1024) (by omega)) ((i % 1024) / 32)
    (by omega) (i % 32) (by omega) x y h1 h2 h3 h4

def geomCell (b : ℤ × ℤ × ℤ × ℤ) : Bool :=
  decide (b.2.1 < 0 ∧ 0 ≤ b.2.2.1 ∧ b.2.2.1 ≤ b.2.2.2 ∧
    150 * b.1 ≤ -21 * 2 ^ 40 - 50 * b.2.2.2 - 153600 ∧
    -21 * 2 ^ 40 - 50 * b.2.2.1 + 153600 ≤ 150 * b.2.1)

def rayChainCell (i : ℕ) : Bool :=
  decide (27648 ≤ i + 1 ∨ (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2)

theorem ray_geom : ∀ m < 27, (List.range 1024).all (fun i => geomCell (rayCellG (1024 * m + i))) = true := by
  decide +kernel

theorem ray_chain : ∀ m < 27, (List.range 1024).all (fun i => rayChainCell (1024 * m + i)) = true := by
  decide +kernel

theorem ray_ends : (rayCellG 0).2.2.1 = 0 ∧ 9 * 2 ^ 40 ≤ 2 * (rayCellG 27647).2.2.2 := by
  decide +kernel

lemma ray_geom' (i : ℕ) (hi : i < 27648) :
    (rayCellG i).2.1 < 0 ∧ 0 ≤ (rayCellG i).2.2.1 ∧ (rayCellG i).2.2.1 ≤ (rayCellG i).2.2.2 ∧
    150 * (rayCellG i).1 ≤ -21 * 2 ^ 40 - 50 * (rayCellG i).2.2.2 - 153600 ∧
    -21 * 2 ^ 40 - 50 * (rayCellG i).2.2.1 + 153600 ≤ 150 * (rayCellG i).2.1 := by
  have h := List.all_eq_true.mp (ray_geom (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simpa [geomCell] using h

lemma ray_chain' (i : ℕ) (hi : i + 1 < 27648) : (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2 := by
  have h := List.all_eq_true.mp (ray_chain (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simp only [rayChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

end CatalanLambda.Cert
"""
open(R+'RayGlue.lean','w',encoding='utf-8',newline='\n').write(txt)
