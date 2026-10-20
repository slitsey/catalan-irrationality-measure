module

public import CatalanLambda.Cert.RayBox
public import CatalanArchive.CatalanLambda.Cert.SigmaData
public import CatalanArchive.CatalanLambda.Cert.RayPilotData

@[expose] public section

/-!
# Pilot: 500 ray boxes of the K=300 certificate, `g ≥ m′` with `m′ = 1.97179`
-/

namespace CatalanLambda.Cert

set_option maxRecDepth 100000

def pilotMp : ℚ := 197179 / 100000

/-- box `i` of a packed list: four signed integers in 64-bit slots, biased by `2^62`. -/
def packedBox (P i : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  let f : ℕ → ℤ := fun k => (((P >>> (64 * (4 * i + k))) % 2 ^ 64 : ℕ) : ℤ) - 2 ^ 62
  (f 0, f 1, f 2, f 3)

def boxSide (b : ℤ × ℤ × ℤ × ℤ) : Bool :=
  decide (b.2.1 < 0 ∧ b.1 ≤ b.2.1 ∧ 0 ≤ b.2.2.1)

def chunkOK (c : ℕ) : Bool :=
  (List.range 100).all (fun i => boxOK sigmaPts pilotMp (packedBox RayPilotDataPacked (100 * c + i)))

def chunkSide (c : ℕ) : Bool :=
  (List.range 100).all (fun i => boxSide (packedBox RayPilotDataPacked (100 * c + i)))

theorem pilot_side : ∀ c < 5, chunkSide c = true := by decide +kernel

theorem pilot_chunk0 : chunkOK 0 = true := by decide +kernel
theorem pilot_chunk1 : chunkOK 1 = true := by decide +kernel
theorem pilot_chunk2 : chunkOK 2 = true := by decide +kernel
theorem pilot_chunk3 : chunkOK 3 = true := by decide +kernel
theorem pilot_chunk4 : chunkOK 4 = true := by decide +kernel

theorem pilot_check : ∀ c < 5, chunkOK c = true := by
  intro c hc
  interval_cases c
  exacts [pilot_chunk0, pilot_chunk1, pilot_chunk2, pilot_chunk3, pilot_chunk4]

/-- Every point of every one of the 500 boxes has `g ≥ 1.97179`. -/
theorem ray_pilot : ∀ c < 5, ∀ j < 100, ∀ x y : ℝ,
    ((packedBox RayPilotDataPacked (100 * c + j)).1 : ℝ) / 2 ^ 40 ≤ x →
    x ≤ ((packedBox RayPilotDataPacked (100 * c + j)).2.1 : ℝ) / 2 ^ 40 →
    ((packedBox RayPilotDataPacked (100 * c + j)).2.2.1 : ℝ) / 2 ^ 40 ≤ y →
    y ≤ ((packedBox RayPilotDataPacked (100 * c + j)).2.2.2 : ℝ) / 2 ^ 40 →
    (pilotMp : ℝ) ≤ gfun sigmaPts x y := by
  intro c hc j hj x y h1 h2 h3 h4
  have hj' : j ∈ List.range 100 := List.mem_range.mpr hj
  have hs := List.all_eq_true.mp (pilot_side c hc) j hj'
  have hk := List.all_eq_true.mp (pilot_check c hc) j hj'
  generalize packedBox RayPilotDataPacked (100 * c + j) = b at *
  obtain ⟨a, b1, c', d⟩ := b
  simp only [boxSide, decide_eq_true_eq] at hs
  exact box_sound sigmaPts pilotMp a b1 c' d hs.1 hs.2.1 hs.2.2 hk x y h1 h2 h3 h4


end CatalanLambda.Cert
