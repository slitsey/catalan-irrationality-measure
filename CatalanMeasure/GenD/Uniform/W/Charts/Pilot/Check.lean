module
public import Mathlib.Tactic.IntervalCases
public import CatalanMeasure.GenD.Uniform.W.Charts.Pilot.Data
@[expose] public section
set_option Elab.async false

/-! Kernel check of the pilot packet with GENERATED chart rows: head, then each chart as its own declaration. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts.Pilot
open CatalanMeasure.GenD.Uniform.W.Prof

set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 50

theorem head_ok : packet.checkHead = true := by decide +kernel

/-- chart `j` of the generated packet -/
def chartJ (j : ℕ) : Chart := chartOf cc packet0.n (cc.types.getD j (0, 0, 0)) cert

theorem ch_ok0 : (chartJ 0).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok1 : (chartJ 1).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok2 : (chartJ 2).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok3 : (chartJ 3).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok4 : (chartJ 4).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok5 : (chartJ 5).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok6 : (chartJ 6).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok7 : (chartJ 7).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok8 : (chartJ 8).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok9 : (chartJ 9).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok10 : (chartJ 10).check packet.n packet.d packet.v = true := by decide +kernel
theorem ch_ok11 : (chartJ 11).check packet.n packet.d packet.v = true := by decide +kernel

theorem types_length : cc.types.length = 12 := by decide +kernel

theorem mem_charts {c : Chart} (hc : c ∈ packet.charts) : ∃ j < 12, c = chartJ j := by
  simp only [packet, generatePacket, packet0] at hc
  obtain ⟨⟨c0, κ⟩, hmem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < 12 := by
    have := hi
    simp [List.length_zip, types_length] at this
    omega
  refine ⟨i, hi', ?_⟩
  simp only [List.getElem_zip, List.getElem_replicate, Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  simp only [chartJ]
  rw [← h1, ← h2]
  simp [List.getD_eq_getElem?_getD, types_length, hi']
  rfl

theorem packet_check : packet.check = true :=
  Packet.check_of_parts head_ok (by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := mem_charts hc
    interval_cases j
    exacts [ch_ok0, ch_ok1, ch_ok2, ch_ok3, ch_ok4, ch_ok5, ch_ok6, ch_ok7, ch_ok8, ch_ok9,
      ch_ok10, ch_ok11])

theorem packet_sound : packet.Sound := Packet.check_sound packet_check

theorem packet_chartsOf : ChartsOf packet cc :=
  generate_chartsOf packet0 cc (by simpa [packet0] using types_length)

end CatalanMeasure.GenD.Uniform.W.Charts.Pilot
