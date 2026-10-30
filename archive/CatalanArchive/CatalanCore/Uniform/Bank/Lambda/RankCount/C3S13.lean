import CatalanCore.Uniform.Bank.Lambda.RankFibre.C3S13
import CatalanCore.Uniform.Bank.Lambda.RunFibres
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankCount
open CatalanCore CatalanCore.Uniform.Content.RankProducer RankFibre RankData
open scoped Classical

noncomputable def C3S13_count0 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter (C3S13_test0 r p s)).card

theorem C3S13_endpoints0 (r p : ℕ) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    0 ≤ ((0 / 1 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ∧ ((0 / 1 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ≤ ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ∧ ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ≤ (p : ℚ) := by
  have hL : (1 : ℚ) * r ≤ (2 : ℚ) * p := by exact_mod_cast hleft
  have hR : (7 : ℚ) * p ≤ (4 : ℚ) * r := by exact_mod_cast hright
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem C3S13_good0 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    goodRunFibres r p 0 s ((0 / 1 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) =
      ((Finset.univ : Finset (ZMod p)).filter (C3S13_test0 r p s)) := by
  have hlo0 := (C3S13_endpoints0 r p hleft hright).1
  ext x
  have hxp : x.val < p := ZMod.val_lt x
  simp only [goodRunFibres, runResidues, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_range, hxp, true_and, C3S13_test0]
  constructor
  · rintro ⟨⟨hpar, hlo, hhi⟩, hgood⟩
    have hxQ : (4 : ℚ) ≤ x.val := by linarith
    have hLQ : (0 : ℚ) * r + (0 : ℚ) * p + 4 ≤ (1 : ℚ) * x.val := by nlinarith [hlo]
    have hRQ : (5 : ℚ) * x.val ≤ (6 : ℚ) * r + (-10 : ℚ) * p - 20 := by nlinarith [hhi]
    exact ⟨hpar, by exact_mod_cast hxQ, by exact_mod_cast hLQ, by exact_mod_cast hRQ, hgood⟩
  · rintro ⟨hpar, hx, hlo, hhi, hgood⟩
    have hLQ : (0 : ℚ) * r + (0 : ℚ) * p + 4 ≤ (1 : ℚ) * x.val := by exact_mod_cast hlo
    have hRQ : (5 : ℚ) * x.val ≤ (6 : ℚ) * r + (-10 : ℚ) * p - 20 := by exact_mod_cast hhi
    exact ⟨⟨hpar, by nlinarith [hLQ], by nlinarith [hRQ]⟩, hgood⟩

theorem C3S13_count_bounds0 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((3 / 5 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) - 6 - ((r - s.card : ℕ) : ℚ) ≤ C3S13_count0 r p s ∧
      (C3S13_count0 r p s : ℚ) ≤ ((3 / 5 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) + 6 := by
  obtain ⟨hl, hle, hh⟩ := C3S13_endpoints0 r p hleft hright
  have h := goodRunFibres_card_bounds r p 0 s ((0 / 1 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) (by decide) hl hle hh
  rw [C3S13_good0 r p s hleft hright] at h
  change _ ≤ (C3S13_count0 r p s : ℚ) ∧ (C3S13_count0 r p s : ℚ) ≤ _ at h
  constructor <;> linarith [h.1, h.2]

noncomputable def C3S13_count1 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter (C3S13_test1 r p s)).card

theorem C3S13_endpoints1 (r p : ℕ) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    0 ≤ ((0 / 1 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ∧ ((0 / 1 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ≤ ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ∧ ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ≤ (p : ℚ) := by
  have hL : (1 : ℚ) * r ≤ (2 : ℚ) * p := by exact_mod_cast hleft
  have hR : (7 : ℚ) * p ≤ (4 : ℚ) * r := by exact_mod_cast hright
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem C3S13_good1 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    goodRunFibres r p 1 s ((0 / 1 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) =
      ((Finset.univ : Finset (ZMod p)).filter (C3S13_test1 r p s)) := by
  have hlo0 := (C3S13_endpoints1 r p hleft hright).1
  ext x
  have hxp : x.val < p := ZMod.val_lt x
  simp only [goodRunFibres, runResidues, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_range, hxp, true_and, C3S13_test1]
  constructor
  · rintro ⟨⟨hpar, hlo, hhi⟩, hgood⟩
    have hxQ : (4 : ℚ) ≤ x.val := by linarith
    have hLQ : (0 : ℚ) * r + (0 : ℚ) * p + 4 ≤ (1 : ℚ) * x.val := by nlinarith [hlo]
    have hRQ : (5 : ℚ) * x.val ≤ (6 : ℚ) * r + (-10 : ℚ) * p - 20 := by nlinarith [hhi]
    exact ⟨hpar, by exact_mod_cast hxQ, by exact_mod_cast hLQ, by exact_mod_cast hRQ, hgood⟩
  · rintro ⟨hpar, hx, hlo, hhi, hgood⟩
    have hLQ : (0 : ℚ) * r + (0 : ℚ) * p + 4 ≤ (1 : ℚ) * x.val := by exact_mod_cast hlo
    have hRQ : (5 : ℚ) * x.val ≤ (6 : ℚ) * r + (-10 : ℚ) * p - 20 := by exact_mod_cast hhi
    exact ⟨⟨hpar, by nlinarith [hLQ], by nlinarith [hRQ]⟩, hgood⟩

theorem C3S13_count_bounds1 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((3 / 5 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) - 6 - ((r - s.card : ℕ) : ℚ) ≤ C3S13_count1 r p s ∧
      (C3S13_count1 r p s : ℚ) ≤ ((3 / 5 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) + 6 := by
  obtain ⟨hl, hle, hh⟩ := C3S13_endpoints1 r p hleft hright
  have h := goodRunFibres_card_bounds r p 1 s ((0 / 1 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) (by decide) hl hle hh
  rw [C3S13_good1 r p s hleft hright] at h
  change _ ≤ (C3S13_count1 r p s : ℚ) ∧ (C3S13_count1 r p s : ℚ) ≤ _ at h
  constructor <;> linarith [h.1, h.2]

noncomputable def C3S13_count2 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter (C3S13_test2 r p s)).card

theorem C3S13_endpoints2 (r p : ℕ) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    0 ≤ ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ∧ ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ≤ ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ∧ ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ≤ (p : ℚ) := by
  have hL : (1 : ℚ) * r ≤ (2 : ℚ) * p := by exact_mod_cast hleft
  have hR : (7 : ℚ) * p ≤ (4 : ℚ) * r := by exact_mod_cast hright
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem C3S13_good2 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    goodRunFibres r p 0 s ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) =
      ((Finset.univ : Finset (ZMod p)).filter (C3S13_test2 r p s)) := by
  have hlo0 := (C3S13_endpoints2 r p hleft hright).1
  ext x
  have hxp : x.val < p := ZMod.val_lt x
  simp only [goodRunFibres, runResidues, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_range, hxp, true_and, C3S13_test2]
  constructor
  · rintro ⟨⟨hpar, hlo, hhi⟩, hgood⟩
    have hxQ : (4 : ℚ) ≤ x.val := by linarith
    have hLQ : (6 : ℚ) * r + (-10 : ℚ) * p + 20 ≤ (5 : ℚ) * x.val := by nlinarith [hlo]
    have hRQ : (4 : ℚ) * x.val ≤ (0 : ℚ) * r + (3 : ℚ) * p - 16 := by nlinarith [hhi]
    exact ⟨hpar, by exact_mod_cast hxQ, by exact_mod_cast hLQ, by exact_mod_cast hRQ, hgood⟩
  · rintro ⟨hpar, hx, hlo, hhi, hgood⟩
    have hLQ : (6 : ℚ) * r + (-10 : ℚ) * p + 20 ≤ (5 : ℚ) * x.val := by exact_mod_cast hlo
    have hRQ : (4 : ℚ) * x.val ≤ (0 : ℚ) * r + (3 : ℚ) * p - 16 := by exact_mod_cast hhi
    exact ⟨⟨hpar, by nlinarith [hLQ], by nlinarith [hRQ]⟩, hgood⟩

theorem C3S13_count_bounds2 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((-3 / 5 : ℚ) * (r : ℚ) + (11 / 8 : ℚ) * (p : ℚ)) - 6 - ((r - s.card : ℕ) : ℚ) ≤ C3S13_count2 r p s ∧
      (C3S13_count2 r p s : ℚ) ≤ ((-3 / 5 : ℚ) * (r : ℚ) + (11 / 8 : ℚ) * (p : ℚ)) + 6 := by
  obtain ⟨hl, hle, hh⟩ := C3S13_endpoints2 r p hleft hright
  have h := goodRunFibres_card_bounds r p 0 s ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) (by decide) hl hle hh
  rw [C3S13_good2 r p s hleft hright] at h
  change _ ≤ (C3S13_count2 r p s : ℚ) ∧ (C3S13_count2 r p s : ℚ) ≤ _ at h
  constructor <;> linarith [h.1, h.2]

noncomputable def C3S13_count3 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter (C3S13_test3 r p s)).card

theorem C3S13_endpoints3 (r p : ℕ) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    0 ≤ ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ∧ ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ≤ ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ∧ ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ≤ (p : ℚ) := by
  have hL : (1 : ℚ) * r ≤ (2 : ℚ) * p := by exact_mod_cast hleft
  have hR : (7 : ℚ) * p ≤ (4 : ℚ) * r := by exact_mod_cast hright
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem C3S13_good3 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    goodRunFibres r p 1 s ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) =
      ((Finset.univ : Finset (ZMod p)).filter (C3S13_test3 r p s)) := by
  have hlo0 := (C3S13_endpoints3 r p hleft hright).1
  ext x
  have hxp : x.val < p := ZMod.val_lt x
  simp only [goodRunFibres, runResidues, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_range, hxp, true_and, C3S13_test3]
  constructor
  · rintro ⟨⟨hpar, hlo, hhi⟩, hgood⟩
    have hxQ : (4 : ℚ) ≤ x.val := by linarith
    have hLQ : (6 : ℚ) * r + (-10 : ℚ) * p + 20 ≤ (5 : ℚ) * x.val := by nlinarith [hlo]
    have hRQ : (4 : ℚ) * x.val ≤ (0 : ℚ) * r + (3 : ℚ) * p - 16 := by nlinarith [hhi]
    exact ⟨hpar, by exact_mod_cast hxQ, by exact_mod_cast hLQ, by exact_mod_cast hRQ, hgood⟩
  · rintro ⟨hpar, hx, hlo, hhi, hgood⟩
    have hLQ : (6 : ℚ) * r + (-10 : ℚ) * p + 20 ≤ (5 : ℚ) * x.val := by exact_mod_cast hlo
    have hRQ : (4 : ℚ) * x.val ≤ (0 : ℚ) * r + (3 : ℚ) * p - 16 := by exact_mod_cast hhi
    exact ⟨⟨hpar, by nlinarith [hLQ], by nlinarith [hRQ]⟩, hgood⟩

theorem C3S13_count_bounds3 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((-3 / 5 : ℚ) * (r : ℚ) + (11 / 8 : ℚ) * (p : ℚ)) - 6 - ((r - s.card : ℕ) : ℚ) ≤ C3S13_count3 r p s ∧
      (C3S13_count3 r p s : ℚ) ≤ ((-3 / 5 : ℚ) * (r : ℚ) + (11 / 8 : ℚ) * (p : ℚ)) + 6 := by
  obtain ⟨hl, hle, hh⟩ := C3S13_endpoints3 r p hleft hright
  have h := goodRunFibres_card_bounds r p 1 s ((6 / 5 : ℚ) * (r : ℚ) + (-2 / 1 : ℚ) * (p : ℚ)) ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) (by decide) hl hle hh
  rw [C3S13_good3 r p s hleft hright] at h
  change _ ≤ (C3S13_count3 r p s : ℚ) ∧ (C3S13_count3 r p s : ℚ) ≤ _ at h
  constructor <;> linarith [h.1, h.2]

noncomputable def C3S13_count4 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter (C3S13_test4 r p s)).card

theorem C3S13_endpoints4 (r p : ℕ) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    0 ≤ ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ∧ ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ≤ ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ∧ ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ≤ (p : ℚ) := by
  have hL : (1 : ℚ) * r ≤ (2 : ℚ) * p := by exact_mod_cast hleft
  have hR : (7 : ℚ) * p ≤ (4 : ℚ) * r := by exact_mod_cast hright
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem C3S13_good4 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    goodRunFibres r p 0 s ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) =
      ((Finset.univ : Finset (ZMod p)).filter (C3S13_test4 r p s)) := by
  have hlo0 := (C3S13_endpoints4 r p hleft hright).1
  ext x
  have hxp : x.val < p := ZMod.val_lt x
  simp only [goodRunFibres, runResidues, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_range, hxp, true_and, C3S13_test4]
  constructor
  · rintro ⟨⟨hpar, hlo, hhi⟩, hgood⟩
    have hxQ : (4 : ℚ) ≤ x.val := by linarith
    have hLQ : (0 : ℚ) * r + (3 : ℚ) * p + 16 ≤ (4 : ℚ) * x.val := by nlinarith [hlo]
    have hRQ : (1 : ℚ) * x.val ≤ (1 : ℚ) * r + (-1 : ℚ) * p - 4 := by nlinarith [hhi]
    exact ⟨hpar, by exact_mod_cast hxQ, by exact_mod_cast hLQ, by exact_mod_cast hRQ, hgood⟩
  · rintro ⟨hpar, hx, hlo, hhi, hgood⟩
    have hLQ : (0 : ℚ) * r + (3 : ℚ) * p + 16 ≤ (4 : ℚ) * x.val := by exact_mod_cast hlo
    have hRQ : (1 : ℚ) * x.val ≤ (1 : ℚ) * r + (-1 : ℚ) * p - 4 := by exact_mod_cast hhi
    exact ⟨⟨hpar, by nlinarith [hLQ], by nlinarith [hRQ]⟩, hgood⟩

theorem C3S13_count_bounds4 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((1 / 2 : ℚ) * (r : ℚ) + (-7 / 8 : ℚ) * (p : ℚ)) - 6 - ((r - s.card : ℕ) : ℚ) ≤ C3S13_count4 r p s ∧
      (C3S13_count4 r p s : ℚ) ≤ ((1 / 2 : ℚ) * (r : ℚ) + (-7 / 8 : ℚ) * (p : ℚ)) + 6 := by
  obtain ⟨hl, hle, hh⟩ := C3S13_endpoints4 r p hleft hright
  have h := goodRunFibres_card_bounds r p 0 s ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) (by decide) hl hle hh
  rw [C3S13_good4 r p s hleft hright] at h
  change _ ≤ (C3S13_count4 r p s : ℚ) ∧ (C3S13_count4 r p s : ℚ) ≤ _ at h
  constructor <;> linarith [h.1, h.2]

noncomputable def C3S13_count5 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter (C3S13_test5 r p s)).card

theorem C3S13_endpoints5 (r p : ℕ) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    0 ≤ ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ∧ ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ≤ ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ∧ ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ≤ (p : ℚ) := by
  have hL : (1 : ℚ) * r ≤ (2 : ℚ) * p := by exact_mod_cast hleft
  have hR : (7 : ℚ) * p ≤ (4 : ℚ) * r := by exact_mod_cast hright
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem C3S13_good5 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    goodRunFibres r p 1 s ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) =
      ((Finset.univ : Finset (ZMod p)).filter (C3S13_test5 r p s)) := by
  have hlo0 := (C3S13_endpoints5 r p hleft hright).1
  ext x
  have hxp : x.val < p := ZMod.val_lt x
  simp only [goodRunFibres, runResidues, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_range, hxp, true_and, C3S13_test5]
  constructor
  · rintro ⟨⟨hpar, hlo, hhi⟩, hgood⟩
    have hxQ : (4 : ℚ) ≤ x.val := by linarith
    have hLQ : (0 : ℚ) * r + (3 : ℚ) * p + 16 ≤ (4 : ℚ) * x.val := by nlinarith [hlo]
    have hRQ : (1 : ℚ) * x.val ≤ (1 : ℚ) * r + (-1 : ℚ) * p - 4 := by nlinarith [hhi]
    exact ⟨hpar, by exact_mod_cast hxQ, by exact_mod_cast hLQ, by exact_mod_cast hRQ, hgood⟩
  · rintro ⟨hpar, hx, hlo, hhi, hgood⟩
    have hLQ : (0 : ℚ) * r + (3 : ℚ) * p + 16 ≤ (4 : ℚ) * x.val := by exact_mod_cast hlo
    have hRQ : (1 : ℚ) * x.val ≤ (1 : ℚ) * r + (-1 : ℚ) * p - 4 := by exact_mod_cast hhi
    exact ⟨⟨hpar, by nlinarith [hLQ], by nlinarith [hRQ]⟩, hgood⟩

theorem C3S13_count_bounds5 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((1 / 2 : ℚ) * (r : ℚ) + (-7 / 8 : ℚ) * (p : ℚ)) - 6 - ((r - s.card : ℕ) : ℚ) ≤ C3S13_count5 r p s ∧
      (C3S13_count5 r p s : ℚ) ≤ ((1 / 2 : ℚ) * (r : ℚ) + (-7 / 8 : ℚ) * (p : ℚ)) + 6 := by
  obtain ⟨hl, hle, hh⟩ := C3S13_endpoints5 r p hleft hright
  have h := goodRunFibres_card_bounds r p 1 s ((0 / 1 : ℚ) * (r : ℚ) + (3 / 4 : ℚ) * (p : ℚ)) ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) (by decide) hl hle hh
  rw [C3S13_good5 r p s hleft hright] at h
  change _ ≤ (C3S13_count5 r p s : ℚ) ∧ (C3S13_count5 r p s : ℚ) ≤ _ at h
  constructor <;> linarith [h.1, h.2]

noncomputable def C3S13_count6 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter (C3S13_test6 r p s)).card

theorem C3S13_endpoints6 (r p : ℕ) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    0 ≤ ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ∧ ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ≤ ((0 / 1 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) ∧ ((0 / 1 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) ≤ (p : ℚ) := by
  have hL : (1 : ℚ) * r ≤ (2 : ℚ) * p := by exact_mod_cast hleft
  have hR : (7 : ℚ) * p ≤ (4 : ℚ) * r := by exact_mod_cast hright
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem C3S13_good6 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    goodRunFibres r p 0 s ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ((0 / 1 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) =
      ((Finset.univ : Finset (ZMod p)).filter (C3S13_test6 r p s)) := by
  have hlo0 := (C3S13_endpoints6 r p hleft hright).1
  ext x
  have hxp : x.val < p := ZMod.val_lt x
  simp only [goodRunFibres, runResidues, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_range, hxp, true_and, C3S13_test6]
  constructor
  · rintro ⟨⟨hpar, hlo, hhi⟩, hgood⟩
    have hxQ : (4 : ℚ) ≤ x.val := by linarith
    have hLQ : (1 : ℚ) * r + (-1 : ℚ) * p + 4 ≤ (1 : ℚ) * x.val := by nlinarith [hlo]
    have hRQ : (1 : ℚ) * x.val ≤ (0 : ℚ) * r + (1 : ℚ) * p - 4 := by nlinarith [hhi]
    exact ⟨hpar, by exact_mod_cast hxQ, by exact_mod_cast hLQ, by exact_mod_cast hRQ, hgood⟩
  · rintro ⟨hpar, hx, hlo, hhi, hgood⟩
    have hLQ : (1 : ℚ) * r + (-1 : ℚ) * p + 4 ≤ (1 : ℚ) * x.val := by exact_mod_cast hlo
    have hRQ : (1 : ℚ) * x.val ≤ (0 : ℚ) * r + (1 : ℚ) * p - 4 := by exact_mod_cast hhi
    exact ⟨⟨hpar, by nlinarith [hLQ], by nlinarith [hRQ]⟩, hgood⟩

theorem C3S13_count_bounds6 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((-1 / 2 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) - 6 - ((r - s.card : ℕ) : ℚ) ≤ C3S13_count6 r p s ∧
      (C3S13_count6 r p s : ℚ) ≤ ((-1 / 2 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) + 6 := by
  obtain ⟨hl, hle, hh⟩ := C3S13_endpoints6 r p hleft hright
  have h := goodRunFibres_card_bounds r p 0 s ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ((0 / 1 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) (by decide) hl hle hh
  rw [C3S13_good6 r p s hleft hright] at h
  change _ ≤ (C3S13_count6 r p s : ℚ) ∧ (C3S13_count6 r p s : ℚ) ≤ _ at h
  constructor <;> linarith [h.1, h.2]

noncomputable def C3S13_count7 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter (C3S13_test7 r p s)).card

theorem C3S13_endpoints7 (r p : ℕ) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    0 ≤ ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ∧ ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ≤ ((0 / 1 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) ∧ ((0 / 1 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) ≤ (p : ℚ) := by
  have hL : (1 : ℚ) * r ≤ (2 : ℚ) * p := by exact_mod_cast hleft
  have hR : (7 : ℚ) * p ≤ (4 : ℚ) * r := by exact_mod_cast hright
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem C3S13_good7 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    goodRunFibres r p 1 s ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ((0 / 1 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) =
      ((Finset.univ : Finset (ZMod p)).filter (C3S13_test7 r p s)) := by
  have hlo0 := (C3S13_endpoints7 r p hleft hright).1
  ext x
  have hxp : x.val < p := ZMod.val_lt x
  simp only [goodRunFibres, runResidues, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_range, hxp, true_and, C3S13_test7]
  constructor
  · rintro ⟨⟨hpar, hlo, hhi⟩, hgood⟩
    have hxQ : (4 : ℚ) ≤ x.val := by linarith
    have hLQ : (1 : ℚ) * r + (-1 : ℚ) * p + 4 ≤ (1 : ℚ) * x.val := by nlinarith [hlo]
    have hRQ : (1 : ℚ) * x.val ≤ (0 : ℚ) * r + (1 : ℚ) * p - 4 := by nlinarith [hhi]
    exact ⟨hpar, by exact_mod_cast hxQ, by exact_mod_cast hLQ, by exact_mod_cast hRQ, hgood⟩
  · rintro ⟨hpar, hx, hlo, hhi, hgood⟩
    have hLQ : (1 : ℚ) * r + (-1 : ℚ) * p + 4 ≤ (1 : ℚ) * x.val := by exact_mod_cast hlo
    have hRQ : (1 : ℚ) * x.val ≤ (0 : ℚ) * r + (1 : ℚ) * p - 4 := by exact_mod_cast hhi
    exact ⟨⟨hpar, by nlinarith [hLQ], by nlinarith [hRQ]⟩, hgood⟩

theorem C3S13_count_bounds7 (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((-1 / 2 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) - 6 - ((r - s.card : ℕ) : ℚ) ≤ C3S13_count7 r p s ∧
      (C3S13_count7 r p s : ℚ) ≤ ((-1 / 2 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) + 6 := by
  obtain ⟨hl, hle, hh⟩ := C3S13_endpoints7 r p hleft hright
  have h := goodRunFibres_card_bounds r p 1 s ((1 / 1 : ℚ) * (r : ℚ) + (-1 / 1 : ℚ) * (p : ℚ)) ((0 / 1 : ℚ) * (r : ℚ) + (1 / 1 : ℚ) * (p : ℚ)) (by decide) hl hle hh
  rw [C3S13_good7 r p s hleft hright] at h
  change _ ≤ (C3S13_count7 r p s : ℚ) ∧ (C3S13_count7 r p s : ℚ) ≤ _ at h
  constructor <;> linarith [h.1, h.2]

theorem C3S13_pointwise (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) (x : ZMod p) :
    (C3S13_assignment a p r m s ha hp29 hp4 hrp hm1 x).kr.card = (if C3S13_test0 r p s x then 1 else 0) + (if C3S13_test7 r p s x then 1 else 0) ∧
    (C3S13_assignment a p r m s ha hp29 hp4 hrp hm1 x).kc.card = (if C3S13_test1 r p s x then 1 else 0) + (if C3S13_test6 r p s x then 1 else 0) := by
  by_cases h0 : C3S13_test0 r p s x
  · rw [C3S13_assignment_on_run0 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h0]
    have hn1 : ¬ C3S13_test1 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn2 : ¬ C3S13_test2 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C3S13_test3 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C3S13_test4 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S13_test5 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S13_test6 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S13_test7 r p s x := by
      intro hj
      rcases h0 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_pos h0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    constructor <;> decide +kernel
  by_cases h1 : C3S13_test1 r p s x
  · rw [C3S13_assignment_on_run1 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h1]
    have hn2 : ¬ C3S13_test2 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn3 : ¬ C3S13_test3 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C3S13_test4 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S13_test5 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S13_test6 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S13_test7 r p s x := by
      intro hj
      rcases h1 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_pos h1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    constructor <;> decide +kernel
  by_cases h2 : C3S13_test2 r p s x
  · rw [C3S13_assignment_on_run2 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h2]
    have hn3 : ¬ C3S13_test3 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn4 : ¬ C3S13_test4 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S13_test5 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S13_test6 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S13_test7 r p s x := by
      intro hj
      rcases h2 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_pos h2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    constructor <;> decide +kernel
  by_cases h3 : C3S13_test3 r p s x
  · rw [C3S13_assignment_on_run3 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h3]
    have hn4 : ¬ C3S13_test4 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn5 : ¬ C3S13_test5 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S13_test6 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S13_test7 r p s x := by
      intro hj
      rcases h3 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7]
    constructor <;> decide +kernel
  by_cases h4 : C3S13_test4 r p s x
  · rw [C3S13_assignment_on_run4 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h4]
    have hn5 : ¬ C3S13_test5 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn6 : ¬ C3S13_test6 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S13_test7 r p s x := by
      intro hj
      rcases h4 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg hn5, if_neg hn6, if_neg hn7]
    constructor <;> decide +kernel
  by_cases h5 : C3S13_test5 r p s x
  · rw [C3S13_assignment_on_run5 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h5]
    have hn6 : ¬ C3S13_test6 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    have hn7 : ¬ C3S13_test7 r p s x := by
      intro hj
      rcases h5 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, if_neg hn6, if_neg hn7]
    constructor <;> decide +kernel
  by_cases h6 : C3S13_test6 r p s x
  · rw [C3S13_assignment_on_run6 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h6]
    have hn7 : ¬ C3S13_test7 r p s x := by
      intro hj
      rcases h6 with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg hn7]
    constructor <;> decide +kernel
  by_cases h7 : C3S13_test7 r p s x
  · rw [C3S13_assignment_on_run7 a p r m s ha hp29 hp4 hrp hm1 hleft hright x h7]
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    constructor <;> decide +kernel
  simp only [C3S13_assignment, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
  constructor <;> rfl

theorem C3S13_row_sum (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    (∑ x : ZMod p, (C3S13_assignment a p r m s ha hp29 hp4 hrp hm1 x).kr.card) = C3S13_count0 r p s + C3S13_count7 r p s := by
  calc
    _ = ∑ x : ZMod p, ((if C3S13_test0 r p s x then 1 else 0) + (if C3S13_test7 r p s x then 1 else 0)) := Finset.sum_congr rfl (fun x _ =>
      (C3S13_pointwise a p r m s ha hp29 hp4 hrp hm1 hleft hright x).1)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, C3S13_count0, C3S13_count7]

theorem C3S13_row_bounds (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((∑ x : ZMod p, (C3S13_assignment a p r m s ha hp29 hp4 hrp hm1 x).kr.card : ℕ) : ℚ) ∧
    ((∑ x : ZMod p, (C3S13_assignment a p r m s ha hp29 hp4 hrp hm1 x).kr.card : ℕ) : ℚ) ≤ ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 48 := by
  rw [C3S13_row_sum a p r m s ha hp29 hp4 hrp hm1 hleft hright]
  push_cast
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have h0 := C3S13_count_bounds0 r p s hleft hright
  have h7 := C3S13_count_bounds7 r p s hleft hright
  constructor <;> linarith [h0.1, h0.2, h7.1, h7.2]

theorem C3S13_col_sum (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    (∑ x : ZMod p, (C3S13_assignment a p r m s ha hp29 hp4 hrp hm1 x).kc.card) = C3S13_count1 r p s + C3S13_count6 r p s := by
  calc
    _ = ∑ x : ZMod p, ((if C3S13_test1 r p s x then 1 else 0) + (if C3S13_test6 r p s x then 1 else 0)) := Finset.sum_congr rfl (fun x _ =>
      (C3S13_pointwise a p r m s ha hp29 hp4 hrp hm1 hleft hright x).2)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, C3S13_count1, C3S13_count6]

theorem C3S13_col_bounds (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hleft : 1 * r ≤ 2 * p)
    (hright : 7 * p ≤ 4 * r) :
    ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((∑ x : ZMod p, (C3S13_assignment a p r m s ha hp29 hp4 hrp hm1 x).kc.card : ℕ) : ℚ) ∧
    ((∑ x : ZMod p, (C3S13_assignment a p r m s ha hp29 hp4 hrp hm1 x).kc.card : ℕ) : ℚ) ≤ ((1 / 10 : ℚ) * (r : ℚ) + (0 / 1 : ℚ) * (p : ℚ)) + 48 := by
  rw [C3S13_col_sum a p r m s ha hp29 hp4 hrp hm1 hleft hright]
  push_cast
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
  have h1 := C3S13_count_bounds1 r p s hleft hright
  have h6 := C3S13_count_bounds6 r p s hleft hright
  constructor <;> linarith [h1.1, h1.2, h6.1, h6.2]

#print axioms C3S13_row_bounds
#print axioms C3S13_col_bounds
end CatalanCore.Uniform.Bank.Lambda.RankCount
