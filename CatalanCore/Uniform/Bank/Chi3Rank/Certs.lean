import CatalanCore.Uniform.Content.RankProducer.Layer
import CatalanCore.Uniform.Bank.Chi3Rank.Closed
set_option Elab.async false

/-! # The four fibre certificates of the chi3 rank layer (lane H, H16)

Class `p ≡ 1 (6)`: a fibre with digit-0 common node and one border node at digit 1
(`E1`: border node a row, kills the row combination `(1/12, 1)`; `O1`: border node a column,
kills the column combination).  Class `p ≡ 5 (6)`: digits `0, 1` common and a border node at
digit 2 (`E5`, `O5`).  All data are `p`-independent rationals, checked by `decide`. -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Finset CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer

def mat3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : ℚ) : ℕ → ℕ → ℚ := fun d e =>
  match d, e with
  | 0, 0 => a00 | 0, 1 => a01 | 0, 2 => a02
  | 1, 0 => a10 | 1, 1 => a11 | 1, 2 => a12
  | 2, 0 => a20 | 2, 1 => a21 | 2, 2 => a22
  | _, _ => 0

def vec3 (a0 a1 a2 : ℚ) : ℕ → ℚ := fun d =>
  match d with | 0 => a0 | 1 => a1 | 2 => a2 | _ => 0

/-- Class 1, border node is a row. -/
def E1 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := vec3 0 (1 / 72) 0
  ee := vec3 (1 / 6) (163 / 864) 0
  Lq := mat3 (1 / 12) 1 0 0 1 0 0 0 0
  Lq' := mat3 12 (-12) 0 0 1 0 0 0 0
  Pq := mat3 1 0 0 0 0 0 0 0 0
  Pq' := mat3 1 0 0 0 0 0 0 0 0
  kr := {0}
  kc := ∅

/-- Class 1, border node is a column. -/
def O1 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := vec3 0 (1 / 72) 0
  ee := vec3 (1 / 6) (163 / 864) 0
  Lq := mat3 1 0 0 0 0 0 0 0 0
  Lq' := mat3 1 0 0 0 0 0 0 0 0
  Pq := mat3 (1 / 12) 0 0 1 1 0 0 0 0
  Pq' := mat3 12 0 0 (-12) 1 0 0 0 0
  kr := ∅
  kc := {0}

/-- Class 5, digit-2 node is a row. -/
def E5 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := vec3 0 (-1 / 18) (-23 / 360)
  ee := vec3 0 (-13 / 72) (-2059 / 10800)
  Lq := mat3 (-323 / 160) (-23 / 40) 1 0 1 0 0 0 1
  Lq' := mat3 (-160 / 323) (-92 / 323) (160 / 323) 0 1 0 0 0 1
  Pq := mat3 1 0 0 0 1 0 0 0 0
  Pq' := mat3 1 0 0 0 1 0 0 0 0
  kr := {0}
  kc := ∅

/-- Class 5, digit-2 node is a column. -/
def O5 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := vec3 0 (-1 / 18) (-23 / 360)
  ee := vec3 0 (-13 / 72) (-2059 / 10800)
  Lq := mat3 1 0 0 0 1 0 0 0 0
  Lq' := mat3 1 0 0 0 1 0 0 0 0
  Pq := mat3 (-323 / 160) 0 0 (-23 / 40) 1 0 1 0 1
  Pq' := mat3 (-160 / 323) 0 0 (-92 / 323) 1 0 (160 / 323) 0 1
  kr := ∅
  kc := {0}

/-- Denominator bound for `p`-integrality. -/
def N0 : ℕ := 465120

def DenOk (c : FibreCert) : Prop :=
  (∀ d ∈ c.R, ∀ e ∈ c.R, (c.Lq d e).den ∣ N0 ∧ (c.Lq' d e).den ∣ N0) ∧
  (∀ d ∈ c.C, ∀ e ∈ c.C, (c.Pq d e).den ∣ N0 ∧ (c.Pq' d e).den ∣ N0)

theorem integral_of_denOk (p : ℕ) [Fact p.Prime] (c : FibreCert) (h : DenOk c) (hp : N0 < p) :
    c.Integral p := by
  have key : ∀ v : ℚ, v.den ∣ N0 → v ∈ S p := by
    intro v hv hd
    have : p ≤ N0 := Nat.le_of_dvd (by norm_num [N0]) (hd.trans hv)
    omega
  exact ⟨fun d hd e he => ⟨key _ (h.1 d hd e he).1, key _ (h.1 d hd e he).2⟩,
    fun d hd e he => ⟨key _ (h.2 d hd e he).1, key _ (h.2 d hd e he).2⟩⟩

theorem E1_ok : E1.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
theorem O1_ok : O1.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
theorem E5_ok : E5.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
theorem O5_ok : O5.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem E1_den : DenOk E1 := by unfold DenOk; constructor <;> decide +kernel
theorem O1_den : DenOk O1 := by unfold DenOk; constructor <;> decide +kernel
theorem E5_den : DenOk E5 := by unfold DenOk; constructor <;> decide +kernel
theorem O5_den : DenOk O5 := by unfold DenOk; constructor <;> decide +kernel

theorem load1 : E1.rload 0 = O1.cload 0 := by
  simp [FibreCert.rload, FibreCert.cload, E1, O1, mat3, vec3]
theorem load5 : E5.rload 0 = O5.cload 0 := by
  simp [FibreCert.rload, FibreCert.cload, E5, O5, mat3, vec3]

theorem load1_val : O1.cload 0 = (13 / 12, 1 / 72) := by
  simp [FibreCert.cload, O1, mat3, vec3]; norm_num
theorem load5_val : O5.cload 0 = (-51 / 32, -23 / 720) := by
  simp [FibreCert.cload, O5, mat3, vec3]; norm_num

end CatalanCore.Uniform.Bank.Chi3Rank
