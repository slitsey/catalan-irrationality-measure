module

public import CatalanFrames.P6Hybrid.ZDual
public import CatalanCore.Uniform.Bank.Plane1.Dips.Geometry

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! Arbitrary known-zero sets and exact natural dual prices. No geometry slope,
frame, level formula or numeric cut is fixed. U=0 is needed only on common nodes. -/
namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Uniform CatalanCore.Arith.Hybrid
open CatalanFrames.P6Hybrid (isRowP isColP cong_cases cong_cases')
open Classical

noncomputable def znU (r m p : ℕ) (K : Finset ℕ) (A : ℕ) : ℕ :=
  (if A∈K then 0 else 1)+(if A∈K ∧ isColP r m (A+p) then 1 else 0)
noncomputable def znV (r m p : ℕ) (K : Finset ℕ) (B : ℕ) : ℕ :=
  (if B∈K then 0 else 1)+(if B∈K ∧ isRowP r m (B+p) then 1 else 0)

theorem znU_nmem {r m p A : ℕ} {K : Finset ℕ} (h : A∉K) : znU r m p K A=1 := by simp [znU,h]
theorem znV_nmem {r m p A : ℕ} {K : Finset ℕ} (h : A∉K) : znV r m p K A=1 := by simp [znV,h]
theorem znU_mem {r m p A : ℕ} {K : Finset ℕ} (h : A∈K) (hc : isColP r m (A+p)) :
    znU r m p K A=1 := by simp [znU,h,hc]
theorem znV_mem {r m p A : ℕ} {K : Finset ℕ} (h : A∈K) (hc : isRowP r m (A+p)) :
    znV r m p K A=1 := by simp [znV,h,hc]

/-- Exact natural full-dual price; no subtractive/cardinality side condition. -/
noncomputable def zPrice (r m p : ℕ) (K : Finset ℕ) : ℕ :=
  (∑ c∈range r,(znU r m p K c+znV r m p K c))+
  ∑ i∈range m,(znU r m p K (r+2*i)+znV r m p K (r+2*i+1))

noncomputable def knownRho (r m p : ℕ) (K : Finset ℕ) (x : Fin r ⊕ Fin m) : ℚ :=
  znU r m p K (Frame.hybRow r m x)
noncomputable def knownGamma (r m p : ℕ) (K : Finset ℕ) (y : Fin r ⊕ Fin m) : ℚ :=
  znV r m p K (Frame.hybCol r m y)

theorem known_dual_value (r m p : ℕ) (K : Finset ℕ) :
    (∑ x,knownRho r m p K x)+(∑ y,knownGamma r m p K y)=(zPrice r m p K : ℚ) := by
  simp only [knownRho,knownGamma,Fintype.sum_sum_type,Frame.hybRow,Frame.hybCol,Sum.elim_inl,Sum.elim_inr]
  rw [← Finset.sum_range (n:=r) (fun i : ℕ => (znU r m p K i : ℚ)),
    ← Finset.sum_range (n:=m) (fun i : ℕ => (znU r m p K (r+2*i) : ℚ)),
    ← Finset.sum_range (n:=r) (fun i : ℕ => (znV r m p K i : ℚ)),
    ← Finset.sum_range (n:=m) (fun i : ℕ => (znV r m p K (r+2*i+1) : ℚ))]
  simp only [zPrice,Nat.cast_add,Nat.cast_sum]
  simp only [Finset.sum_add_distrib]
  ring

/-- Feasibility for every 0/1/2 weight system with the specified known zeros. -/
theorem knownZero_dual_feasible {r m p : ℕ} {K : Finset ℕ}
    (hp : 0<p) (hN : r+2*m≤2*p) (hKp : ∀ t∈K,t<p)
    (W : ℕ → ℕ → ℕ)
    (h2 : ∀ A B,A<r+2*m → B<r+2*m → isRowP r m A → isColP r m B → W A B≤2)
    (h1 : ∀ A B,A<r+2*m → B<r+2*m → isRowP r m A → isColP r m B →
      A≠B → ¬(p:ℤ)∣(A:ℤ)-B → W A B≤1)
    (hd : ∀ A,A<r+2*m → isRowP r m A → isColP r m A → A∈K → W A A=0)
    (hz : ∀ A B,A<r+2*m → B<r+2*m → isRowP r m A → isColP r m B →
      A≠B → ¬(p:ℤ)∣(A:ℤ)-B → A∈K → B∈K → W A B=0)
    (A B : ℕ) (hA : A<r+2*m) (hB : B<r+2*m)
    (hAr : isRowP r m A) (hBc : isColP r m B) :
    (W A B : ℚ)≤(znU r m p K A : ℚ)+(znV r m p K B : ℚ) := by
  have h2R : (W A B : ℚ)≤2 := by exact_mod_cast h2 A B hA hB hAr hBc
  have hu : (0:ℚ)≤znU r m p K A := Nat.cast_nonneg _
  have hv : (0:ℚ)≤znV r m p K B := Nat.cast_nonneg _
  by_cases hAB : A=B
  · subst B
    by_cases hK : A∈K
    · rw [hd A hA hAr hBc hK]
      exact add_nonneg hu hv
    · rw [znU_nmem hK,znV_nmem hK]
      norm_num at h2R ⊢
      exact h2R
  · by_cases hc : (p:ℤ)∣(A:ℤ)-B
    · by_cases hKA : A∈K <;> by_cases hKB : B∈K
      · have hh := cong_cases hp (hKp A hKA) (by omega : B<2*p) hc
        have hb := hKp B hKB
        omega
      · obtain he | he := cong_cases hp (hKp A hKA) (by omega : B<2*p) hc
        · exact False.elim (hAB he.symm)
        · rw [znU_mem hKA (by rw [←he];exact hBc),znV_nmem hKB]
          norm_num at h2R ⊢
          exact h2R
      · obtain he | he := cong_cases' hp (hKp B hKB) (by omega : A<2*p) hc
        · exact False.elim (hAB he)
        · rw [znU_nmem hKA,znV_mem hKB (by rw [←he];exact hAr)]
          norm_num at h2R ⊢
          exact h2R
      · rw [znU_nmem hKA,znV_nmem hKB]
        norm_num at h2R ⊢
        exact h2R
    · have h1R : (W A B : ℚ)≤1 := by exact_mod_cast h1 A B hA hB hAr hBc hAB hc
      by_cases hKA : A∈K <;> by_cases hKB : B∈K
      · rw [hz A B hA hB hAr hBc hAB hc hKA hKB]
        exact add_nonneg hu hv
      · rw [znV_nmem hKB]
        norm_num
        linarith
      · rw [znU_nmem hKA]
        norm_num
        linarith
      · rw [znU_nmem hKA,znV_nmem hKB]
        norm_num at h1R ⊢
        linarith

end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.known_dual_value
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.knownZero_dual_feasible
