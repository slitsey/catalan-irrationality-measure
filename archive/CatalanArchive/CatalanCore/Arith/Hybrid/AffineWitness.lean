module
public import CatalanCore.Arith.Hybrid.AffineDeficit
@[expose] public section
namespace CatalanCore.Arith.Hybrid
lemma affine_le_of_endpoints {s t u a b c d : ℝ} (hu0 : s≤u) (hu1 : u≤t)
    (h0 : a+b*s≤c+d*s) (h1 : a+b*t≤c+d*t) : a+b*u≤c+d*u := by
  rcases le_total b d with hb|hb
  · nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hu0)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hu1)]

noncomputable def lowWitness (A B u : ℝ) : ℝ :=
  let aa := max 1 (A*u)
  let bb := min (5/4) (min (B*u) (1+u))
  min (1/8-u+bb-aa) (bb-9/8)
noncomputable def ncWitness (A B u : ℝ) : ℝ :=
  min (5/4) (B*u)-max 1 (A*u)-1/8

lemma lowWitness_bound {s t u a b A B : ℝ} (hu0 : s≤u) (hu1 : u≤t)
    (h0 : ∀aa∈[1,A*s],∀bb∈[5/4,B*s,1+s],a+b*s≤1/8-s+bb-aa)
    (h1 : ∀aa∈[1,A*t],∀bb∈[5/4,B*t,1+t],a+b*t≤1/8-t+bb-aa)
    (e0 : ∀bb∈[5/4,B*s,1+s],a+b*s≤bb-9/8)
    (e1 : ∀bb∈[5/4,B*t,1+t],a+b*t≤bb-9/8) : a+b*u≤lowWitness A B u := by
  have H00 := affine_le_of_endpoints (a:=a) (b:=b) (c:=1/8+5/4-1) (d:=-1+0-0) hu0 hu1
    (by have h:=h0 (1+0*s) (by simp) (5/4+0*s) (by simp); nlinarith)
    (by have h:=h1 (1+0*t) (by simp) (5/4+0*t) (by simp); nlinarith)
  have H01 := affine_le_of_endpoints (a:=a) (b:=b) (c:=1/8+0-1) (d:=-1+B-0) hu0 hu1
    (by have h:=h0 (1+0*s) (by simp) (0+B*s) (by simp); nlinarith)
    (by have h:=h1 (1+0*t) (by simp) (0+B*t) (by simp); nlinarith)
  have H02 := affine_le_of_endpoints (a:=a) (b:=b) (c:=1/8+1-1) (d:=-1+1-0) hu0 hu1
    (by have h:=h0 (1+0*s) (by simp) (1+1*s) (by simp); nlinarith)
    (by have h:=h1 (1+0*t) (by simp) (1+1*t) (by simp); nlinarith)
  have H10 := affine_le_of_endpoints (a:=a) (b:=b) (c:=1/8+5/4-0) (d:=-1+0-A) hu0 hu1
    (by have h:=h0 (0+A*s) (by simp) (5/4+0*s) (by simp); nlinarith)
    (by have h:=h1 (0+A*t) (by simp) (5/4+0*t) (by simp); nlinarith)
  have H11 := affine_le_of_endpoints (a:=a) (b:=b) (c:=1/8+0-0) (d:=-1+B-A) hu0 hu1
    (by have h:=h0 (0+A*s) (by simp) (0+B*s) (by simp); nlinarith)
    (by have h:=h1 (0+A*t) (by simp) (0+B*t) (by simp); nlinarith)
  have H12 := affine_le_of_endpoints (a:=a) (b:=b) (c:=1/8+1-0) (d:=-1+1-A) hu0 hu1
    (by have h:=h0 (0+A*s) (by simp) (1+1*s) (by simp); nlinarith)
    (by have h:=h1 (0+A*t) (by simp) (1+1*t) (by simp); nlinarith)
  have E0 := affine_le_of_endpoints (a:=a) (b:=b) (c:=5/4-9/8) (d:=0) hu0 hu1
    (by have h:=e0 (5/4+0*s) (by simp); nlinarith)
    (by have h:=e1 (5/4+0*t) (by simp); nlinarith)
  have E1 := affine_le_of_endpoints (a:=a) (b:=b) (c:=0-9/8) (d:=B) hu0 hu1
    (by have h:=e0 (0+B*s) (by simp); nlinarith)
    (by have h:=e1 (0+B*t) (by simp); nlinarith)
  have E2 := affine_le_of_endpoints (a:=a) (b:=b) (c:=1-9/8) (d:=1) hu0 hu1
    (by have h:=e0 (1+1*s) (by simp); nlinarith)
    (by have h:=e1 (1+1*t) (by simp); nlinarith)
  simp only [lowWitness, min_def, max_def]
  split_ifs <;> nlinarith

lemma ncWitness_bound {s t u a b A B : ℝ} (hu0 : s≤u) (hu1 : u≤t)
    (h0 : ∀aa∈[1,A*s],∀bb∈[5/4,B*s],a+b*s≤bb-aa-1/8)
    (h1 : ∀aa∈[1,A*t],∀bb∈[5/4,B*t],a+b*t≤bb-aa-1/8) : a+b*u≤ncWitness A B u := by
  have H00 := affine_le_of_endpoints (a:=a) (b:=b) (c:=5/4-1-1/8) (d:=0-0) hu0 hu1
    (by have h:=h0 (1+0*s) (by simp); have h:=h (5/4+0*s) (by simp); nlinarith)
    (by have h:=h1 (1+0*t) (by simp); have h:=h (5/4+0*t) (by simp); nlinarith)
  have H01 := affine_le_of_endpoints (a:=a) (b:=b) (c:=0-1-1/8) (d:=B-0) hu0 hu1
    (by have h:=h0 (1+0*s) (by simp); have h:=h (0+B*s) (by simp); nlinarith)
    (by have h:=h1 (1+0*t) (by simp); have h:=h (0+B*t) (by simp); nlinarith)
  have H10 := affine_le_of_endpoints (a:=a) (b:=b) (c:=5/4-0-1/8) (d:=0-A) hu0 hu1
    (by have h:=h0 (0+A*s) (by simp); have h:=h (5/4+0*s) (by simp); nlinarith)
    (by have h:=h1 (0+A*t) (by simp); have h:=h (5/4+0*t) (by simp); nlinarith)
  have H11 := affine_le_of_endpoints (a:=a) (b:=b) (c:=0-0-1/8) (d:=B-A) hu0 hu1
    (by have h:=h0 (0+A*s) (by simp); have h:=h (0+B*s) (by simp); nlinarith)
    (by have h:=h1 (0+A*t) (by simp); have h:=h (0+B*t) (by simp); nlinarith)
  simp only [ncWitness, min_def, max_def]
  split_ifs <;> nlinarith
end CatalanCore.Arith.Hybrid
