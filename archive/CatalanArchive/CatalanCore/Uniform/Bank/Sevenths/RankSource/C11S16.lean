import CatalanCore.Uniform.Bank.Sevenths.DigitShape
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankSource
open CatalanCore.Uniform.Content.RankProducer.Geometry

def C11S16_run0_Rset : Finset ℕ := {0, 1, 2}

theorem C11S16_run0_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-12 : ℤ) * p - 24) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C11S16_run0_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C11S16_run0_Rset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run0_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C11S16_run0_Rset] at * <;> omega

def C11S16_run0_Cset : Finset ℕ := {0, 1}

theorem C11S16_run0_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-12 : ℤ) * p - 24) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C11S16_run0_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C11S16_run0_Cset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run0_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C11S16_run0_Cset] at * <;> omega

theorem C11S16_run0_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-12 : ℤ) * p - 24)
    (a k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : 7 * k + a = 2 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C11S16_run1_Rset : Finset ℕ := {0, 1}

theorem C11S16_run1_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-12 : ℤ) * p - 24) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C11S16_run1_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C11S16_run1_Rset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run1_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C11S16_run1_Rset] at * <;> omega

def C11S16_run1_Cset : Finset ℕ := {0, 1, 2}

theorem C11S16_run1_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-12 : ℤ) * p - 24) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C11S16_run1_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C11S16_run1_Cset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run1_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C11S16_run1_Cset] at * <;> omega

theorem C11S16_run1_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-12 : ℤ) * p - 24)
    (a k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : 7 * k + a = 2 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C11S16_run2_Rset : Finset ℕ := {0, 1}

theorem C11S16_run2_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-12 : ℤ) * p + 24)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (2 : ℤ) * p - 28) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C11S16_run2_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C11S16_run2_Rset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run2_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C11S16_run2_Rset] at * <;> omega

def C11S16_run2_Cset : Finset ℕ := {0, 1}

theorem C11S16_run2_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-12 : ℤ) * p + 24)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (2 : ℤ) * p - 28) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C11S16_run2_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C11S16_run2_Cset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run2_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C11S16_run2_Cset] at * <;> omega

theorem C11S16_run2_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-12 : ℤ) * p + 24)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (2 : ℤ) * p - 28)
    (a k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : 7 * k + a = 2 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C11S16_run3_Rset : Finset ℕ := {0, 1}

theorem C11S16_run3_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-12 : ℤ) * p + 24)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (2 : ℤ) * p - 28) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C11S16_run3_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C11S16_run3_Rset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run3_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C11S16_run3_Rset] at * <;> omega

def C11S16_run3_Cset : Finset ℕ := {0, 1}

theorem C11S16_run3_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-12 : ℤ) * p + 24)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (2 : ℤ) * p - 28) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C11S16_run3_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C11S16_run3_Cset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run3_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C11S16_run3_Cset] at * <;> omega

theorem C11S16_run3_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-12 : ℤ) * p + 24)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (2 : ℤ) * p - 28)
    (a k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : 7 * k + a = 2 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C11S16_run4_Rset : Finset ℕ := {0, 1}

theorem C11S16_run4_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (2 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-1 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C11S16_run4_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C11S16_run4_Rset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run4_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C11S16_run4_Rset] at * <;> omega

def C11S16_run4_Cset : Finset ℕ := {0, 1}

theorem C11S16_run4_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (2 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-1 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C11S16_run4_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C11S16_run4_Cset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run4_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C11S16_run4_Cset] at * <;> omega

theorem C11S16_run4_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (2 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-1 : ℤ) * p - 4)
    (a k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : 7 * k + a = 2 * p) :
    (if k < x then 1 else 0) = 1 := by
  split_ifs <;> omega

def C11S16_run5_Rset : Finset ℕ := {0, 1}

theorem C11S16_run5_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (2 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-1 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C11S16_run5_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C11S16_run5_Rset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run5_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C11S16_run5_Rset] at * <;> omega

def C11S16_run5_Cset : Finset ℕ := {0, 1}

theorem C11S16_run5_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (2 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-1 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C11S16_run5_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C11S16_run5_Cset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run5_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C11S16_run5_Cset] at * <;> omega

theorem C11S16_run5_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (2 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-1 : ℤ) * p - 4)
    (a k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : 7 * k + a = 2 * p) :
    (if k < x then 1 else 0) = 1 := by
  split_ifs <;> omega

def C11S16_run6_Rset : Finset ℕ := {0}

theorem C11S16_run6_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-1 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C11S16_run6_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C11S16_run6_Rset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run6_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C11S16_run6_Rset] at * <;> omega

def C11S16_run6_Cset : Finset ℕ := {0, 1}

theorem C11S16_run6_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-1 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C11S16_run6_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C11S16_run6_Cset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run6_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C11S16_run6_Cset] at * <;> omega

theorem C11S16_run6_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-1 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (a k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : 7 * k + a = 2 * p) :
    (if k < x then 1 else 0) = 1 := by
  split_ifs <;> omega

def C11S16_run7_Rset : Finset ℕ := {0, 1}

theorem C11S16_run7_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-1 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C11S16_run7_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C11S16_run7_Rset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run7_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C11S16_run7_Rset] at * <;> omega

def C11S16_run7_Cset : Finset ℕ := {0}

theorem C11S16_run7_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-1 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C11S16_run7_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C11S16_run7_Cset] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [C11S16_run7_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C11S16_run7_Cset] at * <;> omega

theorem C11S16_run7_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 49 * r ≤ 96 * p)
    (hright : 12 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-1 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (a k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : 7 * k + a = 2 * p) :
    (if k < x then 1 else 0) = 1 := by
  split_ifs <;> omega
end CatalanCore.Uniform.Bank.Sevenths.RankSource
