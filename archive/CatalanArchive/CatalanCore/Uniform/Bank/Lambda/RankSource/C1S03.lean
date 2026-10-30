import CatalanCore.Uniform.Bank.Lambda.DigitShape
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankSource

def C1S03_run0_Rset : Finset ℕ := {0, 1, 2, 3, 4}

theorem C1S03_run0_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C1S03_run0_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C1S03_run0_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run0_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C1S03_run0_Rset] at * <;> omega

def C1S03_run0_Cset : Finset ℕ := {0, 1, 2, 3, 4}

theorem C1S03_run0_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C1S03_run0_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C1S03_run0_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run0_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C1S03_run0_Cset] at * <;> omega

theorem C1S03_run0_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 1 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C1S03_run1_Rset : Finset ℕ := {0, 1, 2, 3, 4}

theorem C1S03_run1_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C1S03_run1_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C1S03_run1_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run1_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C1S03_run1_Rset] at * <;> omega

def C1S03_run1_Cset : Finset ℕ := {0, 1, 2, 3, 4}

theorem C1S03_run1_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C1S03_run1_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C1S03_run1_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run1_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C1S03_run1_Cset] at * <;> omega

theorem C1S03_run1_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 1 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C1S03_run2_Rset : Finset ℕ := {0, 1, 2, 3, 4}

theorem C1S03_run2_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-4 : ℤ) * p + 4)
    (hhi : (4 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C1S03_run2_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C1S03_run2_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run2_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C1S03_run2_Rset] at * <;> omega

def C1S03_run2_Cset : Finset ℕ := {0, 1, 2, 3}

theorem C1S03_run2_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-4 : ℤ) * p + 4)
    (hhi : (4 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C1S03_run2_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C1S03_run2_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run2_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C1S03_run2_Cset] at * <;> omega

theorem C1S03_run2_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-4 : ℤ) * p + 4)
    (hhi : (4 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 1 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C1S03_run3_Rset : Finset ℕ := {0, 1, 2, 3}

theorem C1S03_run3_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-4 : ℤ) * p + 4)
    (hhi : (4 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C1S03_run3_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C1S03_run3_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run3_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C1S03_run3_Rset] at * <;> omega

def C1S03_run3_Cset : Finset ℕ := {0, 1, 2, 3, 4}

theorem C1S03_run3_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-4 : ℤ) * p + 4)
    (hhi : (4 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C1S03_run3_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C1S03_run3_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run3_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C1S03_run3_Cset] at * <;> omega

theorem C1S03_run3_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-4 : ℤ) * p + 4)
    (hhi : (4 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 1 * p) :
    (if k < x then 1 else 0) = 0 := by
  split_ifs <;> omega

def C1S03_run4_Rset : Finset ℕ := {0, 1, 2, 3, 4}

theorem C1S03_run4_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (4 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 16)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (-20 : ℤ) * p - 20) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C1S03_run4_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C1S03_run4_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run4_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C1S03_run4_Rset] at * <;> omega

def C1S03_run4_Cset : Finset ℕ := {0, 1, 2, 3}

theorem C1S03_run4_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (4 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 16)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (-20 : ℤ) * p - 20) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C1S03_run4_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C1S03_run4_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run4_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C1S03_run4_Cset] at * <;> omega

theorem C1S03_run4_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (4 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 16)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (-20 : ℤ) * p - 20)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 1 * p) :
    (if k < x then 1 else 0) = 1 := by
  split_ifs <;> omega

def C1S03_run5_Rset : Finset ℕ := {0, 1, 2, 3}

theorem C1S03_run5_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (4 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 16)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (-20 : ℤ) * p - 20) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C1S03_run5_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C1S03_run5_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run5_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C1S03_run5_Rset] at * <;> omega

def C1S03_run5_Cset : Finset ℕ := {0, 1, 2, 3, 4}

theorem C1S03_run5_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (4 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 16)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (-20 : ℤ) * p - 20) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C1S03_run5_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C1S03_run5_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run5_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C1S03_run5_Cset] at * <;> omega

theorem C1S03_run5_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (4 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 16)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (-20 : ℤ) * p - 20)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 1 * p) :
    (if k < x then 1 else 0) = 1 := by
  split_ifs <;> omega

def C1S03_run6_Rset : Finset ℕ := {0, 1, 2, 3}

theorem C1S03_run6_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (5 : ℤ) * x ≥ (6 : ℤ) * r + (-20 : ℤ) * p + 20)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C1S03_run6_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C1S03_run6_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run6_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C1S03_run6_Rset] at * <;> omega

def C1S03_run6_Cset : Finset ℕ := {0, 1, 2, 3}

theorem C1S03_run6_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (5 : ℤ) * x ≥ (6 : ℤ) * r + (-20 : ℤ) * p + 20)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C1S03_run6_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C1S03_run6_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run6_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C1S03_run6_Cset] at * <;> omega

theorem C1S03_run6_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (5 : ℤ) * x ≥ (6 : ℤ) * r + (-20 : ℤ) * p + 20)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 1 * p) :
    (if k < x then 1 else 0) = 1 := by
  split_ifs <;> omega

def C1S03_run7_Rset : Finset ℕ := {0, 1, 2, 3}

theorem C1S03_run7_R (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (5 : ℤ) * x ≥ (6 : ℤ) * r + (-20 : ℤ) * p + 20)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4) :
    ∀ d : ℕ, rowDigit r m p x d ↔ d ∈ C1S03_run7_Rset := by
  intro d
  constructor
  · intro h
    have hd := rowDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [rowDigit, C1S03_run7_Rset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run7_Rset] at h; omega
    interval_cases d <;> norm_num [rowDigit, C1S03_run7_Rset] at * <;> omega

def C1S03_run7_Cset : Finset ℕ := {0, 1, 2, 3}

theorem C1S03_run7_C (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (5 : ℤ) * x ≥ (6 : ℤ) * r + (-20 : ℤ) * p + 20)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4) :
    ∀ d : ℕ, colDigit r m p x d ↔ d ∈ C1S03_run7_Cset := by
  intro d
  constructor
  · intro h
    have hd := colDigit_lt_six hm1 hrp hx h
    interval_cases d <;> norm_num [colDigit, C1S03_run7_Cset] at * <;> omega
  · intro h
    have hd : d < 6 := by norm_num [C1S03_run7_Cset] at h; omega
    interval_cases d <;> norm_num [colDigit, C1S03_run7_Cset] at * <;> omega

theorem C1S03_run7_bit (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 6 * r ≤ 25 * p)
    (hright : 4 * p ≤ 1 * r)
    (hlo : (5 : ℤ) * x ≥ (6 : ℤ) * r + (-20 : ℤ) * p + 20)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (a k : ℕ) (ha : a = 1 ∨ a = 3) (hk : 4 * k + a = 1 * p) :
    (if k < x then 1 else 0) = 1 := by
  split_ifs <;> omega
end CatalanCore.Uniform.Bank.Lambda.RankSource
