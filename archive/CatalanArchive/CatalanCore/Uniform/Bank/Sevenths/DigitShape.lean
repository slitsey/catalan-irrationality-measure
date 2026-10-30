import CatalanCore.Uniform.Content.RankProducer.Geometry
import CatalanCore.Uniform.Bank.Sevenths.Rounding
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Uniform.Content.RankProducer.Geometry

theorem rowDigit_lt_seven {r m p x d : ℕ} (hround : 12 * m ≤ r + 6)
    (hrp : r ≤ 6 * p) (hx : 4 ≤ x) (h : rowDigit r m p x d) : d < 7 :=
  rowDigit_lt (by omega) h

theorem colDigit_lt_seven {r m p x d : ℕ} (hround : 12 * m ≤ r + 6)
    (hrp : r ≤ 6 * p) (hx : 4 ≤ x) (h : colDigit r m p x d) : d < 7 :=
  colDigit_lt (by omega) h

#print axioms rowDigit_lt_seven
end CatalanCore.Uniform.Bank.Sevenths
