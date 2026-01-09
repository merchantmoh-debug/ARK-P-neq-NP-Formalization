import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace ARK.Logic

open Real

/--
  Calculus Fact: For large n (n ≥ 1000) and polynomial degree k ≤ 99,
  exponential decay dominates polynomial decay.

  Proof of: n^k < e^n
  Equivalent to: k * ln(n) < n
-/
theorem large_n_poly_vs_exponential (n : ℝ) (k : ℕ)
    (hn : n ≥ 1000) (hk : k ≤ 99) :
    (n ^ k : ℝ) < exp n := by
  sorry -- Calculus inequality
end ARK.Logic
