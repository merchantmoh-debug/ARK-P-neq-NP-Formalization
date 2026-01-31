
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Real

/-- 
  Bound on `exp 1`. 
  This is a missing numerical bound in Mathlib's SpecialFunctions.Exp.
  Useful for asymptotic comparisons (e.g., n^k vs e^n).
-/
lemma two_le_exp_one : 2 ≤ exp 1 := by
  have h1 : (2 : ℝ) = 1 + 1 := by norm_num
  rw [h1]
  exact add_one_le_exp 1

/-- 
  Bound on `log 1000`. Useful for large-n complexity thresholds. 
  Proof relies on 1000 < 1024 = 2^10 <= e^10.
-/
lemma log_1000_lt_10 : log 1000 < 10 := by
  rw [log_lt_iff_lt_exp (by norm_num)]
  calc (1000 : ℝ) < (2 : ℝ) ^ 10 := by norm_num
    _ ≤ (exp 1) ^ 10 := by 
      gcongr
      exact two_le_exp_one
    _ = exp 10 := by rw [←exp_nat_mul]; norm_num

end Real
