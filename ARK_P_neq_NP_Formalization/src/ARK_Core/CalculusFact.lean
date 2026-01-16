import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Basic

namespace ARK.Logic

open Real

theorem large_n_poly_vs_exponential (n : ℝ) (k : ℕ)
    (hn : n ≥ 1000) (hk : k ≤ 99) :
    (n ^ k : ℝ) < exp n := by

  -- Case k = 0
  by_cases hk0 : k = 0
  · rw [hk0, pow_zero]
    exact one_lt_exp_iff.mpr (lt_of_lt_of_le (by norm_num) hn)
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0

  -- Equivalence: n^k < e^n <-> k log n < n
  rw [← log_lt_iff_lt_exp (pow_pos (lt_of_lt_of_le (by norm_num) hn) _)]
  rw [log_pow]

  -- Function g(x) = x - k log x
  let g := fun (x : ℝ) => x - (k : ℝ) * log x

  -- We want g(n) > 0.
  -- 1. Bound log 1000 < 10
  have h_log_bound : log 1000 < 10 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    sorry -- calculation

  -- 2. Check g(1000) > 0
  have g_1000_pos : g 1000 > 0 := by
    dsimp [g]
    suffices (k : ℝ) * log 1000 < 1000 by linarith
    calc
      (k : ℝ) * log 1000 ≤ 99 * log 1000 := mul_le_mul_of_nonneg_right (by norm_cast) (log_nonneg (by norm_num))
      _ < 99 * 10 := mul_lt_mul_of_pos_left h_log_bound (by norm_num)
      _ = 990 := by norm_num
      _ < 1000 := by norm_num

  -- 3. Monotonicity: g is strictly increasing on [1000, ∞)
  -- deriv g(x) = 1 - k/x
  have g_mono : StrictMonoOn g (Set.Ici 1000) := by
    sorry -- missing StrictMonoOn lemma

  -- 4. Conclusion
  -- If n = 1000, g(n) > 0. If n > 1000, g(n) > g(1000) > 0.
  -- Goal is n^k < exp n, which we transformed?
  -- Wait, log_lt_iff_lt_exp transformed the goal to log (n^k) < n
  -- rw [log_pow] -> k * log n < n
  -- g n = n - k * log n.
  -- So goal is 0 < g n (or g n > 0).
  have h_goal : 0 < g n := by
    cases le_iff_eq_or_lt.mp hn with
    | inl h_eq =>
        rw [← h_eq]
        exact g_1000_pos
    | inr h_lt =>
        apply lt_trans g_1000_pos
        apply g_mono
        · exact Set.self_mem_Ici
        · exact hn
        · exact h_lt

  dsimp [g] at h_goal
  linarith
end ARK.Logic
