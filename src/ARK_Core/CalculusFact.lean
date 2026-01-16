import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum

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
  have n_pos : 0 < n := by linarith
  have log_n_pos : 0 < log n := log_pos (by linarith)

  -- 1. Convert to log scale: n^k < e^n ↔ k * log n < n
  rw [← rpow_natCast, rpow_def_of_pos n_pos, exp_lt_exp]
  rw [mul_comm]

  -- 2. Bound k by 99: It suffices to prove 99 * log n < n
  -- We prove n - 99 * log n > 0

  -- 3. Define f(x) = x - 99 * log x
  let f (x : ℝ) := x - 99 * log x

  -- 4. Show f is strictly increasing for x ≥ 1000
  have f_strict_mono : StrictMonoOn f (Set.Ici 1000) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1000)
    · apply ContinuousOn.sub continuousOn_id
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log continuousOn_id
      intro x hx
      dsimp
      have : 1000 ≤ x := hx
      linarith
    · intro x hx
      rw [interior_Ici] at hx
      have : 1000 < x := hx
      have x_pos : 0 < x := by linarith
      have x_ne_zero : x ≠ 0 := ne_of_gt x_pos
      dsimp [f]
      have diff_1 : DifferentiableAt ℝ id x := differentiableAt_id
      have diff_2 : DifferentiableAt ℝ (fun y => 99 * log y) x := (differentiableAt_log x_ne_zero).const_mul 99
      -- Ensure we match deriv_sub pattern
      change 0 < deriv (id - fun y => 99 * log y) x
      rw [deriv_sub diff_1 diff_2]
      rw [deriv_id]
      -- Use explicit named arguments
      rw [deriv_const_mul (hd := differentiableAt_log x_ne_zero) (c := 99)]
      rw [deriv_log x]
      rw [← div_eq_mul_inv]
      rw [lt_sub_iff_add_lt, zero_add, div_lt_one x_pos]
      linarith

  -- 5. Show f(1000) > 0
  have f_1000_pos : 0 < f 1000 := by
    dsimp [f]
    rw [sub_pos]
    have log_1000_bound : log 1000 < 7 := by
      rw [← exp_lt_exp, exp_log (by norm_num)]
      -- Need 1000 < e^7.
      have e_gt : (2.718 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have e7_gt_rpow : (2.718 : ℝ) ^ (7 : ℝ) < exp 7 := by
        rw [← Real.exp_one_rpow 7]
        apply Real.rpow_lt_rpow (by norm_num) e_gt (by norm_num)
      have e7_gt : (2.718 : ℝ) ^ 7 < exp 7 := by
        -- Manually cast 7 to Nat
        rw [(by norm_num : (7 : ℝ) = (7 : ℕ)), Real.rpow_natCast] at e7_gt_rpow
        exact e7_gt_rpow
      have : (1000 : ℝ) < 2.718 ^ 7 := by
         norm_num
      apply lt_trans this e7_gt
    linarith

  -- 6. Conclusion: f(n) > 0 implies n > 99 * log n
  have f_n_pos : 0 < f n := by
    rcases lt_or_eq_of_le hn with h_lt | h_eq
    · apply lt_trans f_1000_pos
      apply f_strict_mono (Set.mem_Ici.mpr (le_refl 1000)) hn h_lt
    · rw [← h_eq]
      exact f_1000_pos

  dsimp [f] at f_n_pos
  rw [sub_pos] at f_n_pos
  -- f_n_pos : 99 * log n < n

  calc
    (k : ℝ) * log n ≤ 99 * log n := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (le_of_lt log_n_pos)
    _ < n := f_n_pos

end ARK.Logic
