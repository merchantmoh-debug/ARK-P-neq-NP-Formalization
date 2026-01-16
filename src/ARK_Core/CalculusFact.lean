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
  have h_n_pos : 0 < n := by linarith
  have h_nk_pos : 0 < n ^ k := pow_pos h_n_pos k
  rw [← log_lt_iff_lt_exp h_nk_pos]
  rw [log_pow]

  -- Define f(x) = x - k * log x
  let f := fun (x : ℝ) => x - k * log x

  have h_diff_log : ∀ x, x ≥ 1000 → DifferentiableAt ℝ log x := by
    intro x hx
    have : x ≠ 0 := by linarith
    apply DifferentiableAt.log
    exact differentiableAt_id
    exact this

  have h_diff_term2 : ∀ x, x ≥ 1000 → DifferentiableAt ℝ (fun x => (k : ℝ) * log x) x := by
    intro x hx; apply DifferentiableAt.const_mul; apply h_diff_log x hx

  have h_deriv : ∀ x, x ≥ 1000 → deriv f x > 0 := by
    intro x hx
    have hx_pos : 0 < x := by linarith
    dsimp [f]
    change deriv (id - (fun x => (k : ℝ) * log x)) x > 0
    rw [deriv_sub differentiableAt_id (h_diff_term2 x hx)]
    rw [deriv_id, deriv_const_mul (k:ℝ) (h_diff_log x hx)]
    rw [deriv_log x]
    simp
    rw [← div_eq_mul_inv, div_lt_one hx_pos]
    calc (k : ℝ) ≤ 99 := Nat.cast_le.mpr hk
      _ < 1000 := by norm_num
      _ ≤ x := hx

  have h_mono : StrictMonoOn f (Set.Ici 1000) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1000)
    · apply ContinuousOn.sub continuousOn_id
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log continuousOn_id
      intro x hx
      simp at hx
      have : x ≠ 0 := by linarith
      exact this
    · intro x hx
      simp at hx
      apply h_deriv x (le_of_lt hx)

  -- f(n) >= f(1000)
  have h_mem : (1000 : ℝ) ∈ Set.Ici (1000 : ℝ) := le_refl (1000 : ℝ)
  have f_ge_f1000 : f 1000 ≤ f n := h_mono.monotoneOn h_mem hn hn

  -- Prove f(1000) > 0
  have f1000_pos : 0 < f 1000 := by
    dsimp [f]
    rw [sub_pos]
    have log_1000_lt_7 : log 1000 < 7 := by
      rw [log_lt_iff_lt_exp (by norm_num)]
      have h1 : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have h2 : (2.7 : ℝ) ^ 7 < (exp 1) ^ 7 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
      have h3 : (1000 : ℝ) < (2.7 : ℝ) ^ 7 := by norm_num
      have h4 : (1000 : ℝ) < (exp 1) ^ 7 := lt_trans h3 h2
      rw [← exp_nat_mul (1:ℝ) 7] at h4
      simp at h4
      exact h4

    calc (k : ℝ) * log 1000 ≤ 99 * log 1000 := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (log_nonneg (by norm_num))
        _ < 99 * 7 := mul_lt_mul_of_pos_left log_1000_lt_7 (by norm_num)
        _ = 693 := by norm_num
        _ < 1000 := by norm_num

  have f_n_pos : 0 < f n := lt_of_lt_of_le f1000_pos f_ge_f1000

  dsimp [f] at f_n_pos
  rw [sub_pos] at f_n_pos
  exact f_n_pos

end ARK.Logic
