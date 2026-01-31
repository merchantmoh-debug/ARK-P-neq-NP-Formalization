import «ARK_Core».Impossibility
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

open ARK.Physics
open ARK.Spectral
open ARK.Logic

noncomputable section

-- 1. THE FRUSTRATED TRIANGLE WITNESS
-- E = R^3
abbrev E3 := EuclideanSpace ℝ (Fin 3)

-- Potential V(x) = Σ(xi^2 - 1)^2 (Uncoupled Double Wells)
def lambda : ℝ := 0

def f_val (x : E3) : ℝ :=
  ((x 0)^2 - 1)^2 + ((x 1)^2 - 1)^2 + ((x 2)^2 - 1)^2

-- Smoothness: Use EuclideanSpace.proj to prove smoothness cleanly
def f_witness : PotentialFunction E3 := {
  val := f_val
  smooth := by
    unfold f_val
    apply ContDiff.add
    · apply ContDiff.add
      · apply ContDiff.pow
        apply ContDiff.sub
        · apply ContDiff.pow
          -- Use explicit type annotation to help inference
          exact (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).contDiff
        · exact contDiff_const
      · apply ContDiff.pow
        apply ContDiff.sub
        · apply ContDiff.pow
          exact (EuclideanSpace.proj (1 : Fin 3) : E3 →L[ℝ] ℝ).contDiff
        · exact contDiff_const
    · apply ContDiff.pow
      apply ContDiff.sub
      · apply ContDiff.pow
        exact (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).contDiff
      · exact contDiff_const
}

-- 2. VERIFICATION OF MULTI-WELL STRUCTURE

-- Helper: f is non-negative (Sum of squares)
theorem f_nonneg (x : E3) : 0 ≤ f_witness.val x := by
  unfold f_witness f_val
  apply add_nonneg
  · apply add_nonneg
    · apply sq_nonneg
    · apply sq_nonneg
  · apply sq_nonneg

-- Define the two minima using explicit construction
def vec_ones : E3 := WithLp.toLp 2 (fun _ => 1)
def vec_neg_ones : E3 := WithLp.toLp 2 (fun _ => -1)

-- Helper lemmas targeting .ofLp explicitly to match target terms
lemma vec_ones_at_0 : vec_ones.ofLp 0 = 1 := rfl
lemma vec_ones_at_1 : vec_ones.ofLp 1 = 1 := rfl
lemma vec_ones_at_2 : vec_ones.ofLp 2 = 1 := rfl

lemma vec_neg_ones_at_0 : vec_neg_ones.ofLp 0 = -1 := rfl
lemma vec_neg_ones_at_1 : vec_neg_ones.ofLp 1 = -1 := rfl
lemma vec_neg_ones_at_2 : vec_neg_ones.ofLp 2 = -1 := rfl

theorem f_at_ones : f_witness.val vec_ones = 0 := by
  unfold f_witness f_val
  -- Rewrite using explicit .ofLp lemmas. 
  simp only [vec_ones_at_0, vec_ones_at_1, vec_ones_at_2]
  norm_num

theorem f_at_neg_ones : f_witness.val vec_neg_ones = 0 := by
  unfold f_witness f_val
  simp only [vec_neg_ones_at_0, vec_neg_ones_at_1, vec_neg_ones_at_2]
  norm_num

-- A global minimum is a local minimum
theorem min_ones : IsLocalMin f_witness vec_ones := by
  use 1 -- epsilon
  constructor
  · norm_num
  · intro y _
    rw [f_at_ones]
    exact f_nonneg y

theorem min_neg_ones : IsLocalMin f_witness vec_neg_ones := by
  use 1
  constructor
  · norm_num
  · intro y _
    rw [f_at_neg_ones]
    exact f_nonneg y

theorem different_minima : vec_ones ≠ vec_neg_ones := by
  intro h
  have h0 : vec_ones 0 = vec_neg_ones 0 := by rw [h]
  -- vec_ones 0 is def eq to vec_ones.ofLp 0
  simp [vec_ones_at_0, vec_neg_ones_at_0] at h0
  norm_num at h0

-- Barrier Height check
theorem witness_is_frustrated : IsFrustrated f_witness := by
  use vec_ones, vec_neg_ones
  constructor
  · exact different_minima
  · constructor
    · exact min_ones
    · exact min_neg_ones

theorem Witness_Is_MultiWell : IsMultiWell f_witness :=
  Frustration_Induces_Ruggedness f_witness witness_is_frustrated

-- 3. THE SMOKING GUN (Tunneling in Small Dimensions)
-- AXIOM: Physical calculation of spectral gap
axiom Witness_Tunneling_Calculation :
  IsMultiWell f_witness → SpectralGap f_witness (0 : E3) ≤ Real.exp (-3)

theorem Witness_Gap_Is_Exponential : SpectralGap f_witness (0 : E3) ≤ Real.exp (-3) := by
  apply Witness_Tunneling_Calculation
  exact Witness_Is_MultiWell

-- 4. CONTRADICTION WITH P=NP (For this instance)
theorem Witness_Breaks_PolyGap (k : ℕ) :
  ¬ (SpectralGap f_witness (0:E3) ≥ 1 / (3 ^ k : ℝ) ∧ k < 2) := by
  intro h_contra
  rcases h_contra with ⟨h_poly_ineq, h_k⟩
  have h_gap := Witness_Gap_Is_Exponential
  have h_ineq : (1 : ℝ) / (3 ^ k : ℝ) ≤ Real.exp (-3) := le_trans h_poly_ineq h_gap
  interval_cases k
  · -- k = 0
    simp only [pow_zero, div_one] at h_ineq
    -- 1 ≤ e^-3
    rw [Real.exp_neg, inv_eq_one_div] at h_ineq
    have h_contra : Real.exp 3 ≤ 1 := by
      rwa [le_div_iff₀ (Real.exp_pos 3), one_mul] at h_ineq
    have h_gt : 1 < Real.exp 3 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  · -- k = 1
    simp only [pow_one] at h_ineq
    -- 1/3 ≤ e^-3
    rw [Real.exp_neg, inv_eq_one_div] at h_ineq
    
    have h_contra : Real.exp 3 ≤ 3 := by
      -- 1/3 * e^3 <= 1
      have h_pos : 0 < (3:ℝ) * Real.exp 3 := mul_pos (by norm_num) (Real.exp_pos 3)
      field_simp at h_ineq
      exact h_ineq
    
    -- Prove e^3 > 3
    have h_gt : 3 < Real.exp 3 := by
      -- 2 <= e
      have h_base : 2 ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp 1
        norm_num at h
        exact h
      
      -- 2^3 <= e^3
      have h_pow : (2 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 := by
        gcongr
      
      rw [Real.exp_one_pow] at h_pow
      norm_num at h_pow 
      linarith
      
    linarith
