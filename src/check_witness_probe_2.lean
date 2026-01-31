import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

#check WithLp.equiv
#check WithLp.toLp
#print WithLp

-- Check for any lemma that unifies WithLp application
#check Two < Real.exp 1 -- invalid syntax, but looking for logic
example : 2 < Real.exp 1 := by
  have : 2.7 < Real.exp 1 := Real.exp_one_gt_d9
  linarith
