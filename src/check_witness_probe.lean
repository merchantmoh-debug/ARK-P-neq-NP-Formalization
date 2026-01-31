import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Probe 1: Signature of contDiff_apply
#check @contDiff_apply

-- Probe 2: EuclideanSpace coercion
abbrev E3 := EuclideanSpace ℝ (Fin 3)
#check (fun _ => 1 : E3)
#check (fun (i:Fin 3) => (1:ℝ))
