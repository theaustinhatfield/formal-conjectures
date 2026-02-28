/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 100

*Reference:* [erdosproblems.com/100](https://www.erdosproblems.com/100)

* [Guth and Katz](https://arxiv.org/abs/1011.4105)
* [Piepmeyer](No references found)
-/

open Set Metric Filter Real
open scoped EuclideanGeometry

namespace Erdos100

/-- Distances determined by a set of points. -/
def Distances (A : Finset ℝ²) : Finset ℝ :=
  (A ×ˢ A).image fun p => dist p.1 p.2

/--
Every real number strictly between 0 and `diam A`
appears exactly once as a distance between two points in A.
-/
def DistancesSeparated (A : Finset ℝ²) : Prop :=
  ∀ d, 0 < d → d < diam (A : Set ℝ²) →
    ∃! p : ℝ² × ℝ², p.1 ∈ A ∧ p.2 ∈ A ∧ dist p.1 p.2 = d

/--
Does every set of $n$ points in $\mathbb{R}^2$ determine
$\gg n / \log n$ distinct distances?

(Guth and Katz [GuKa15] proved this.)
-/
@[category research solved, AMS 52]
theorem erdos_100_guth_katz :
    ∃ C > 0, ∀ᶠ n in atTop,
    ∀ A : Finset ℝ², A.card = n →
      diam (A : Set ℝ²) ≥ C * n / log n := by
  sorry

/-- From [Piepmeyer]: 9 points with diameter $< 5$.
TODO: find reference -/
@[category research formally solved using formal_conjectures at "https://github.com/theaustinhatfield/formal-conjectures/blob/solve-erdos-100-piepmeyer/FormalConjectures/ErdosProblems/100.lean", AMS 52]
theorem erdos_100_piepmeyer :
    ∃ A : Finset ℝ², A.card = 9 ∧ DistancesSeparated A ∧
      diam (A : Set ℝ²) < 5 := by
  sorry

end Erdos100
