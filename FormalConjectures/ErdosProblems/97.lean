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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 97

*Reference:* [erdosproblems.com/97](https://www.erdosproblems.com/97)
-/

open EuclideanGeometry
open Real

namespace Erdos97

def HasNEquidistantPointsAt (n : ℕ) (A : Finset ℝ²) (p : ℝ²) : Prop :=
  ∃ r : ℝ, r > 0 ∧ (A.filter fun q ↦ dist p q = r).card ≥ n

def HasNEquidistantPointsOn (n : ℕ) (A : Finset ℝ²) (B : Finset ℝ²) : Prop :=
  ∀ p ∈ B, HasNEquidistantPointsAt n A p

def HasNEquidistantProperty (n : ℕ) (A : Finset ℝ²) : Prop :=
  HasNEquidistantPointsOn n A A

def HasNUnitDistanceProperty (n : ℕ) (A : Finset ℝ²) : Prop :=
  ∀ p ∈ A, (A.filter fun q ↦ dist p q = 1).card ≥ n

/--
Erdős originally conjectured this (in [Er46b]) with no 3 vertices equidistant,
but Danzer found a convex polygon on 9 points such that every vertex has three
vertices equidistant from it (but this distance depends on the vertex).
Danzer's construction is explained in [Er87b].

[Er46b] Erdős, P., _On sets of distances of $n$ points_. Amer. Math. Monthly (1946), 248-250.
[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive geometry (Siófok, 1985), 167-177.
-/
@[category research formally solved using formal_conjectures at "https://github.com/theaustinhatfield/formal-conjectures/blob/solve-erdos-97-danzer/FormalConjectures/ErdosProblems/97.lean", AMS 52]
theorem erdos_97.variants.three_equidistant :
    ∃ A : Finset ℝ², A.Nonempty ∧ ConvexIndep A ∧ HasNEquidistantProperty 3 A := by
  sorry

/--
Erdős also conjectured that there is a $k$ for which every convex polygon has a vertex
with no other $k$ vertices equidistant from it.
-/
@[category research open, AMS 52]
theorem erdos_97.variants.k_equidistant : answer(sorry) ↔
    ∃ k : ℕ, ∀ A : Finset ℝ², A.Nonempty → ConvexIndep A → ¬HasNEquidistantProperty k A := by
  sorry

/--
Fishburn and Reeds [FiRe92] have found a convex polygon on 20 points such that
every vertex has three vertices equidistant from it (and this distance is the same for all vertices).

[FiRe92] Fishburn, P. C. and Reeds, J. A., _Unit distances between vertices of a convex polygon_. Comput. Geom. (1992), 81-91.
-/
@[category research solved, AMS 52]
theorem erdos_97.variants.three_unit_distance :
    ∃ A : Finset ℝ², A.Nonempty ∧ ConvexIndep A ∧ HasNUnitDistanceProperty 3 A := by
  sorry

/--
A two-part partition $\{A, B\}$ of $V$ is a cut if the convex hulls of $A$ and $B$ are disjoint.
-/
def IsCut (V A B : Finset ℝ²) : Prop :=
  A ∪ B = V ∧ Disjoint A B ∧
  Disjoint (convexHull ℝ (A : Set ℝ²)) (convexHull ℝ (B : Set ℝ²))

/--
The number of possible cuts of $V$ into two subsets $A$ and $B$ is known to be exactly $n(n-1)/2 + 1$
when $V$ is in general position.
-/
def HasCorrectNumberOfCuts (V : Finset ℝ²) : Prop :=
  let cuts := (V.powerset.filter (fun A ↦ IsCut V A (V \ A))).card
  cuts = V.card * (V.card - 1) + 2 -- We count (A, B) and (B, A) as separate.

/--
A set of $n$ points is convex independent if it has exactly $2^n$ cuts.
-/
@[category research solved, AMS 52]
theorem erdos_97 :
    answer(sorry) ↔ ∀ A : Finset ℝ², A.Nonempty → ConvexIndep A → ¬HasNEquidistantProperty 4 A := by
  sorry

end Erdos97
