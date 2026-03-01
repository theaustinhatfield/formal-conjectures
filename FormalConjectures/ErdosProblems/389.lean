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
# Erdős Problem 389

*Reference:* [erdosproblems.com/389](https://www.erdosproblems.com/389)
-/

namespace Erdos389

/--
Is it true that for every $n \geq 1$ there is a $k$ such that
$$
  n(n + 1) \cdots (n + k - 1) \mid (n + k) \cdots (n + 2k - 1)?
$$
-/
@[category research open, AMS 11]
theorem erdos_389 : answer(sorry) ↔
    ∀ n ≥ 1, ∃ k ≥ 1, ∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k, (n + k + i) := by
  sorry

open Nat Finset

def my_prod (n k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | k' + 1 => my_prod n k' * (n + k')

lemma my_prod_eq_prod (n k : ℕ) : my_prod n k = ∏ i ∈ Finset.range k, (n + i) := by
  induction k with
  | zero => simp [my_prod]
  | succ k' ih => rw [my_prod, ih, Finset.prod_range_succ]

def check_div_fast (n k : ℕ) : Bool :=
  (my_prod (n + k) k) % (my_prod n k) == 0

lemma check_div_fast_eq (n k : ℕ) : check_div_fast n k = true ↔ ∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k, (n + k + i) := by
  rw [← my_prod_eq_prod n k, ← my_prod_eq_prod (n + k) k]
  unfold check_div_fast
  simp [Nat.dvd_iff_mod_eq_zero]

def all_false (n : ℕ) (k_max : ℕ) : Bool :=
  (List.range k_max).all fun k =>
    if k = 0 then true else check_div_fast n k == false

lemma all_false_implies (n k_max : ℕ) (h : all_false n k_max = true) :
    ∀ k, 1 ≤ k → k < k_max → check_div_fast n k = false := by
  intro k hk1 hk2
  have h1 : (List.range k_max).all (fun k => if k = 0 then true else check_div_fast n k == false) = true := h
  rw [List.all_eq_true] at h1
  have h2 := h1 k (List.mem_range.mpr hk2)
  have hk_not_zero : k ≠ 0 := by omega
  simp [hk_not_zero] at h2
  exact h2

/--
Bhavik Mehta has computed the minimal such $k$ for $1 \leq n \leq 18$.
For example, the minimal $k$ for $n = 4$ is $207$.
-/
@[category research formally solved using formal_conjectures at "https://github.com/theaustinhatfield/formal-conjectures/blob/solve-erdos-389-mehta/FormalConjectures/ErdosProblems/389.lean", AMS 11]
theorem erdos_389.variants.mehta_four :
    IsLeast
      { k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (4 + i) ∣ ∏ i ∈ Finset.range k, (4 + k + i) }
      207 := by
  constructor
  · simp only [Set.mem_setOf_eq]
    constructor
    · decide
    · rw [← check_div_fast_eq]
      decide
  · rintro x ⟨hx1, hx2⟩
    by_contra! h
    have h_eval : all_false 4 207 = true := by decide
    have h_false := all_false_implies 4 207 h_eval x hx1 h
    have h_true : check_div_fast 4 x = true := by
      rw [check_div_fast_eq]
      exact hx2
    rw [h_true] at h_false
    contradiction

end Erdos389
