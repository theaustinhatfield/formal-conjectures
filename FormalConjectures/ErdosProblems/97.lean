/-
Copyright 2026 The Formal Conjectures Authors.

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

set_option linter.style.copyright false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option maxHeartbeats 0
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Set EuclideanGeometry Real Finset

namespace Erdos97

def HasNEquidistantPointsAt (n : ℕ) (A : Finset ℝ²) (p : ℝ²) : Prop :=
  ∃ r : ℝ, r > 0 ∧ (A.filter fun q ↦ dist p q = r).card ≥ n

def HasNEquidistantPointsOn (n : ℕ) (A : Finset ℝ²) (B : Finset ℝ²) : Prop :=
  ∀ p ∈ B, HasNEquidistantPointsAt n A p

def HasNEquidistantProperty (n : ℕ) (A : Finset ℝ²) : Prop :=
  HasNEquidistantPointsOn n A A

lemma dist_sq_eq_sum (p q : ℝ²) :
    dist p q ^ 2 = (p 0 - q 0)^2 + (p 1 - q 1)^2 := by
  have hd : dist p q = Real.sqrt (∑ i, dist (p i) (q i) ^ 2) := EuclideanSpace.dist_eq p q
  rw [hd]
  have hpos : 0 ≤ ∑ i, dist (p i) (q i) ^ 2 := by positivity
  rw [Real.sq_sqrt hpos]
  have hsum : ∑ i : Fin 2, dist (p i) (q i) ^ 2 = dist (p 0) (q 0) ^ 2 + dist (p 1) (q 1) ^ 2 := by
    rw [Fin.sum_univ_two]
  rw [hsum]
  have hd0 : dist (p 0) (q 0) = |p 0 - q 0| := Real.dist_eq (p 0) (q 0)
  have hd1 : dist (p 1) (q 1) = |p 1 - q 1| := Real.dist_eq (p 1) (q 1)
  rw [hd0, hd1]
  have hsq0 : |p 0 - q 0| ^ 2 = (p 0 - q 0) ^ 2 := sq_abs (p 0 - q 0)
  have hsq1 : |p 1 - q 1| ^ 2 = (p 1 - q 1) ^ 2 := sq_abs (p 1 - q 1)
  rw [hsq0, hsq1]

lemma sep_lemma (s : Finset ℝ²) (x : ℝ²) (v : ℝ²) (c : ℝ)
    (hx : c < (v 0 * x 0 + v 1 * x 1))
    (hs : ∀ y ∈ s, (v 0 * y 0 + v 1 * y 1) ≤ c) :
    x ∉ convexHull ℝ (s : Set ℝ²) := by
  intro h
  let f : ℝ² →ₗ[ℝ] ℝ :=
    { toFun := fun p => v 0 * p 0 + v 1 * p 1
      map_add' := fun p q => by simp; ring
      map_smul' := fun r p => by simp; ring }
  have hc : Convex ℝ {p : ℝ² | f p ≤ c} := by
    have H : {p : ℝ² | f p ≤ c} = f ⁻¹' (Set.Iic c) := rfl
    rw [H]
    exact Convex.linear_preimage (convex_Iic c) f
  have hs_sub : (s : Set ℝ²) ⊆ {p : ℝ² | f p ≤ c} := by
    intro y hy
    exact hs y (Finset.mem_coe.mp hy)
  have h_conv := convexHull_min hs_sub hc
  have h_in := h_conv h
  simp only [Set.mem_setOf_eq] at h_in
  change f x ≤ c at h_in
  dsimp [f] at h_in
  linarith

lemma my_convex_indep (A : Finset ℝ²) (h : ∀ p ∈ A, p ∉ convexHull ℝ ((A.erase p) : Set ℝ²)) : ConvexIndep (A : Set ℝ²) := by
  intro p hp
  have h1 := h p (Finset.mem_coe.mp hp)
  have h2 : (A : Set ℝ²) \ {p} = (A.erase p : Set ℝ²) := by
    ext x
    simp
  rw [h2]
  exact h1

lemma card_three_of_insert {α : Type*} [DecidableEq α] (a b c : α)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (insert a (insert b {c}) : Finset α).card = 3 := by
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_singleton c]
    · intro h
      rw [Finset.mem_singleton] at h
      exact hbc h
  · intro h
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact hab rfl
    · exact hca.symm rfl


lemma exact_dist (a b : ℝ) (ha : 0 ≤ a) (h : a^2 = b) : a = Real.sqrt b := by
  have h1 : Real.sqrt (a^2) = Real.sqrt b := by rw [h]
  have h2 : Real.sqrt (a^2) = a := Real.sqrt_sq ha
  rw [h2] at h1
  exact h1

noncomputable def s3 : ℝ := Real.sqrt 3
@[simp] lemma s3_sq : s3 ^ 2 = 3 := by
  dsimp [s3]; rw [Real.sq_sqrt (by norm_num)]
@[simp] lemma s3_mul_s3 : s3 * s3 = 3 := by
  dsimp [s3]; rw [← sq, Real.sq_sqrt (by norm_num)]

noncomputable def P0x : ℝ := -1 / 1
noncomputable def P0y : ℝ := -1 / 1
noncomputable def P0 : ℝ² := !₂[P0x * s3, P0y]

noncomputable def P1x : ℝ := -8991 / 10927
noncomputable def P1y : ℝ := -26503 / 10927
noncomputable def P1 : ℝ² := !₂[P1x * s3, P1y]

noncomputable def P2x : ℝ := -10753 / 18529
noncomputable def P2y : ℝ := -44665 / 18529
noncomputable def P2 : ℝ² := !₂[P2x * s3, P2y]

noncomputable def P3x : ℝ := 1 / 1
noncomputable def P3y : ℝ := -1 / 1
noncomputable def P3 : ℝ² := !₂[P3x * s3, P3y]

noncomputable def P4x : ℝ := 17747 / 10927
noncomputable def P4y : ℝ := -235 / 10927
noncomputable def P4 : ℝ² := !₂[P4x * s3, P4y]

noncomputable def P5x : ℝ := 27709 / 18529
noncomputable def P5y : ℝ := 6203 / 18529
noncomputable def P5 : ℝ² := !₂[P5x * s3, P5y]

noncomputable def P6x : ℝ := 0 / 1
noncomputable def P6y : ℝ := 2 / 1
noncomputable def P6 : ℝ² := !₂[P6x * s3, P6y]

noncomputable def P7x : ℝ := -8756 / 10927
noncomputable def P7y : ℝ := 26738 / 10927
noncomputable def P7 : ℝ² := !₂[P7x * s3, P7y]

noncomputable def P8x : ℝ := -16956 / 18529
noncomputable def P8y : ℝ := 38462 / 18529
noncomputable def P8 : ℝ² := !₂[P8x * s3, P8y]

noncomputable def A : Finset ℝ² := insert P0 (insert P1 (insert P2 (insert P3 (insert P4 (insert P5 (insert P6 (insert P7 {P8})))))))

lemma in_A_P0 : P0 ∈ A := by simp [A]
lemma in_A_P1 : P1 ∈ A := by simp [A]
lemma in_A_P2 : P2 ∈ A := by simp [A]
lemma in_A_P3 : P3 ∈ A := by simp [A]
lemma in_A_P4 : P4 ∈ A := by simp [A]
lemma in_A_P5 : P5 ∈ A := by simp [A]
lemma in_A_P6 : P6 ∈ A := by simp [A]
lemma in_A_P7 : P7 ∈ A := by simp [A]
lemma in_A_P8 : P8 ∈ A := by simp [A]

lemma dist_P0_P1_sq : dist P0 P1 ^ 2 = 23232 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P0, P1, P0x, P0y, P1x, P1y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P1_P0_sq : dist P1 P0 ^ 2 = 23232 / 10927 := by rw [dist_comm, dist_P0_P1_sq]

lemma P0_ne_P1 : P0 ≠ P1 := by
  intro h; have h1 : dist P0 P1 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P0 P1 ^ 2 = 23232 / 10927 := dist_P0_P1_sq
  rw [h1] at h2; norm_num at h2
lemma P1_ne_P0 : P1 ≠ P0 := P0_ne_P1.symm

lemma dist_P0_P2_sq : dist P0 P2 ^ 2 = 46656 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P0, P2, P0x, P0y, P2x, P2y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P2_P0_sq : dist P2 P0 ^ 2 = 46656 / 18529 := by rw [dist_comm, dist_P0_P2_sq]

lemma P0_ne_P2 : P0 ≠ P2 := by
  intro h; have h1 : dist P0 P2 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P0 P2 ^ 2 = 46656 / 18529 := dist_P0_P2_sq
  rw [h1] at h2; norm_num at h2
lemma P2_ne_P0 : P2 ≠ P0 := P0_ne_P2.symm

lemma dist_P0_P3_sq : dist P0 P3 ^ 2 = 12 / 1 := by
  rw [dist_sq_eq_sum]
  dsimp [P0, P3, P0x, P0y, P3x, P3y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P3_P0_sq : dist P3 P0 ^ 2 = 12 / 1 := by rw [dist_comm, dist_P0_P3_sq]

lemma P0_ne_P3 : P0 ≠ P3 := by
  intro h; have h1 : dist P0 P3 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P0 P3 ^ 2 = 12 / 1 := dist_P0_P3_sq
  rw [h1] at h2; norm_num at h2
lemma P3_ne_P0 : P3 ≠ P0 := P0_ne_P3.symm

lemma dist_P0_P4_sq : dist P0 P4 ^ 2 = 236196 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P0, P4, P0x, P0y, P4x, P4y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P4_P0_sq : dist P4 P0 ^ 2 = 236196 / 10927 := by rw [dist_comm, dist_P0_P4_sq]

lemma P0_ne_P4 : P0 ≠ P4 := by
  intro h; have h1 : dist P0 P4 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P0 P4 ^ 2 = 236196 / 10927 := dist_P0_P4_sq
  rw [h1] at h2; norm_num at h2
lemma P4_ne_P0 : P4 ≠ P0 := P0_ne_P4.symm

lemma dist_P0_P5_sq : dist P0 P5 ^ 2 = 379164 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P0, P5, P0x, P0y, P5x, P5y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P5_P0_sq : dist P5 P0 ^ 2 = 379164 / 18529 := by rw [dist_comm, dist_P0_P5_sq]

lemma P0_ne_P5 : P0 ≠ P5 := by
  intro h; have h1 : dist P0 P5 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P0 P5 ^ 2 = 379164 / 18529 := dist_P0_P5_sq
  rw [h1] at h2; norm_num at h2
lemma P5_ne_P0 : P5 ≠ P0 := P0_ne_P5.symm

lemma dist_P0_P6_sq : dist P0 P6 ^ 2 = 12 / 1 := by
  rw [dist_sq_eq_sum]
  dsimp [P0, P6, P0x, P0y, P6x, P6y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P6_P0_sq : dist P6 P0 ^ 2 = 12 / 1 := by rw [dist_comm, dist_P0_P6_sq]

lemma P0_ne_P6 : P0 ≠ P6 := by
  intro h; have h1 : dist P0 P6 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P0 P6 ^ 2 = 12 / 1 := dist_P0_P6_sq
  rw [h1] at h2; norm_num at h2
lemma P6_ne_P0 : P6 ≠ P0 := P0_ne_P6.symm

lemma dist_P0_P7_sq : dist P0 P7 ^ 2 = 12 / 1 := by
  rw [dist_sq_eq_sum]
  dsimp [P0, P7, P0x, P0y, P7x, P7y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P7_P0_sq : dist P7 P0 ^ 2 = 12 / 1 := by rw [dist_comm, dist_P0_P7_sq]

lemma P0_ne_P7 : P0 ≠ P7 := by
  intro h; have h1 : dist P0 P7 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P0 P7 ^ 2 = 12 / 1 := dist_P0_P7_sq
  rw [h1] at h2; norm_num at h2
lemma P7_ne_P0 : P7 ≠ P0 := P0_ne_P7.symm

lemma dist_P0_P8_sq : dist P0 P8 ^ 2 = 175692 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P0, P8, P0x, P0y, P8x, P8y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P8_P0_sq : dist P8 P0 ^ 2 = 175692 / 18529 := by rw [dist_comm, dist_P0_P8_sq]

lemma P0_ne_P8 : P0 ≠ P8 := by
  intro h; have h1 : dist P0 P8 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P0 P8 ^ 2 = 175692 / 18529 := dist_P0_P8_sq
  rw [h1] at h2; norm_num at h2
lemma P8_ne_P0 : P8 ≠ P0 := P0_ne_P8.symm

lemma dist_P1_P2_sq : dist P1 P2 ^ 2 = 5108736 / 28923769 := by
  rw [dist_sq_eq_sum]
  dsimp [P1, P2, P1x, P1y, P2x, P2y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P2_P1_sq : dist P2 P1 ^ 2 = 5108736 / 28923769 := by rw [dist_comm, dist_P1_P2_sq]

lemma P1_ne_P2 : P1 ≠ P2 := by
  intro h; have h1 : dist P1 P2 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P1 P2 ^ 2 = 5108736 / 28923769 := dist_P1_P2_sq
  rw [h1] at h2; norm_num at h2
lemma P2_ne_P1 : P2 ≠ P1 := P1_ne_P2.symm

lemma dist_P1_P3_sq : dist P1 P3 ^ 2 = 12 / 1 := by
  rw [dist_sq_eq_sum]
  dsimp [P1, P3, P1x, P1y, P3x, P3y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P3_P1_sq : dist P3 P1 ^ 2 = 12 / 1 := by rw [dist_comm, dist_P1_P3_sq]

lemma P1_ne_P3 : P1 ≠ P3 := by
  intro h; have h1 : dist P1 P3 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P1 P3 ^ 2 = 12 / 1 := dist_P1_P3_sq
  rw [h1] at h2; norm_num at h2
lemma P3_ne_P1 : P3 ≠ P1 := P1_ne_P3.symm

lemma dist_P1_P4_sq : dist P1 P4 ^ 2 = 259428 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P1, P4, P1x, P1y, P4x, P4y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P4_P1_sq : dist P4 P1 ^ 2 = 259428 / 10927 := by rw [dist_comm, dist_P1_P4_sq]

lemma P1_ne_P4 : P1 ≠ P4 := by
  intro h; have h1 : dist P1 P4 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P1 P4 ^ 2 = 259428 / 10927 := dist_P1_P4_sq
  rw [h1] at h2; norm_num at h2
lemma P4_ne_P1 : P4 ≠ P1 := P1_ne_P4.symm

lemma dist_P1_P5_sq : dist P1 P5 ^ 2 = 259428 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P1, P5, P1x, P1y, P5x, P5y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P5_P1_sq : dist P5 P1 ^ 2 = 259428 / 10927 := by rw [dist_comm, dist_P1_P5_sq]

lemma P1_ne_P5 : P1 ≠ P5 := by
  intro h; have h1 : dist P1 P5 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P1 P5 ^ 2 = 259428 / 10927 := dist_P1_P5_sq
  rw [h1] at h2; norm_num at h2
lemma P5_ne_P1 : P5 ≠ P1 := P1_ne_P5.symm

lemma dist_P1_P6_sq : dist P1 P6 ^ 2 = 236196 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P1, P6, P1x, P1y, P6x, P6y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P6_P1_sq : dist P6 P1 ^ 2 = 236196 / 10927 := by rw [dist_comm, dist_P1_P6_sq]

lemma P1_ne_P6 : P1 ≠ P6 := by
  intro h; have h1 : dist P1 P6 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P1 P6 ^ 2 = 236196 / 10927 := dist_P1_P6_sq
  rw [h1] at h2; norm_num at h2
lemma P6_ne_P1 : P6 ≠ P1 := P1_ne_P6.symm

lemma dist_P1_P7_sq : dist P1 P7 ^ 2 = 259428 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P1, P7, P1x, P1y, P7x, P7y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P7_P1_sq : dist P7 P1 ^ 2 = 259428 / 10927 := by rw [dist_comm, dist_P1_P7_sq]

lemma P1_ne_P7 : P1 ≠ P7 := by
  intro h; have h1 : dist P1 P7 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P1 P7 ^ 2 = 259428 / 10927 := dist_P1_P7_sq
  rw [h1] at h2; norm_num at h2
lemma P7_ne_P1 : P7 ≠ P1 := P1_ne_P7.symm

lemma dist_P1_P8_sq : dist P1 P8 ^ 2 = 586766268 / 28923769 := by
  rw [dist_sq_eq_sum]
  dsimp [P1, P8, P1x, P1y, P8x, P8y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P8_P1_sq : dist P8 P1 ^ 2 = 586766268 / 28923769 := by rw [dist_comm, dist_P1_P8_sq]

lemma P1_ne_P8 : P1 ≠ P8 := by
  intro h; have h1 : dist P1 P8 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P1 P8 ^ 2 = 586766268 / 28923769 := dist_P1_P8_sq
  rw [h1] at h2; norm_num at h2
lemma P8_ne_P1 : P8 ≠ P1 := P1_ne_P8.symm

lemma dist_P2_P3_sq : dist P2 P3 ^ 2 = 175692 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P2, P3, P2x, P2y, P3x, P3y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P3_P2_sq : dist P3 P2 ^ 2 = 175692 / 18529 := by rw [dist_comm, dist_P2_P3_sq]

lemma P2_ne_P3 : P2 ≠ P3 := by
  intro h; have h1 : dist P2 P3 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P2 P3 ^ 2 = 175692 / 18529 := dist_P2_P3_sq
  rw [h1] at h2; norm_num at h2
lemma P3_ne_P2 : P3 ≠ P2 := P2_ne_P3.symm

lemma dist_P2_P4_sq : dist P2 P4 ^ 2 = 586766268 / 28923769 := by
  rw [dist_sq_eq_sum]
  dsimp [P2, P4, P2x, P2y, P4x, P4y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P4_P2_sq : dist P4 P2 ^ 2 = 586766268 / 28923769 := by rw [dist_comm, dist_P2_P4_sq]

lemma P2_ne_P4 : P2 ≠ P4 := by
  intro h; have h1 : dist P2 P4 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P2 P4 ^ 2 = 586766268 / 28923769 := dist_P2_P4_sq
  rw [h1] at h2; norm_num at h2
lemma P4_ne_P2 : P4 ≠ P2 := P2_ne_P4.symm

lemma dist_P2_P5_sq : dist P2 P5 ^ 2 = 379164 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P2, P5, P2x, P2y, P5x, P5y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P5_P2_sq : dist P5 P2 ^ 2 = 379164 / 18529 := by rw [dist_comm, dist_P2_P5_sq]

lemma P2_ne_P5 : P2 ≠ P5 := by
  intro h; have h1 : dist P2 P5 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P2 P5 ^ 2 = 379164 / 18529 := dist_P2_P5_sq
  rw [h1] at h2; norm_num at h2
lemma P5_ne_P2 : P5 ≠ P2 := P2_ne_P5.symm

lemma dist_P2_P6_sq : dist P2 P6 ^ 2 = 379164 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P2, P6, P2x, P2y, P6x, P6y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P6_P2_sq : dist P6 P2 ^ 2 = 379164 / 18529 := by rw [dist_comm, dist_P2_P6_sq]

lemma P2_ne_P6 : P2 ≠ P6 := by
  intro h; have h1 : dist P2 P6 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P2 P6 ^ 2 = 379164 / 18529 := dist_P2_P6_sq
  rw [h1] at h2; norm_num at h2
lemma P6_ne_P2 : P6 ≠ P2 := P2_ne_P6.symm

lemma dist_P2_P7_sq : dist P2 P7 ^ 2 = 259428 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P2, P7, P2x, P2y, P7x, P7y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P7_P2_sq : dist P7 P2 ^ 2 = 259428 / 10927 := by rw [dist_comm, dist_P2_P7_sq]

lemma P2_ne_P7 : P2 ≠ P7 := by
  intro h; have h1 : dist P2 P7 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P2 P7 ^ 2 = 259428 / 10927 := dist_P2_P7_sq
  rw [h1] at h2; norm_num at h2
lemma P7_ne_P2 : P7 ≠ P2 := P2_ne_P7.symm

lemma dist_P2_P8_sq : dist P2 P8 ^ 2 = 379164 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P2, P8, P2x, P2y, P8x, P8y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P8_P2_sq : dist P8 P2 ^ 2 = 379164 / 18529 := by rw [dist_comm, dist_P2_P8_sq]

lemma P2_ne_P8 : P2 ≠ P8 := by
  intro h; have h1 : dist P2 P8 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P2 P8 ^ 2 = 379164 / 18529 := dist_P2_P8_sq
  rw [h1] at h2; norm_num at h2
lemma P8_ne_P2 : P8 ≠ P2 := P2_ne_P8.symm

lemma dist_P3_P4_sq : dist P3 P4 ^ 2 = 23232 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P3, P4, P3x, P3y, P4x, P4y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P4_P3_sq : dist P4 P3 ^ 2 = 23232 / 10927 := by rw [dist_comm, dist_P3_P4_sq]

lemma P3_ne_P4 : P3 ≠ P4 := by
  intro h; have h1 : dist P3 P4 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P3 P4 ^ 2 = 23232 / 10927 := dist_P3_P4_sq
  rw [h1] at h2; norm_num at h2
lemma P4_ne_P3 : P4 ≠ P3 := P3_ne_P4.symm

lemma dist_P3_P5_sq : dist P3 P5 ^ 2 = 46656 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P3, P5, P3x, P3y, P5x, P5y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P5_P3_sq : dist P5 P3 ^ 2 = 46656 / 18529 := by rw [dist_comm, dist_P3_P5_sq]

lemma P3_ne_P5 : P3 ≠ P5 := by
  intro h; have h1 : dist P3 P5 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P3 P5 ^ 2 = 46656 / 18529 := dist_P3_P5_sq
  rw [h1] at h2; norm_num at h2
lemma P5_ne_P3 : P5 ≠ P3 := P3_ne_P5.symm

lemma dist_P3_P6_sq : dist P3 P6 ^ 2 = 12 / 1 := by
  rw [dist_sq_eq_sum]
  dsimp [P3, P6, P3x, P3y, P6x, P6y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P6_P3_sq : dist P6 P3 ^ 2 = 12 / 1 := by rw [dist_comm, dist_P3_P6_sq]

lemma P3_ne_P6 : P3 ≠ P6 := by
  intro h; have h1 : dist P3 P6 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P3 P6 ^ 2 = 12 / 1 := dist_P3_P6_sq
  rw [h1] at h2; norm_num at h2
lemma P6_ne_P3 : P6 ≠ P3 := P3_ne_P6.symm

lemma dist_P3_P7_sq : dist P3 P7 ^ 2 = 236196 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P3, P7, P3x, P3y, P7x, P7y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P7_P3_sq : dist P7 P3 ^ 2 = 236196 / 10927 := by rw [dist_comm, dist_P3_P7_sq]

lemma P3_ne_P7 : P3 ≠ P7 := by
  intro h; have h1 : dist P3 P7 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P3 P7 ^ 2 = 236196 / 10927 := dist_P3_P7_sq
  rw [h1] at h2; norm_num at h2
lemma P7_ne_P3 : P7 ≠ P3 := P3_ne_P7.symm

lemma dist_P3_P8_sq : dist P3 P8 ^ 2 = 379164 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P3, P8, P3x, P3y, P8x, P8y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P8_P3_sq : dist P8 P3 ^ 2 = 379164 / 18529 := by rw [dist_comm, dist_P3_P8_sq]

lemma P3_ne_P8 : P3 ≠ P8 := by
  intro h; have h1 : dist P3 P8 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P3 P8 ^ 2 = 379164 / 18529 := dist_P3_P8_sq
  rw [h1] at h2; norm_num at h2
lemma P8_ne_P3 : P8 ≠ P3 := P3_ne_P8.symm

lemma dist_P4_P5_sq : dist P4 P5 ^ 2 = 5108736 / 28923769 := by
  rw [dist_sq_eq_sum]
  dsimp [P4, P5, P4x, P4y, P5x, P5y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P5_P4_sq : dist P5 P4 ^ 2 = 5108736 / 28923769 := by rw [dist_comm, dist_P4_P5_sq]

lemma P4_ne_P5 : P4 ≠ P5 := by
  intro h; have h1 : dist P4 P5 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P4 P5 ^ 2 = 5108736 / 28923769 := dist_P4_P5_sq
  rw [h1] at h2; norm_num at h2
lemma P5_ne_P4 : P5 ≠ P4 := P4_ne_P5.symm

lemma dist_P4_P6_sq : dist P4 P6 ^ 2 = 12 / 1 := by
  rw [dist_sq_eq_sum]
  dsimp [P4, P6, P4x, P4y, P6x, P6y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P6_P4_sq : dist P6 P4 ^ 2 = 12 / 1 := by rw [dist_comm, dist_P4_P6_sq]

lemma P4_ne_P6 : P4 ≠ P6 := by
  intro h; have h1 : dist P4 P6 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P4 P6 ^ 2 = 12 / 1 := dist_P4_P6_sq
  rw [h1] at h2; norm_num at h2
lemma P6_ne_P4 : P6 ≠ P4 := P4_ne_P6.symm

lemma dist_P4_P7_sq : dist P4 P7 ^ 2 = 259428 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P4, P7, P4x, P4y, P7x, P7y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P7_P4_sq : dist P7 P4 ^ 2 = 259428 / 10927 := by rw [dist_comm, dist_P4_P7_sq]

lemma P4_ne_P7 : P4 ≠ P7 := by
  intro h; have h1 : dist P4 P7 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P4 P7 ^ 2 = 259428 / 10927 := dist_P4_P7_sq
  rw [h1] at h2; norm_num at h2
lemma P7_ne_P4 : P7 ≠ P4 := P4_ne_P7.symm

lemma dist_P4_P8_sq : dist P4 P8 ^ 2 = 259428 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P4, P8, P4x, P4y, P8x, P8y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P8_P4_sq : dist P8 P4 ^ 2 = 259428 / 10927 := by rw [dist_comm, dist_P4_P8_sq]

lemma P4_ne_P8 : P4 ≠ P8 := by
  intro h; have h1 : dist P4 P8 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P4 P8 ^ 2 = 259428 / 10927 := dist_P4_P8_sq
  rw [h1] at h2; norm_num at h2
lemma P8_ne_P4 : P8 ≠ P4 := P4_ne_P8.symm

lemma dist_P5_P6_sq : dist P5 P6 ^ 2 = 175692 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P5, P6, P5x, P5y, P6x, P6y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P6_P5_sq : dist P6 P5 ^ 2 = 175692 / 18529 := by rw [dist_comm, dist_P5_P6_sq]

lemma P5_ne_P6 : P5 ≠ P6 := by
  intro h; have h1 : dist P5 P6 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P5 P6 ^ 2 = 175692 / 18529 := dist_P5_P6_sq
  rw [h1] at h2; norm_num at h2
lemma P6_ne_P5 : P6 ≠ P5 := P5_ne_P6.symm

lemma dist_P5_P7_sq : dist P5 P7 ^ 2 = 586766268 / 28923769 := by
  rw [dist_sq_eq_sum]
  dsimp [P5, P7, P5x, P5y, P7x, P7y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P7_P5_sq : dist P7 P5 ^ 2 = 586766268 / 28923769 := by rw [dist_comm, dist_P5_P7_sq]

lemma P5_ne_P7 : P5 ≠ P7 := by
  intro h; have h1 : dist P5 P7 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P5 P7 ^ 2 = 586766268 / 28923769 := dist_P5_P7_sq
  rw [h1] at h2; norm_num at h2
lemma P7_ne_P5 : P7 ≠ P5 := P5_ne_P7.symm

lemma dist_P5_P8_sq : dist P5 P8 ^ 2 = 379164 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P5, P8, P5x, P5y, P8x, P8y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P8_P5_sq : dist P8 P5 ^ 2 = 379164 / 18529 := by rw [dist_comm, dist_P5_P8_sq]

lemma P5_ne_P8 : P5 ≠ P8 := by
  intro h; have h1 : dist P5 P8 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P5 P8 ^ 2 = 379164 / 18529 := dist_P5_P8_sq
  rw [h1] at h2; norm_num at h2
lemma P8_ne_P5 : P8 ≠ P5 := P5_ne_P8.symm

lemma dist_P6_P7_sq : dist P6 P7 ^ 2 = 23232 / 10927 := by
  rw [dist_sq_eq_sum]
  dsimp [P6, P7, P6x, P6y, P7x, P7y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P7_P6_sq : dist P7 P6 ^ 2 = 23232 / 10927 := by rw [dist_comm, dist_P6_P7_sq]

lemma P6_ne_P7 : P6 ≠ P7 := by
  intro h; have h1 : dist P6 P7 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P6 P7 ^ 2 = 23232 / 10927 := dist_P6_P7_sq
  rw [h1] at h2; norm_num at h2
lemma P7_ne_P6 : P7 ≠ P6 := P6_ne_P7.symm

lemma dist_P6_P8_sq : dist P6 P8 ^ 2 = 46656 / 18529 := by
  rw [dist_sq_eq_sum]
  dsimp [P6, P8, P6x, P6y, P8x, P8y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P8_P6_sq : dist P8 P6 ^ 2 = 46656 / 18529 := by rw [dist_comm, dist_P6_P8_sq]

lemma P6_ne_P8 : P6 ≠ P8 := by
  intro h; have h1 : dist P6 P8 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P6 P8 ^ 2 = 46656 / 18529 := dist_P6_P8_sq
  rw [h1] at h2; norm_num at h2
lemma P8_ne_P6 : P8 ≠ P6 := P6_ne_P8.symm

lemma dist_P7_P8_sq : dist P7 P8 ^ 2 = 5108736 / 28923769 := by
  rw [dist_sq_eq_sum]
  dsimp [P7, P8, P7x, P7y, P8x, P8y]
  ring_nf <;> try simp only [s3_sq] <;> try norm_num
lemma dist_P8_P7_sq : dist P8 P7 ^ 2 = 5108736 / 28923769 := by rw [dist_comm, dist_P7_P8_sq]

lemma P7_ne_P8 : P7 ≠ P8 := by
  intro h; have h1 : dist P7 P8 ^ 2 = 0 := by rw [h, dist_self, sq, mul_zero]
  have h2 : dist P7 P8 ^ 2 = 5108736 / 28923769 := dist_P7_P8_sq
  rw [h1] at h2; norm_num at h2
lemma P8_ne_P7 : P8 ≠ P7 := P7_ne_P8.symm

noncomputable def v0 : ℝ² := !₂[-100 * s3, -37]
noncomputable def c0 : ℝ := 3680155 / 10927
lemma sep_P0 : P0 ∉ convexHull ℝ ((A.erase P0) : Set ℝ²) := by
  apply sep_lemma _ _ v0 c0
  · dsimp [v0, P0, P0x, P0y, c0]
    calc
      3680155 / 10927 < 337 / 1 := by norm_num
      _ = (-100 * s3) * (-1/1 * s3) + -37 * (-1/1) := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
  · intro y hy
    simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact False.elim (hy.1 rfl)
    · dsimp [v0, P1, P1x, P1y, c0]
      have h_eq : (-100 * s3) * (-8991/10927 * s3) + -37 * (-26503/10927) = 3677911/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v0, P2, P2x, P2y, c0]
      have h_eq : (-100 * s3) * (-10753/18529 * s3) + -37 * (-44665/18529) = 4878505/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v0, P3, P3x, P3y, c0]
      have h_eq : (-100 * s3) * (1/1 * s3) + -37 * (-1/1) = -263/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v0, P4, P4x, P4y, c0]
      have h_eq : (-100 * s3) * (17747/10927 * s3) + -37 * (-235/10927) = -5315405/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v0, P5, P5x, P5y, c0]
      have h_eq : (-100 * s3) * (27709/18529 * s3) + -37 * (6203/18529) = -8542211/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v0, P6, P6x, P6y, c0]
      have h_eq : (-100 * s3) * (0/1 * s3) + -37 * (2/1) = -74/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v0, P7, P7x, P7y, c0]
      have h_eq : (-100 * s3) * (-8756/10927 * s3) + -37 * (26738/10927) = 1637494/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v0, P8, P8x, P8y, c0]
      have h_eq : (-100 * s3) * (-16956/18529 * s3) + -37 * (38462/18529) = 3663706/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num

noncomputable def v1 : ℝ² := !₂[-100 * s3, -100]
noncomputable def c1 : ℝ := 13081466800 / 28923769
lemma sep_P1 : P1 ∉ convexHull ℝ ((A.erase P1) : Set ℝ²) := by
  apply sep_lemma _ _ v1 c1
  · dsimp [v1, P1, P1x, P1y, c1]
    calc
      13081466800 / 28923769 < 5347600 / 10927 := by norm_num
      _ = (-100 * s3) * (-8991/10927 * s3) + -100 * (-26503/10927) := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
  · intro y hy
    simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · dsimp [v1, P0, P0x, P0y, c1]
      have h_eq : (-100 * s3) * (-1/1 * s3) + -100 * (-1/1) = 400/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · exact False.elim (hy.1 rfl)
    · dsimp [v1, P2, P2x, P2y, c1]
      have h_eq : (-100 * s3) * (-10753/18529 * s3) + -100 * (-44665/18529) = 7692400/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v1, P3, P3x, P3y, c1]
      have h_eq : (-100 * s3) * (1/1 * s3) + -100 * (-1/1) = -200/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v1, P4, P4x, P4y, c1]
      have h_eq : (-100 * s3) * (17747/10927 * s3) + -100 * (-235/10927) = -5300600/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v1, P5, P5x, P5y, c1]
      have h_eq : (-100 * s3) * (27709/18529 * s3) + -100 * (6203/18529) = -8933000/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v1, P6, P6x, P6y, c1]
      have h_eq : (-100 * s3) * (0/1 * s3) + -100 * (2/1) = -200/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v1, P7, P7x, P7y, c1]
      have h_eq : (-100 * s3) * (-8756/10927 * s3) + -100 * (26738/10927) = -47000/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v1, P8, P8x, P8y, c1]
      have h_eq : (-100 * s3) * (-16956/18529 * s3) + -100 * (38462/18529) = 1240600/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num

noncomputable def v2 : ℝ² := !₂[1 * s3, -48]
noncomputable def c2 : ℝ := 3296135229 / 28923769
lemma sep_P2 : P2 ∉ convexHull ℝ ((A.erase P2) : Set ℝ²) := by
  apply sep_lemma _ _ v2 c2
  · dsimp [v2, P2, P2x, P2y, c2]
    calc
      3296135229 / 28923769 < 2111661 / 18529 := by norm_num
      _ = (1 * s3) * (-10753/18529 * s3) + -48 * (-44665/18529) := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
  · intro y hy
    simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · dsimp [v2, P0, P0x, P0y, c2]
      have h_eq : (1 * s3) * (-1/1 * s3) + -48 * (-1/1) = 45/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v2, P1, P1x, P1y, c2]
      have h_eq : (1 * s3) * (-8991/10927 * s3) + -48 * (-26503/10927) = 1245171/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · exact False.elim (hy.1 rfl)
    · dsimp [v2, P3, P3x, P3y, c2]
      have h_eq : (1 * s3) * (1/1 * s3) + -48 * (-1/1) = 51/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v2, P4, P4x, P4y, c2]
      have h_eq : (1 * s3) * (17747/10927 * s3) + -48 * (-235/10927) = 64521/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v2, P5, P5x, P5y, c2]
      have h_eq : (1 * s3) * (27709/18529 * s3) + -48 * (6203/18529) = -214617/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v2, P6, P6x, P6y, c2]
      have h_eq : (1 * s3) * (0/1 * s3) + -48 * (2/1) = -96/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v2, P7, P7x, P7y, c2]
      have h_eq : (1 * s3) * (-8756/10927 * s3) + -48 * (26738/10927) = -1309692/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v2, P8, P8x, P8y, c2]
      have h_eq : (1 * s3) * (-16956/18529 * s3) + -48 * (38462/18529) = -1897044/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num

noncomputable def v3 : ℝ² := !₂[1 * s3, -3]
noncomputable def c3 : ℝ := 106455 / 18529
lemma sep_P3 : P3 ∉ convexHull ℝ ((A.erase P3) : Set ℝ²) := by
  apply sep_lemma _ _ v3 c3
  · dsimp [v3, P3, P3x, P3y, c3]
    calc
      106455 / 18529 < 6 / 1 := by norm_num
      _ = (1 * s3) * (1/1 * s3) + -3 * (-1/1) := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
  · intro y hy
    simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · dsimp [v3, P0, P0x, P0y, c3]
      have h_eq : (1 * s3) * (-1/1 * s3) + -3 * (-1/1) = 0/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v3, P1, P1x, P1y, c3]
      have h_eq : (1 * s3) * (-8991/10927 * s3) + -3 * (-26503/10927) = 52536/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v3, P2, P2x, P2y, c3]
      have h_eq : (1 * s3) * (-10753/18529 * s3) + -3 * (-44665/18529) = 101736/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · exact False.elim (hy.1 rfl)
    · dsimp [v3, P4, P4x, P4y, c3]
      have h_eq : (1 * s3) * (17747/10927 * s3) + -3 * (-235/10927) = 53946/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v3, P5, P5x, P5y, c3]
      have h_eq : (1 * s3) * (27709/18529 * s3) + -3 * (6203/18529) = 64518/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v3, P6, P6x, P6y, c3]
      have h_eq : (1 * s3) * (0/1 * s3) + -3 * (2/1) = -6/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v3, P7, P7x, P7y, c3]
      have h_eq : (1 * s3) * (-8756/10927 * s3) + -3 * (26738/10927) = -106482/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v3, P8, P8x, P8y, c3]
      have h_eq : (1 * s3) * (-16956/18529 * s3) + -3 * (38462/18529) = -166254/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num

noncomputable def v4 : ℝ² := !₂[1 * s3, -1]
noncomputable def c4 : ℝ := 130814668 / 28923769
lemma sep_P4 : P4 ∉ convexHull ℝ ((A.erase P4) : Set ℝ²) := by
  apply sep_lemma _ _ v4 c4
  · dsimp [v4, P4, P4x, P4y, c4]
    calc
      130814668 / 28923769 < 53476 / 10927 := by norm_num
      _ = (1 * s3) * (17747/10927 * s3) + -1 * (-235/10927) := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
  · intro y hy
    simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · dsimp [v4, P0, P0x, P0y, c4]
      have h_eq : (1 * s3) * (-1/1 * s3) + -1 * (-1/1) = -2/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v4, P1, P1x, P1y, c4]
      have h_eq : (1 * s3) * (-8991/10927 * s3) + -1 * (-26503/10927) = -470/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v4, P2, P2x, P2y, c4]
      have h_eq : (1 * s3) * (-10753/18529 * s3) + -1 * (-44665/18529) = 12406/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v4, P3, P3x, P3y, c4]
      have h_eq : (1 * s3) * (1/1 * s3) + -1 * (-1/1) = 4/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · exact False.elim (hy.1 rfl)
    · dsimp [v4, P5, P5x, P5y, c4]
      have h_eq : (1 * s3) * (27709/18529 * s3) + -1 * (6203/18529) = 76924/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v4, P6, P6x, P6y, c4]
      have h_eq : (1 * s3) * (0/1 * s3) + -1 * (2/1) = -2/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v4, P7, P7x, P7y, c4]
      have h_eq : (1 * s3) * (-8756/10927 * s3) + -1 * (26738/10927) = -53006/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v4, P8, P8x, P8y, c4]
      have h_eq : (1 * s3) * (-16956/18529 * s3) + -1 * (38462/18529) = -89330/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num

noncomputable def v5 : ℝ² := !₂[1 * s3, 2]
noncomputable def c5 : ℝ := 144405925 / 28923769
lemma sep_P5 : P5 ∉ convexHull ℝ ((A.erase P5) : Set ℝ²) := by
  apply sep_lemma _ _ v5 c5
  · dsimp [v5, P5, P5x, P5y, c5]
    calc
      144405925 / 28923769 < 95533 / 18529 := by norm_num
      _ = (1 * s3) * (27709/18529 * s3) + 2 * (6203/18529) := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
  · intro y hy
    simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · dsimp [v5, P0, P0x, P0y, c5]
      have h_eq : (1 * s3) * (-1/1 * s3) + 2 * (-1/1) = -5/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v5, P1, P1x, P1y, c5]
      have h_eq : (1 * s3) * (-8991/10927 * s3) + 2 * (-26503/10927) = -79979/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v5, P2, P2x, P2y, c5]
      have h_eq : (1 * s3) * (-10753/18529 * s3) + 2 * (-44665/18529) = -121589/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v5, P3, P3x, P3y, c5]
      have h_eq : (1 * s3) * (1/1 * s3) + 2 * (-1/1) = 1/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v5, P4, P4x, P4y, c5]
      have h_eq : (1 * s3) * (17747/10927 * s3) + 2 * (-235/10927) = 52771/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · exact False.elim (hy.1 rfl)
    · dsimp [v5, P6, P6x, P6y, c5]
      have h_eq : (1 * s3) * (0/1 * s3) + 2 * (2/1) = 4/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v5, P7, P7x, P7y, c5]
      have h_eq : (1 * s3) * (-8756/10927 * s3) + 2 * (26738/10927) = 27208/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v5, P8, P8x, P8y, c5]
      have h_eq : (1 * s3) * (-16956/18529 * s3) + 2 * (38462/18529) = 26056/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num

noncomputable def v6 : ℝ² := !₂[1 * s3, 3]
noncomputable def c6 : ℝ := 106455 / 18529
lemma sep_P6 : P6 ∉ convexHull ℝ ((A.erase P6) : Set ℝ²) := by
  apply sep_lemma _ _ v6 c6
  · dsimp [v6, P6, P6x, P6y, c6]
    calc
      106455 / 18529 < 6 / 1 := by norm_num
      _ = (1 * s3) * (0/1 * s3) + 3 * (2/1) := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
  · intro y hy
    simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · dsimp [v6, P0, P0x, P0y, c6]
      have h_eq : (1 * s3) * (-1/1 * s3) + 3 * (-1/1) = -6/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v6, P1, P1x, P1y, c6]
      have h_eq : (1 * s3) * (-8991/10927 * s3) + 3 * (-26503/10927) = -106482/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v6, P2, P2x, P2y, c6]
      have h_eq : (1 * s3) * (-10753/18529 * s3) + 3 * (-44665/18529) = -166254/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v6, P3, P3x, P3y, c6]
      have h_eq : (1 * s3) * (1/1 * s3) + 3 * (-1/1) = 0/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v6, P4, P4x, P4y, c6]
      have h_eq : (1 * s3) * (17747/10927 * s3) + 3 * (-235/10927) = 52536/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v6, P5, P5x, P5y, c6]
      have h_eq : (1 * s3) * (27709/18529 * s3) + 3 * (6203/18529) = 101736/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · exact False.elim (hy.1 rfl)
    · dsimp [v6, P7, P7x, P7y, c6]
      have h_eq : (1 * s3) * (-8756/10927 * s3) + 3 * (26738/10927) = 53946/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v6, P8, P8x, P8y, c6]
      have h_eq : (1 * s3) * (-16956/18529 * s3) + 3 * (38462/18529) = 64518/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num

noncomputable def v7 : ℝ² := !₂[-100 * s3, 92]
noncomputable def c7 : ℝ := 13464291928 / 28923769
lemma sep_P7 : P7 ∉ convexHull ℝ ((A.erase P7) : Set ℝ²) := by
  apply sep_lemma _ _ v7 c7
  · dsimp [v7, P7, P7x, P7y, c7]
    calc
      13464291928 / 28923769 < 5086696 / 10927 := by norm_num
      _ = (-100 * s3) * (-8756/10927 * s3) + 92 * (26738/10927) := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
  · intro y hy
    simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · dsimp [v7, P0, P0x, P0y, c7]
      have h_eq : (-100 * s3) * (-1/1 * s3) + 92 * (-1/1) = 208/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v7, P1, P1x, P1y, c7]
      have h_eq : (-100 * s3) * (-8991/10927 * s3) + 92 * (-26503/10927) = 259024/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v7, P2, P2x, P2y, c7]
      have h_eq : (-100 * s3) * (-10753/18529 * s3) + 92 * (-44665/18529) = -883280/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v7, P3, P3x, P3y, c7]
      have h_eq : (-100 * s3) * (1/1 * s3) + 92 * (-1/1) = -392/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v7, P4, P4x, P4y, c7]
      have h_eq : (-100 * s3) * (17747/10927 * s3) + 92 * (-235/10927) = -5345720/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v7, P5, P5x, P5y, c7]
      have h_eq : (-100 * s3) * (27709/18529 * s3) + 92 * (6203/18529) = -7742024/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v7, P6, P6x, P6y, c7]
      have h_eq : (-100 * s3) * (0/1 * s3) + 92 * (2/1) = 184/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · exact False.elim (hy.1 rfl)
    · dsimp [v7, P8, P8x, P8y, c7]
      have h_eq : (-100 * s3) * (-16956/18529 * s3) + 92 * (38462/18529) = 8625304/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num

noncomputable def v8 : ℝ² := !₂[-100 * s3, 9]
noncomputable def c8 : ℝ := 10824897 / 37058
lemma sep_P8 : P8 ∉ convexHull ℝ ((A.erase P8) : Set ℝ²) := by
  apply sep_lemma _ _ v8 c8
  · dsimp [v8, P8, P8x, P8y, c8]
    calc
      10824897 / 37058 < 5432958 / 18529 := by norm_num
      _ = (-100 * s3) * (-16956/18529 * s3) + 9 * (38462/18529) := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
  · intro y hy
    simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy.2 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · dsimp [v8, P0, P0x, P0y, c8]
      have h_eq : (-100 * s3) * (-1/1 * s3) + 9 * (-1/1) = 291/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v8, P1, P1x, P1y, c8]
      have h_eq : (-100 * s3) * (-8991/10927 * s3) + 9 * (-26503/10927) = 2458773/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v8, P2, P2x, P2y, c8]
      have h_eq : (-100 * s3) * (-10753/18529 * s3) + 9 * (-44665/18529) = 2823915/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v8, P3, P3x, P3y, c8]
      have h_eq : (-100 * s3) * (1/1 * s3) + 9 * (-1/1) = -309/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v8, P4, P4x, P4y, c8]
      have h_eq : (-100 * s3) * (17747/10927 * s3) + 9 * (-235/10927) = -5326215/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v8, P5, P5x, P5y, c8]
      have h_eq : (-100 * s3) * (27709/18529 * s3) + 9 * (6203/18529) = -8256873/18529 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v8, P6, P6x, P6y, c8]
      have h_eq : (-100 * s3) * (0/1 * s3) + 9 * (2/1) = 18/1 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · dsimp [v8, P7, P7x, P7y, c8]
      have h_eq : (-100 * s3) * (-8756/10927 * s3) + 9 * (26738/10927) = 2867442/10927 := by
        ring_nf <;> try simp only [s3_sq] <;> try norm_num
      rw [h_eq]; norm_num
    · exact False.elim (hy.1 rfl)

lemma mem_A_cases (p : ℝ²) (hp : p ∈ A) : p = P0 ∨ p = P1 ∨ p = P2 ∨ p = P3 ∨ p = P4 ∨ p = P5 ∨ p = P6 ∨ p = P7 ∨ p = P8 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp
  exact hp

lemma has_equidistant : HasNEquidistantProperty 3 A := by
  intro p hp
  have hp_cases := mem_A_cases p hp
  rcases hp_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · use Real.sqrt (12 / 1)
    refine ⟨by norm_num, ?_⟩
    have h_sub : (insert P3 (insert P6 {P7}) : Finset ℝ²) ⊆ A.filter (fun q => dist P0 q = Real.sqrt (12 / 1)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl|rfl|rfl
      · refine ⟨in_A_P3, ?_⟩
        have hsq : dist P0 P3 ^ 2 = 12 / 1 := dist_P0_P3_sq
        exact exact_dist (dist P0 P3) (12 / 1) dist_nonneg hsq
      · refine ⟨in_A_P6, ?_⟩
        have hsq : dist P0 P6 ^ 2 = 12 / 1 := dist_P0_P6_sq
        exact exact_dist (dist P0 P6) (12 / 1) dist_nonneg hsq
      · refine ⟨in_A_P7, ?_⟩
        have hsq : dist P0 P7 ^ 2 = 12 / 1 := dist_P0_P7_sq
        exact exact_dist (dist P0 P7) (12 / 1) dist_nonneg hsq
    have h_card : (insert P3 (insert P6 {P7}) : Finset ℝ²).card = 3 := by
      apply card_three_of_insert P3 P6 P7
      · exact P3_ne_P6
      · exact P6_ne_P7
      · exact P7_ne_P3
    rw [←h_card]
    exact Finset.card_le_card h_sub
  · use Real.sqrt (259428 / 10927)
    refine ⟨by norm_num, ?_⟩
    have h_sub : (insert P4 (insert P5 {P7}) : Finset ℝ²) ⊆ A.filter (fun q => dist P1 q = Real.sqrt (259428 / 10927)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl|rfl|rfl
      · refine ⟨in_A_P4, ?_⟩
        have hsq : dist P1 P4 ^ 2 = 259428 / 10927 := dist_P1_P4_sq
        exact exact_dist (dist P1 P4) (259428 / 10927) dist_nonneg hsq
      · refine ⟨in_A_P5, ?_⟩
        have hsq : dist P1 P5 ^ 2 = 259428 / 10927 := dist_P1_P5_sq
        exact exact_dist (dist P1 P5) (259428 / 10927) dist_nonneg hsq
      · refine ⟨in_A_P7, ?_⟩
        have hsq : dist P1 P7 ^ 2 = 259428 / 10927 := dist_P1_P7_sq
        exact exact_dist (dist P1 P7) (259428 / 10927) dist_nonneg hsq
    have h_card : (insert P4 (insert P5 {P7}) : Finset ℝ²).card = 3 := by
      apply card_three_of_insert P4 P5 P7
      · exact P4_ne_P5
      · exact P5_ne_P7
      · exact P7_ne_P4
    rw [←h_card]
    exact Finset.card_le_card h_sub
  · use Real.sqrt (379164 / 18529)
    refine ⟨by norm_num, ?_⟩
    have h_sub : (insert P5 (insert P6 {P8}) : Finset ℝ²) ⊆ A.filter (fun q => dist P2 q = Real.sqrt (379164 / 18529)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl|rfl|rfl
      · refine ⟨in_A_P5, ?_⟩
        have hsq : dist P2 P5 ^ 2 = 379164 / 18529 := dist_P2_P5_sq
        exact exact_dist (dist P2 P5) (379164 / 18529) dist_nonneg hsq
      · refine ⟨in_A_P6, ?_⟩
        have hsq : dist P2 P6 ^ 2 = 379164 / 18529 := dist_P2_P6_sq
        exact exact_dist (dist P2 P6) (379164 / 18529) dist_nonneg hsq
      · refine ⟨in_A_P8, ?_⟩
        have hsq : dist P2 P8 ^ 2 = 379164 / 18529 := dist_P2_P8_sq
        exact exact_dist (dist P2 P8) (379164 / 18529) dist_nonneg hsq
    have h_card : (insert P5 (insert P6 {P8}) : Finset ℝ²).card = 3 := by
      apply card_three_of_insert P5 P6 P8
      · exact P5_ne_P6
      · exact P6_ne_P8
      · exact P8_ne_P5
    rw [←h_card]
    exact Finset.card_le_card h_sub
  · use Real.sqrt (12 / 1)
    refine ⟨by norm_num, ?_⟩
    have h_sub : (insert P0 (insert P1 {P6}) : Finset ℝ²) ⊆ A.filter (fun q => dist P3 q = Real.sqrt (12 / 1)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl|rfl|rfl
      · refine ⟨in_A_P0, ?_⟩
        have hsq : dist P3 P0 ^ 2 = 12 / 1 := dist_P3_P0_sq
        exact exact_dist (dist P3 P0) (12 / 1) dist_nonneg hsq
      · refine ⟨in_A_P1, ?_⟩
        have hsq : dist P3 P1 ^ 2 = 12 / 1 := dist_P3_P1_sq
        exact exact_dist (dist P3 P1) (12 / 1) dist_nonneg hsq
      · refine ⟨in_A_P6, ?_⟩
        have hsq : dist P3 P6 ^ 2 = 12 / 1 := dist_P3_P6_sq
        exact exact_dist (dist P3 P6) (12 / 1) dist_nonneg hsq
    have h_card : (insert P0 (insert P1 {P6}) : Finset ℝ²).card = 3 := by
      apply card_three_of_insert P0 P1 P6
      · exact P0_ne_P1
      · exact P1_ne_P6
      · exact P6_ne_P0
    rw [←h_card]
    exact Finset.card_le_card h_sub
  · use Real.sqrt (259428 / 10927)
    refine ⟨by norm_num, ?_⟩
    have h_sub : (insert P1 (insert P7 {P8}) : Finset ℝ²) ⊆ A.filter (fun q => dist P4 q = Real.sqrt (259428 / 10927)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl|rfl|rfl
      · refine ⟨in_A_P1, ?_⟩
        have hsq : dist P4 P1 ^ 2 = 259428 / 10927 := dist_P4_P1_sq
        exact exact_dist (dist P4 P1) (259428 / 10927) dist_nonneg hsq
      · refine ⟨in_A_P7, ?_⟩
        have hsq : dist P4 P7 ^ 2 = 259428 / 10927 := dist_P4_P7_sq
        exact exact_dist (dist P4 P7) (259428 / 10927) dist_nonneg hsq
      · refine ⟨in_A_P8, ?_⟩
        have hsq : dist P4 P8 ^ 2 = 259428 / 10927 := dist_P4_P8_sq
        exact exact_dist (dist P4 P8) (259428 / 10927) dist_nonneg hsq
    have h_card : (insert P1 (insert P7 {P8}) : Finset ℝ²).card = 3 := by
      apply card_three_of_insert P1 P7 P8
      · exact P1_ne_P7
      · exact P7_ne_P8
      · exact P8_ne_P1
    rw [←h_card]
    exact Finset.card_le_card h_sub
  · use Real.sqrt (379164 / 18529)
    refine ⟨by norm_num, ?_⟩
    have h_sub : (insert P0 (insert P2 {P8}) : Finset ℝ²) ⊆ A.filter (fun q => dist P5 q = Real.sqrt (379164 / 18529)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl|rfl|rfl
      · refine ⟨in_A_P0, ?_⟩
        have hsq : dist P5 P0 ^ 2 = 379164 / 18529 := dist_P5_P0_sq
        exact exact_dist (dist P5 P0) (379164 / 18529) dist_nonneg hsq
      · refine ⟨in_A_P2, ?_⟩
        have hsq : dist P5 P2 ^ 2 = 379164 / 18529 := dist_P5_P2_sq
        exact exact_dist (dist P5 P2) (379164 / 18529) dist_nonneg hsq
      · refine ⟨in_A_P8, ?_⟩
        have hsq : dist P5 P8 ^ 2 = 379164 / 18529 := dist_P5_P8_sq
        exact exact_dist (dist P5 P8) (379164 / 18529) dist_nonneg hsq
    have h_card : (insert P0 (insert P2 {P8}) : Finset ℝ²).card = 3 := by
      apply card_three_of_insert P0 P2 P8
      · exact P0_ne_P2
      · exact P2_ne_P8
      · exact P8_ne_P0
    rw [←h_card]
    exact Finset.card_le_card h_sub
  · use Real.sqrt (12 / 1)
    refine ⟨by norm_num, ?_⟩
    have h_sub : (insert P0 (insert P3 {P4}) : Finset ℝ²) ⊆ A.filter (fun q => dist P6 q = Real.sqrt (12 / 1)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl|rfl|rfl
      · refine ⟨in_A_P0, ?_⟩
        have hsq : dist P6 P0 ^ 2 = 12 / 1 := dist_P6_P0_sq
        exact exact_dist (dist P6 P0) (12 / 1) dist_nonneg hsq
      · refine ⟨in_A_P3, ?_⟩
        have hsq : dist P6 P3 ^ 2 = 12 / 1 := dist_P6_P3_sq
        exact exact_dist (dist P6 P3) (12 / 1) dist_nonneg hsq
      · refine ⟨in_A_P4, ?_⟩
        have hsq : dist P6 P4 ^ 2 = 12 / 1 := dist_P6_P4_sq
        exact exact_dist (dist P6 P4) (12 / 1) dist_nonneg hsq
    have h_card : (insert P0 (insert P3 {P4}) : Finset ℝ²).card = 3 := by
      apply card_three_of_insert P0 P3 P4
      · exact P0_ne_P3
      · exact P3_ne_P4
      · exact P4_ne_P0
    rw [←h_card]
    exact Finset.card_le_card h_sub
  · use Real.sqrt (259428 / 10927)
    refine ⟨by norm_num, ?_⟩
    have h_sub : (insert P1 (insert P2 {P4}) : Finset ℝ²) ⊆ A.filter (fun q => dist P7 q = Real.sqrt (259428 / 10927)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl|rfl|rfl
      · refine ⟨in_A_P1, ?_⟩
        have hsq : dist P7 P1 ^ 2 = 259428 / 10927 := dist_P7_P1_sq
        exact exact_dist (dist P7 P1) (259428 / 10927) dist_nonneg hsq
      · refine ⟨in_A_P2, ?_⟩
        have hsq : dist P7 P2 ^ 2 = 259428 / 10927 := dist_P7_P2_sq
        exact exact_dist (dist P7 P2) (259428 / 10927) dist_nonneg hsq
      · refine ⟨in_A_P4, ?_⟩
        have hsq : dist P7 P4 ^ 2 = 259428 / 10927 := dist_P7_P4_sq
        exact exact_dist (dist P7 P4) (259428 / 10927) dist_nonneg hsq
    have h_card : (insert P1 (insert P2 {P4}) : Finset ℝ²).card = 3 := by
      apply card_three_of_insert P1 P2 P4
      · exact P1_ne_P2
      · exact P2_ne_P4
      · exact P4_ne_P1
    rw [←h_card]
    exact Finset.card_le_card h_sub
  · use Real.sqrt (379164 / 18529)
    refine ⟨by norm_num, ?_⟩
    have h_sub : (insert P2 (insert P3 {P5}) : Finset ℝ²) ⊆ A.filter (fun q => dist P8 q = Real.sqrt (379164 / 18529)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl|rfl|rfl
      · refine ⟨in_A_P2, ?_⟩
        have hsq : dist P8 P2 ^ 2 = 379164 / 18529 := dist_P8_P2_sq
        exact exact_dist (dist P8 P2) (379164 / 18529) dist_nonneg hsq
      · refine ⟨in_A_P3, ?_⟩
        have hsq : dist P8 P3 ^ 2 = 379164 / 18529 := dist_P8_P3_sq
        exact exact_dist (dist P8 P3) (379164 / 18529) dist_nonneg hsq
      · refine ⟨in_A_P5, ?_⟩
        have hsq : dist P8 P5 ^ 2 = 379164 / 18529 := dist_P8_P5_sq
        exact exact_dist (dist P8 P5) (379164 / 18529) dist_nonneg hsq
    have h_card : (insert P2 (insert P3 {P5}) : Finset ℝ²).card = 3 := by
      apply card_three_of_insert P2 P3 P5
      · exact P2_ne_P3
      · exact P3_ne_P5
      · exact P5_ne_P2
    rw [←h_card]
    exact Finset.card_le_card h_sub


/--
Erdős originally conjectured this (in [Er46b]) with no 3 vertices equidistant,
but Danzer found a convex polygon on 9 points such that every vertex has three
vertices equidistant from it (but this distance depends on the vertex).
Danzer's construction is explained in [Er87b].
-/
@[category research formally solved using formal_conjectures at "https://github.com/theaustinhatfield/formal-conjectures/blob/solve-erdos-97-danzer/FormalConjectures/ErdosProblems/97.lean", AMS 52]
theorem erdos_97.variants.three_equidistant :
    ∃ A : Finset ℝ², A.Nonempty ∧ ConvexIndep A ∧ HasNEquidistantProperty 3 A := by
  use A
  refine ⟨?_, ?_, has_equidistant⟩
  · use P0; exact in_A_P0
  · apply my_convex_indep
    intro p hp
    have hp_cases := mem_A_cases p hp
    rcases hp_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact sep_P0
    · exact sep_P1
    · exact sep_P2
    · exact sep_P3
    · exact sep_P4
    · exact sep_P5
    · exact sep_P6
    · exact sep_P7
    · exact sep_P8

end Erdos97
