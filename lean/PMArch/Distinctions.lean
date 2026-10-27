import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Only distinctions cost

A configuration assigns each site one of two states (`false` = vacuum-like, `true` = defect).
Suppose the maintenance cost is

* **local** — a sum of a site term `s(x_v)` and a neighbour term `c(x_u, x_v)` over adjacent
  ordered pairs;
* **relative to the vacuum** — the vacuum's local terms vanish, `s(false) = 0`, `c(false,false) = 0`
  (the vacuum is the reference, Closure);
* **relabeling-symmetric** — exchanging the two state names changes nothing,
  `s(a) = s(!a)`, `c(a,b) = c(!a,!b)` (Closure: which state is called "vacuum" is not intrinsic).

`only_distinctions_cost`: then the cost is `c(false,true)` times the number of adjacent pairs in
different states. Uniform regions — the defect's interior as well as the vacuum — cost nothing;
the cost is the boundary measure, with one density. Toll sets that density to one transition.
-/

namespace PMArch.Distinctions
open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adjacent ordered pairs. -/
def pairs : Finset (V × V) := univ.filter fun p => G.Adj p.1 p.2

/-- A local cost: site terms plus neighbour terms. -/
def localCost (s : Bool → ℝ) (c : Bool → Bool → ℝ) (x : V → Bool) : ℝ :=
  ∑ v, s (x v) + ∑ p ∈ pairs G, c (x p.1) (x p.2)

/-- Distinctions: adjacent pairs in different states. -/
def distinctions (x : V → Bool) : Finset (V × V) := (pairs G).filter fun p => x p.1 ≠ x p.2

theorem only_distinctions_cost (s : Bool → ℝ) (c : Bool → Bool → ℝ)
    (hs0 : s false = 0) (hc0 : c false false = 0)
    (hsflip : ∀ a, s a = s (!a)) (hcflip : ∀ a b, c a b = c (!a) (!b)) (x : V → Bool) :
    localCost G s c x = c false true * (distinctions G x).card := by
  have hs : ∀ a, s a = 0 := by
    intro a; cases a
    · exact hs0
    · rw [hsflip]; exact hs0
  have hc : ∀ a b, c a b = if a = b then 0 else c false true := by
    intro a b
    cases a <;> cases b
    · simp [hc0]
    · simp
    · simp only [Bool.true_eq_false, ite_false]; rw [hcflip]; rfl
    · simp only [ite_true]; rw [hcflip]; exact hc0
  unfold localCost distinctions
  simp only [hs, sum_const_zero, zero_add]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hc]
  by_cases h : x p.1 = x p.2 <;> simp [h]

/-- **Relabeling symmetry is what removes area costs.** An area cost (each defect site costs one)
is local and vanishes on the vacuum, but distinguishes the two state names. -/
theorem area_breaks_relabeling :
    let s : Bool → ℝ := fun a => if a then 1 else 0
    s false = 0 ∧ s true ≠ s (!true) := by
  simp

end PMArch.Distinctions
