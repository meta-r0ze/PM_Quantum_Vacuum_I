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
the cost is the boundary measure, with one density. A primitive transition across a boundary
edge is one event, and the ordered count lists each cut edge twice
(`distinctions_card_eq_two_mul`), so one transition per boundary edge is density `1/2` per ordered
pair (`cost_per_cut_edge`).
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

/-- Undirected cut edges: adjacent pairs in different states, each counted once. -/
def cutEdges [LinearOrder V] (x : V → Bool) : Finset (V × V) :=
  (distinctions G x).filter fun p => p.1 < p.2

/-- **Each cut edge occurs twice among the ordered distinctions.** -/
theorem distinctions_card_eq_two_mul [LinearOrder V] (x : V → Bool) :
    (distinctions G x).card = 2 * (cutEdges G x).card := by
  set D := distinctions G x
  have hne : ∀ p ∈ D, p.1 ≠ p.2 := by
    intro p hp h
    simp only [D, distinctions, mem_filter] at hp
    exact hp.2 (by rw [h])
  have hsplit : D = D.filter (fun p => p.1 < p.2) ∪ D.filter (fun p => p.2 < p.1) := by
    ext p
    simp only [mem_union, mem_filter]
    constructor
    · intro h
      rcases lt_or_gt_of_ne (hne p h) with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint (D.filter fun p => p.1 < p.2) (D.filter fun p => p.2 < p.1) := by
    rw [disjoint_filter]; intro p _ h1 h2; exact lt_asymm h1 h2
  have hswap : (D.filter fun p => p.2 < p.1) =
      (D.filter fun p => p.1 < p.2).map (Equiv.prodComm V V).toEmbedding := by
    ext ⟨a, b⟩
    simp only [D, distinctions, pairs, mem_filter, mem_univ, true_and, mem_map_equiv,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨G.adj_symm h1, Ne.symm h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨G.adj_symm h1, Ne.symm h2⟩, h3⟩
  rw [hsplit, card_union_of_disjoint hdisj, hswap, card_map]
  simp only [cutEdges, D]; omega

/-- **One transition per cut edge.** A primitive transition across a boundary edge (a swap of
the two neighbouring states) is one event, while the ordered distinction count lists that edge
twice. So the density that makes the cost one transition per boundary edge is `1/2` per ordered
distinction, and the cost is the number of cut edges. -/
theorem cost_per_cut_edge [LinearOrder V] (x : V → Bool) :
    localCost G (fun _ => 0) (fun a b => if a = b then 0 else 1 / 2) x = (cutEdges G x).card := by
  rw [only_distinctions_cost G _ _ rfl rfl (fun _ => rfl)
    (fun a b => by cases a <;> cases b <;> rfl), distinctions_card_eq_two_mul]
  push_cast; norm_num

end PMArch.Distinctions
