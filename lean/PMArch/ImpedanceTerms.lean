import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Structural lemmas behind individual impedance terms

These lemmas do not prove the full six-term law. They isolate the steps of the
original System 2 arguments that are purely mathematical, so that the remaining
premises are visible as premises.

* **Governor.** A credit spread over a cycle of `n` slots that no slot can tell
  apart from its successor (Homogeneity: no preferred time) is uniform; if the
  total is `χ`, each slot carries exactly `χ / n`.
* **Map.** Among closed surfaces, the Euler characteristic is at most `2`, with
  equality exactly for the sphere.
* **Margin (local volume).** Any tree with `σ` edges has `σ + 1` vertices.
  If in addition one vertex is adjacent to every other (radius one), every edge
  touches that vertex: the tree is the star.
* **Toll / Margin counting.** Independent (product) configuration spaces have
  multiplicative cardinality.
-/

namespace PMArch.ImpedanceTerms

open Finset

/-! ## Governor: shift invariance forces uniform distribution -/

theorem shift_invariant_const {n : ℕ} [NeZero n] (f : ZMod n → ℝ)
    (h : ∀ i, f (i + 1) = f i) : ∀ i, f i = f 0 := by
  have hk : ∀ k : ℕ, f (k : ZMod n) = f 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, h, ih]
  intro i
  rw [← ZMod.natCast_zmod_val i]
  exact hk _

/-- Homogeneity over a cycle of `n` slots plus a fixed total `χ` determines the
per-slot share: it is `χ / n`. -/
theorem governor_uniform {n : ℕ} [NeZero n] (f : ZMod n → ℝ) (χ : ℝ)
    (h : ∀ i, f (i + 1) = f i) (htot : ∑ i, f i = χ) :
    ∀ i, f i = χ / n := by
  have hc := shift_invariant_const f h
  have hsum : ∑ i, f i = n * f 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hc i)]
    simp [ZMod.card]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  intro i
  rw [hc i, eq_div_iff hn, ← htot, hsum, mul_comm]

/-- Baseline instance: a credit of `2` over the `43`-cycle gives `2/43` per slot. -/
theorem governor_baseline (f : ZMod 43 → ℝ) (h : ∀ i, f (i + 1) = f i)
    (htot : ∑ i, f i = 2) : ∀ i, f i = 2 / 43 := by
  have := governor_uniform f 2 h htot
  simpa using this

/-! ## Map: the sphere maximizes the Euler characteristic -/

/-- Closed connected surfaces by the classification theorem: orientable of genus
`g`, or non-orientable with `k ≥ 1` crosscaps. -/
inductive ClosedSurface
  | orientable (g : ℕ)
  | nonorientable (k : ℕ) (hk : 1 ≤ k)

def ClosedSurface.euler : ClosedSurface → ℤ
  | .orientable g => 2 - 2 * g
  | .nonorientable k _ => 2 - k

theorem euler_le_two (S : ClosedSurface) : S.euler ≤ 2 := by
  cases S <;> simp [ClosedSurface.euler]

theorem euler_eq_two_iff (S : ClosedSurface) :
    S.euler = 2 ↔ S = .orientable 0 := by
  cases S with
  | orientable g =>
    simp only [ClosedSurface.euler, ClosedSurface.orientable.injEq]; omega
  | nonorientable k hk =>
    simp only [ClosedSurface.euler, reduceCtorEq, iff_false]; omega

/-! ## Margin: trees with `σ` edges, and the radius-one star -/

theorem tree_vertices {V : Type*} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsTree) (σ : ℕ) (hσ : G.edgeFinset.card = σ) :
    Fintype.card V = σ + 1 := by
  rw [← hG.card_edgeFinset, hσ]

/-- In an acyclic graph in which a center `c` is adjacent to every other vertex,
every edge has `c` as an endpoint: the graph is a star centred at `c`. -/
theorem radius_one_star {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (c : V) (hc : ∀ v, v ≠ c → G.Adj c v) :
    ∀ u v, G.Adj u v → u = c ∨ v = c := by
  intro u v huv
  by_contra hne
  push Not at hne
  obtain ⟨hu, hv⟩ := hne
  have huv' : u ≠ v := G.ne_of_adj huv
  -- direct path u → v
  let p : G.Path u v := ⟨SimpleGraph.Walk.cons huv .nil, by simp [huv']⟩
  -- path u → c → v
  have hcu : G.Adj u c := (hc u hu).symm
  let q : G.Path u v :=
    ⟨SimpleGraph.Walk.cons hcu (SimpleGraph.Walk.cons (hc v hv) .nil), by
      simp [SimpleGraph.Walk.cons_isPath_iff, hu, huv', hv.symm]⟩
  have := congrArg (fun r : G.Path u v => r.1.length) ((hG.subsingleton_path u v).elim p q)
  simp [p, q] at this

/-! ## Counting: independent factors multiply -/

theorem product_count (a b c : ℕ) :
    Fintype.card (Fin a × Fin b × Fin c) = a * b * c := by
  simp [mul_assoc]

theorem margin_volume :
    Fintype.card (Fin 31 × Fin (5 + 1) × Fin 43 × Fin 43) = 31 * 6 * 43 ^ 2 := by
  simp

end PMArch.ImpedanceTerms
