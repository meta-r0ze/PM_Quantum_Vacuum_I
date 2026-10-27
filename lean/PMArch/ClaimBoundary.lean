import PMArch.TranslationD
import PMArch.E8Unique
import PMArch.PhysicalBridge

/-!
# Paper I: exact boundary of the proposed persistence-to-vacuum claim

This module does not define the philosophical word persistence so as to force E8.
It composes the existing lattice theorems and exposes the extra hypotheses.
The finite clock examples are operational models, not alternative quantum vacua.
-/
noncomputable section
namespace PMArch.ClaimBoundary
open Matrix

/-- Integral equivalence, allowing the rank to be determined by constraints. -/
def IsE8 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ e : Fin 8 ≃ Fin n, ∃ P : Matrix (Fin 8) (Fin 8) ℤ,
    IsUnit P.det ∧ Pᵀ * A.submatrix e e * P = Lattices.gram

/-- Minimality is over the entire nonzero positive even unimodular lattice
class, not an assumed upper bound of eight. It remains a selection premise. -/
def MinimalRank (n : ℕ) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin m) (Fin m) ℤ),
    (B.map (Int.cast : ℤ → ℝ)).PosDef →
    (∀ z : Fin m → ℤ, Even (z ⬝ᵥ (B *ᵥ z))) → IsUnit B.det →
    0 < m → n ≤ m

/-- A single checked chain from finite cost levels and the two state-sum
symmetries to E8. The integral quadratic lattice model, these symmetries,
nontriviality and rank minimization are explicit; FCC alone is not the input. -/
theorem state_sum_selects_e8 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hsym : A.IsSymm)
    (hfinite : ∀ c : ℤ, ({z : Fin n → ℤ | z ⬝ᵥ (A *ᵥ z) ≤ c}).Finite)
    (hT : ∀ s : ℂ, 0 < s.re →
      RankEight.theta (A.map (Int.cast : ℤ → ℝ)) (s - Complex.I) =
      RankEight.theta (A.map (Int.cast : ℤ → ℝ)) s)
    (hS : ∀ s : ℂ, 0 < s.re →
      RankEight.theta (A.map (Int.cast : ℤ → ℝ)) s =
      ((s ^ (1 / 2 : ℂ)) ^ n)⁻¹ *
      RankEight.theta (A.map (Int.cast : ℤ → ℝ)) s⁻¹)
    (hnonzero : 0 < n) (hminimal : MinimalRank n) : IsE8 A := by
  have hp := (Translation.posDef_iff_finite_levels hsym).mpr hfinite
  have he := (Translation.even_iff_T_invariant hp).mpr hT
  have hd := (Translation.unimodular_iff_S_covariant hp).mpr hS
  have h8 := RankEight.e8_even_unimodular
  have hle : n ≤ 8 := hminimal 8 Lattices.gram h8.1 h8.2.1 h8.2.2 (by decide)
  have hn := RankEight.minimal_rank_eight_of_lattice A hp he hd hnonzero hle
  subst n
  obtain ⟨P, hP, hgram⟩ := E8Unique.e8_unique A hp he hd
  exact ⟨Equiv.refl _, P, hP, by simpa using hgram⟩

/-- The numerical conclusion still needs electromagnetic matching, even after
E8 and the clock have been selected. The cost law and other baseline integers
are definitions/inputs through `baseline`, not deductions from the schedule. -/
theorem clock_and_matching_select_inverse_coupling {Δ : ℕ}
    (encode : Fin 32 → Fin Δ) (hinj : Function.Injective encode)
    (advance : Equiv.Perm (Fin Δ)) (active : Finset (Fin Δ))
    (hactive : active.card = 32) (hgap : NoAdjacentIdle advance active)
    (hc : Δ ∈ discriminantCandidates)
    (gSquared : ℝ) (hg : 0 < gSquared)
    (hmatch : 4 * Real.pi / gSquared = impedance {baseline with period := Δ}) :
    Δ = 43 ∧
    (137.035999212381397211 : ℝ) < (gSquared / (4 * Real.pi))⁻¹ ∧
    (gSquared / (4 * Real.pi))⁻¹ < (137.035999212381397213 : ℝ) := by
  have hd := schedule_selects_43 encode hinj advance active hactive hgap hc
  subst Δ
  refine ⟨rfl, ?_⟩
  apply physical_inverse_coupling_bounds gSquared hg
  simpa only [baseline, geometricIndex] using hmatch

/-- One explicit operational interpretation of finite resources, preserved
identity and ordered causal updates. This is deliberately not a definition
of all PM postulates or a quantum-vacuum construction. -/
structure FiniteClock where
  update : Equiv.Perm (Fin 2 × Fin 2)
  preservesLabel : ∀ x, (update x).1 = x.1
  tick : ℝ
  tickPositive : 0 < tick
  response : ℝ
  responsePositive : 0 < response

/-- A conserved nontrivial label and a moving clock, with any positive
response coefficient. No proposed constitutive impedance law is imposed. -/
def clockWithResponse (Z : ℝ) (hZ : 0 < Z) : FiniteClock where
  update := Equiv.prodCongr (Equiv.refl _) (finRotate 2)
  preservesLabel := fun _ => rfl
  tick := 1
  tickPositive := by norm_num
  response := Z
  responsePositive := hZ

theorem clock_moves (Z : ℝ) (hZ : 0 < Z) :
    (clockWithResponse Z hZ).update (0,0) ≠ (0,0) := by
  change ((0 : Fin 2), finRotate 2 (0 : Fin 2)) ≠ (0,0)
  decide

theorem clock_preserves_distinctions (Z : ℝ) (hZ : 0 < Z) (t : ℕ) :
    Function.Injective (((clockWithResponse Z hZ).update :
      (Fin 2 × Fin 2) → (Fin 2 × Fin 2))^[t]) :=
  (clockWithResponse Z hZ).update.injective.iterate t

/-- The finite reversible dynamics and the positive tick can be identical
while the response differs. This is an independence witness for this explicit
operational model; it does not refute an additional physical matching law. -/
theorem operational_constraints_leave_response_free :
    ∃ a b : FiniteClock, a.update = b.update ∧ a.tick = b.tick ∧
      a.response ≠ b.response := by
  refine ⟨clockWithResponse 1 (by norm_num), clockWithResponse 2 (by norm_num),
    rfl, rfl, ?_⟩
  norm_num [clockWithResponse]

/-- Geometric symmetries alone cannot select an overall cost normalization.
Any positive multiple preserves every given cost symmetry and zero set. -/
theorem cost_scale_freedom {S : Type*} (Q : S → ℝ) (f : S → S)
    (hQ : ∀ x, Q (f x) = Q x) (c : ℝ) (hc : 0 < c) :
    (∀ x, c * Q (f x) = c * Q x) ∧
    (∀ x, c * Q x = 0 ↔ Q x = 0) := by
  constructor
  · intro x; rw [hQ]
  · intro x; simp [hc.ne']

end PMArch.ClaimBoundary
