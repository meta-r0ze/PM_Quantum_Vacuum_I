import PMArch.OrthogonalExchange
import PMArch.Research.OperationalDuality

/-!
# Exchange locality with the readout-completeness route to unimodularity

Research variant of the E8 selection, superseded by `Vacuum.geometric_selects_e8`.
-/
noncomputable section
namespace PMArch.OrthogonalExchange
open Matrix

/-- The new evenness criterion composes with the existing readout and rank
constraints. All physical applicability premises remain visible. -/
theorem orthogonal_exchange_selects_e8 {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hs : A.IsSymm)
    (hfinite : ∀ c : ℤ, ({z : Label n | z ⬝ᵥ (A *ᵥ z) ≤ c}).Finite)
    (C : Exchange n) (halt : Alternating C) (hloc : OrthogonalLocal A C)
    (hnonzero : C ≠ 0)
    (hread : OperationalDuality.FiniteReadoutComplete A A.det.natAbs)
    (hn : 0 < n) (hmin : ClaimBoundary.MinimalRank n) : ClaimBoundary.IsE8 A := by
  have hp := (Translation.posDef_iff_finite_levels hs).mpr hfinite
  have he := orthogonal_nontrivial_exchange_forces_even A hs C halt hloc hnonzero
  have hd := (OperationalDuality.intrinsic_readout_iff_unimodular A hp).mp hread
  exact ClaimBoundary.state_sum_selects_e8 A hs hfinite
    ((Translation.even_iff_T_invariant hp).mp he)
    ((Translation.unimodular_iff_S_covariant hp).mp hd) hn hmin

end PMArch.OrthogonalExchange
