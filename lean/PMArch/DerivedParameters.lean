import PMArch.Vacuum
import PMArch.ImpedanceTerms
import PMArch.CliffordSignature

/-!
# The integer inputs of the index are forced

`Impedance.baseline = ⟨D, Δ, ν, σ, χ⟩ = ⟨4, 43, 16, 5, 2⟩` was a typed-in parameter record.
Here every entry is derived:

* `D = n/2 = 4`: the coordinate sector is one of two isomorphic halves of the forced `E₈`.
* `Δ = 43`: the clock (`Vacuum.vacuum_selects`).
* `ν = 16`: two `D₄` glue classes of 8 minimal vectors each (`Channels`).
* `χ = 2`: **Postulate H** — the defect boundary is a closed surface of least topological
  complexity (Economy applied to the boundary), hence the sphere.
* `σ = (D − q) + 2 = 5`: positions in space times points of the boundary surface, where
  **Postulate G** (a complex structure from the Clifford volume element, `ω² = −1`) forces one
  time direction, `q = 1`, up to the overall sign convention.
-/

namespace PMArch.Derived
open ImpedanceTerms

/-- **Postulate G.** The coordinate-sector volume element squares to `−1` (it supplies the
complex structure), with `q` the number of time directions; by the overall sign convention the
time directions are the minority. -/
structure SignaturePostulate (q : Fin 5) : Prop where
  complex : (-1 : ℝ) ^ q.val = -1
  convention : q.val ≤ 2

theorem one_time {q : Fin 5} (h : SignaturePostulate q) : q.val = 1 := by
  rcases (Clifford.negative_square_iff q).mp h.complex with h1 | h3
  · exact h1
  · have := h.convention; omega

/-- **Postulate H.** The defect boundary is a closed connected surface with no more
topological complexity than any other: its Euler characteristic is maximal. -/
def BoundaryPostulate (S : ClosedSurface) : Prop := ∀ T : ClosedSurface, T.euler ≤ S.euler

theorem boundary_sphere {S : ClosedSurface} (h : BoundaryPostulate S) :
    S = .orientable 0 ∧ S.euler = 2 := by
  have h2 : S.euler = 2 := le_antisymm (euler_le_two S) (by simpa [ClosedSurface.euler] using h (.orientable 0))
  exact ⟨(euler_eq_two_iff S).mp h2, h2⟩

/-- Configuration dimension: spatial directions plus the two dimensions of the boundary
surface. -/
def configDim (D q : ℕ) : ℕ := (D - q) + 2

/-- The parameter record built from the substrate, the clock, the boundary and the signature. -/
def derived (s : Vacuum.Substrate) (Δ : ℕ) (q : Fin 5) (S : ClosedSurface) : Parameters :=
  ⟨s.n / 2, Δ, Channels.nu, configDim (s.n / 2) q.val, S.euler.toNat⟩

lemma rank_eight {s : Vacuum.Substrate} (h : ClaimBoundary.IsE8 s.A) : s.n = 8 := by
  obtain ⟨e, _⟩ := h
  simpa using (Fintype.card_congr e).symm

/-- **All integer inputs are forced.** -/
theorem parameters_forced {s : Vacuum.Substrate} {Δ : ℕ} {q : Fin 5} {S : ClosedSurface}
    (h : Vacuum.Geometric s) (hmin : Vacuum.Economical s) (hsec : Vacuum.SectorPostulates s)
    (hc : Vacuum.ClockPostulates s Δ) (hG : SignaturePostulate q) (hH : BoundaryPostulate S) :
    derived s Δ q S = baseline := by
  obtain ⟨he8, -, h43, -⟩ := Vacuum.vacuum_selects h hmin hsec hc
  have hn := rank_eight he8
  have hq := one_time hG
  have hS := (boundary_sphere hH).2
  simp only [derived, configDim, hn, h43, hq, hS, Channels.nu_eq, baseline]
  rfl

/-- **Main numerical theorem.** All postulates force the parameter record, and the six-term
index evaluated on it lies in the certified interval. -/
theorem index_bounds {s : Vacuum.Substrate} {Δ : ℕ} {q : Fin 5} {S : ClosedSurface}
    (h : Vacuum.Geometric s) (hmin : Vacuum.Economical s) (hsec : Vacuum.SectorPostulates s)
    (hc : Vacuum.ClockPostulates s Δ) (hG : SignaturePostulate q) (hH : BoundaryPostulate S) :
    (137.035999212381397211 : ℝ) < impedance (derived s Δ q S) ∧
      impedance (derived s Δ q S) < (137.035999212381397213 : ℝ) := by
  rw [parameters_forced h hmin hsec hc hG hH]
  exact geometricIndex_bounds

theorem signature_witness : SignaturePostulate 1 := ⟨by norm_num, by decide⟩
theorem boundary_witness : BoundaryPostulate (.orientable 0) := fun T => by
  simpa [ClosedSurface.euler] using euler_le_two T

end PMArch.Derived
