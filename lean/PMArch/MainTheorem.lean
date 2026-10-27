import PMArch.NetIndex
import PMArch.DerivedParameters
import PMArch.FinalPremises
import PMArch.PersistencePremises
import PMArch.Distinctions
import PMArch.Descartes
import PMArch.TollFilters
import PMArch.ClosureSymmetry
import PMArch.VacuumIndependence

/-!
# Main theorem

From the persistence postulates — the geometric postulates (`Vacuum.Geometric`), Economy
(`Vacuum.Economical`), the sector postulate (`Vacuum.SectorPostulates`), the clock postulates
(`Vacuum.ClockPostulates`), the signature postulate G and the boundary postulate H — the substrate
is `E₈` with two `D₄` sectors, the clock period is `43`, every integer input of the index is forced,
and the index, read as net transitions per cycle, is

`43π + 2 + 334/(32³·5·172) + 1/(31·6·43²) − 1/167 − 2/43 ∈ (137.035999212381397211, …213)`.

The meaning of each term (Capacity, Map, Toll, Margin, Protocol, Governor) is established by the
supporting modules; see `E8-SUBSTRATE-VALUES.md` for the map from term to theorem.
-/

namespace PMArch.Main
open ImpedanceTerms

theorem persistence_selects {s : Vacuum.Substrate} {Δ : ℕ} {q : Fin 5} {S : ClosedSurface}
    (h : Vacuum.Geometric s) (hmin : Vacuum.Economical s) (hsec : Vacuum.SectorPostulates s)
    (hc : Vacuum.ClockPostulates s Δ) (hG : Derived.SignaturePostulate q)
    (hH : Derived.BoundaryPostulate S) :
    ClaimBoundary.IsE8 s.A ∧
      (∃ T : Matrix (Fin s.n) (Fin 8) ℤ, T.transpose * s.A * T = Channels.d4d4) ∧
      Δ = 43 ∧ Derived.derived s Δ q S = baseline ∧
      impedance (Derived.derived s Δ q S) =
        43 * Real.pi + 2 + 334 / (32 ^ 3 * 5 * 172) + 1 / (31 * 6 * 43 ^ 2) - 1 / 167 - 2 / 43 ∧
      (137.035999212381397211 : ℝ) < impedance (Derived.derived s Δ q S) ∧
      impedance (Derived.derived s Δ q S) < (137.035999212381397213 : ℝ) := by
  obtain ⟨he8, hd4, h43, -⟩ := Vacuum.vacuum_selects h hmin hsec hc
  have hp := Derived.parameters_forced h hmin hsec hc hG hH
  refine ⟨he8, hd4, h43, hp, ?_, ?_⟩
  · rw [hp]
    have := geometricIndex_exact
    unfold geometricIndex at this
    rw [this]; ring
  · rw [hp]; exact geometricIndex_bounds

/-- The postulates are jointly satisfiable. -/
theorem postulates_satisfiable :
    ∃ (s : Vacuum.Substrate) (Δ : ℕ) (q : Fin 5) (S : ClosedSurface),
      Vacuum.Geometric s ∧ Vacuum.Economical s ∧ Vacuum.SectorPostulates s ∧
        Vacuum.ClockPostulates s Δ ∧ Derived.SignaturePostulate q ∧ Derived.BoundaryPostulate S :=
  ⟨Vacuum.e8, 43, 1, .orientable 0, Vacuum.e8_geometric, Vacuum.e8_economical, Vacuum.e8_sectors,
    Vacuum.e8_clock, Derived.signature_witness, Derived.boundary_witness⟩

end PMArch.Main
