import PMArch.ProtocolToll

/-!
# Toll and Protocol share one residual address set

The defect's embedding occupies `σ` of the `R_M` coordinate–phase addresses. The addresses it
does not occupy form the residual set; any injective placement leaves exactly `R_M − σ` of
them (`residual_card`). Protocol's channel count and Toll's non-aliasing factor are both this
set, so `167` is one quantity, not two choices.

`toll_as_filters`: Toll is the product of independent filter probabilities on uniform labels —
two legs fixed (`1/N` each), the third leg in one of `χ` boundary orientations (`χ/N`), the
interaction label fixed (`1/σ`), and a non-aliasing target address (`(R_M − σ)/R_M`).
-/

noncomputable section
namespace PMArch.TollFilters
open Finset

/-- An injective embedding of `σ` labels into `R` addresses leaves `R − σ` residual addresses. -/
theorem residual_card {σ R : ℕ} (e : Fin σ → Fin R) (he : Function.Injective e) :
    (univ \ univ.image e).card = R - σ := by
  rw [card_sdiff_of_subset (subset_univ _), card_image_of_injective _ he]
  simp

/-- Non-aliasing probability of a uniformly chosen target address. -/
theorem nonaliasing_prob {σ R : ℕ} (e : Fin σ → Fin R) (he : Function.Injective e) :
    ((univ \ univ.image e).card : ℝ) / Fintype.card (Fin R) = ((R : ℝ) - σ) / R := by
  have hle : σ ≤ R := by simpa using Fintype.card_le_of_injective e he
  rw [residual_card e he, Fintype.card_fin, Nat.cast_sub hle]

/-- Protocol over the residual set: unit channels in parallel. -/
theorem protocol_residual {σ R : ℕ} (e : Fin σ → Fin R) (he : Function.Injective e) :
    ProtocolToll.protocolCredit (fun _ : ↥(univ \ univ.image e) => (1 : ℝ)) =
      -(1 / ((R : ℝ) - σ)) := by
  have hle : σ ≤ R := by simpa using Fintype.card_le_of_injective e he
  simp only [ProtocolToll.protocolCredit, ProtocolToll.parallelAdmittance, sum_const, card_univ,
    Fintype.card_coe, residual_card e he, nsmul_eq_mul, mul_one, one_div, Nat.cast_sub hle]

/-- **Toll as independent filters.** -/
theorem toll_as_filters (N σ R χ : ℝ) :
    χ * (R - σ) / (N ^ 3 * σ * R) = (1 / N) * (1 / N) * (χ / N) * (1 / σ) * ((R - σ) / R) :=
  ProtocolToll.toll_factorization N σ R χ

end PMArch.TollFilters
