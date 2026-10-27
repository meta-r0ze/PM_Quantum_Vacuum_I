import PMArch.Impedance

/-! Protocol and Toll as conditional constitutive laws. Parallel Ohmic channels,
unit admittances, uniform sampling and the chosen event are explicit inputs. -/
noncomputable section
namespace PMArch.ProtocolToll
open Finset

/-- Currents in parallel channels add at a shared potential difference. -/
theorem parallel_current {ι : Type*} [Fintype ι] (y : ι → ℝ) (v : ℝ) :
    ∑ i, y i * v = (∑ i, y i) * v := by rw [sum_mul]

def parallelAdmittance {ι : Type*} [Fintype ι] (y : ι → ℝ) : ℝ := ∑ i, y i

def protocolCredit {ι : Type*} [Fintype ι] (y : ι → ℝ) : ℝ :=
  -(parallelAdmittance y)⁻¹

theorem identical_channels (n : ℕ) (g : ℝ) :
    protocolCredit (fun _ : Fin n => g) = -(1 / ((n : ℝ) * g)) := by
  simp [protocolCredit, parallelAdmittance, one_div]

/-- The effective resistance follows from I = G V when G and V are nonzero. -/
theorem resistance_from_ohm {g v i : ℝ} (hg : g ≠ 0) (hv : v ≠ 0)
    (hi : i = g * v) : v / i = 1 / g := by
  rw [hi]
  field_simp

/-- Unit channel admittances and the stipulated negative credit recover Protocol. -/
theorem protocol_from_unit_channels (p : Parameters) (h : p.embeddingDimension < p.resolution) :
    protocolCredit (fun _ : Fin (p.resolution - p.embeddingDimension) => (1 : ℝ)) =
      protocolTerm p := by
  simp [protocolCredit, parallelAdmittance, protocolTerm, Nat.cast_sub (Nat.le_of_lt h), one_div]

theorem protocol_baseline :
    protocolCredit (fun _ : Fin 167 => (1 : ℝ)) = -(1 / 167) := by
  rw [identical_channels]
  norm_num

/-- Coordinate count alone does not fix Protocol: changing each admittance changes it. -/
theorem doubled_admittance_changes_protocol :
    protocolCredit (fun _ : Fin 167 => (2 : ℝ)) ≠
      protocolCredit (fun _ : Fin 167 => (1 : ℝ)) := by
  rw [identical_channels, identical_channels]
  norm_num

abbrev Trial (N σ R : ℕ) := Fin N × Fin N × Fin N × Fin σ × Fin R

/-- A general version of the paper's specified Toll event. -/
def placement {N σ R χ : ℕ} (hN : 0 < N) (hσ : 0 < σ)
    (hχ : χ ≤ N) (hR : σ ≤ R) (v : Fin χ × Fin (R - σ)) : Trial N σ R :=
  (⟨0, hN⟩, ⟨0, hN⟩, ⟨v.1.val, lt_of_lt_of_le v.1.isLt hχ⟩,
    ⟨0, hσ⟩, ⟨v.2.val + σ, by have := v.2.isLt; omega⟩)

theorem placement_injective {N σ R χ : ℕ} (hN : 0 < N) (hσ : 0 < σ)
    (hχ : χ ≤ N) (hR : σ ≤ R) : Function.Injective (placement hN hσ hχ hR) := by
  intro a b h
  have h1 := congrArg (fun x : Trial N σ R => x.2.2.1.val) h
  have h2 := congrArg (fun x : Trial N σ R => x.2.2.2.2.val) h
  apply Prod.ext
  · apply Fin.ext; exact h1
  · apply Fin.ext
    dsimp [placement] at h2
    omega

def event {N σ R χ : ℕ} (hN : 0 < N) (hσ : 0 < σ)
    (hχ : χ ≤ N) (hR : σ ≤ R) : Finset (Trial N σ R) :=
  univ.image (placement hN hσ hχ hR)

theorem event_count {N σ R χ : ℕ} (hN : 0 < N) (hσ : 0 < σ)
    (hχ : χ ≤ N) (hR : σ ≤ R) :
    (event hN hσ hχ hR).card = χ * (R - σ) := by
  rw [event, card_image_of_injective _ (placement_injective hN hσ hχ hR)]
  simp

theorem trial_count (N σ R : ℕ) : Fintype.card (Trial N σ R) = N^3 * σ * R := by
  simp [Trial]
  ring

theorem uniform_event_mass {N σ R χ : ℕ} (hN : 0 < N) (hσ : 0 < σ)
    (hχ : χ ≤ N) (hR : σ ≤ R) :
    ((event hN hσ hχ hR).card : ℝ) / Fintype.card (Trial N σ R) =
      χ * ((R : ℝ) - σ) / ((N : ℝ)^3 * σ * R) := by
  rw [event_count, trial_count]
  push_cast [Nat.cast_sub hR]
  rfl

/-- The product prior explains the factorization after the sampling law is specified. -/
theorem toll_factorization (N σ R χ : ℝ) :
    χ * (R - σ) / (N^3 * σ * R) =
      (1/N) * (1/N) * (χ/N) * (1/σ) * ((R-σ)/R) := by
  simp only [div_eq_mul_inv, mul_inv_rev ]
  ring

/-- General Toll formula, including the side condition omitted by baseline-only counting. -/
theorem toll_from_sampling (p : Parameters) (hp : p.Admissible)
    (hχ : p.eulerCharacteristic ≤ p.nodeCapacity) :
    ((event hp.2.1 hp.2.2.1 hχ (Nat.le_of_lt hp.2.2.2.1)).card : ℝ) /
      Fintype.card (Trial p.nodeCapacity p.embeddingDimension p.resolution) = tollTerm p := by
  exact uniform_event_mass hp.2.1 hp.2.2.1 hχ (Nat.le_of_lt hp.2.2.2.1)

/-- The event has genuinely probabilistic mass, independent of its later cost interpretation. -/
theorem event_mass_bounds {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Finset Ω) :
    0 ≤ (E.card : ℝ) / Fintype.card Ω ∧ (E.card : ℝ) / Fintype.card Ω ≤ 1 := by
  constructor
  · positivity
  · by_cases h : Fintype.card Ω = 0
    · simp [h]
    · have hd : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Nat.pos_of_ne_zero h
      apply (div_le_one hd).mpr
      exact_mod_cast E.card_le_univ

theorem uniform_singletons_sum (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    (∑ _ : Ω, (1 : ℝ) / Fintype.card Ω) = 1 := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hc]

/-- The cubic channel count is a three-leg choice; counting permits any arity. -/
theorem arity_trial_count (N σ R k : ℕ) :
    Fintype.card ((Fin k → Fin N) × Fin σ × Fin R) = N^k*σ*R := by
  simp [mul_assoc]

theorem arity_changes_toll :
    (334 : ℝ)/(32^2*5*172) ≠ 334/(32^3*5*172) := by norm_num

end PMArch.ProtocolToll
