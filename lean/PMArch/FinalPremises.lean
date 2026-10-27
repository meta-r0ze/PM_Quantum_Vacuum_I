import PMArch.E8Invariants
import PMArch.DerivedParameters

/-!
# The last premises

* **Description length 31** (`description_length`). A persisting defect's description over one
  transition is a record of independent fields: its channel content (`ν`), its configuration
  (`σ`), its boundary closures (`χ`), and where it is and where it goes next (`D` each, Causality).
  Independent fields concatenate, so the label count is the sum, `ν + σ + χ + 2D = 31` on the forced
  parameters. The forced substrate gives the same number intrinsically: `(|Φ(E₈)| + 8)/8 = 31`,
  its 240 nearest-neighbour moves plus its 8 coordinate directions, per coordinate.
* **The defect's invisible symmetry** (`orientation_relabelings`). The boundary's discrete data
  beyond its distinctions is its orientation, a two-element set (`Orientation.two_orientations`).
  Its relabelings are the identity and the flip — nothing else.
* **A leg carries its local observation** (`leg_factorization`). Under Closure a vertex can only
  respond to what is locally observable. If an update is insensitive to differences the local
  observation cannot see, it factors through that observation; when the observation is binary,
  the leg's effective alphabet is one bit.
-/

namespace PMArch.FinalPremises
open Matrix

/-- The fields of a defect's description: channel content, configuration, boundary closures,
current and next coordinates. -/
abbrev Description (p : Parameters) :=
  Fin p.sectorChannels ⊕ Fin p.embeddingDimension ⊕ Fin p.eulerCharacteristic ⊕
    Fin p.dimension ⊕ Fin p.dimension

/-- **Description length.** On the forced parameters the description has 31 labels, equal to the
substrate's moves-plus-directions per coordinate. -/
theorem description_length :
    Fintype.card (Description baseline) = baseline.embeddingLoad ∧
      Fintype.card (Description baseline) = 31 ∧
      (Nat.card {z : Fin 8 → ℤ // z ⬝ᵥ (Lattices.gram *ᵥ z) = 2} + 8) / 8 = 31 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Description, Fintype.card_sum, Fintype.card_fin]; decide
  · simp only [Description, Fintype.card_sum, Fintype.card_fin]; decide
  · rw [ThetaE8.e8_card_roots]

/-- **The only relabelings of the orientation data are the identity and the flip.** -/
theorem orientation_relabelings :
    Fintype.card (Equiv.Perm (Fin 2)) = 2 ∧
      ∀ σ : Equiv.Perm (Fin 2), σ = 1 ∨ σ = Equiv.swap 0 1 := by
  refine ⟨by rw [Fintype.card_perm]; rfl, by decide⟩

/-- **A leg carries its local observation.** An update that cannot distinguish states with the
same local observation factors through the observation. -/
theorem leg_factorization {S R : Type*} [Inhabited R] (obs : S → Bool) (f : S → R)
    (hinv : ∀ a b, obs a = obs b → f a = f b) :
    ∃ g : Bool → R, ∀ s, f s = g (obs s) := by
  classical
  refine ⟨fun o => if h : ∃ s, obs s = o then f h.choose else default, ?_⟩
  · intro s
    have h : ∃ t, obs t = obs s := ⟨s, rfl⟩
    simp only [h, dite_true]
    exact hinv _ _ h.choose_spec |>.symm

/-- **Every coordinate is needed (Conservation), none is spare (Economy).** For a state with
independent nontrivial coordinates, a description keeping only the coordinates in `K` is
injective exactly when it keeps them all. -/
theorem description_minimal {ι : Type*} [DecidableEq ι] {F : ι → Type*} [∀ i, Nontrivial (F i)]
    [∀ i, Inhabited (F i)] (K : Set ι) :
    Function.Injective (fun (x : ∀ i, F i) (i : K) => x i) ↔ ∀ i, i ∈ K := by
  constructor
  · intro hinj i
    by_contra hi
    obtain ⟨a, b, hab⟩ := exists_pair_ne (F i)
    let x0 : ∀ j, F j := fun _ => default
    have : Function.update x0 i a = Function.update x0 i b := hinj (by
      funext j
      have hj : (j : ι) ≠ i := fun h => hi (h ▸ j.2)
      simp [Function.update_of_ne hj])
    exact hab (by simpa using congrFun this i)
  · intro hK x y hxy
    funext i
    exact congrFun hxy ⟨i, hK i⟩

/-- On the forced parameters: the defect's 31 binary coordinates are all required. -/
theorem defect_description_minimal (K : Set (Description baseline)) :
    Function.Injective (fun (x : Description baseline → Bool) (i : K) => x i) ↔ ∀ i, i ∈ K :=
  description_minimal (F := fun _ => Bool) K

end PMArch.FinalPremises
