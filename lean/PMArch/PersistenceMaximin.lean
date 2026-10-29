import PMArch.PersistenceEvents
import PMArch.TollFilters
import PMFramework.LawSelection

/-!
# The uniform measure as the law that persists for every reference

The correction terms are probabilities that a configuration returns to its reference. On the
channel labels and the clock slots the uniform measure is forced by symmetry
(`ChannelSymmetry.invariant_uniform`, `ImpedanceTerms.governor_uniform`). The `σ` interaction
directions, the residual target addresses and Margin's configurations have no such symmetry; the
`σ` labels are even of two kinds. This module does not need symmetry.

By Closure no label is intrinsically the reference: whichever configuration a defect currently
holds is its reference. Under a law `p` a defect referenced to `ω` returns with probability `p ω`,
so the persistence the law guarantees for every defect is `min_ω p ω` (`guaranteed`). A law that
favours some labels starves the others, and the defects referenced to those fail first. The
persistence premise is that the law in force is one that no other law beats on this guarantee
(`Maximin`), the same reading as Capacity, which is the largest allocation the causal bound
admits.

This premise is the framework's Selection Principle applied to event laws
(`PMFramework.LawSelection`): among candidate laws with positive initial weight, the surviving
ensemble concentrates on the law of least long-run cost rate. Scored by the worst-case rate
`−log min p` or by the average rate `−(1/|Ω|) Σ log p` (a reference that visits every label),
that law is the uniform law (`selected_uniform_worst`, `selected_uniform_average`), which is
exactly the maximin law (`maximin_iff_selected`).

* `guaranteed_le`: every law guarantees at most `1/|Ω|`.
* `maximin_iff`: a law attains that exactly when it is uniform. So the maximin law exists, is
  unique, and is uniform on any finite label set, whatever its labels are.
* `maximin_product`: on a product of label sets the maximin law is the product of the uniform
  laws. The independence of the Toll filters and of Margin's three domains is derived, not
  assumed.
* `toll_maximin`, `protocol_maximin`, `margin_maximin`: Toll, Protocol and Margin are the
  persistence probabilities of the maximin laws on their configuration spaces.
-/

noncomputable section
namespace PMArch.PersistenceMaximin
open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- A probability law on a finite label set. -/
def IsLaw (p : Ω → ℝ) : Prop := (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1

/-- The persistence a law guarantees whatever the reference: its least return probability. -/
def guaranteed (p : Ω → ℝ) : ℝ := univ.inf' univ_nonempty p

/-- No law guarantees more persistence for every reference. -/
def Maximin (p : Ω → ℝ) : Prop := IsLaw p ∧ ∀ q : Ω → ℝ, IsLaw q → guaranteed q ≤ guaranteed p

lemma card_pos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos

/-- **No law guarantees more than `1/|Ω|`.** -/
theorem guaranteed_le (p : Ω → ℝ) (hp : IsLaw p) : guaranteed p ≤ 1 / Fintype.card Ω := by
  have h : ∑ _ω : Ω, guaranteed p ≤ ∑ ω, p ω :=
    sum_le_sum fun ω _ => inf'_le _ (mem_univ ω)
  rw [sum_const, card_univ, nsmul_eq_mul, hp.2] at h
  rw [le_div_iff₀ card_pos]; linarith

def uniform : Ω → ℝ := fun _ => 1 / Fintype.card Ω

theorem uniform_law : IsLaw (uniform (Ω := Ω)) := by
  refine ⟨fun _ => by unfold uniform; positivity, ?_⟩
  simp only [uniform, sum_const, card_univ, nsmul_eq_mul]
  field_simp [card_pos.ne']

theorem uniform_guaranteed : guaranteed (uniform (Ω := Ω)) = 1 / Fintype.card Ω := by
  unfold guaranteed uniform
  exact inf'_const _ _

/-- **The maximin law is exactly the uniform law.** -/
theorem maximin_iff (p : Ω → ℝ) : Maximin p ↔ ∀ ω, p ω = 1 / Fintype.card Ω := by
  constructor
  · rintro ⟨hp, hmax⟩
    have hg : 1 / Fintype.card Ω ≤ guaranteed p := uniform_guaranteed (Ω := Ω) ▸ hmax _ uniform_law
    have hlow : ∀ ω, 1 / Fintype.card Ω ≤ p ω := fun ω => hg.trans (inf'_le _ (mem_univ ω))
    have hz : ∑ ω, (p ω - 1 / Fintype.card Ω) = 0 := by
      rw [sum_sub_distrib, hp.2, sum_const, card_univ, nsmul_eq_mul]
      field_simp [card_pos.ne']; ring
    have := (sum_eq_zero_iff_of_nonneg fun ω _ => sub_nonneg.2 (hlow ω)).mp hz
    intro ω; linarith [this ω (mem_univ ω)]
  · intro h
    have hp : p = uniform := funext h
    subst hp
    exact ⟨uniform_law, fun q hq => (guaranteed_le q hq).trans uniform_guaranteed.ge⟩

theorem maximin_exists : Maximin (uniform (Ω := Ω)) := (maximin_iff _).mpr fun _ => rfl

/-- Under the maximin law an event's probability is its counting measure. -/
theorem maximin_event {p : Ω → ℝ} (hp : Maximin p) (E : Finset Ω) :
    ∑ ω ∈ E, p ω = PersistenceEvents.mass E := by
  rw [sum_congr rfl fun ω _ => (maximin_iff p).mp hp ω, sum_const, nsmul_eq_mul,
    PersistenceEvents.mass]
  ring

/-- **Independence is derived.** On a product of label sets the maximin law is the product of
the uniform laws. -/
theorem maximin_product {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    {p : α × β → ℝ} (hp : Maximin p) (a : α) (b : β) :
    p (a, b) = (1 / Fintype.card α) * (1 / Fintype.card β) := by
  rw [(maximin_iff p).mp hp, Fintype.card_prod]; push_cast; ring

/-- **The maximin law is the law that selection keeps.** -/
theorem maximin_iff_selected (p : Ω → ℝ) : Maximin p ↔ p = PMFramework.LawSelection.uniform := by
  rw [maximin_iff]
  constructor
  · intro h; funext ω; exact h ω
  · rintro rfl ω; rfl

/-- The selected law minimizes both long-run cost rates, and only it does. -/
theorem maximin_minimizes_rates {p : Ω → ℝ} (hp : PMFramework.LawSelection.PosLaw p) :
    Maximin p ↔ PMFramework.LawSelection.averageRate p = Real.log (Fintype.card Ω) ∧
      PMFramework.LawSelection.worstRate p = Real.log (Fintype.card Ω) := by
  rw [maximin_iff_selected, PMFramework.LawSelection.averageRate_eq_iff hp,
    PMFramework.LawSelection.worstRate_eq_iff hp, and_self]

/-! ## The correction terms -/

/-- **Toll.** With the maximin law on the vertex configurations (three legs and a direction) and
on the target address, the persistence probability of a transition is the Toll term. -/
theorem toll_maximin {p : Fin 32 × Fin 32 × Fin 32 × Fin 5 → ℝ} (hp : Maximin p)
    {q : Fin 172 → ℝ} (hq : Maximin q) (e : Fin 5 → Fin 172) (he : Function.Injective e) :
    (∑ x ∈ ({0} : Finset (Fin 32)) ×ˢ ({0} : Finset (Fin 32)) ×ˢ
        (univ.filter fun o : Fin 32 => (o : ℕ) < 2) ×ˢ ({0} : Finset (Fin 5)), p x) *
      (∑ t ∈ univ \ univ.image e, q t) = tollTerm baseline := by
  rw [maximin_event hp, maximin_event hq, PersistenceEvents.toll_persistence]
  congr 1
  have := TollFilters.nonaliasing_prob e he
  rw [PersistenceEvents.mass, this]; norm_num

/-- **Protocol.** Under the maximin law on the residual addresses, the one successor is reached
with the Protocol probability. -/
theorem protocol_maximin {p : Fin 167 → ℝ} (hp : Maximin p) (s : Fin 167) :
    p s = -protocolTerm baseline := by
  rw [(maximin_iff p).mp hp]
  norm_num [protocolTerm, baseline, Parameters.resolution]

/-- **Margin.** Under the maximin law on the configurations of a localized defect, the reference
configuration has the Margin probability. -/
theorem margin_maximin {p : Fin 31 × Fin 6 × Fin 43 × Fin 43 → ℝ} (hp : Maximin p)
    (x : Fin 31 × Fin 6 × Fin 43 × Fin 43) : p x = marginTerm baseline := by
  rw [(maximin_iff p).mp hp]
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num [marginTerm, baseline, Parameters.embeddingLoad, Parameters.intrinsicLoad]

end PMArch.PersistenceMaximin
