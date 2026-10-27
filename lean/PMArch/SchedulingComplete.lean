import PMArch.Selection

namespace PMArch

def idlePlacement (Δ M : ℕ) (h : 2 * M ≤ Δ) (i : Fin M) : Fin Δ :=
  ⟨2 * i.val, by omega⟩

theorem idlePlacement_injective (Δ M : ℕ) (h : 2 * M ≤ Δ) :
    Function.Injective (idlePlacement Δ M h) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  dsimp [idlePlacement] at hv
  omega

/-- M idle slots at 0,2,...,2M-2. -/
def spacedIdle (Δ M : ℕ) (h : 2 * M ≤ Δ) : Finset (Fin Δ) :=
  Finset.univ.image (idlePlacement Δ M h)

theorem spacedIdle_card (Δ M : ℕ) (h : 2 * M ≤ Δ) :
    (spacedIdle Δ M h).card = M := by
  rw [spacedIdle, Finset.card_image_of_injective _ (idlePlacement_injective Δ M h)]
  simp

theorem spacedIdle_isolated (Δ M : ℕ) (h : 2 * M ≤ Δ) :
    NoAdjacentIdle (finRotate Δ) (Finset.univ \ spacedIdle Δ M h) := by
  intro s hs
  have hs' : s ∈ spacedIdle Δ M h := by simpa using hs
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs'
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hn
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hn
  cases Δ with
  | zero => omega
  | succ d =>
    have hi : 2 * i.val < d := by omega
    have hv := congrArg Fin.val hj
    simp only [idlePlacement, finRotate_of_lt hi] at hv
    omega

/-- Complete existence criterion on a single cycle; Δ=N=0 is allowed. -/
theorem cyclic_schedule_exists_iff (N Δ : ℕ) :
    (∃ active : Finset (Fin Δ), active.card = N ∧
      NoAdjacentIdle (finRotate Δ) active) ↔ N ≤ Δ ∧ Δ ≤ 2 * N := by
  constructor
  · rintro ⟨a, ha, hi⟩
    constructor
    · have hc := Finset.card_le_univ a
      simpa [ha] using hc
    · have hc := periodic_schedule_bound (finRotate Δ) a hi
      simpa [ha] using hc
  · rintro ⟨hlo, hhi⟩
    have hb : 2 * (Δ - N) ≤ Δ := by omega
    refine ⟨Finset.univ \ spacedIdle Δ (Δ - N) hb, ?_,
      spacedIdle_isolated Δ (Δ - N) hb⟩
    have hc := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (spacedIdle Δ (Δ - N) hb))
    rw [spacedIdle_card] at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega

end PMArch
