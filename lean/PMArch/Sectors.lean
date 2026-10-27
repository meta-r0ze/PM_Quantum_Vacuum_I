import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Sector selection, channel count, and relational time

* `sector_selection`: among the rank-4 simply-laced root lattices (`A₄`, `D₄`, `A₃A₁`, `A₂A₂`,
  `A₂A₁A₁`, `A₁⁴`), `D₄` is the only one that is irreducible and has involutive glue
  (`2Λ* ⊆ Λ`). That this list is complete is the standard classification of simply-laced root
  systems; root subsystems of `E₈` are simply laced.
* `nu_eq_sixteen`: any two distinct channels among the three 8-dimensional representations
  `8_v, 8_s, 8_c` give `ν = 16`.
* `obs_injOn_iff`: if observations record only whether an idle run follows each active
  transition, schedules with idle runs of length at most `k` are reconstructable iff `k ≤ 1`;
  then the period is at most `2N` (`period_le_two_mul`).
-/

namespace PMArch.Sectors
open Matrix

/-! ## Rank-4 sectors -/

/-- Involutive glue: `2Λ* ⊆ Λ`, i.e. there is an integral `M` with `C M = 2`. -/
def InvolutiveGlue (C : Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  ∃ M : Matrix (Fin 4) (Fin 4) ℤ, C * M = (2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)

/-- Irreducibility: the Dynkin diagram is connected. -/
def Connected (C : Fin 4 → Fin 4 → ℤ) : Prop :=
  ∀ S : Finset (Fin 4), S.Nonempty → S ≠ Finset.univ → ∃ i ∈ S, ∃ j ∉ S, C i j ≠ 0

instance (C : Fin 4 → Fin 4 → ℤ) : Decidable (Connected C) := by
  unfold Connected; infer_instance

lemma involutiveGlue_iff (C A : Matrix (Fin 4) (Fin 4) ℤ) {d : ℤ} (hd : d ≠ 0)
    (h1 : C * A = d • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (h2 : A * C = d • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    InvolutiveGlue C ↔ ∀ i j, d ∣ 2 * A i j := by
  constructor
  · rintro ⟨M, hM⟩ i j
    have e : d • M = (2 : ℤ) • A := by
      calc d • M = (A * C) * M := by rw [h2, Matrix.smul_mul, Matrix.one_mul]
        _ = A * (C * M) := Matrix.mul_assoc _ _ _
        _ = (2 : ℤ) • A := by rw [hM, Matrix.mul_smul, Matrix.mul_one]
    have := congrFun (congrFun e i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact ⟨M i j, by linarith⟩
  · intro h
    choose k hk using h
    refine ⟨Matrix.of fun i j => k i j, ?_⟩
    have e : d • (C * Matrix.of fun i j => k i j) = d • ((2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) := by
      have hA : d • (Matrix.of fun i j => k i j) = (2 : ℤ) • A := by
        ext i j; simp [hk i j]
      rw [← Matrix.mul_smul, hA, Matrix.mul_smul, h1, smul_comm]
    exact smul_right_injective _ hd e

def cA4 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, -1, 0], ![0, -1, 2, -1], ![0, 0, -1, 2]]
def cD4 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, -1, -1], ![0, -1, 2, 0], ![0, -1, 0, 2]]
def cA3A1 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, -1, 0], ![0, -1, 2, 0], ![0, 0, 0, 2]]
def cA2A2 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, 0, 0], ![0, 0, 2, -1], ![0, 0, -1, 2]]
def cA2A1A1 : Fin 4 → Fin 4 → ℤ := ![![2, -1, 0, 0], ![-1, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]]
def cA1x4 : Fin 4 → Fin 4 → ℤ := ![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]]

def aA4 : Fin 4 → Fin 4 → ℤ := ![![4, 3, 2, 1], ![3, 6, 4, 2], ![2, 4, 6, 3], ![1, 2, 3, 4]]
def aD4 : Fin 4 → Fin 4 → ℤ := ![![4, 4, 2, 2], ![4, 8, 4, 4], ![2, 4, 4, 2], ![2, 4, 2, 4]]
def aA3A1 : Fin 4 → Fin 4 → ℤ := ![![6, 4, 2, 0], ![4, 8, 4, 0], ![2, 4, 6, 0], ![0, 0, 0, 4]]
def aA2A2 : Fin 4 → Fin 4 → ℤ := ![![6, 3, 0, 0], ![3, 6, 0, 0], ![0, 0, 6, 3], ![0, 0, 3, 6]]
def aA2A1A1 : Fin 4 → Fin 4 → ℤ := ![![8, 4, 0, 0], ![4, 8, 0, 0], ![0, 0, 6, 0], ![0, 0, 0, 6]]
def aA1x4 : Fin 4 → Fin 4 → ℤ := ![![8, 0, 0, 0], ![0, 8, 0, 0], ![0, 0, 8, 0], ![0, 0, 0, 8]]

/-- The rank-4 simply-laced root lattices, indexed `A₄, D₄, A₃A₁, A₂A₂, A₂A₁A₁, A₁⁴`. -/
def candF : Fin 6 → Fin 4 → Fin 4 → ℤ := ![cA4, cD4, cA3A1, cA2A2, cA2A1A1, cA1x4]
def adjF : Fin 6 → Fin 4 → Fin 4 → ℤ := ![aA4, aD4, aA3A1, aA2A2, aA2A1A1, aA1x4]
def cand (k : Fin 6) : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of (candF k)
def adjC (k : Fin 6) : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of (adjF k)
def detC : Fin 6 → ℤ := ![5, 4, 8, 9, 12, 16]

lemma cand_mul : ∀ k, cand k * adjC k = detC k • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by decide
lemma mul_cand : ∀ k, adjC k * cand k = detC k • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by decide

/-- Divisibility test on a plain array (decidable). -/
def DivCond (d : ℤ) (A : Fin 4 → Fin 4 → ℤ) : Prop := ∀ i j, d ∣ 2 * A i j

instance (d : ℤ) (A : Fin 4 → Fin 4 → ℤ) : Decidable (DivCond d A) := by
  unfold DivCond; infer_instance

lemma involutive_cand (k : Fin 6) :
    InvolutiveGlue (cand k) ↔ DivCond (detC k) (adjF k) :=
  involutiveGlue_iff _ _ (by fin_cases k <;> decide) (cand_mul k) (mul_cand k)

/-- **Sector selection.** Among the rank-4 simply-laced root lattices, `D₄` (index 1) is the
only one that is irreducible with involutive glue. `A₁⁴` has involutive glue but is reducible;
`A₄` is irreducible but its glue is `ℤ/5`. -/
theorem sector_selection (k : Fin 6) :
    (Connected (candF k) ∧ InvolutiveGlue (cand k)) ↔ k = 1 := by
  rw [involutive_cand]
  fin_cases k <;> decide

/-! ## Channel count -/

/-- The three 8-dimensional representations `8_v, 8_s, 8_c` of `so(8)`. -/
def chanDim : Fin 3 → ℕ := fun _ => 8

/-- **ν = 16.** Any two distinct channels give 16 real coordinates, whichever pair is chosen. -/
theorem nu_eq_sixteen (s : Finset (Fin 3)) (hs : s.card = 2) : ∑ i ∈ s, chanDim i = 16 := by
  simp [chanDim, hs]

/-! ## Relational time -/

section Aliasing
variable {N : ℕ}

/-- Local observation: for each active transition, whether an idle run follows it. -/
def obs (g : Fin N → ℕ) : Fin N → Bool := fun i => decide (0 < g i)

/-- Cycle length: `N` active slots plus the idle runs `g i`. -/
def period (g : Fin N → ℕ) : ℕ := N + ∑ i, g i

/-- **Reconstruction from local data.** Schedules whose idle runs have length at most `k` are
determined by their observations iff `k ≤ 1`. -/
theorem obs_injOn_iff (hN : 0 < N) (k : ℕ) :
    Set.InjOn obs {g : Fin N → ℕ | ∀ i, g i ≤ k} ↔ k ≤ 1 := by
  constructor
  · intro h
    by_contra hk
    push Not at hk
    let i0 : Fin N := ⟨0, hN⟩
    let g1 : Fin N → ℕ := fun _ => 1
    let g2 : Fin N → ℕ := Function.update g1 i0 2
    have hmem1 : g1 ∈ {g : Fin N → ℕ | ∀ i, g i ≤ k} := fun i => by simp [g1]; omega
    have hmem2 : g2 ∈ {g : Fin N → ℕ | ∀ i, g i ≤ k} := fun i => by
      simp only [g2, g1, Function.update_apply]; split_ifs <;> omega
    have hobs : obs g1 = obs g2 := by
      funext i; simp only [obs, g2, g1, Function.update_apply]; split_ifs <;> simp
    have := congrFun (h hmem1 hmem2 hobs) i0
    simp [g1, g2] at this
  · intro hk g hg g' hg' he
    funext i
    have h0 := congrFun he i
    have h1 := hg i
    have h2 := hg' i
    simp only [obs, decide_eq_decide] at h0
    omega

/-- With idle runs of length at most one, the period is at most `2N`. -/
theorem period_le_two_mul (g : Fin N → ℕ) (h : ∀ i, g i ≤ 1) : period g ≤ 2 * N := by
  have : ∑ i, g i ≤ ∑ _i : Fin N, 1 := Finset.sum_le_sum fun i _ => h i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  unfold period
  omega

/-- **Aliasing.** Lengthening any nonempty idle run changes the period but not the
observation. -/
theorem aliasing (g : Fin N → ℕ) (i : Fin N) (hi : 1 ≤ g i) :
    obs (Function.update g i (g i + 1)) = obs g ∧
      period (Function.update g i (g i + 1)) = period g + 1 := by
  constructor
  · funext j
    simp only [obs, Function.update_apply]
    split_ifs with hj
    · subst hj; simp; omega
    · rfl
  · unfold period
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase,
      ← Finset.add_sum_erase _ g (Finset.mem_univ i)]
    ring

end Aliasing

end PMArch.Sectors
