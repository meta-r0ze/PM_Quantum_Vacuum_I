import PMArch.ClaimBoundary
import PMArch.Postulates
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Testing the three remaining substrate-selection implications

Positive results are conditional on named, independently stated structural or
cost premises. Counterexamples concern the explicitly formalized operational
properties, not a constructed competing quantum vacuum. No new physical axiom.
-/
noncomputable section
namespace PMArch.ConstraintFoundations
open Matrix Filter
open scoped Topology

/-- Finite generation, commuting additive translations and absence of torsion
supply integer coordinates. Neither a quadratic cost nor a physical real-space
embedding nor these algebraic premises follows from generic persistence here. -/
theorem integer_coordinates (M : Type*) [AddCommGroup M]
    [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M] :
    ∃ n : ℕ, Nonempty (M ≃ₗ[ℤ] (Fin n → ℤ)) := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  exact ⟨n, ⟨b.equivFun⟩⟩

/-- An integer-valued symmetric bilinear cost on a finitely generated,
torsion-free additive address group has an integral Gram representation.
Integrality and bilinearity are explicit assumptions, not derived from FCC. -/
theorem integer_gram_representation (M : Type*) [AddCommGroup M]
    [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]
    (B : LinearMap.BilinForm ℤ M) (hs : ∀ x y, B x y = B y x) :
    ∃ n : ℕ, ∃ e : M ≃ₗ[ℤ] (Fin n → ℤ),
      ∃ A : Matrix (Fin n) (Fin n) ℤ,
        A.IsSymm ∧ ∀ x y, B x y = e x ⬝ᵥ (A *ᵥ e y) := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  refine ⟨n, b.equivFun, LinearMap.BilinForm.toMatrix b B, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, LinearMap.BilinForm.toMatrix_apply]
    exact hs (b j) (b i)
  · intro x y
    simpa only [Module.Basis.equivFun_apply] using
      LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B x y

/-- Finite cost sublevels then force positive definiteness of that Gram
matrix. This closes a conditional lattice-class construction without assuming
a Gram matrix at the outset; the address and cost premises remain explicit. -/
theorem finite_budget_gram (M : Type*) [AddCommGroup M]
    [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]
    (B : LinearMap.BilinForm ℤ M) (hs : ∀ x y, B x y = B y x)
    (hf : ∀ c : ℤ, ({x : M | B x x ≤ c}).Finite) :
    ∃ n : ℕ, ∃ e : M ≃ₗ[ℤ] (Fin n → ℤ),
      ∃ A : Matrix (Fin n) (Fin n) ℤ,
        (A.map (Int.cast : ℤ → ℝ)).PosDef ∧
        ∀ x y, B x y = e x ⬝ᵥ (A *ᵥ e y) := by
  obtain ⟨n, e, A, hsym, he⟩ := integer_gram_representation M B hs
  refine ⟨n, e, A, ?_, he⟩
  apply (Translation.posDef_iff_finite_levels hsym).mpr
  intro c
  refine ((hf c).image e).subset ?_
  intro z hz
  refine ⟨e.symm z, ?_, by simp⟩
  change B (e.symm z) (e.symm z) ≤ c
  rw [he]
  simpa using hz

/-- Reflection is reversible on every integral coordinate model. -/
def reflect {n : ℕ} : Equiv.Perm (Fin n → ℤ) where
  toFun := fun z => -z
  invFun := fun z => -z
  left_inv := neg_neg
  right_inv := neg_neg

/-- Reflection preserves the quadratic cost for every Gram matrix, including
odd or non-unimodular ones. Conservation does not select the modular laws. -/
theorem reflection_preserves_cost {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (z : Fin n → ℤ) :
    reflect z ⬝ᵥ (A *ᵥ reflect z) = z ⬝ᵥ (A *ᵥ z) := by
  simp [reflect, Matrix.mulVec_neg]

theorem reflection_nontrivial :
    reflect (fun _ : Fin 1 => (1 : ℤ)) ≠ (fun _ => 1) := by
  intro h
  have h0 := congrFun h 0
  norm_num [reflect] at h0

/-- For positive integral costs, a period-two theta shift is always available.
The period-one shift required for E8 selection is a stronger condition. -/
theorem natural_theta_period_two {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (τ : UpperHalfPlane) :
    ThetaE8.thetaH A ((2 : ℝ) +ᵥ τ) = ThetaE8.thetaH A τ :=
  Translation.thetaH_vadd_two τ

/-- A finite-budget integral quadratic model with a reversible cost-preserving
update can fail the period-one theta law. This uses the existing odd-lattice
witness; no numerical evaluation of a theta series is assumed. -/
theorem finite_conserved_model_without_T :
    ∃ A : Matrix (Fin 1) (Fin 1) ℤ,
      (A.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit A.det ∧
      (∀ c : ℤ, ({z : Fin 1 → ℤ | z ⬝ᵥ (A *ᵥ z) ≤ c}).Finite) ∧
      (∀ z, reflect z ⬝ᵥ (A *ᵥ reflect z) = z ⬝ᵥ (A *ᵥ z)) ∧
      ¬ (∀ s : ℂ, 0 < s.re →
        RankEight.theta (A.map (Int.cast : ℤ → ℝ)) (s - Complex.I) =
        RankEight.theta (A.map (Int.cast : ℤ → ℝ)) s) := by
  obtain ⟨A, hp, hd, hodd, _⟩ := Postulates.evenness_needed
  have hs : A.IsSymm := by
    ext i j
    have : i = j := Subsingleton.elim _ _
    subst j
    rfl
  refine ⟨A, hp, hd, (Translation.posDef_iff_finite_levels hs).mp hp,
    reflection_preserves_cost A, ?_⟩
  intro hT
  exact hodd ((Translation.even_iff_T_invariant hp).mpr hT)

/-- Evenness, finite cost levels and reversible cost-preserving updates do
not force the self-dual inversion law. The A1 lattice is a witness. -/
theorem finite_even_conserved_model_without_S :
    ∃ A : Matrix (Fin 1) (Fin 1) ℤ,
      (A.map (Int.cast : ℤ → ℝ)).PosDef ∧
      (∀ z : Fin 1 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) ∧
      (∀ c : ℤ, ({z : Fin 1 → ℤ | z ⬝ᵥ (A *ᵥ z) ≤ c}).Finite) ∧
      (∀ z, reflect z ⬝ᵥ (A *ᵥ reflect z) = z ⬝ᵥ (A *ᵥ z)) ∧
      ¬ (∀ s : ℂ, 0 < s.re →
        RankEight.theta (A.map (Int.cast : ℤ → ℝ)) s =
        ((s ^ (1 / 2 : ℂ)) ^ 1)⁻¹ *
        RankEight.theta (A.map (Int.cast : ℤ → ℝ)) s⁻¹) := by
  obtain ⟨A, hp, he, hdet, _⟩ := Postulates.unimodularity_needed
  have hs : A.IsSymm := by
    ext i j
    have : i = j := Subsingleton.elim _ _
    subst j
    rfl
  refine ⟨A, hp, he, (Translation.posDef_iff_finite_levels hs).mp hp,
    reflection_preserves_cost A, ?_⟩
  intro hS
  exact hdet ((Translation.unimodular_iff_S_covariant hp).mpr hS)

/-- Rank minimality is mathematically equivalent to rank eight within the
nonzero positive even unimodular class. This does not derive minimization. -/
theorem minimal_rank_iff_eight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hp : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (he : ∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z)))
    (hd : IsUnit A.det) (hn : 0 < n) :
    ClaimBoundary.MinimalRank n ↔ n = 8 := by
  constructor
  · intro hmin
    have h8 := RankEight.e8_even_unimodular
    exact RankEight.minimal_rank_eight_of_lattice A hp he hd hn
      (hmin 8 Lattices.gram h8.1 h8.2.1 h8.2.2 (by decide))
  · intro h8
    subst n
    intro m B hpB heB hdB hm
    have hdiv := RankEight.rank_dvd_eight B hpB heB hdB
    obtain ⟨k, hk⟩ := hdiv
    omega

/-- A least-cost principle selects minimum rank if cost is a strictly
increasing function of rank alone. That cost-rank relation is the new physical
obligation, not a consequence of finite capacity. -/
theorem least_cost_implies_minimal_rank (cost : ℕ → ℝ) (hcost : StrictMono cost)
    (n : ℕ)
    (hselected : ∀ (m : ℕ) (B : Matrix (Fin m) (Fin m) ℤ),
      (B.map (Int.cast : ℤ → ℝ)).PosDef →
      (∀ z : Fin m → ℤ, Even (z ⬝ᵥ (B *ᵥ z))) → IsUnit B.det →
      0 < m → cost n ≤ cost m) : ClaimBoundary.MinimalRank n := by
  intro m B hp he hd hm
  exact hcost.le_iff_le.mp (hselected m B hp he hd hm)

/-- Under a specified positive cost per coordinate, rank cost is increasing. -/
theorem linear_rank_cost_strict (κ : ℝ) (hκ : 0 < κ) :
    StrictMono (fun n : ℕ => κ * n) := by
  intro m n hmn
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hmn) hκ

/-- Full refresh: each independent coordinate incurs the same toll at the
same flux. This is an operational workload model, not a derived vacuum law. -/
def refreshCost (toll flux : ℝ) (n : ℕ) : ℝ := (∑ _ : Fin n, toll) * flux

theorem refresh_cost_exact (toll flux : ℝ) (n : ℕ) :
    refreshCost toll flux n = (toll * flux) * n := by
  simp [refreshCost]
  ring

theorem refresh_cost_strict (toll flux : ℝ) (ht : 0 < toll) (hf : 0 < flux) :
    StrictMono (refreshCost toll flux) := by
  have he : refreshCost toll flux = fun n : ℕ => (toll * flux) * n := by
    funext n
    exact refresh_cost_exact toll flux n
  rw [he]
  exact linear_rank_cost_strict (toll * flux) (mul_pos ht hf)

/-- Derive the relative exponential survival penalty from the explicit full
refresh costs. A common hazard coefficient and this workload law are inputs. -/
theorem refresh_survival_ratio (β toll flux T : ℝ) (n m : ℕ) :
    Real.exp (-β * (refreshCost toll flux n * T)) /
      Real.exp (-β * (refreshCost toll flux m * T)) =
    Real.exp (-(β * (toll * flux) * ((n : ℝ) - m)) * T) := by
  rw [← Real.exp_sub, refresh_cost_exact, refresh_cost_exact]
  congr 1
  ring

/-- With positive fixed prior odds and cost rate κ per rank, higher-rank
relative survivor weight is positive at every finite time. -/
def rankOdds (β κ prior : ℝ) (n m : ℕ) (T : ℝ) : ℝ :=
  prior * Real.exp (-(β * κ * ((n : ℝ) - m)) * T)

theorem rank_odds_positive (β κ prior : ℝ) (n m : ℕ) (T : ℝ)
    (hp : 0 < prior) : 0 < rankOdds β κ prior n m T :=
  mul_pos hp (Real.exp_pos _)

/-- The same model asymptotically suppresses every higher rank. It does not
make the higher rank impossible at any finite time. -/
theorem higher_rank_odds_tend_to_zero (β κ prior : ℝ) (n m : ℕ)
    (hβ : 0 < β) (hκ : 0 < κ) (hmn : m < n) :
    Tendsto (rankOdds β κ prior n m) atTop (𝓝 0) := by
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hdiff : 0 < (n : ℝ) - m := by linarith
  have hneg : -(β * κ * ((n : ℝ) - m)) < 0 :=
    neg_lt_zero.mpr (mul_pos (mul_pos hβ hκ) hdiff)
  have h := (Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg hneg)).const_mul prior
  change Tendsto (fun T : ℝ => prior * Real.exp (-(β * κ * ((n : ℝ) - m)) * T))
    atTop (𝓝 0)
  simpa only [Function.comp_def, id_eq, neg_mul, mul_zero] using h

/-- The lower-rank share of a two-candidate survivor ensemble tends to one.
The rank cost law, common hazard, and fixed prior odds are model premises. -/
theorem lower_rank_share_tends_to_one (β κ prior : ℝ) (n m : ℕ)
    (hβ : 0 < β) (hκ : 0 < κ) (hmn : m < n) :
    Tendsto (fun T : ℝ => 1 / (1 + rankOdds β κ prior n m T)) atTop (𝓝 1) := by
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := hc.add (higher_rank_odds_tend_to_zero β κ prior n m hβ hκ hmn)
  have hdiv := hc.div h (by norm_num : (1 : ℝ) + 0 ≠ 0)
  change Tendsto ((fun _ : ℝ => (1 : ℝ)) /
    (fun T : ℝ => 1 + rankOdds β κ prior n m T)) atTop (𝓝 1)
  simpa only [add_zero, div_one] using hdiv

/-- Conservation and a common exponential survival law do not alone imply
that larger rank has larger cost. Assigning rates 1 and 2 favors rank 16 over
rank 8. The rank labels do not occur in this survival formula without a link. -/
theorem higher_rank_not_excluded_by_survival (β T : ℝ) (hβ : 0 < β) (hT : 0 < T) :
    Real.exp (-β * (1 : ℝ) * T) > Real.exp (-β * 2 * T) := by
  apply Real.exp_lt_exp.mpr
  nlinarith [mul_pos hβ hT]

end PMArch.ConstraintFoundations
