import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.GroupTheory.OrderOfElement
import PMArch.PhysicalBridge
import PMArch.Lattices

noncomputable section
open Complex Matrix
open scoped Real

namespace PMArch.RankEight

/-- Quadratic form `xᵀ G x`. -/
def qf {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (G *ᵥ x)

/-- Integer vectors viewed as real vectors. -/
def vcast {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ := fun i => (z i : ℝ)

lemma qf_smul {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (x : Fin n → ℝ) :
    qf G (r • x) = r ^ 2 * qf G x := by
  simp only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

lemma continuous_qf {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) : Continuous (qf G) := by
  show Continuous fun x : Fin n → ℝ => ∑ i, x i * ∑ j, G i j * x j
  fun_prop

lemma qf_pos {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {x : Fin n → ℝ}
    (hx : x ≠ 0) : 0 < qf G x := by
  simpa [qf] using hG.dotProduct_mulVec_pos hx

lemma dot_self_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma dot_self_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (dot_self_nonneg x) (Ne.symm (mt dotProduct_self_eq_zero.mp hx))

/-- A positive-definite form dominates a positive multiple of the Euclidean form. -/
lemma exists_lower {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    ∃ l > 0, ∀ x, l * (x ⬝ᵥ x) ≤ qf G x := by
  set K : Set (Fin n → ℝ) := {x | x ⬝ᵥ x = 1} with hK
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by simp only [dotProduct]; fun_prop) continuous_const
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have hx' : ∑ j, x j * x j = 1 := hx
      have h1 : x i * x i ≤ 1 := hx' ▸ Finset.single_le_sum
        (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
      rw [Real.norm_eq_abs]
      nlinarith [abs_mul_abs_self (x i), abs_nonneg (x i)]
  have hnorm : ∀ x : Fin n → ℝ, x ≠ 0 → (Real.sqrt (x ⬝ᵥ x))⁻¹ • x ∈ K := by
    intro x hx
    have hp := dot_self_pos hx
    show ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ⬝ᵥ ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← sq, inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  by_cases hne : K.Nonempty
  · obtain ⟨u, hu, hmin⟩ := hKc.exists_isMinOn hne (continuous_qf G).continuousOn
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp [hK] at hu
    refine ⟨qf G u, qf_pos hG hu0, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [qf]
    have hp := dot_self_pos hx
    have h1 := hmin (hnorm x hx)
    simp only [Set.mem_ofPred_eq, qf_smul, inv_pow, Real.sq_sqrt hp.le] at h1
    rw [le_inv_mul_iff₀ hp] at h1
    linarith [mul_comm (qf G u) (x ⬝ᵥ x)]
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [qf]
    · exact absurd ⟨_, hnorm x hx⟩ hne

lemma summable_gauss1 {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Summable (fun k : ℤ => Real.exp (-a * ((k : ℝ) - t) ^ 2)) := by
  have hs := summable_pow_mul_jacobiTheta₂_term_bound (a * |t| / π) (T := a / π)
    (div_pos ha Real.pi_pos) 0
  refine hs.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun k => ?_)
  simp only [pow_zero, one_mul, Int.cast_abs]
  apply Real.exp_le_exp.mpr
  have hpi := Real.pi_pos.ne'
  have : -π * (a / π * (k : ℝ) ^ 2 - 2 * (a * |t| / π) * |(k : ℝ)|) =
      -a * (k : ℝ) ^ 2 + 2 * a * (|t| * |(k : ℝ)|) := by field_simp; ring
  rw [this]
  have h1 : t * k ≤ |t| * |(k : ℝ)| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [sq_nonneg t]

lemma summable_pi_prod (n : ℕ) : ∀ (f : Fin n → ℤ → ℝ), (∀ i k, 0 ≤ f i k) →
    (∀ i, Summable (f i)) → Summable (fun z : Fin n → ℤ => ∏ i, f i (z i)) := by
  induction n with
  | zero =>
    intro f _ _
    exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ n ih =>
    intro f h0 hs
    have ih' : Summable (fun z : Fin n → ℤ => ∏ i : Fin n, f (Fin.succ i) (z i)) :=
      ih (fun i => f (Fin.succ i)) (fun i => h0 _) (fun i => hs _)
    have hp : Summable (fun p : ℤ × (Fin n → ℤ) =>
        f 0 p.1 * ∏ i : Fin n, f (Fin.succ i) (p.2 i)) :=
      Summable.mul_of_nonneg (f := f 0)
        (g := fun (y : Fin n → ℤ) => ∏ i : Fin n, f (Fin.succ i) (y i))
        (hs 0) ih' (fun k => h0 0 k)
        (fun y => Finset.prod_nonneg fun i _ => h0 (Fin.succ i) (y i))
    refine (Equiv.summable_iff (Fin.consEquiv fun _ => ℤ)).mp ?_
    convert hp using 1
    ext p
    simp [Fin.prod_univ_succ]

lemma summable_qf {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) {a : ℝ}
    (ha : 0 < a) (c : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ => Real.exp (-a * qf G (vcast z - c))) := by
  obtain ⟨l, hl, hb⟩ := exists_lower G hG
  have hs := summable_pi_prod n (fun i k => Real.exp (-(a * l) * ((k : ℝ) - c i) ^ 2))
    (fun _ _ => (Real.exp_pos _).le) (fun i => summable_gauss1 (mul_pos ha hl) (c i))
  refine hs.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun z => ?_)
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have h1 := hb (vcast z - c)
  have h2 : (vcast z - c) ⬝ᵥ (vcast z - c) = ∑ i, ((z i : ℝ) - c i) ^ 2 := by
    simp [dotProduct, vcast, sq]
  rw [h2] at h1
  have h3 : ∑ i, -(a * l) * ((z i : ℝ) - c i) ^ 2 = -a * (l * ∑ i, ((z i : ℝ) - c i) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3]
  nlinarith


section Block
variable {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)

/-- First-row coupling vector. -/
def bv : Fin n → ℝ := fun j => G 0 (Fin.succ j)

/-- Lower-right block. -/
def tailM : Matrix (Fin n) (Fin n) ℝ := G.submatrix Fin.succ Fin.succ

/-- Schur complement of the `(0,0)` entry. -/
def schur : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => G (Fin.succ i) (Fin.succ j) - G 0 (Fin.succ i) * G 0 (Fin.succ j) / G 0 0

variable {G}

lemma symm_of_posDef (hG : G.PosDef) (i j : Fin (n + 1)) : G j i = G i j := by
  simpa using hG.1.apply i j

lemma qf_cons (hs : ∀ i j, G j i = G i j) (x0 : ℝ) (y : Fin n → ℝ) :
    qf G (Fin.cons x0 y) = G 0 0 * x0 ^ 2 + 2 * x0 * (bv G ⬝ᵥ y) + qf (tailM G) y := by
  simp only [qf, dotProduct, mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    tailM, submatrix_apply, bv]
  have h0 : ∀ i : Fin n, G (Fin.succ i) 0 = G 0 (Fin.succ i) := fun i => hs 0 (Fin.succ i)
  simp only [h0]
  have e1 : ∑ i : Fin n, y i * (G 0 (Fin.succ i) * x0 + ∑ j : Fin n, G (Fin.succ i) (Fin.succ j) * y j)
      = x0 * ∑ i : Fin n, G 0 (Fin.succ i) * y i
        + ∑ i : Fin n, y i * ∑ j : Fin n, G (Fin.succ i) (Fin.succ j) * y j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1]; ring

lemma qf_schur (y : Fin n → ℝ) :
    qf (schur G) y = qf (tailM G) y - (bv G ⬝ᵥ y) ^ 2 / G 0 0 := by
  simp only [qf, dotProduct, mulVec, schur, of_apply, tailM, submatrix_apply, bv]
  have e : ∀ i : Fin n, ∑ j : Fin n, (G (Fin.succ i) (Fin.succ j)
      - G 0 (Fin.succ i) * G 0 (Fin.succ j) / G 0 0) * y j
      = ∑ j : Fin n, G (Fin.succ i) (Fin.succ j) * y j
        - G 0 (Fin.succ i) * (∑ j : Fin n, G 0 (Fin.succ j) * y j) / G 0 0 := by
    intro i
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [e, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [sq, Finset.sum_mul, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma g_pos (hG : G.PosDef) : 0 < G 0 0 := by
  have h := qf_pos hG (x := Fin.cons 1 0) (by
    intro h; simpa using congrFun h 0)
  rw [qf_cons (symm_of_posDef hG)] at h
  simpa [qf] using h

lemma schur_posDef (hG : G.PosDef) : (schur G).PosDef := by
  have hs := symm_of_posDef hG
  have hg := g_pos hG
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun y hy => ?_
  · ext i j
    simp only [conjTranspose_apply, schur, of_apply, star_trivial]
    rw [hs (Fin.succ i) (Fin.succ j)]; ring
  · have hx : (Fin.cons (-(bv G ⬝ᵥ y) / G 0 0) y : Fin (n + 1) → ℝ) ≠ 0 := by
      intro h; apply hy
      have := congrArg Fin.tail h
      simp only [Fin.tail_cons] at this
      exact this
    have h := qf_pos hG hx
    rw [qf_cons hs] at h
    have : qf (schur G) y = G 0 0 * (-(bv G ⬝ᵥ y) / G 0 0) ^ 2
        + 2 * (-(bv G ⬝ᵥ y) / G 0 0) * (bv G ⬝ᵥ y) + qf (tailM G) y := by
      rw [qf_schur]; field_simp; ring
    have hpos : 0 < qf (schur G) y := by rw [this]; exact h
    simpa [qf] using hpos

/-- The inverse form restricted by the first coordinate. -/
lemma qf_inv_cons (hG : G.PosDef) (μ : ℝ) (u : Fin n → ℝ) :
    qf G⁻¹ (Fin.cons μ u) = qf (schur G)⁻¹ (u - (μ / G 0 0) • bv G) + μ ^ 2 / G 0 0 := by
  have hs := symm_of_posDef hG
  have hg := g_pos hG
  have hS := schur_posDef hG
  have hSdet : IsUnit (schur G).det := (isUnit_iff_isUnit_det _).mp hS.isUnit
  have hGdet : IsUnit G.det := (isUnit_iff_isUnit_det _).mp hG.isUnit
  obtain ⟨x', hx'⟩ : ∃ x', x' = (schur G)⁻¹ *ᵥ (u - (μ / G 0 0) • bv G) := ⟨_, rfl⟩
  have hSx : schur G *ᵥ x' = u - (μ / G 0 0) • bv G := by
    rw [hx', mulVec_mulVec, mul_nonsing_inv _ hSdet, one_mulVec]
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = (μ - bv G ⬝ᵥ x') / G 0 0 := ⟨_, rfl⟩
  have hGx : G *ᵥ (Fin.cons x0 x') = Fin.cons μ u := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have : ∑ j : Fin n, G 0 (Fin.succ j) * x' j = bv G ⬝ᵥ x' := rfl
      rw [this, hx0]; field_simp; ring
    · have hi := congrFun hSx i
      simp only [mulVec, dotProduct, schur, of_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, bv] at hi
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [hs 0 (Fin.succ i)]
      have e : ∑ j : Fin n, (G (Fin.succ i) (Fin.succ j)
          - G 0 (Fin.succ i) * G 0 (Fin.succ j) / G 0 0) * x' j
          = ∑ j : Fin n, G (Fin.succ i) (Fin.succ j) * x' j
            - G 0 (Fin.succ i) * (bv G ⬝ᵥ x') / G 0 0 := by
        simp only [sub_mul, Finset.sum_sub_distrib, dotProduct, bv, Finset.mul_sum,
          Finset.sum_div]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e] at hi
      rw [hx0]
      field_simp at hi ⊢
      linarith
  have hinv : G⁻¹ *ᵥ (Fin.cons μ u) = Fin.cons x0 x' := by
    rw [← hGx, mulVec_mulVec, nonsing_inv_mul _ hGdet, one_mulVec]
  have h1 : qf G⁻¹ (Fin.cons μ u) = μ * x0 + u ⬝ᵥ x' := by
    rw [qf, hinv]; simp [dotProduct, Fin.sum_univ_succ]
  have h2 : qf (schur G)⁻¹ (u - (μ / G 0 0) • bv G)
      = u ⬝ᵥ x' - μ / G 0 0 * (bv G ⬝ᵥ x') := by
    rw [qf, ← hx', sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [h1, h2, hx0]
  field_simp
  ring

end Block

section Poisson

lemma norm_term (s : ℂ) (q r : ℝ) :
    ‖cexp (-π * s * (q : ℂ) + 2 * π * I * (r : ℂ))‖ = Real.exp (-(π * s.re) * q) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_re]

lemma norm_term' (t : ℂ) (q : ℝ) :
    ‖cexp (-π * t * (q : ℂ))‖ = Real.exp (-(π * t.re) * q) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_re]

lemma inv_re_pos {s : ℂ} (hs : 0 < s.re) : 0 < (s⁻¹).re := by
  rw [Complex.inv_re]
  exact div_pos hs (Complex.normSq_pos.mpr fun h => by simp [h] at hs)

lemma summable_lhs {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) {s : ℂ}
    (hs : 0 < s.re) (c : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ =>
      cexp (-π * s * (qf G (vcast z) : ℂ) + 2 * π * I * ((c ⬝ᵥ vcast z : ℝ) : ℂ))) := by
  refine Summable.of_norm ?_
  have h := summable_qf G hG (mul_pos Real.pi_pos hs) 0
  simp only [sub_zero] at h
  simpa only [norm_term] using h

lemma summable_rhs {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) {t : ℂ}
    (ht : 0 < t.re) (c : Fin n → ℝ) :
    Summable (fun m : Fin n → ℤ => cexp (-π * t * (qf G (vcast m - c) : ℂ))) := by
  refine Summable.of_norm ?_
  simpa only [norm_term'] using summable_qf G hG (mul_pos Real.pi_pos ht) c

lemma cpow_half_mul_real {s : ℂ} (hs : s ≠ 0) {g : ℝ} (hg : 0 < g) :
    (s * (g : ℂ)) ^ (1 / 2 : ℂ) = s ^ (1 / 2 : ℂ) * (g : ℂ) ^ (1 / 2 : ℂ) := by
  have hg' : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hs hg'), cpow_def_of_ne_zero hs,
    cpow_def_of_ne_zero hg', log_mul_ofReal g hg s hs, ← Complex.exp_add,
    ← Complex.ofReal_log hg.le]
  ring_nf

lemma vcast_cons {n : ℕ} (k : ℤ) (y : Fin n → ℤ) :
    vcast (Fin.cons k y : Fin (n + 1) → ℤ) = Fin.cons (k : ℝ) (vcast y) := by
  ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [vcast]

lemma dot_cons {n : ℕ} (c : Fin (n + 1) → ℝ) (x0 : ℝ) (v : Fin n → ℝ) :
    c ⬝ᵥ (Fin.cons x0 v : Fin (n + 1) → ℝ) = c 0 * x0 + Fin.tail c ⬝ᵥ v := by
  simp [dotProduct, Fin.sum_univ_succ, Fin.tail]

lemma cons_sub {n : ℕ} (c : Fin (n + 1) → ℝ) (x0 : ℝ) (v : Fin n → ℝ) :
    (Fin.cons x0 v : Fin (n + 1) → ℝ) - c = Fin.cons (x0 - c 0) (v - Fin.tail c) := by
  ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [Fin.tail]

lemma tsum_cons_split {n : ℕ} (F : (Fin (n + 1) → ℤ) → ℂ) (hF : Summable F) :
    ∑' z, F z = ∑' y : Fin n → ℤ, ∑' k : ℤ, F (Fin.cons k y) := by
  let e : (Fin n → ℤ) × ℤ ≃ (Fin (n + 1) → ℤ) :=
    (Equiv.prodComm _ _).trans (Fin.consEquiv fun _ => ℤ)
  have h : Summable (fun p => F (e p)) := (e.summable_iff).mpr hF
  rw [← e.tsum_eq F, h.tsum_prod]
  rfl

lemma tsum_cons_split' {n : ℕ} (F : (Fin (n + 1) → ℤ) → ℂ) (hF : Summable F) :
    ∑' z, F z = ∑' k : ℤ, ∑' y : Fin n → ℤ, F (Fin.cons k y) := by
  let e : ℤ × (Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) := Fin.consEquiv fun _ => ℤ
  have h : Summable (fun p => F (e p)) := (e.summable_iff).mpr hF
  rw [← e.tsum_eq F, h.tsum_prod]
  rfl

/-- Poisson summation for a positive-definite real quadratic form on `ℤⁿ`, with a real
character. The constant depends only on the form. Proved by induction on the rank, using
one-dimensional Poisson summation and the Schur complement. -/
theorem poisson (n : ℕ) : ∀ G : Matrix (Fin n) (Fin n) ℝ, G.PosDef → ∃ C : ℂ,
    ∀ s : ℂ, 0 < s.re → ∀ c : Fin n → ℝ,
      ∑' z : Fin n → ℤ, cexp (-π * s * (qf G (vcast z) : ℂ)
          + 2 * π * I * ((c ⬝ᵥ vcast z : ℝ) : ℂ))
        = C * ((s ^ (1 / 2 : ℂ)) ^ n)⁻¹ *
          ∑' m : Fin n → ℤ, cexp (-π * s⁻¹ * (qf G⁻¹ (vcast m - c) : ℂ)) := by
  induction n with
  | zero =>
    intro G _
    refine ⟨1, fun s _ c => ?_⟩
    have h0 : ∀ f : (Fin 0 → ℤ) → ℂ, ∑' z, f z = f 0 := fun f =>
      tsum_eq_single 0 (fun b hb => absurd (Subsingleton.elim b 0) hb)
    rw [h0, h0]
    simp [qf]
  | succ n ih =>
    intro G hG
    have hsym := symm_of_posDef hG
    have hg := g_pos hG
    have hS := schur_posDef hG
    obtain ⟨CS, hCS⟩ := ih (schur G) hS
    refine ⟨CS * (((G 0 0 : ℝ) : ℂ) ^ (1 / 2 : ℂ))⁻¹, fun s hsr c => ?_⟩
    have hs0 : s ≠ 0 := fun h => by simp [h] at hsr
    have hsinv := inv_re_pos hsr
    have hg' : ((G 0 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg.ne'
    -- Step A: split off the first coordinate.
    rw [tsum_cons_split _ (summable_lhs G hG hsr c)]
    -- Step B: one-dimensional Poisson summation in that coordinate.
    have hB : ∀ y : Fin n → ℤ,
        ∑' k : ℤ, cexp (-π * s * (qf G (vcast (Fin.cons k y : Fin (n + 1) → ℤ)) : ℂ)
          + 2 * π * I * ((c ⬝ᵥ vcast (Fin.cons k y : Fin (n + 1) → ℤ) : ℝ) : ℂ))
        = 1 / (s * ((G 0 0 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) * ∑' m : ℤ,
          (cexp (-π * s * (qf (schur G) (vcast y) : ℂ) + 2 * π * I *
              (((Fin.tail c + (((m : ℝ) - c 0) / G 0 0) • bv G) ⬝ᵥ vcast y : ℝ) : ℂ))
            * cexp (-π * s⁻¹ * ((((m : ℝ) - c 0) ^ 2 / G 0 0 : ℝ) : ℂ))) := by
      intro y
      set β : ℝ := bv G ⬝ᵥ vcast y with hβ
      have hterm : ∀ k : ℤ,
          cexp (-π * s * (qf G (vcast (Fin.cons k y : Fin (n + 1) → ℤ)) : ℂ)
            + 2 * π * I * ((c ⬝ᵥ vcast (Fin.cons k y : Fin (n + 1) → ℤ) : ℝ) : ℂ))
          = cexp (-π * (s * ((G 0 0 : ℝ) : ℂ)) * (k : ℂ) ^ 2
              + 2 * π * (-s * (β : ℂ) + I * (c 0 : ℂ)) * k)
            * cexp (-π * s * (qf (tailM G) (vcast y) : ℂ)
              + 2 * π * I * ((Fin.tail c ⬝ᵥ vcast y : ℝ) : ℂ)) := by
        intro k
        rw [← Complex.exp_add, vcast_cons, qf_cons hsym, dot_cons]
        congr 1
        rw [← hβ]
        push_cast
        ring
      simp only [hterm]
      rw [tsum_mul_right]
      have hre : 0 < (s * ((G 0 0 : ℝ) : ℂ)).re := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; simp; positivity
      rw [Complex.tsum_exp_neg_quadratic hre, mul_assoc, ← tsum_mul_right]
      congr 1
      refine tsum_congr fun m => ?_
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [qf_schur, add_dotProduct, smul_dotProduct, smul_eq_mul, ← hβ]
      have hIB : I * (-s * (β : ℂ) + I * (c 0 : ℂ)) = -(I * s * β) - c 0 := by
        ring_nf; rw [I_sq]; ring
      rw [hIB]
      push_cast
      field_simp
      linear_combination (-(s ^ 2) * (β : ℂ) ^ 2) * I_sq
    rw [tsum_congr hB, tsum_mul_left]
    -- Step C: exchange the order of summation.
    have hΦ : Summable (Function.uncurry fun (y : Fin n → ℤ) (m : ℤ) =>
        cexp (-π * s * (qf (schur G) (vcast y) : ℂ) + 2 * π * I *
            (((Fin.tail c + (((m : ℝ) - c 0) / G 0 0) • bv G) ⬝ᵥ vcast y : ℝ) : ℂ))
          * cexp (-π * s⁻¹ * ((((m : ℝ) - c 0) ^ 2 / G 0 0 : ℝ) : ℂ))) := by
      have h1 : Summable (fun y : Fin n → ℤ =>
          Real.exp (-(π * s.re) * qf (schur G) (vcast y))) := by
        simpa only [sub_zero] using summable_qf (schur G) hS (mul_pos Real.pi_pos hsr) 0
      have h2 := summable_gauss1 (div_pos (mul_pos Real.pi_pos hsinv) hg) (c 0)
      refine Summable.of_norm_bounded (Summable.mul_of_nonneg h1 h2
        (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)) ?_
      rintro ⟨y, m⟩
      simp only [Function.uncurry_apply_pair]
      rw [norm_mul, norm_term, norm_term']
      apply le_of_eq
      congr 2
      ring
    rw [← hΦ.tsum_comm]
    -- Steps D and E: apply the induction hypothesis and reassemble the inverse form.
    have hD : ∀ m : ℤ, ∑' y : Fin n → ℤ,
        cexp (-π * s * (qf (schur G) (vcast y) : ℂ) + 2 * π * I *
            (((Fin.tail c + (((m : ℝ) - c 0) / G 0 0) • bv G) ⬝ᵥ vcast y : ℝ) : ℂ))
          * cexp (-π * s⁻¹ * ((((m : ℝ) - c 0) ^ 2 / G 0 0 : ℝ) : ℂ))
        = CS * ((s ^ (1 / 2 : ℂ)) ^ n)⁻¹ * ∑' w : Fin n → ℤ,
          cexp (-π * s⁻¹ * (qf G⁻¹ (vcast (Fin.cons m w : Fin (n + 1) → ℤ) - c) : ℂ)) := by
      intro m
      rw [tsum_mul_right, hCS s hsr, mul_assoc, ← tsum_mul_right]
      congr 1
      refine tsum_congr fun w => ?_
      rw [← Complex.exp_add, vcast_cons, cons_sub, qf_inv_cons hG]
      congr 1
      have e : vcast w - (Fin.tail c + (((m : ℝ) - c 0) / G 0 0) • bv G)
          = (vcast w - Fin.tail c) - (((m : ℝ) - c 0) / G 0 0) • bv G := by abel
      rw [e]
      push_cast
      ring
    rw [tsum_congr hD, tsum_mul_left,
      ← tsum_cons_split' _ (summable_rhs G⁻¹ hG.inv hsinv c),
      cpow_half_mul_real hs0 hg, pow_succ]
    ring

end Poisson

section Rank

/-- Theta series `∑ exp(-π s zᵀGz)` of a real Gram matrix. -/
def theta {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (s : ℂ) : ℂ :=
  ∑' z : Fin n → ℤ, cexp (-π * s * (qf G (vcast z) : ℂ))

lemma sq_half (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  rw [one_div]
  simp


lemma qf_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    qf (A.map (Int.cast : ℤ → ℝ)) (vcast z) = ((z ⬝ᵥ (A *ᵥ z) : ℤ) : ℝ) := by
  have hv : vcast (A *ᵥ z) = A.map (Int.cast : ℤ → ℝ) *ᵥ vcast z := by
    ext i; simp [vcast, mulVec, dotProduct]
  rw [qf, ← hv]; simp [vcast, dotProduct]

/-- The theta series is nonzero (indeed positive) at `s = 1`. -/
theorem theta_one_ne_zero {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hpos : G.PosDef) :
    theta G 1 ≠ 0 := by
  have hsum : Summable (fun z : Fin n → ℤ => Real.exp (-(π * 1) * qf G (vcast z))) := by
    simpa only [sub_zero] using summable_qf G hpos (mul_pos Real.pi_pos one_pos) 0
  have : theta G 1 = ((∑' z : Fin n → ℤ, Real.exp (-(π * 1) * qf G (vcast z)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun z => ?_
    push_cast
    ring_nf
  rw [this, Complex.ofReal_ne_zero]
  exact (hsum.tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)).ne'

/-- Evenness: the theta series is invariant under `s ↦ s - i`. -/
theorem theta_shift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (heven : ∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (s : ℂ) :
    theta (A.map (Int.cast : ℤ → ℝ)) (s - I) = theta (A.map (Int.cast : ℤ → ℝ)) s := by
  refine tsum_congr fun z => ?_
  obtain ⟨k, hk⟩ := heven z
  rw [qf_cast, hk]
  push_cast
  have : -(π : ℂ) * (s - I) * ((k : ℂ) + k) = -π * s * ((k : ℂ) + k) + k * (2 * π * I) := by
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Self-duality and Poisson summation: `θ(s) = s^{-n/2} θ(1/s)` for `Re s > 0`. -/
theorem theta_inversion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) (hdet : IsUnit A.det) (s : ℂ) (hs : 0 < s.re) :
    theta (A.map (Int.cast : ℤ → ℝ)) s
      = ((s ^ (1 / 2 : ℂ)) ^ n)⁻¹ * theta (A.map (Int.cast : ℤ → ℝ)) s⁻¹ := by
  set G := A.map (Int.cast : ℤ → ℝ) with hGdef
  obtain ⟨C, hC⟩ := poisson n G hpos
  have hGu : IsUnit G.det := (isUnit_iff_isUnit_det G).mp hpos.isUnit
  have hv : ∀ z : Fin n → ℤ, vcast (A *ᵥ z) = G *ᵥ vcast z := by
    intro z; ext i; simp [vcast, G, mulVec, dotProduct]
  have hdual : ∀ t : ℂ, ∑' m : Fin n → ℤ, cexp (-π * t * (qf G⁻¹ (vcast m - 0) : ℂ))
      = theta G t := by
    intro t
    let e : (Fin n → ℤ) ≃ (Fin n → ℤ) :=
      { toFun := fun z => A *ᵥ z
        invFun := fun m => A⁻¹ *ᵥ m
        left_inv := fun z => by simp [mulVec_mulVec, nonsing_inv_mul A hdet]
        right_inv := fun m => by simp [mulVec_mulVec, mul_nonsing_inv A hdet] }
    rw [← e.tsum_eq]
    refine tsum_congr fun z => ?_
    show cexp (-π * t * (qf G⁻¹ (vcast (A *ᵥ z) - 0) : ℂ)) = _
    rw [sub_zero, hv, qf, mulVec_mulVec, nonsing_inv_mul G hGu, one_mulVec, dotProduct_comm]
    rfl
  have hP : ∀ s : ℂ, 0 < s.re → theta G s = C * ((s ^ (1 / 2 : ℂ)) ^ n)⁻¹ * theta G s⁻¹ := by
    intro s hs
    have h := hC s hs 0
    simp only [zero_dotProduct, Complex.ofReal_zero, mul_zero, add_zero] at h
    rw [hdual] at h
    exact h
  have hθ1 := theta_one_ne_zero G hpos
  have hC1 : C = 1 := by
    have h := hP 1 (by simp)
    simp only [Complex.one_cpow, one_pow, inv_one, mul_one] at h
    have h' : (C - 1) * theta G 1 = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · exact absurd h'' hθ1
  rw [hP s hs, hC1, one_mul]

/-- **Rank of an even unimodular lattice.** A positive-definite, even, unimodular integral
Gram matrix has size divisible by eight. Proof: the theta series is invariant under
`s ↦ s - i` (evenness) and satisfies `θ(1/s) = s^{n/2} θ(s)` (Poisson summation and
self-duality); following `1 → 1+i → (1+i)/2 → 1` gives `θ(1) = x^n θ(1)` with `x² = -i`,
and `θ(1) > 0`. -/
theorem rank_dvd_eight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z)))
    (hdet : IsUnit A.det) : 8 ∣ n := by
  set G := A.map (Int.cast : ℤ → ℝ) with hGdef
  have hP := theta_inversion A hpos hdet
  have hT := theta_shift A heven
  have hθ1 := theta_one_ne_zero G hpos
  have hre1 : 0 < (1 + I).re := by simp
  have hre2 : 0 < ((1 + I) / 2).re := by simp
  have e1 : (1 + I)⁻¹ = (1 + I) / 2 - I := by
    refine inv_eq_of_mul_eq_one_right ?_
    ring_nf; rw [I_sq]; ring
  have e2 : ((1 + I) / 2)⁻¹ = 1 - I := by
    refine inv_eq_of_mul_eq_one_right ?_
    ring_nf; rw [I_sq]; ring
  have h1 : theta G 1 = theta G (1 + I) := by
    have := hT (1 + I); rwa [add_sub_cancel_right] at this
  have h2 : theta G (1 + I) = (((1 + I) ^ (1 / 2 : ℂ)) ^ n)⁻¹ * theta G ((1 + I) / 2) := by
    rw [hP _ hre1, e1, hT]
  have h3 : theta G ((1 + I) / 2) = ((((1 + I) / 2) ^ (1 / 2 : ℂ)) ^ n)⁻¹ * theta G 1 := by
    rw [hP _ hre2, e2, hT]
  set x : ℂ := ((1 + I) ^ (1 / 2 : ℂ) * ((1 + I) / 2) ^ (1 / 2 : ℂ))⁻¹ with hxdef
  have hxn : x ^ n = 1 := by
    have h : theta G 1 = x ^ n * theta G 1 := by
      rw [hxdef, inv_pow, mul_pow, mul_inv, mul_assoc, ← h3, ← h2, ← h1]
    have h' : (x ^ n - 1) * theta G 1 = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · exact absurd h'' hθ1
  have hx2 : x ^ 2 = -I := by
    rw [hxdef, inv_pow, mul_pow, sq_half, sq_half]
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (-1 - I / 2) * I_sq
  have hx4 : x ^ 2 ^ 2 = -1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, hx2]; ring_nf; rw [I_sq]
  have hord : orderOf x = 2 ^ (2 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [hx4]; norm_num
    · rw [pow_succ, pow_mul, hx4]; norm_num
  have := orderOf_dvd_of_pow_eq_one hxn
  rw [hord] at this
  simpa using this

/-- Postulate M with the divisibility now proved: a nonzero positive-definite even
unimodular lattice of rank at most eight has rank exactly eight. -/
theorem minimal_rank_eight_of_lattice {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z)))
    (hdet : IsUnit A.det) (hn : 0 < n) (hle : n ≤ 8) : n = 8 :=
  PMArch.minimal_rank_eight hn (rank_dvd_eight A hpos heven hdet) hle

/-- The explicit E8 Gram matrix satisfies the hypotheses of `rank_dvd_eight`,
so they are consistent and the minimum rank eight is attained. -/
theorem e8_even_unimodular :
    (Lattices.gram.map (Int.cast : ℤ → ℝ)).PosDef ∧
      (∀ z : Fin 8 → ℤ, Even (z ⬝ᵥ (Lattices.gram *ᵥ z))) ∧ IsUnit Lattices.gram.det := by
  refine ⟨PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_, fun z => ?_,
    Lattices.gram_unimodular⟩
  · ext i j
    have h : Lattices.gram j i = Lattices.gram i j := by
      simpa using congrFun (congrFun Lattices.gram_symmetric i) j
    simp [conjTranspose_apply, h]
  · simpa [Lattices.realPairing] using Lattices.real_positive_norm x hx
  · obtain ⟨k, hk⟩ := Lattices.even_norm z
    exact ⟨k, by rw [← two_mul, ← hk]; rfl⟩

end Rank

end PMArch.RankEight
