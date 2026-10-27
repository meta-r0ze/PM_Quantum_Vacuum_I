import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# ELEM.Nonvanishing.Hermite: the reduced derivative matrix has independent rows

This is the mechanism of van Dijk's auxiliary-prime nonvanishing
(hexagon 2610.00409v1, p. 2, stated there for odd inert primes in `ℤ[√d]`), in the form the
elementary companion (twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae)
uses in its section 4.1 for `O_K = ℤ[ω]` and the auxiliary prime `R` itself.

* The root count: over a field in which `1, …, J - 1` are nonzero, a nonzero polynomial whose
  derivatives of orders `0, …, J - 1` vanish at each point of a finite set `Z` has degree at least
  `#Z * J`.
* The matrix form: in characteristic `R ≥ J`, the matrix with rows `(r, s)`, `r < R`, `s < S`,
  columns `(i, k)`, `i` a node, `k < J`, and entries `(r)_k x_i^(r-k) w_i^s` with `w_i = x_i ^ R`
  has linearly independent rows, provided the `x_i` are distinct and `R S ≤ (#nodes) J`. The reason
  is that `(r + R s)_k = (r)_k` in characteristic `R`, so the matrix is the Hermite-interpolation
  matrix of the one-variable monomials `X ^ (r + R s)`, whose exponents are distinct.

The node type is any finite type, so that the results apply to `ELEM.Node q R` directly.
-/

set_option autoImplicit false

namespace ELEM

open Polynomial

/-- Vanishing of the derivatives of orders `0, …, J - 1` at `t` gives root multiplicity at
least `J`, when `1, …, J - 1` are nonzero in `K`. -/
theorem le_rootMultiplicity_of_iterate_derivative {K : Type*} [Field K] {G : K[X]}
    (hG : G ≠ 0) {t : K} {J : ℕ} (hJ : ∀ m, m < J → m ≠ 0 → (m : K) ≠ 0)
    (hvan : ∀ k < J, (derivative^[k] G).eval t = 0) : J ≤ G.rootMultiplicity t := by
  rcases J with _ | n
  · exact Nat.zero_le _
  · refine Nat.succ_le_of_lt
      (lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' hG
        (fun m hm => hvan m (Nat.lt_succ_of_le hm)) ?_)
    intro m hm hm0
    exact mem_nonZeroDivisors_of_ne_zero (hJ m (Nat.lt_succ_of_le hm) hm0)

/-- The root count: order-`J` vanishing at the points of `Z` forces `natDegree ≥ #Z * J`. -/
theorem card_mul_le_natDegree_of_iterate_derivative {K : Type*} [Field K] {G : K[X]}
    (hG : G ≠ 0) (Z : Finset K) {J : ℕ} (hJ : ∀ m, m < J → m ≠ 0 → (m : K) ≠ 0)
    (hvan : ∀ z ∈ Z, ∀ k < J, (derivative^[k] G).eval z = 0) :
    Z.card * J ≤ G.natDegree := by
  classical
  have hle : J • Z.val ≤ G.roots := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_nsmul, count_roots]
    by_cases ha : a ∈ Z
    · rw [Multiset.count_eq_one_of_mem Z.nodup ha, mul_one]
      exact le_rootMultiplicity_of_iterate_derivative hG hJ (hvan a ha)
    · rw [Multiset.count_eq_zero_of_notMem ha, mul_zero]
      exact Nat.zero_le _
  calc Z.card * J = Multiset.card (J • Z.val) := by
        rw [Multiset.card_nsmul, mul_comm]; rfl
    _ ≤ Multiset.card G.roots := Multiset.card_le_card hle
    _ ≤ G.natDegree := card_roots' G

/-- In characteristic `p ≥ J`, a polynomial of degree `< #Z * J` that vanishes to order `J` at
every point of `Z` is zero. -/
theorem eq_zero_of_iterate_derivative_charP {K : Type*} [Field K] (p : ℕ) [CharP K p]
    {G : K[X]} (Z : Finset K) {J : ℕ} (hJp : J ≤ p) (hdeg : G.natDegree < Z.card * J)
    (hvan : ∀ z ∈ Z, ∀ k < J, (derivative^[k] G).eval z = 0) : G = 0 := by
  by_contra hG
  refine absurd (card_mul_le_natDegree_of_iterate_derivative hG Z ?_ hvan) (not_le.mpr hdeg)
  intro m hm hm0 h
  rw [CharP.cast_eq_zero_iff K p] at h
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h
  omega

/-- `(r + R s)_k = (r)_k` in characteristic `R` (falling factorials). -/
theorem descFactorial_add_mul_cast {K : Type*} [CommRing K] (R : ℕ) [CharP K R]
    (r s k : ℕ) : (((r + R * s).descFactorial k : ℕ) : K) = ((r.descFactorial k : ℕ) : K) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul, ih]
    by_cases hk : k ≤ r
    · rw [show r + R * s - k = (r - k) + R * s by omega, Nat.cast_add, Nat.cast_mul,
        CharP.cast_eq_zero K R, zero_mul, add_zero]
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, mul_zero, mul_zero]

/-- The `k`-th derivative of `X ^ (r + R s)` at `x` is the matrix entry `(r)_k x^(r-k) (x^R)^s`,
in characteristic `R`. -/
theorem eval_iterate_derivative_X_pow_add_mul {K : Type*} [CommRing K] (R : ℕ) [CharP K R]
    (r s k : ℕ) (x : K) :
    (derivative^[k] (X ^ (r + R * s) : K[X])).eval x
      = ((r.descFactorial k : ℕ) : K) * x ^ (r - k) * (x ^ R) ^ s := by
  rw [iterate_derivative_X_pow_eq_natCast_mul, eval_mul, eval_natCast, eval_pow, eval_X,
    descFactorial_add_mul_cast R]
  by_cases hk : k ≤ r
  · rw [show r + R * s - k = (r - k) + R * s by omega, pow_add, pow_mul, mul_assoc]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

/-- The derivative matrix over a ring `K`: rows `(r, s)`, columns `(i, k)` with `i` a node,
entry `(r)_k x_i^(r-k) w_i^s`. -/
def derivMatrix {K : Type*} [CommRing K] {ι : Type*} (R S J : ℕ) (x w : ι → K) :
    Matrix (Fin R × Fin S) (ι × Fin J) K :=
  fun p c => (((p.1 : ℕ).descFactorial c.2 : ℕ) : K) * x c.1 ^ ((p.1 : ℕ) - c.2)
    * w c.1 ^ (p.2 : ℕ)

/-- `(r, s) ↦ r + R s` is injective on `Fin R × Fin S`. -/
theorem add_mul_injective {R S : ℕ} {p q : Fin R × Fin S}
    (h : (p.1 : ℕ) + R * p.2 = q.1 + R * q.2) : p = q := by
  have hR : 0 < R := p.1.pos
  have h1 : (p.1 : ℕ) = q.1 := by
    have := congrArg (· % R) h
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.1.isLt, Nat.mod_eq_of_lt q.1.isLt]
      using this
  have h2 : (p.2 : ℕ) = q.2 := by
    have := congrArg (· / R) h
    simpa [Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt p.1.isLt, Nat.div_eq_of_lt q.1.isLt]
      using this
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- **The nonvanishing step for the reduced matrix** (van Dijk's mechanism), with abstract nodes:
in characteristic `R ≥ J`, with distinct nodes `x_i` and `R S ≤ (#nodes) J`, the derivative matrix
with `w_i = x_i ^ R` has linearly independent rows. A vanishing row combination `g` gives the
polynomial `G = ∑ g_(r,s) X^(r + R s)` of degree `< R S`, which vanishes to order `J` at every
node; so `G = 0`, and its coefficients `g` are `0` because the exponents are distinct. -/
theorem derivMatrix_rows_linearIndependent {K : Type*} [Field K] (R : ℕ) [CharP K R]
    {S J : ℕ} {ι : Type*} [Fintype ι] (hJR : J ≤ R) (hRS : R * S ≤ Fintype.card ι * J)
    (x : ι → K) (hx : Function.Injective x) :
    LinearIndependent K (derivMatrix R S J x (fun i => x i ^ R)).row := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have hRS0 : 0 < R * S := Nat.mul_pos p.1.pos p.2.pos
  let G : K[X] := ∑ q : Fin R × Fin S, C (g q) * X ^ ((q.1 : ℕ) + R * q.2)
  have hval : ∀ i : ι, ∀ k : Fin J, (derivative^[k] G).eval (x i) = 0 := by
    intro i k
    have h1 := congrFun hg (i, k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [← h1, iterate_derivative_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [iterate_derivative_C_mul, eval_mul, eval_C, eval_iterate_derivative_X_pow_add_mul R]
    simp only [Matrix.row, derivMatrix, mul_assoc]
  have hdeg : G.natDegree < (Finset.univ.image x).card * J := by
    rw [Finset.card_image_of_injective _ hx, Finset.card_univ]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := R * S - 1) ?_)
      (by omega)
    intro q _
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    have hq1 := q.1.isLt
    have hq2 := q.2.isLt
    have : R * (q.2 : ℕ) + R ≤ R * S := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hq2
    omega
  have hG : G = 0 := by
    refine eq_zero_of_iterate_derivative_charP R _ hJR hdeg ?_
    intro z hz k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact hval i ⟨k, hk⟩
  have hcoeff := congrArg (fun P : K[X] => P.coeff ((p.1 : ℕ) + R * p.2)) hG
  simp only [G, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hcoeff
  rw [Finset.sum_eq_single p] at hcoeff
  · simpa using hcoeff
  · intro q _ hqp
    split_ifs with h
    · exact absurd (add_mul_injective h).symm hqp
    · exact mul_zero _
  · intro hp; exact absurd (Finset.mem_univ p) hp

end ELEM
