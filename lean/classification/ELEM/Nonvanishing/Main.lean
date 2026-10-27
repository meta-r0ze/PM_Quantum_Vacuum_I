import ELEM.Hypotheses
import ELEM.Frobenius
import ELEM.Nonvanishing.Minor
import ELEM.Nonvanishing.Hermite
import ELEM.Nonvanishing.Params

/-!
# ELEM.Nonvanishing.Main: some `N × N` minor of `M q R` is nonzero

This proves `ELEM.Nonvanishing` (section 4.1 of the elementary companion,
twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae). The mechanism is van
Dijk's auxiliary-prime nonvanishing (hexagon 2610.00409v1, p. 2), which van Dijk states for odd
inert primes in `ℤ[√d]`; the setting `O_K = ℤ[ω]` with the auxiliary prime `R` itself is the
companion's.

Proof. Reduce mod `R` by `φ = redHom (cq q) R : ℤ[ω] → 𝔽_R[ω]`, a field of characteristic `R`
because `R` is inert. Frobenius is conjugation there (`pow_char_eq_star`, ELEM.Frobenius), so the
reduced matrix is entrywise `(r)_k x^(r-k) (x^R)^s` with `x = φ(z)` (`map_redHom_M`), the
derivative matrix of `ELEM.Nonvanishing.Hermite` with `w = x^R`. Its rows are independent, since
`J ≤ R`, `R S ≤ n J` and the reduced nodes are distinct (ELEM.Nonvanishing.Params). Independent
rows over the field give a nonzero maximal minor of the reduced matrix, and so of `M q R` itself
(ELEM.Nonvanishing.Minor).
-/

set_option autoImplicit false

open QuadraticAlgebra

namespace ELEM

/-- **The reduced matrix.** Mod an inert prime `R`, `M q R` is the derivative matrix of the reduced
nodes `x = φ(z)` with `w = x^R`: the entry `(r)_k z^(r-k) z̄^s` maps to `(r)_k x^(r-k) (x^R)^s`,
because `φ(z̄) = φ(z)̄ = φ(z)^R` (Frobenius is conjugation in `𝔽_R[ω]`). -/
theorem map_redHom_M (q R : ℕ) [Fact R.Prime] [Fact (IsInert (cq q) R)] :
    (M q R).map (redHom (cq q) R) =
      derivMatrix R (Sof R) (Jof R) (fun n => redHom (cq q) R (node q R n))
        (fun n => redHom (cq q) R (node q R n) ^ R) := by
  refine Matrix.ext fun rs zk => ?_
  simp only [Matrix.map_apply, M, derivMatrix, map_mul, map_pow, map_natCast, redHom_star,
    pow_char_eq_star]

/-- **Section 4.1 (van Dijk's auxiliary-prime nonvanishing)**: for an inert prime `R` with
`q⁴ < R ≤ q⁵`, some `N × N` minor of `M q R` is nonzero. -/
theorem nonvanishing : Nonvanishing := by
  intro q R hq hR hi h4 _h5
  have := Fact.mk hR
  have := Fact.mk hi
  have hq3 : 3 ≤ q := le_trans (by norm_num) hq.large
  have hLI : LinearIndependent (Fp2 (cq q) R) ((M q R).map (redHom (cq q) R)).row := by
    rw [map_redHom_M]
    exact derivMatrix_rows_linearIndependent R (Jof_le hR.one_lt.le)
      (R_mul_Sof_le R (by omega)) _
      (redHom_node_injective (two_A0_add_one_le hq3 h4) (two_B0_add_one_le hq3 h4))
  obtain ⟨f, -, hf⟩ := exists_det_submatrix_ne_zero_of_map (redHom (cq q) R) (M q R) hLI
  exact ⟨f, hf⟩

end ELEM
