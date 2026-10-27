import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# ELEM.Nonvanishing.Minor: full row rank gives a nonzero maximal minor

Over a field, a matrix with linearly independent rows has a square
submatrix, on an injective choice of columns, with nonzero determinant. Through a ring
homomorphism (for us, reduction modulo the auxiliary prime `R`), a minor that is nonzero after
reduction is nonzero before it; together these give the step "the rows are independent mod `R`, so
fix a nonzero `N × N` minor `D₀`" of the nonvanishing argument (van Dijk, hexagon 2610.00409v1,
p. 2, as used in section 4.1 of the elementary companion, twinheterodox/tenth-discriminant,
companions/elementary, commit 64694aae).
-/

set_option autoImplicit false

namespace ELEM

open Matrix Module

/-- Full row rank over a field gives a nonzero maximal minor: some injective choice of columns
`f : m → n` makes the square submatrix `A.submatrix id f` nonsingular. -/
theorem exists_det_submatrix_ne_zero {K : Type*} [Field K] {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] (A : Matrix m n K) (hA : LinearIndependent K A.row) :
    ∃ f : m → n, Function.Injective f ∧ (A.submatrix id f).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card m = Fintype.card κ := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hspan,
      ← rank_eq_finrank_span_cols, hA.rank_matrix]
  let e : m ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hcol : (A.submatrix id (a ∘ e)).col = A.col ∘ a ∘ e := by
    ext j i; rfl
  have hli' : LinearIndependent K (A.submatrix id (a ∘ e)).col := by
    rw [hcol]; exact hli.comp e e.injective
  exact ((isUnit_iff_isUnit_det _).mp (linearIndependent_cols_iff_isUnit.mp hli')).ne_zero

/-- A minor that is nonzero after a ring homomorphism is nonzero before it. -/
theorem det_submatrix_ne_zero_of_map {S F : Type*} [CommRing S] [CommRing F] (φ : S →+* F)
    {m n : Type*} [Fintype m] [DecidableEq m] (A : Matrix m n S) (f : m → n)
    (h : ((A.map φ).submatrix id f).det ≠ 0) : (A.submatrix id f).det ≠ 0 := by
  intro h0
  apply h
  rw [submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

/-- The two together: if the image of `A` under `φ` has linearly independent rows over the field
`F`, some maximal minor of `A` itself is nonzero. -/
theorem exists_det_submatrix_ne_zero_of_map {S F : Type*} [CommRing S] [Field F] (φ : S →+* F)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] (A : Matrix m n S)
    (hA : LinearIndependent F (A.map φ).row) :
    ∃ f : m → n, Function.Injective f ∧ (A.submatrix id f).det ≠ 0 := by
  obtain ⟨f, hf, hdet⟩ := exists_det_submatrix_ne_zero (A.map φ) hA
  exact ⟨f, hf, det_submatrix_ne_zero_of_map φ A f hdet⟩

end ELEM
