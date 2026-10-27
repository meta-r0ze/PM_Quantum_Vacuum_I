import ELEM.Frobenius

/-!
# ELEM.Nonvanishing.Params: the parameter facts of the nonvanishing step

For the matrix `M q R` of the elementary companion's (10) (twinheterodox/tenth-discriminant,
companions/elementary, commit 64694aae), with `S = ⌊R/12⌋`,
`J = ⌈R/48⌉`, `A₀ = ⌈√(R √q)⌉`, `B₀ = ⌈√(R / √q)⌉` and `n = (2 A₀ + 1)(2 B₀ + 1)` nodes:

* `J ≤ R` (`Jof_le`);
* `A₀ B₀ ≥ R`, hence `n ≥ 4 R` and `R S ≤ n J` (`R_mul_Sof_le`);
* `2 A₀ + 1 ≤ R` and `2 B₀ + 1 ≤ R` once `q ≥ 3` and `R > q⁴` (`two_A0_add_one_le`,
  `two_B0_add_one_le`);
* hence the nodes stay distinct after reduction mod `R` (`redHom_node_injective`): the
  coordinates `a = i - A₀` and `b = j - B₀` of two nodes differ by less than `R`. This is the
  companion's "nodes are distinct mod `R`", proved coordinatewise rather than through the norm.
-/

set_option autoImplicit false

open QuadraticAlgebra

namespace ELEM

/-- `J = ⌈R/48⌉ ≤ R` for `R ≥ 1`. -/
theorem Jof_le {R : ℕ} (hR : 1 ≤ R) : Jof R ≤ R := by
  unfold Jof; omega

/-- `A₀ B₀ ≥ R`, because `A₀ ≥ √(R √q)`, `B₀ ≥ √(R / √q)` and the product of the square roots is
`R`. -/
theorem le_A0_mul_B0 {q : ℕ} (R : ℕ) (hq : 0 < q) : R ≤ A0 q R * B0 q R := by
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have key : (R : ℝ) ≤ (A0 q R : ℝ) * B0 q R := by
    calc (R : ℝ) = √((R : ℝ) * √q) * √((R : ℝ) / √q) := by
          rw [← Real.sqrt_mul (by positivity),
            show (R : ℝ) * √q * (R / √q) = R * R by field_simp, Real.sqrt_mul_self hR0]
      _ ≤ A0 q R * B0 q R :=
          mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  exact_mod_cast key

/-- The node count: `#Node = (2 A₀ + 1)(2 B₀ + 1) ≥ 4 R`. -/
theorem four_mul_le_card_node {q : ℕ} (R : ℕ) (hq : 0 < q) :
    4 * R ≤ Fintype.card (Node q R) := by
  have h := le_A0_mul_B0 R hq
  simp only [Node, Fintype.card_prod, Fintype.card_fin]
  nlinarith

/-- `R S ≤ n J`, from `12 S ≤ R ≤ 48 J` and `n ≥ 4 R`. -/
theorem R_mul_Sof_le {q : ℕ} (R : ℕ) (hq : 0 < q) :
    R * Sof R ≤ Fintype.card (Node q R) * Jof R := by
  have hn := four_mul_le_card_node R hq
  have h12 : 12 * Sof R ≤ R := by unfold Sof; omega
  have h48 : R ≤ 48 * Jof R := by unfold Jof; omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 48 by norm_num)
  calc 48 * (R * Sof R) = 4 * R * (12 * Sof R) := by ring
    _ ≤ 4 * R * R := Nat.mul_le_mul_left _ h12
    _ ≤ Fintype.card (Node q R) * (48 * Jof R) := Nat.mul_le_mul hn h48
    _ = 48 * (Fintype.card (Node q R) * Jof R) := by ring

/-- If `16 x ≤ R²` and `R ≥ 6`, then `2 ⌈√x⌉ + 1 ≤ R`. -/
theorem two_ceil_sqrt_add_one_le {x : ℝ} {R : ℕ} (hx : 16 * x ≤ (R : ℝ) ^ 2)
    (hR : 6 ≤ R) : 2 * ⌈√x⌉₊ + 1 ≤ R := by
  have hR6 : (6 : ℝ) ≤ R := by exact_mod_cast hR
  have hs : √x ≤ (R : ℝ) / 4 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : ((R : ℝ) / 4) ^ 2 = (R : ℝ) ^ 2 / 16 := by ring
    rw [this]; linarith
  have hc : (⌈√x⌉₊ : ℝ) < √x + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have : ((2 * ⌈√x⌉₊ + 1 : ℕ) : ℝ) < R := by push_cast; linarith
  exact (by exact_mod_cast this : 2 * ⌈√x⌉₊ + 1 < R).le

/-- `16 q < R` and `16 ≤ R`, from `q ≥ 3` and `R > q⁴`. -/
theorem sixteen_mul_lt {q R : ℕ} (hq : 3 ≤ q) (hR : q ^ 4 < R) : 16 * q < R ∧ 16 ≤ R := by
  have h9 : 9 ≤ q * q := Nat.mul_le_mul hq hq
  have h27 : 27 ≤ q * q * q := Nat.mul_le_mul h9 hq
  have h4 : q ^ 4 = q * q * q * q := by ring
  have : 16 * q ≤ q * q * q * q := Nat.mul_le_mul_right q (by omega)
  constructor <;> nlinarith

/-- `2 A₀ + 1 ≤ R` for `q ≥ 3` and `R > q⁴`: `16 R √q ≤ R²` since `16 √q ≤ 16 q < R`. -/
theorem two_A0_add_one_le {q R : ℕ} (hq : 3 ≤ q) (hR : q ^ 4 < R) : 2 * A0 q R + 1 ≤ R := by
  obtain ⟨h16q, h16⟩ := sixteen_mul_lt hq hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hsq : √(q : ℝ) ≤ q :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ q by omega)))
  have h16q' : (16 : ℝ) * q < R := by exact_mod_cast h16q
  have hmain : 16 * ((R : ℝ) * √q) ≤ (R : ℝ) ^ 2 := by
    have : 16 * √(q : ℝ) ≤ R := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hR0]
  exact two_ceil_sqrt_add_one_le hmain (by omega)

/-- `2 B₀ + 1 ≤ R` for `q ≥ 3` and `R > q⁴`: `16 R / √q ≤ 16 R ≤ R²`. -/
theorem two_B0_add_one_le {q R : ℕ} (hq : 3 ≤ q) (hR : q ^ 4 < R) : 2 * B0 q R + 1 ≤ R := by
  obtain ⟨-, h16⟩ := sixteen_mul_lt hq hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have h16' : (16 : ℝ) ≤ R := by exact_mod_cast h16
  have h1 : (1 : ℝ) ≤ √(q : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
    rw [one_pow]; exact_mod_cast (show 1 ≤ q by omega)
  have hdiv : (R : ℝ) / √q ≤ R := div_le_self hR0 h1
  have hmain : 16 * ((R : ℝ) / √q) ≤ (R : ℝ) ^ 2 := by nlinarith
  exact two_ceil_sqrt_add_one_le hmain (by omega)

/-- **The nodes are distinct mod `R`.** If `2 A₀ + 1 ≤ R` and `2 B₀ + 1 ≤ R`, reduction mod `R`
is injective on the nodes: two nodes with the same image have coordinates congruent mod `R` and
differing by less than `R`. -/
theorem redHom_node_injective {q R : ℕ} (hA : 2 * A0 q R + 1 ≤ R) (hB : 2 * B0 q R + 1 ≤ R) :
    Function.Injective (fun n : Node q R => redHom (cq q) R (node q R n)) := by
  intro n n' h
  have hre := congrArg QuadraticAlgebra.re h
  have him := congrArg QuadraticAlgebra.im h
  simp only [redHom_re, redHom_im, node] at hre him
  push_cast at hre him
  rw [sub_left_inj] at hre him
  have h1 := n.1.isLt
  have h1' := n'.1.isLt
  have h2 := n.2.isLt
  have h2' := n'.2.isLt
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    at hre him
  exact Prod.ext (Fin.ext hre) (Fin.ext him)

end ELEM
