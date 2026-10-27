import Mathlib

/-!
# CN1.Finite.Params: the principal form's coefficients as functions of the radicand

For `K = ℚ(√-m)`, `m ≥ 1` squarefree, the ring of integers is `ℤ[ω]` with `ω² = t·ω - c`,
and the norm of `x + y·ω` is the principal form `Q(x, y) = x² + t·x·y + c·y²`:

* `m ≡ 3 (mod 4)`: `ω = (1 + √-m)/2`, `t = 1`, `c = (m + 1)/4`, `|disc K| = d = m`;
* otherwise:      `ω = √-m`,           `t = 0`, `c = m`,         `|disc K| = d = 4m`.

In both cases `4c - t² = d`. These are pure `ℕ`
functions so that the 190 witness instances can be checked by `decide`.
-/

namespace CN1.Finite

/-- The linear coefficient `t` of the principal form: `1` iff `m ≡ 3 (mod 4)`. -/
def tOf (m : ℕ) : ℕ := if m % 4 = 3 then 1 else 0

/-- The constant coefficient `c` of the principal form: `(m+1)/4` if `m ≡ 3 (mod 4)`, else `m`. -/
def cOf (m : ℕ) : ℕ := if m % 4 = 3 then (m + 1) / 4 else m

/-- The absolute discriminant `d = |disc ℚ(√-m)|`: `m` if `m ≡ 3 (mod 4)`, else `4m`. -/
def dOf (m : ℕ) : ℕ := if m % 4 = 3 then m else 4 * m

theorem tOf_eq_zero_or_one (m : ℕ) : tOf m = 0 ∨ tOf m = 1 := by
  unfold tOf; split_ifs <;> simp

theorem four_mul_cOf (m : ℕ) : 4 * cOf m = dOf m + tOf m ^ 2 := by
  unfold cOf dOf tOf; split_ifs with h <;> norm_num <;> omega

theorem le_dOf (m : ℕ) : m ≤ dOf m := by
  unfold dOf; split_ifs <;> omega

theorem tOf_of_mod (m : ℕ) (h : m % 4 = 3) : tOf m = 1 := by simp [tOf, h]

theorem four_mul_cOf_of_mod (m : ℕ) (h : m % 4 = 3) : 4 * cOf m = m + 1 := by
  simp only [cOf, h, if_true]; omega

theorem dOf_of_mod (m : ℕ) (h : m % 4 = 3) : dOf m = m := by simp [dOf, h]

end CN1.Finite
