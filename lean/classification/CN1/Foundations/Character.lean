import CN1.Foundations.Basic

/-!
# The Kronecker character `χ_{-d}` as a Mathlib `DirichletCharacter ℂ d`

Pinned environment: Lean v4.34.1, Mathlib d13f23b.

For squarefree `m ≥ 1` with `d = disc m` (`m` if `m ≡ 3 (mod 4)`, else `4m`), we build
`kroneckerChar m : DirichletCharacter ℂ (disc m)`, the real primitive character of `ℚ(√-m)`:

* `m ≡ 3 (mod 4)`: `a ↦ J(a | m)`, the Jacobi symbol, at level `m`;
* `m ≡ 1 (mod 4)`: `χ₄ · J(· | m)` at level `4m`;
* `m ≡ 2 (mod 4)`, `m = 2m'`: `χ₈' · J(· | m')` if `m' ≡ 1 (mod 4)`, `χ₈ · J(· | m')` if
  `m' ≡ 3 (mod 4)`, at level `8m' = 4m`;

all lifted to level `disc m` by `DirichletCharacter.changeLevel`. We prove it is quadratic
(`kroneckerChar_isQuadratic`), odd (`kroneckerChar_neg_one : χ(-1) = -1`, hence
`kroneckerChar_ne_one`), and compute its values at primes: for an odd prime `p ∤ d`,
`χ(p) = (-m / p)` is the Legendre symbol (`kroneckerChar_apply_prime_of_ne_two`), and for
`m ≡ 3 (mod 4)`, `χ(2) = χ₈(m)` (`kroneckerChar_apply_two`). The proofs are quadratic
reciprocity for the Jacobi symbol (`jacobiSym.quadratic_reciprocity_*`) and the supplementary
laws (`jacobiSym.at_neg_one`, `legendreSym.at_neg`, `legendreSym.at_neg_two`).

Mathlib-only.
-/

set_option autoImplicit false

namespace CN1.Foundations

open ZMod
open DirichletCharacter (changeLevel changeLevel_eq_cast_of_dvd changeLevel_eq_cast_of_dvd')

/-! ### The Jacobi-symbol character `a ↦ J(a | n)` at level `n`. -/

section JacobiChar

/-- `J(a.val | n)` depends only on the class of `a` in `ZMod n`. -/
lemma jacobiSym_val_eq (n : ℕ) [NeZero n] (a : ZMod n) (k : ℤ) (hk : (k : ZMod n) = a) :
    jacobiSym a.val n = jacobiSym k n := by
  apply jacobiSym.mod_left'
  rw [← ZMod.intCast_eq_intCast_iff']
  simp [hk]

/-- The Jacobi-symbol character `a ↦ J(a | n)` as a Dirichlet character of level `n`. -/
noncomputable def jacobiChar (n : ℕ) [NeZero n] : DirichletCharacter ℂ n where
  toFun a := (jacobiSym a.val n : ℂ)
  map_one' := by
    show (jacobiSym (1 : ZMod n).val n : ℂ) = 1
    rw [jacobiSym_val_eq n 1 1 (by simp), jacobiSym.one_left]; simp
  map_mul' a b := by
    show (jacobiSym (a * b).val n : ℂ) = (jacobiSym a.val n : ℂ) * (jacobiSym b.val n : ℂ)
    rw [jacobiSym_val_eq n (a * b) (a.val * b.val) (by simp), jacobiSym.mul_left]
    push_cast; rfl
  map_nonunit' a ha := by
    show (jacobiSym a.val n : ℂ) = 0
    have hc : ¬ Nat.Coprime a.val n := by
      rwa [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    have : jacobiSym a.val n = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hc
    rw [this]; simp

lemma jacobiChar_apply (n : ℕ) [NeZero n] (a : ZMod n) :
    jacobiChar n a = (jacobiSym a.val n : ℂ) := rfl

theorem jacobiChar_intCast (n : ℕ) [NeZero n] (k : ℤ) :
    jacobiChar n (k : ZMod n) = (jacobiSym k n : ℂ) := by
  rw [jacobiChar_apply, jacobiSym_val_eq n _ k rfl]

theorem jacobiChar_natCast (n : ℕ) [NeZero n] (k : ℕ) :
    jacobiChar n (k : ZMod n) = (jacobiSym k n : ℂ) := by
  rw [← Int.cast_natCast, jacobiChar_intCast]

theorem jacobiChar_isQuadratic (n : ℕ) [NeZero n] : (jacobiChar n).IsQuadratic := by
  intro a
  rw [jacobiChar_apply]
  rcases jacobiSym.trichotomy a.val n with h | h | h <;> rw [h] <;> norm_num

end JacobiChar

/-! ### `χ₄`, `χ₈`, `χ₈'` with values in `ℂ`. -/

/-- `χ₄` with values in `ℂ`. -/
noncomputable def chi4 : DirichletCharacter ℂ 4 := χ₄.ringHomComp (Int.castRingHom ℂ)

/-- `χ₈` with values in `ℂ`. -/
noncomputable def chi8 : DirichletCharacter ℂ 8 := χ₈.ringHomComp (Int.castRingHom ℂ)

/-- `χ₈'` with values in `ℂ`. -/
noncomputable def chi8' : DirichletCharacter ℂ 8 := χ₈'.ringHomComp (Int.castRingHom ℂ)

lemma chi4_apply (a : ZMod 4) : chi4 a = (χ₄ a : ℂ) := rfl
lemma chi8_apply (a : ZMod 8) : chi8 a = (χ₈ a : ℂ) := rfl
lemma chi8'_apply (a : ZMod 8) : chi8' a = (χ₈' a : ℂ) := rfl

lemma chi4_isQuadratic : chi4.IsQuadratic := isQuadratic_χ₄.comp _
lemma chi8_isQuadratic : chi8.IsQuadratic := isQuadratic_χ₈.comp _
lemma chi8'_isQuadratic : chi8'.IsQuadratic := isQuadratic_χ₈'.comp _

/-! ### Quadratic characters are closed under `changeLevel` and products. -/

section Quadratic

variable {R : Type*} [CommRing R]

lemma isQuadratic_changeLevel {n N : ℕ} (h : n ∣ N) {ψ : DirichletCharacter R n}
    (hψ : ψ.IsQuadratic) : (changeLevel h ψ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [changeLevel_eq_cast_of_dvd]
    exact hψ _
  · left; exact MulChar.map_nonunit _ ha

lemma isQuadratic_mul {M : Type*} [CommMonoid M] {χ ψ : MulChar M R}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) : (χ * ψ).IsQuadratic := by
  intro a
  rw [MulChar.mul_apply]
  rcases hχ a with h | h | h <;> rcases hψ a with h' | h' | h' <;> simp [h, h']

lemma isQuadratic_one {M : Type*} [CommMonoid M] [Nontrivial R] :
    (1 : MulChar M R).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · right; left; exact MulChar.one_apply ha
  · left; exact MulChar.map_nonunit _ ha

end Quadratic

/-! ### The Kronecker character `χ_{-d}`. -/

section Kronecker

variable {m : ℕ}

lemma four_dvd_disc (h3 : m % 4 ≠ 3) : 4 ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact dvd_mul_right 4 m

lemma dvd_disc (h3 : m % 4 ≠ 3) : m ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact dvd_mul_left m 4

lemma eight_dvd_disc (h3 : m % 4 ≠ 3) (h2 : m % 2 = 0) : 8 ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact ⟨m / 2, by omega⟩

lemma half_dvd_disc (h3 : m % 4 ≠ 3) (h2 : m % 2 = 0) : m / 2 ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact ⟨8, by omega⟩

/-- **The Kronecker character** `χ_{-d}`, `d = disc m`, as a Dirichlet character of level `d`.
For `m = 0` (excluded by `Squarefree m`) it is the trivial character. -/
noncomputable def kroneckerChar (m : ℕ) : DirichletCharacter ℂ (disc m) :=
  if h0 : m = 0 then 1
  else if h3 : m % 4 = 3 then
    changeLevel (dvd_of_eq (disc_of_three_mod_four h3).symm) (@jacobiChar m ⟨h0⟩)
  else if h2 : m % 2 = 1 then
    changeLevel (four_dvd_disc h3) chi4 * changeLevel (dvd_disc h3) (@jacobiChar m ⟨h0⟩)
  else
    changeLevel (eight_dvd_disc h3 (by omega)) (if m / 2 % 4 = 1 then chi8' else chi8) *
      changeLevel (half_dvd_disc h3 (by omega)) (@jacobiChar (m / 2) ⟨by omega⟩)

/-- Case `m ≡ 3 (mod 4)`: `χ(a) = J(a | m)` for `a` coprime to `d = m`. -/
theorem kroneckerChar_apply_of_three_mod_four (h3 : m % 4 = 3) {a : ℤ}
    (ha : IsCoprime a (disc m)) : kroneckerChar m (a : ZMod (disc m)) = (jacobiSym a m : ℂ) := by
  have h0 : m ≠ 0 := by omega
  simp only [kroneckerChar, h0, h3, ↓reduceDIte]
  rw [changeLevel_eq_cast_of_dvd' _ _ ha, jacobiChar_intCast]

/-- Case `m ≡ 1 (mod 4)`: `χ(a) = χ₄(a) J(a | m)` for `a` coprime to `d = 4m`. -/
theorem kroneckerChar_apply_of_one_mod_four (h1 : m % 4 = 1) {a : ℤ}
    (ha : IsCoprime a (disc m)) :
    kroneckerChar m (a : ZMod (disc m)) = (χ₄ a : ℂ) * (jacobiSym a m : ℂ) := by
  have h0 : m ≠ 0 := by omega
  have h3 : m % 4 ≠ 3 := by omega
  have h2 : m % 2 = 1 := by omega
  simp only [kroneckerChar, h0, h3, h2, ↓reduceDIte]
  rw [MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ ha, changeLevel_eq_cast_of_dvd' _ _ ha,
    jacobiChar_intCast, chi4_apply]

/-- Case `m ≡ 2 (mod 4)`, `m = 2m'`: `χ(a) = χ₈'(a) J(a | m')` if `m' ≡ 1 (mod 4)`, and
`χ(a) = χ₈(a) J(a | m')` if `m' ≡ 3 (mod 4)`, for `a` coprime to `d = 8m'`. -/
theorem kroneckerChar_apply_of_two_mod_four (h2 : m % 4 = 2) {a : ℤ}
    (ha : IsCoprime a (disc m)) :
    kroneckerChar m (a : ZMod (disc m)) =
      (if m / 2 % 4 = 1 then (χ₈' a : ℂ) else (χ₈ a : ℂ)) * (jacobiSym a (m / 2) : ℂ) := by
  have h0 : m ≠ 0 := by omega
  have h3 : m % 4 ≠ 3 := by omega
  have h2' : ¬ m % 2 = 1 := by omega
  simp only [kroneckerChar, h0, h3, h2', ↓reduceDIte]
  rw [MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ ha, changeLevel_eq_cast_of_dvd' _ _ ha,
    jacobiChar_intCast]
  split_ifs <;> rfl

/-- `χ_{-d}` is a quadratic character (values in `{0, 1, -1}`). -/
theorem kroneckerChar_isQuadratic (m : ℕ) : (kroneckerChar m).IsQuadratic := by
  by_cases h0 : m = 0
  · simp only [kroneckerChar, h0, ↓reduceDIte]
    exact isQuadratic_one
  have : NeZero m := ⟨h0⟩
  by_cases h3 : m % 4 = 3
  · simp only [kroneckerChar, h0, h3, ↓reduceDIte]
    exact isQuadratic_changeLevel _ (jacobiChar_isQuadratic m)
  by_cases h2 : m % 2 = 1
  · simp only [kroneckerChar, h0, h3, h2, ↓reduceDIte]
    exact isQuadratic_mul (isQuadratic_changeLevel _ chi4_isQuadratic)
      (isQuadratic_changeLevel _ (jacobiChar_isQuadratic m))
  · have : NeZero (m / 2) := ⟨by omega⟩
    simp only [kroneckerChar, h0, h3, h2, ↓reduceDIte]
    refine isQuadratic_mul (isQuadratic_changeLevel _ ?_)
      (isQuadratic_changeLevel _ (jacobiChar_isQuadratic (m / 2)))
    split_ifs
    · exact chi8'_isQuadratic
    · exact chi8_isQuadratic

lemma squarefree_mod_four_cases (hm : Squarefree m) : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
  have := squarefree_mod_four_ne_zero hm; omega

/-- **`χ_{-d}` is odd**: `χ(-1) = -1`. -/
theorem kroneckerChar_neg_one (hm : Squarefree m) : kroneckerChar m (-1) = -1 := by
  have hcop : IsCoprime (-1 : ℤ) (disc m : ℤ) := isCoprime_one_left.neg_left
  have hcast : (-1 : ZMod (disc m)) = ((-1 : ℤ) : ZMod (disc m)) := by simp
  rw [hcast]
  rcases squarefree_mod_four_cases hm with h1 | h2 | h3
  · rw [kroneckerChar_apply_of_one_mod_four h1 hcop,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), χ₄_nat_one_mod_four h1,
      χ₄_int_three_mod_four (by decide)]
    simp
  · rw [kroneckerChar_apply_of_two_mod_four h2 hcop,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega))]
    have hm' : m / 2 % 4 = 1 ∨ m / 2 % 4 = 3 := by omega
    rcases hm' with h | h
    · rw [if_pos h, χ₄_nat_one_mod_four h, χ₈'_int_eq_if_mod_eight]
      norm_num
    · rw [if_neg (by omega), χ₄_nat_three_mod_four h, χ₈_int_eq_if_mod_eight]
      norm_num
  · rw [kroneckerChar_apply_of_three_mod_four h3 hcop,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), χ₄_nat_three_mod_four h3]
    simp

/-- **`χ_{-d}` is non-trivial.** -/
theorem kroneckerChar_ne_one (hm : Squarefree m) : kroneckerChar m ≠ 1 := by
  intro h
  have h1 := kroneckerChar_neg_one hm
  rw [h, MulChar.one_apply isUnit_one.neg] at h1
  norm_num at h1

/-! ### Values at primes: `χ(p) = (-m / p)`. -/

section Values

variable {p : ℕ} [hp : Fact p.Prime]

/-- `m ≡ 3 (mod 4)`, `p` an odd prime: `J(p | m) = (-m / p)`. -/
lemma jacobiSym_eq_legendreSym_neg_of_three_mod_four (h3 : m % 4 = 3) (hp2 : p ≠ 2) :
    jacobiSym p m = legendreSym p (-(m : ℤ)) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  rw [legendreSym.at_neg hp2, jacobiSym.legendreSym.to_jacobiSym]
  rcases Nat.odd_mod_four_iff.mp hpodd with h1 | h1
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 (Nat.odd_iff.mpr (by omega)),
      χ₄_nat_one_mod_four h1, one_mul]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four h1 h3, χ₄_nat_three_mod_four h1,
      neg_one_mul]

/-- `m ≡ 1 (mod 4)`, `p` an odd prime: `χ₄(p) J(p | m) = (-m / p)`. -/
lemma chi4_mul_jacobiSym_eq_legendreSym_neg_of_one_mod_four (h1 : m % 4 = 1) (hp2 : p ≠ 2) :
    χ₄ p * jacobiSym p m = legendreSym p (-(m : ℤ)) := by
  have hpodd : _root_.Odd p := hp.out.odd_of_ne_two hp2
  rw [legendreSym.at_neg hp2, jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym.quadratic_reciprocity_one_mod_four' hpodd h1]

/-- `m = 2m'` with `m'` odd, `p` an odd prime: `ψ(p) J(p | m') = (-m / p)`, where `ψ = χ₈'` if
`m' ≡ 1 (mod 4)` and `ψ = χ₈` if `m' ≡ 3 (mod 4)`. -/
lemma chi8_mul_jacobiSym_eq_legendreSym_neg_of_two_mod_four (h2 : m % 4 = 2) (hp2 : p ≠ 2) :
    (if m / 2 % 4 = 1 then χ₈' p else χ₈ p) * jacobiSym p (m / 2) = legendreSym p (-(m : ℤ)) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hm : (m : ℤ) = 2 * ((m / 2 : ℕ) : ℤ) := by push_cast; omega
  have hm'odd : _root_.Odd (m / 2) := Nat.odd_iff.mpr (by omega)
  rw [hm, neg_mul_eq_neg_mul, legendreSym.mul, legendreSym.at_neg_two hp2,
    jacobiSym.legendreSym.to_jacobiSym]
  have hm' : m / 2 % 4 = 1 ∨ m / 2 % 4 = 3 := by omega
  rcases hm' with h | h
  · rw [if_pos h, jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hpodd) h]
  · rw [if_neg (by omega)]
    have h8 : χ₈' (p : ZMod 8) = χ₄ (p : ZMod 4) * χ₈ (p : ZMod 8) := by
      have := χ₈'_int_eq_χ₄_mul_χ₈ (p : ℤ)
      simpa using this
    rw [h8]
    rcases Nat.odd_mod_four_iff.mp hpodd with h1 | h1
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hm'odd, χ₄_nat_one_mod_four h1, one_mul]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four h1 h, χ₄_nat_three_mod_four h1]
      ring

/-- **The value of `χ_{-d}` at an odd prime `p ∤ d`** is the Legendre symbol `(-m / p)`. -/
theorem kroneckerChar_apply_prime_of_ne_two (hm : Squarefree m) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = (legendreSym p (-(m : ℤ)) : ℂ) := by
  have hcop : IsCoprime (p : ℤ) (disc m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpd)
  rw [← Int.cast_natCast (R := ZMod (disc m))]
  rcases squarefree_mod_four_cases hm with h1 | h2 | h3
  · rw [kroneckerChar_apply_of_one_mod_four h1 hcop,
      ← chi4_mul_jacobiSym_eq_legendreSym_neg_of_one_mod_four h1 hp2]
    push_cast
    try rfl
  · rw [kroneckerChar_apply_of_two_mod_four h2 hcop,
      ← chi8_mul_jacobiSym_eq_legendreSym_neg_of_two_mod_four h2 hp2]
    split_ifs <;> push_cast <;> try rfl
  · rw [kroneckerChar_apply_of_three_mod_four h3 hcop,
      ← jacobiSym_eq_legendreSym_neg_of_three_mod_four h3 hp2]

/-- **The value of `χ_{-d}` at `2`** when `d = m ≡ 3 (mod 4)` is `χ₈(m)`: `1` if `m ≡ 7 (mod 8)`
(2 splits), `-1` if `m ≡ 3 (mod 8)` (2 is inert). -/
theorem kroneckerChar_apply_two (h3 : m % 4 = 3) :
    kroneckerChar m (2 : ZMod (disc m)) = (χ₈ (m : ZMod 8) : ℂ) := by
  have hodd : _root_.Odd m := Nat.odd_iff.mpr (by omega)
  have hcop : IsCoprime (2 : ℤ) (disc m : ℤ) := by
    rw [disc_of_three_mod_four h3]
    have : IsCoprime ((2 : ℕ) : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_left.mpr hodd)
    exact_mod_cast this
  have hcast : (2 : ZMod (disc m)) = ((2 : ℤ) : ZMod (disc m)) := by simp
  rw [hcast, kroneckerChar_apply_of_three_mod_four h3 hcop, jacobiSym.at_two hodd]

lemma neg_natCast_ne_zero_of_not_dvd_disc (hpd : ¬ p ∣ disc m) : (-(m : ZMod p)) ≠ 0 := by
  rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  refine hpd (h.trans ?_)
  unfold disc; split_ifs
  · exact dvd_rfl
  · exact dvd_mul_left m 4

/-- For an odd prime `p ∤ d`: `χ(p) = 1 ↔ -m` is a square mod `p`. -/
theorem kroneckerChar_apply_prime_eq_one_iff (hm : Squarefree m) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 1 ↔ IsSquare (-(m : ZMod p)) := by
  rw [kroneckerChar_apply_prime_of_ne_two hm hp2 hpd]
  have hne : ((-(m : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast; exact neg_natCast_ne_zero_of_not_dvd_disc hpd
  have := legendreSym.eq_one_iff p hne
  push_cast at this
  rw [← this]
  norm_cast

/-- For an odd prime `p ∤ d`: `χ(p) = -1 ↔ -m` is not a square mod `p`. -/
theorem kroneckerChar_apply_prime_eq_neg_one_iff (hm : Squarefree m) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = -1 ↔ ¬ IsSquare (-(m : ZMod p)) := by
  rw [kroneckerChar_apply_prime_of_ne_two hm hp2 hpd]
  have := legendreSym.eq_neg_one_iff p (a := -(m : ℤ))
  push_cast at this
  rw [← this]
  norm_cast

end Values

end Kronecker

end CN1.Foundations
